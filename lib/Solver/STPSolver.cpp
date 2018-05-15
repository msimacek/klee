//===-- STPSolver.cpp -----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#ifdef ENABLE_STP
#include "STPSolver.h"
#include "STPBuilder.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/Constraints.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/ErrorHandling.h"

#include <errno.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/shm.h>

namespace {

llvm::cl::opt<bool> DebugDumpSTPQueries(
    "debug-dump-stp-queries", llvm::cl::init(false),
    llvm::cl::desc("Dump every STP query to stderr (default=off)"));

llvm::cl::opt<bool> IgnoreSolverFailures(
    "ignore-solver-failures", llvm::cl::init(false),
    llvm::cl::desc("Ignore any solver failures (default=off)"));
}

#define vc_bvBoolExtract IAMTHESPAWNOFSATAN

static unsigned char *shared_memory_ptr;
static int shared_memory_id = 0;
// Darwin by default has a very small limit on the maximum amount of shared
// memory, which will quickly be exhausted by KLEE running its tests in
// parallel. For now, we work around this by just requesting a smaller size --
// in practice users hitting this limit on counterexample sizes probably already
// are hitting more serious scalability issues.
#ifdef __APPLE__
static const unsigned shared_memory_size = 1 << 16;
#else
static const unsigned shared_memory_size = 1 << 20;
#endif

static void stp_error_handler(const char *err_msg) {
  fprintf(stderr, "error: STP Error: %s\n", err_msg);
  abort();
}

namespace klee {

class STPSolverImpl : public SolverImpl {
private:
  VC vc;
  STPBuilder *builder;
  double timeout;
  bool useForkedSTP;
  SolverRunStatus runStatusCode;

public:
  STPSolverImpl(bool _useForkedSTP, bool _optimizeDivides = true);
  ~STPSolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) { timeout = _timeout; }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &query,
                            std::shared_ptr<const Assignment> &result,
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
};

STPSolverImpl::STPSolverImpl(bool _useForkedSTP, bool _optimizeDivides)
    : vc(vc_createValidityChecker()),
      builder(new STPBuilder(vc, _optimizeDivides)), timeout(0.0),
      useForkedSTP(_useForkedSTP), runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
  assert(vc && "unable to create validity checker");
  assert(builder && "unable to create STPBuilder");

  // In newer versions of STP, a memory management mechanism has been
  // introduced that automatically invalidates certain C interface
  // pointers at vc_Destroy time.  This caused double-free errors
  // due to the ExprHandle destructor also attempting to invalidate
  // the pointers using vc_DeleteExpr.  By setting EXPRDELETE to 0
  // we restore the old behaviour.
  vc_setInterfaceFlags(vc, EXPRDELETE, 0);

  make_division_total(vc);

  vc_registerErrorHandler(::stp_error_handler);

  if (useForkedSTP) {
    assert(shared_memory_id == 0 && "shared memory id already allocated");
    shared_memory_id =
        shmget(IPC_PRIVATE, shared_memory_size, IPC_CREAT | 0700);
    if (shared_memory_id < 0)
      llvm::report_fatal_error("unable to allocate shared memory region");
    shared_memory_ptr = (unsigned char *)shmat(shared_memory_id, NULL, 0);
    if (shared_memory_ptr == (void *)-1)
      llvm::report_fatal_error("unable to attach shared memory region");
    shmctl(shared_memory_id, IPC_RMID, NULL);
  }
}

STPSolverImpl::~STPSolverImpl() {
  // Detach the memory region.
  shmdt(shared_memory_ptr);
  shared_memory_ptr = 0;
  shared_memory_id = 0;

  delete builder;

  vc_Destroy(vc);
}

/***/

char *STPSolverImpl::getConstraintLog(const Query &query) {
  vc_push(vc);
  for (std::vector<ref<Expr> >::const_iterator it = query.constraints.begin(),
                                               ie = query.constraints.end();
       it != ie; ++it)
    vc_assertFormula(vc, builder->construct(*it));
  assert(query.expr == ConstantExpr::alloc(0, Expr::Bool) &&
         "Unexpected expression in query!");

  char *buffer;
  unsigned long length;
  vc_printQueryStateToBuffer(vc, builder->getFalse(), &buffer, &length, false);
  vc_pop(vc);

  return buffer;
}

bool STPSolverImpl::computeTruth(const Query &query, bool &isValid) {
  std::shared_ptr<const Assignment> result;
  bool hasSolution;

  if (!computeInitialValues(query, result, hasSolution))
    return false;

  isValid = !hasSolution;
  return true;
}

bool STPSolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::shared_ptr<const Assignment> assignment;
  bool hasSolution;

  if (!computeInitialValues(query.withFalse(), assignment, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  result = assignment->evaluate(query.expr);

  return true;
}

static SolverImpl::SolverRunStatus
runAndGetCex(::VC vc, STPBuilder *builder, ::VCExpr q,
             const std::vector<ref<ReadExpr> > &reads,
             std::shared_ptr<const Assignment>& result,
             bool &hasSolution) {
  // XXX I want to be able to timeout here, safely
  hasSolution = !vc_query(vc, q);

  if (hasSolution) {
    Assignment::map_bindings_ty bindings;
    for (ref<ReadExpr> read : reads) {
      const Array *array = read->updates.root;
      ExprHandle indexExpr =
          vc_getCounterExample(vc, builder->construct(read->index));
      unsigned index = getBVUnsigned(indexExpr);
      ExprHandle valueExpr =
          vc_getCounterExample(vc, builder->getInitialRead(array, index));
      unsigned value = getBVUnsigned(valueExpr);
      bindings[read->updates.root].add(index, value);
    }
    result = std::make_shared<Assignment>(bindings);
  }

  if (true == hasSolution) {
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  } else {
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  }
}

static void stpTimeoutHandler(int x) { _exit(52); }

static SolverImpl::SolverRunStatus
runAndGetCexForked(::VC vc, STPBuilder *builder, ::VCExpr q,
                   const std::vector<ref<ReadExpr> > &reads,
                   std::shared_ptr<const Assignment>& result,
                   bool &hasSolution, double timeout) {
  fflush(stdout);
  fflush(stderr);
  int pid = fork();
  if (pid == -1) {
    klee_warning("fork failed (for STP) - %s", llvm::sys::StrError(errno).c_str());
    if (!IgnoreSolverFailures)
      exit(1);
    return SolverImpl::SOLVER_RUN_STATUS_FORK_FAILED;
  }

  if (pid == 0) {
    if (timeout) {
      ::alarm(0); /* Turn off alarm so we can safely set signal handler */
      ::signal(SIGALRM, stpTimeoutHandler);
      ::alarm(std::max(1, (int)timeout));
    }
    unsigned res = vc_query(vc, q);
    if (!res) {
      Assignment::map_bindings_ty bindings;
      for (ref<ReadExpr> read : reads) {
        const Array *array = read->updates.root;
        ExprHandle indexExpr =
            vc_getCounterExample(vc, builder->construct(read->index));
        unsigned index = getBVUnsigned(indexExpr);
        ExprHandle valueExpr =
            vc_getCounterExample(vc, builder->getInitialRead(array, index));
        unsigned value = getBVUnsigned(valueExpr);
        bindings[read->updates.root].add(index, value);
      }
      size_t size = Assignment::toMemory(bindings, shared_memory_ptr, shared_memory_size);
      if (size == 0)
        llvm::report_fatal_error("not enough shared memory for counterexample");
    }
    _exit(res);
  } else {
    int status;
    pid_t res;

    do {
      res = waitpid(pid, &status, 0);
    } while (res < 0 && errno == EINTR);

    if (res < 0) {
      klee_warning("waitpid() for STP failed");
      if (!IgnoreSolverFailures)
        exit(1);
      return SolverImpl::SOLVER_RUN_STATUS_WAITPID_FAILED;
    }

    // From timed_run.py: It appears that linux at least will on
    // "occasion" return a status when the process was terminated by a
    // signal, so test signal first.
    if (WIFSIGNALED(status) || !WIFEXITED(status)) {
      klee_warning("STP did not return successfully.  Most likely you forgot "
                   "to run 'ulimit -s unlimited'");
      if (!IgnoreSolverFailures) {
        exit(1);
      }
      return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
    }

    int exitcode = WEXITSTATUS(status);
    if (exitcode == 0) {
      hasSolution = true;
    } else if (exitcode == 1) {
      hasSolution = false;
    } else if (exitcode == 52) {
      klee_warning("STP timed out");
      // mark that a timeout occurred
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    } else {
      klee_warning("STP did not return a recognized code");
      if (!IgnoreSolverFailures)
        exit(1);
      return SolverImpl::SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE;
    }

    if (hasSolution) {
      result = std::make_shared<Assignment>(shared_memory_ptr);
    }

    if (true == hasSolution) {
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    } else {
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
    }
  }
}
bool STPSolverImpl::computeInitialValues(
    const Query &query, std::shared_ptr<const Assignment>& result,
    bool &hasSolution) {
  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  TimerStatIncrementer t(stats::queryTime);

  vc_push(vc);

  for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it)
    vc_assertFormula(vc, builder->construct(*it));

  ++stats::queries;
  ++stats::queryCounterexamples;

  ExprHandle stp_e = builder->construct(query.expr);

  if (DebugDumpSTPQueries) {
    char *buf;
    unsigned long len;
    vc_printQueryStateToBuffer(vc, stp_e, &buf, &len, false);
    klee_warning("STP query:\n%.*s\n", (unsigned)len, buf);
  }

  std::vector<ref<ReadExpr> > reads;
  findReads(query.expr, true, reads);
  for (const auto constraint: query.constraints)
    findReads(constraint, true, reads);
  bool success;
  if (useForkedSTP) {
    runStatusCode = runAndGetCexForked(vc, builder, stp_e, reads, result,
                                       hasSolution, timeout);
    success = ((SOLVER_RUN_STATUS_SUCCESS_SOLVABLE == runStatusCode) ||
               (SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE == runStatusCode));
  } else {
    runStatusCode =
        runAndGetCex(vc, builder, stp_e, reads, result, hasSolution);
    success = true;
  }

  if (success) {
    if (hasSolution)
      ++stats::queriesInvalid;
    else
      ++stats::queriesValid;
  }

  vc_pop(vc);

  return success;
}

SolverImpl::SolverRunStatus STPSolverImpl::getOperationStatusCode() {
  return runStatusCode;
}

STPSolver::STPSolver(bool useForkedSTP, bool optimizeDivides)
    : Solver(new STPSolverImpl(useForkedSTP, optimizeDivides)) {}

char *STPSolver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void STPSolver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}
}
#endif // ENABLE_STP
