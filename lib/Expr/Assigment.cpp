//===-- Assignment.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/util/Assignment.h"
namespace klee {

void Assignment::dump() const {
  if (bindings.size() == 0) {
    llvm::errs() << "No bindings\n";
    return;
  }
  for (bindings_ty::const_iterator i = bindings.begin(), e = bindings.end(); i != e;
       ++i) {
    llvm::errs() << (*i).first->name << "\n[";
    i->second.dump();
    llvm::errs() << "]\n";
  }
}

void Assignment::createConstraintsFromAssignment(
    std::vector<ref<Expr> > &out) const {
  assert(out.size() == 0 && "out should be empty");
  for (bindings_ty::const_iterator it = bindings.begin(), ie = bindings.end();
       it != ie; ++it) {
    const Array *array = it->first;
    const auto &values = it->second;
    for (const auto pair : values.asMap()) {
      unsigned arrayIndex = pair.first;
      unsigned char value = pair.second;
      out.push_back(EqExpr::create(
          ReadExpr::create(UpdateList(array, 0),
                           ConstantExpr::alloc(arrayIndex, array->getDomain())),
          ConstantExpr::alloc(value, array->getRange())));
    }
  }
}

void MapArrayModel::toCompact(CompactArrayModel& model) const {
  model.skipRanges.clear();
  model.values.clear();
  unsigned cursor = 0;
  for (const auto item : content) {
    unsigned difference = item.first - cursor;
    if (shouldSkip(difference)) {
      model.skipRanges.push_back({cursor, difference});
    } else {
      model.values.resize(model.values.size() + difference);
    }
    model.values.push_back(item.second);
    cursor = item.first + 1;
  }
}

size_t MapArrayModel::toCompactMemory(void *mem, size_t limit) const {
  unsigned skipRangeCount = 0;
  unsigned valueCount = 0;
  unsigned cursor = 0;
  // first compute the counts
  for (const auto item : content) {
    unsigned difference = item.first - cursor;
    if (shouldSkip(difference)) {
      skipRangeCount++;
    } else {
      valueCount += difference;
    }
    valueCount++;
    cursor = item.first + 1;
  }
  size_t size = 2 * sizeof(unsigned) // sizes
      + skipRangeCount * sizeof(SkipRange) // skipRanges
      + valueCount * sizeof(uint64_t); // values
  if (size >= limit)
    return 0; // above limit, won't fit
  // now construct the values
  unsigned *header = (unsigned*)mem;
  header[0] = skipRangeCount;
  header[1] = valueCount;
  SkipRange *skipRanges = (SkipRange*)(header + 2);
  uint64_t *values = (uint64_t*)(skipRanges + skipRangeCount);
  cursor = 0;
  for (const auto item : content) {
    unsigned difference = item.first - cursor;
    if (shouldSkip(difference)) {
      *(skipRanges++) = {cursor, difference};
    } else {
      for (unsigned i = 0; i < difference; i++)
        *(values++) = 0;
    }
    *(values++) = item.second;
    cursor = item.first + 1;
  }
  return size;
  }

  size_t Assignment::toMemory(const map_bindings_ty& bindings, void* mem,
                              size_t limit) {
    size_t size = sizeof(unsigned);
    if (size >= limit)
      return 0; // won't fit
    unsigned *arrayCount = (unsigned*)mem;
    *arrayCount = bindings.size();
    mem = arrayCount + 1;
    for (const auto binding : bindings) {
      size += sizeof(const Array*);
      if (size >= limit)
        return 0;
      const Array **arrayHeader = (const Array**)mem;
      *arrayHeader = binding.first;
      mem = arrayHeader + 1;
      size_t modelSize = binding.second.toCompactMemory(mem, limit - size);
      if (modelSize == 0)
        return 0;
      size += modelSize;
      mem = (char*)mem + modelSize;
    }
    return size;
  }

  Assignment::Assignment(void *mem) {
    unsigned *arrayCount = (unsigned*)mem;
    mem = arrayCount + 1;
    for (unsigned i = 0; i < *arrayCount; i++) {
      Array **arrayHeader = (Array**)mem;
      mem = arrayHeader + 1;
      CompactArrayModel &model = bindings[*arrayHeader];
      size_t modelSize = model.fromMemory(mem);
      mem = (char*)mem + modelSize;
    }
  }


size_t CompactArrayModel::fromMemory(void *mem) {
  unsigned *header = (unsigned*)mem;
  unsigned skipRangeCount = header[0];
  unsigned valueCount = header[1];
  SkipRange *skipRanges = (SkipRange*)(header + 2);
  uint64_t *values = (uint64_t*)(skipRanges + skipRangeCount);
  this->skipRanges.reserve(skipRangeCount);
  this->values.reserve(valueCount);
  for (unsigned i = 0; i < skipRangeCount; i++)
    this->skipRanges.push_back(skipRanges[i]);
  for (unsigned i = 0; i < valueCount; i++)
    this->values.push_back(values[i]);
  return 2 * sizeof(unsigned) + skipRangeCount * sizeof(SkipRange)
      + valueCount * sizeof(uint64_t);
}

uint8_t CompactArrayModel::get(unsigned index) const {
  unsigned skipTotal = 0;
  for (const SkipRange item : skipRanges) {
    unsigned skipStart = item.start;
    unsigned skipCount = item.length;
    unsigned skipEnd = skipStart + skipCount;
    if (index < skipEnd) {
      if (index >= skipStart) {
        // it's within skipped range, so it can be anything, for example 0
        return 0;
      } else {
        return values[index - skipTotal];
      }
    }
    skipTotal += skipCount;
  }
  if (index - skipTotal < values.size())
    return values[index - skipTotal];
  return 0;
}

std::map<uint32_t, uint8_t> CompactArrayModel::asMap() const {
  std::map<uint32_t, uint8_t> retMap;
  unsigned index = 0;
  unsigned cursor = 0;
  for (const SkipRange item : skipRanges) {
    for (; index < item.start; index++, cursor++) {
      retMap[index] = values[cursor];
    }
    index += item.length;
  }
  for (; cursor < values.size(); cursor++, index++) {
    retMap[index] = values[cursor];
  }
  return retMap;
}

std::vector<uint8_t> CompactArrayModel::asVector() const {
  std::vector<uint8_t> result;
  unsigned index = 0;
  unsigned cursor = 0;
  for (const SkipRange item : skipRanges) {
    for (; index < item.start; index++, cursor++) {
      result.push_back(values[cursor]);
    }
    index += item.length;
    result.resize(result.size() + item.length);
  }
  for (; cursor < values.size(); cursor++, index++) {
    result.push_back(values[cursor]);
  }
  return result;
}

void CompactArrayModel::dump() const {
  // TODO
}
}
