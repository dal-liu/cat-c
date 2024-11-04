#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <deque>
#include <unordered_map>
#include <unordered_set>

using namespace llvm;

namespace {
bool printDefTable = false;
bool printReachingDefs = false;

enum CAT_API {
  CAT_new,
  CAT_add,
  CAT_sub,
  CAT_get,
  CAT_set,
  CAT_destroy,
};

std::unordered_map<Function *, CAT_API> CATMap;

using CATInsts = std::unordered_map<BasicBlock *, std::vector<CallInst *>>;
using DefTable =
    std::unordered_map<Instruction *, std::unordered_set<Instruction *>>;
using DFASet =
    std::unordered_map<Instruction *, std::unordered_set<Instruction *>>;

class CATVisitor : public InstVisitor<CATVisitor> {
public:
  CATVisitor(CATInsts &CATInsts) : CATInsts(CATInsts) {}

  void visitCallInst(CallInst &inst) {
    auto parent = inst.getParent();
    auto callee = inst.getCalledFunction();
    if (CATMap.contains(callee)) {
      CATInsts[parent].push_back(&inst);
    }
  }

private:
  CATInsts &CATInsts;
};

void getCATInsts(Function &F, CATInsts &CATInsts) {
  CATVisitor visitor(CATInsts);
  for (auto &b : F) {
    CATInsts[&b] = {};
    for (auto &inst : b) {
      visitor.visit(&inst);
    }
  }
}

void createDefTable(Function &F, CATInsts const &CATInsts, DefTable &defTable) {
  for (auto &b : F) {
    for (auto inst : CATInsts.at(&b)) {
      auto callee = inst->getCalledFunction();
      switch (CATMap.at(callee)) {
      case CAT_API::CAT_new:
        defTable[inst].insert(inst);
        break;
      case CAT_API::CAT_add:
      case CAT_API::CAT_sub:
      case CAT_API::CAT_set:
        if (auto arg = dyn_cast<Instruction>(inst->getArgOperand(0))) {
          defTable[arg].insert(inst);
          defTable[arg].insert(arg);
        }
        break;
      default:
        break;
      }
    }
  }

  if (printDefTable) {
    for (auto &[var, defs] : defTable) {
      for (auto &def : defs) {
        errs() << F.getName() << *var << *def << "\n";
      }
    }
  }
}

struct WorkList {
public:
  void append(BasicBlock *b) {
    if (!blocks.contains(b)) {
      blocks.insert(b);
      todo.push_back(b);
    }
  }

  BasicBlock *pop() {
    auto b = todo.front();
    todo.pop_front();
    blocks.erase(b);
    return b;
  }

  bool empty() { return todo.empty(); }

private:
  std::unordered_set<BasicBlock *> blocks;
  std::deque<BasicBlock *> todo;
};

void createReachingDefs(Function &F, CATInsts const &CATInsts,
                        DefTable const &defTable, DFASet &in, DFASet &out) {
  int size = 0;
  for (auto &pair : CATInsts) {
    size += pair.second.size();
  }

  std::vector<Instruction *> intToCAT(size);
  std::unordered_map<Instruction *, int> CATToInt;
  std::unordered_map<Instruction *, std::unordered_set<Instruction *>> gen,
      kill;
  std::unordered_map<BasicBlock *, std::unordered_set<Instruction *>> genB,
      killB, inB, outB;

  int i = 0;
  for (auto &b : F) {
    auto vec = CATInsts.at(&b);
    for (auto it = vec.rbegin(); it != vec.rend(); it++) {
      auto inst = *it;
      intToCAT[i] = inst;
      CATToInt[inst] = i;
      i++;

      auto callee = inst->getCalledFunction();
      switch (CATMap.at(callee)) {
      case CAT_API::CAT_new:
        gen[inst].insert(inst);
        if (!killB[&b].contains(inst)) {
          genB[&b].insert(inst);
        }
        for (auto def : defTable.at(inst)) {
          if (def != inst) {
            kill[inst].insert(def);
            killB[&b].insert(def);
          }
        }
        break;
      case CAT_API::CAT_add:
      case CAT_API::CAT_sub:
      case CAT_API::CAT_set:
        if (auto arg = dyn_cast<Instruction>(inst->getArgOperand(0))) {
          gen[inst].insert(inst);
          if (!killB[&b].contains(inst)) {
            genB[&b].insert(inst);
          }
          for (auto def : defTable.at(arg)) {
            if (def != inst) {
              kill[inst].insert(def);
              killB[&b].insert(def);
            }
          }
        }
        break;
      default:
        break;
      }
    }
  }

  std::unordered_map<BasicBlock *, BitVector> genBV, killBV, inBV, outBV;
  WorkList workList;

  for (auto &b : F) {
    genBV[&b] = BitVector(size);
    for (auto inst : genB[&b]) {
      genBV[&b].set(CATToInt[inst]);
    }
    killBV[&b] = BitVector(size);
    for (auto inst : killB[&b]) {
      killBV[&b].set(CATToInt[inst]);
    }
    inBV[&b] = BitVector(size);
    outBV[&b] = BitVector(size);
    workList.append(&b);
  }

  while (!workList.empty()) {
    auto b = workList.pop();
    auto oldOut = outBV[b];
    for (auto p : predecessors(b)) {
      inBV[b] |= outBV[p];
    }

    outBV[b] = inBV[b];
    outBV[b].reset(killBV[b]);
    outBV[b] |= genBV[b];

    if (oldOut != outBV[b]) {
      for (auto s : successors(b)) {
        workList.append(s);
      }
    }
  }

  for (auto &b : F) {
    for (auto i : inBV[&b].set_bits()) {
      inB[&b].insert(intToCAT[i]);
    }
    for (auto i : outBV[&b].set_bits()) {
      outB[&b].insert(intToCAT[i]);
    }
  }

  for (auto &b : F) {
    auto vec = CATInsts.at(&b);
    if (vec.empty()) {
      continue;
    }

    auto front = vec[0];
    in[front] = inB[&b];
    out[front] = gen[front];
    for (auto inst : in[front]) {
      if (!kill[front].contains(inst)) {
        out[front].insert(inst);
      }
    }

    for (unsigned long i = 1; i < vec.size() - 1; i++) {
      auto t = vec[i], tNext = vec[i + 1];
      in[tNext] = out[t];
      out[tNext] = gen[tNext];
      for (auto inst : in[tNext]) {
        if (!kill[tNext].contains(inst)) {
          out[tNext].insert(inst);
        }
      }
    }
  }

  if (printReachingDefs) {
    for (auto &b : F) {
      auto front = &b.front();
      in[front] = inB[&b];
      out[front] = gen[front];
      for (auto inst : in[front]) {
        if (!kill[front].contains(inst)) {
          out[front].insert(inst);
        }
      }

      auto t = front;
      while (t != &b.back()) {
        auto tNext = t->getNextNode();
        in[tNext] = out[t];
        out[tNext] = gen[tNext];
        for (auto inst : in[tNext]) {
          if (!kill[tNext].contains(inst)) {
            out[tNext].insert(inst);
          }
        }
        t = tNext;
      }
    }

    errs() << "Function \"" << F.getName() << "\""
           << "\n";
    for (auto &b : F) {
      for (auto &inst : b) {
        errs() << "INSTRUCTION:" << inst << "\nIN\n{\n";
        for (auto i : in[&inst]) {
          errs() << *i << "\n";
        }
        errs() << "}\nOUT\n{\n";
        for (auto i : out[&inst]) {
          errs() << *i << "\n";
        }
        errs() << "}\n";
      }
    }
  }
}

struct CAT : public FunctionPass {
  static char ID;

  CAT() : FunctionPass(ID) {}

  // This function is invoked once at the initialization phase of the compiler
  // The LLVM IR of functions isn't ready at this point
  bool doInitialization(Module &M) override {
    CATMap[M.getFunction("CAT_new")] = CAT_API::CAT_new;
    CATMap[M.getFunction("CAT_add")] = CAT_API::CAT_add;
    CATMap[M.getFunction("CAT_sub")] = CAT_API::CAT_sub;
    CATMap[M.getFunction("CAT_get")] = CAT_API::CAT_get;
    CATMap[M.getFunction("CAT_set")] = CAT_API::CAT_set;
    CATMap[M.getFunction("CAT_destroy")] = CAT_API::CAT_destroy;
    return false;
  }

  // This function is invoked once per function compiled
  // The LLVM IR of the input functions is ready and it can be analyzed and/or
  // transformed
  bool runOnFunction(Function &F) override {
    CATInsts CATInsts;
    getCATInsts(F, CATInsts);

    DefTable defTable;
    createDefTable(F, CATInsts, defTable);

    DFASet in, out;
    createReachingDefs(F, CATInsts, defTable, in, out);

    return false;
  }

  // We don't modify the program, so we preserve all analyses.
  // The LLVM IR of functions isn't ready at this point
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};
} // namespace

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT *_PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
                                        [](const PassManagerBuilder &,
                                           legacy::PassManagerBase &PM) {
                                          if (!_PassMaker) {
                                            PM.add(_PassMaker = new CAT());
                                          }
                                        }); // ** for -Ox
static RegisterStandardPasses
    _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
              [](const PassManagerBuilder &, legacy::PassManagerBase &PM) {
                if (!_PassMaker) {
                  PM.add(_PassMaker = new CAT());
                }
              }); // ** for -O0
