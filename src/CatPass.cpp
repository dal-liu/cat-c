#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <deque>
#include <map>
#include <set>

using namespace llvm;

namespace {
enum CAT_API {
  CAT_new,
  CAT_add,
  CAT_sub,
  CAT_get,
  CAT_set,
  CAT_destroy,
};

std::map<Function *, CAT_API> CATMap;

class CATDefVisitor : public InstVisitor<CATDefVisitor> {
public:
  CATDefVisitor(std::map<CallInst *, std::set<CallInst *>> &defTable)
      : defTable(defTable) {}

  void visitCallInst(CallInst &inst) {
    auto callee = inst.getCalledFunction();
    if (CATMap.contains(callee)) {
      switch (CATMap.at(callee)) {
      case CAT_API::CAT_new:
        defTable[&inst].insert(&inst);
        break;
      case CAT_API::CAT_add:
      case CAT_API::CAT_sub:
      case CAT_API::CAT_set:
        if (auto arg = dyn_cast<CallInst>(inst.getArgOperand(0))) {
          defTable[arg].insert(&inst);
        }
        break;
      default:
        break;
      }
    }
  }

private:
  std::map<CallInst *, std::set<CallInst *>> &defTable;
};

void createDefTable(Function &F,
                    std::map<CallInst *, std::set<CallInst *>> &defTable) {
  CATDefVisitor defVisitor(defTable);
  for (auto &inst : instructions(F)) {
    defVisitor.visit(inst);
  }

  // for (auto &[var, defs] : defTable) {
  //   for (auto &def : defs) {
  //     errs() << F.getName() << *var << *def << "\n";
  //   }
  // }
}

class CATGenKillVisitor : public InstVisitor<CATGenKillVisitor> {
public:
  CATGenKillVisitor(std::map<CallInst *, std::set<CallInst *>> const &defTable,
                    std::map<Instruction *, std::set<CallInst *>> &gen,
                    std::map<Instruction *, std::set<CallInst *>> &kill,
                    std::map<BasicBlock *, std::set<CallInst *>> &genB,
                    std::map<BasicBlock *, std::set<CallInst *>> &killB)
      : defTable(defTable), gen(gen), kill(kill), genB(genB), killB(killB){};

  void visitCallInst(CallInst &inst) {
    auto parent = inst.getParent();
    auto callee = inst.getCalledFunction();
    if (CATMap.contains(callee)) {
      switch (CATMap.at(callee)) {
      case CAT_API::CAT_new:
        gen[&inst].insert(&inst);
        if (!killB[parent].contains(&inst)) {
          genB[parent].insert(&inst);
        }
        for (auto def : defTable.at(&inst)) {
          if (def != &inst) {
            kill[&inst].insert(def);
            killB[parent].insert(def);
          }
        }
        break;
      case CAT_API::CAT_add:
      case CAT_API::CAT_sub:
      case CAT_API::CAT_set:
        if (auto arg = dyn_cast<CallInst>(inst.getArgOperand(0))) {
          gen[&inst].insert(&inst);
          if (!killB[parent].contains(&inst)) {
            genB[parent].insert(&inst);
          }
          for (auto def : defTable.at(arg)) {
            if (def != &inst) {
              kill[&inst].insert(def);
              killB[parent].insert(def);
            }
          }
        }
        break;
      default:
        break;
      }
    }
  }

private:
  std::map<CallInst *, std::set<CallInst *>> const &defTable;
  std::map<Instruction *, std::set<CallInst *>> &gen, &kill;
  std::map<BasicBlock *, std::set<CallInst *>> &genB, &killB;
};

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
  std::set<BasicBlock *> blocks;
  std::deque<BasicBlock *> todo;
};

void createReachingDefs(
    Function &F, std::map<CallInst *, std::set<CallInst *>> const &defTable,
    std::map<Instruction *, std::set<CallInst *>> &in,
    std::map<Instruction *, std::set<CallInst *>> &out) {
  std::map<Instruction *, std::set<CallInst *>> gen, kill;
  std::map<BasicBlock *, std::set<CallInst *>> genB, killB;
  CATGenKillVisitor genKillVisitor(defTable, gen, kill, genB, killB);
  for (auto &b : F) {
    for (auto it = b.rbegin(); it != b.rend(); it++) {
      genKillVisitor.visit(*it);
    }
  }

  std::map<CallInst *, int> CATToInt;
  std::vector<CallInst *> intToCAT;
  int i = 0;
  for (auto &inst : instructions(F)) {
    if (auto callInst = dyn_cast<CallInst>(&inst)) {
      auto callee = callInst->getCalledFunction();
      if (CATMap.contains(callee)) {
        CATToInt[callInst] = i;
        intToCAT.push_back(callInst);
        i++;
      }
    }
  }

  std::map<BasicBlock *, BitVector> genBV, killBV;
  std::map<BasicBlock *, BitVector> inBV, outBV;
  WorkList workList;
  for (auto &b : F) {
    genBV[&b] = BitVector(i);
    killBV[&b] = BitVector(i);
    inBV[&b] = BitVector(i);
    outBV[&b] = BitVector(i);
    for (auto &inst : genB[&b]) {
      genBV[&b].set(CATToInt[inst]);
    }
    for (auto &inst : killB[&b]) {
      killBV[&b].set(CATToInt[inst]);
    }
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

  std::map<BasicBlock *, std::set<CallInst *>> inB, outB;
  for (auto &b : F) {
    for (auto i : inBV[&b].set_bits()) {
      inB[&b].insert(intToCAT[i]);
    }
    for (auto i : outBV[&b].set_bits()) {
      outB[&b].insert(intToCAT[i]);
    }
  }

  for (auto &b : F) {
    for (auto &inst : b) {
      in[&inst] = {};
      out[&inst] = {};
    }
    auto front = &b.front();
    in[front] = inB[&b];
    out[front] = gen[front];
    for (auto i : in[front]) {
      if (!kill[front].contains(i)) {
        out[front].insert(i);
      }
    }
    auto inst = front;
    while (inst != &b.back()) {
      auto next = inst->getNextNode();
      in[next] = out[inst];
      out[next] = gen[next];
      for (auto i : in[next]) {
        if (!kill[next].contains(i)) {
          out[next].insert(i);
        }
      }
      inst = next;
    }
  }

  // for (auto &b : F) {
  //   errs() << "BASICBLOCK:" << b.front() << "\n";
  //   errs() << "GEN\n";
  //   for (auto i : genB.at(&b)) {
  //     errs() << *i << "\n";
  //   }
  //   errs() << "KILL\n";
  //   for (auto i : killB.at(&b)) {
  //     errs() << *i << "\n";
  //   }
  // }

  errs() << "Function \"" << F.getName() << "\""
         << "\n";
  for (auto &b : F) {
    for (auto &inst : b) {
      errs() << "INSTRUCTION:" << inst << "\nIN\n{\n";
      for (auto i : in.at(&inst)) {
        errs() << *i << "\n";
      }
      errs() << "}\nOUT\n{\n";
      for (auto i : out.at(&inst)) {
        errs() << *i << "\n";
      }
      errs() << "}\n";
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
    std::map<CallInst *, std::set<CallInst *>> defTable;
    std::map<Instruction *, std::set<CallInst *>> in, out;

    createDefTable(F, defTable);

    createReachingDefs(F, defTable, in, out);

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
