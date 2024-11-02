#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <map>

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
    auto *callee = inst.getCalledFunction();
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

    CATDefVisitor visitor(defTable);
    for (auto &inst : instructions(F)) {
      visitor.visit(inst);
    }

    for (auto [var, defs] : defTable) {
      for (auto def : defs) {
        errs() << F.getName() << *var << *def << "\n";
      }
    }
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
