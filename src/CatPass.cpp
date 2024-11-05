#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <algorithm>
#include <deque>
#include <unordered_map>
#include <unordered_set>

// #define PRINT_DEF_TABLE
// #define PRINT_REACHING_DEFS

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

using CATInsts = std::unordered_map<BasicBlock *, std::vector<CallInst *>>;
using DefTable =
    std::unordered_map<Instruction *, std::unordered_set<Instruction *>>;
using DFASet =
    std::unordered_map<Instruction *, std::unordered_set<Instruction *>>;

std::unordered_map<Function *, CAT_API> CATMap;

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

#ifdef PRINT_DEF_TABLE
  for (auto &[var, defs] : defTable) {
    for (auto &def : defs) {
      errs() << F->getName() << *var << *def << "\n";
    }
  }
#endif
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

#ifndef PRINT_REACHING_DEFS
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

    for (int i = 0; i < (int)vec.size() - 1; i++) {
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
#else
  for (auto &b : F) {
    auto front = &b.front();
    auto &inFront = in[front];
    auto &outFront = out[front];
    auto &genFront = gen[front];
    auto &killFront = kill[front];
    inFront = inB[&b];
    outFront = genFront;
    for (auto inst : inFront) {
      if (!killFront.contains(inst)) {
        outFront.insert(inst);
      }
    }

    auto t = front;
    while (t != &b.back()) {
      auto tNext = t->getNextNode();
      auto &inNext = in[tNext];
      auto &outNext = out[tNext];
      auto &genNext = gen[tNext];
      auto &killNext = kill[tNext];
      inNext = out[t];
      outNext = genNext;
      for (auto inst : inNext) {
        if (!killNext.contains(inst)) {
          outNext.insert(inst);
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
#endif
}

bool hasCycle(Instruction *val) {
  std::vector<Value *> stack = {val};
  std::set<Value *> visited;
  while (!stack.empty()) {
    auto inst = stack.back();
    stack.pop_back();
    if (visited.contains(inst)) {
      return true;
    }
    visited.insert(inst);
    if (auto phi = dyn_cast<PHINode>(inst)) {
      for (unsigned int i = 0; i < phi->getNumIncomingValues(); i++) {
        stack.push_back(phi->getIncomingValue(i));
      }
    }
  }
  return false;
}

ConstantInt *getConstant(Value *val, CallInst *inst, DFASet const &in) {
  ConstantInt *ci = nullptr;

  if (auto phi = dyn_cast<PHINode>(val)) {
    if (hasCycle(phi)) {
      return nullptr;
    }
    for (unsigned int i = 0; i < phi->getNumIncomingValues(); i++) {
      auto inc = phi->getIncomingValue(i);
      if (isa<UndefValue>(inc)) {
        continue;
      }
      if (auto c = getConstant(inc, inst, in)) {
        if (!ci || c->getSExtValue() != ci->getSExtValue()) {
          ci = c;
          continue;
        }
      }
      return nullptr;
    }
  }

  for (auto i : in.at(inst)) {
    if (auto call = dyn_cast<CallInst>(i)) {
      auto callee = call->getCalledFunction();
      if (CATMap.contains(callee)) {
        switch (CATMap.at(callee)) {
        case CAT_API::CAT_new:
          if (call != val) {
            continue;
          }
          break;
        case CAT_API::CAT_add:
        case CAT_API::CAT_sub:
          if (call->getArgOperand(0) == val) {
            return nullptr;
          }
          continue;
        case CAT_API::CAT_set:
          if (call->getArgOperand(0) != val) {
            continue;
          }
          break;
        default:
          continue;
        }

        auto arg = CATMap.at(callee) == CAT_API::CAT_new
                       ? call->getArgOperand(0)
                       : call->getArgOperand(1);
        if (auto c = dyn_cast<ConstantInt>(arg)) {
          if (!ci || c->getSExtValue() == ci->getSExtValue()) {
            ci = c;
            continue;
          }
          return nullptr;
        }
        return nullptr;
      }
    }
  }

  return ci;
}

bool doConstantPropagation(Function &F, DFASet const &in) {
  bool modified = false;
  std::vector<std::tuple<CallInst *, ConstantInt *>> toReplace;

  for (auto &inst : instructions(F)) {
    if (auto call = dyn_cast<CallInst>(&inst)) {
      auto it = CATMap.find(call->getCalledFunction());
      if (it != CATMap.end() && it->second == CAT_API::CAT_get) {
        auto arg = call->getArgOperand(0);
        if (auto constant = getConstant(arg, call, in)) {
          toReplace.push_back({call, constant});
          modified = true;
        }
      }
    }
  }

  for (auto &[inst, constant] : toReplace) {
    auto parent = inst->getParent();
    BasicBlock::iterator ii(inst);
    ReplaceInstWithValue(parent->getInstList(), ii, constant);
  }

  return modified;
}

bool doConstantFolding(Function &F, DFASet const &in) {
  bool modified = false;
  std::vector<CallInst *> toDelete;

  for (auto &inst : instructions(F)) {
    if (auto call = dyn_cast<CallInst>(&inst)) {
      auto it = CATMap.find(call->getCalledFunction());
      if (it != CATMap.end() &&
          (it->second == CAT_API::CAT_add || it->second == CAT_API::CAT_sub)) {
        auto lhs = getConstant(call->getArgOperand(1), call, in),
             rhs = getConstant(call->getArgOperand(2), call, in);

        if (!lhs || !rhs) {
          continue;
        }

        auto leftConst = lhs->getSExtValue(), rightConst = rhs->getSExtValue();

        IRBuilder<> builder(call);
        auto M = F.getParent();
        auto setFunc = M->getFunction("CAT_set");
        auto intType = IntegerType::get(M->getContext(), 64);
        auto constant = it->second == CAT_API::CAT_add ? leftConst + rightConst
                                                       : leftConst - rightConst;
        auto constInt = ConstantInt::get(intType, constant, true);

        auto setInst =
            builder.CreateCall(setFunc, {call->getArgOperand(0), constInt});
        call->replaceAllUsesWith(setInst);
        toDelete.push_back(call);
        modified = true;
      }
    }
  }

  for (auto inst : toDelete) {
    inst->eraseFromParent();
  }

  return modified;
}

bool doAlgebraicSimplification(Function &F, DFASet const &in) {
  bool modified = false;
  std::vector<CallInst *> toDelete;

  for (auto &inst : instructions(F)) {
    if (auto call = dyn_cast<CallInst>(&inst)) {
      IRBuilder<> builder(call);
      auto M = F.getParent();
      auto getFunc = M->getFunction("CAT_get");
      auto setFunc = M->getFunction("CAT_set");
      auto it = CATMap.find(call->getCalledFunction());

      if (it == CATMap.end()) {
        continue;
      }

      if (it->second == CAT_API::CAT_add) {
        auto lhs = getConstant(call->getArgOperand(1), call, in),
             rhs = getConstant(call->getArgOperand(2), call, in);

        if (lhs && lhs->getSExtValue() == 0) {
          auto getInst = builder.CreateCall(getFunc, {call->getArgOperand(2)});
          auto setInst =
              builder.CreateCall(setFunc, {call->getArgOperand(0), getInst});
          call->replaceAllUsesWith(setInst);
          toDelete.push_back(call);
          modified = true;

        } else if (rhs && rhs->getSExtValue() == 0) {
          auto getInst = builder.CreateCall(getFunc, {call->getArgOperand(1)});
          auto setInst =
              builder.CreateCall(setFunc, {call->getArgOperand(0), getInst});
          call->replaceAllUsesWith(setInst);
          toDelete.push_back(call);
          modified = true;
        }

      } else if (it->second == CAT_API::CAT_sub) {
        auto rhs = getConstant(call->getArgOperand(2), call, in);

        if (rhs && rhs->getSExtValue() == 0) {
          auto getInst = builder.CreateCall(getFunc, {call->getArgOperand(1)});
          auto setInst =
              builder.CreateCall(setFunc, {call->getArgOperand(0), getInst});
          call->replaceAllUsesWith(setInst);
          toDelete.push_back(call);
          modified = true;
        }
      }
    }
  }

  for (auto inst : toDelete) {
    inst->eraseFromParent();
  }

  return modified;
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

    bool modified = false;
    modified |= doConstantPropagation(F, in);
    modified |= doConstantFolding(F, in);
    modified |= doAlgebraicSimplification(F, in);

    return modified;
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
