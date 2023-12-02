//===-- Frequent Path Loop Invariant Code Motion Pass --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===---------------------------------------------------------------------===//
//
// EECS583 F23 - This pass can be used as a template for your FPLICM homework
//               assignment.
//               The passes get registered as "fplicm-correctness" and
//               "fplicm-performance".
//
//
////===-------------------------------------------------------------------===//
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <unordered_set>

/* *******Implementation Starts Here******* */
// You can include more Header files here
/* *******Implementation Ends Here******* */

using namespace llvm;

namespace
{
  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass>
  {

    struct bbSinkingAnalysis
    {
      Instruction *gen = nullptr;
      bool kill = false;
      Value *in = nullptr;
      Value *out = nullptr;
    };

    void getAllocas(Function &F, std::vector<Value *> &allocas)
    {
      for (auto &bb : F)
      {
        for (auto &i : bb)
        {
          if (i.getOpcode() == Instruction::Alloca)
          {
            errs() << i << "\n";
            allocas.push_back(cast<Value>(&i));
          }
        }
      }
    }

    void findGenKillInOut(Function &F, Value *alloca, std::unordered_map<BasicBlock *, bbSinkingAnalysis> &analysis)
    {
      for (auto &bb : F)
      {
        bbSinkingAnalysis res;
        for (auto &i : bb)
        {
          if (i.getOpcode() == Instruction::Store && i.getOperand(1) == alloca)
          {
            res.kill = false;
            res.gen = &i;
          }
          if (i.getOpcode() == Instruction::Load && i.getOperand(0) == alloca)
          {
            res.gen = nullptr;
            res.kill = true;
          }
        }
        analysis[&bb] = res;
      }

      bool change = true;
      while (change)
      {
        for (auto &bb : F)
        {
          auto &res = analysis[&bb];
          auto oldin = res.in;

          for (auto pred : predecessors(&bb))
          {
            auto out = analysis[pred].out;
            if (out == nullptr)
            {
              res.in = nullptr;
              break;
            }
            if (res.in == nullptr)
            {
              res.in = out;
              continue;
            }
            if (res.in != out)
            {
              res.in = nullptr;
              break;
            }
          }

          if (res.gen)
          {
            res.out = res.gen;
          }
          else if (!res.kill)
          {
            res.out = res.in;
          }

          change = oldin != res.in;
        }
      }
    }

    bool findPartialDeadStores(Function &F, Value *alloca, std::unordered_map<BasicBlock *, bbSinkingAnalysis> &analysis)
    {
      std::unordered_set<Instruction *> pds;
      for (auto &bb : F)
      {
        auto bbAnalysis = analysis[&bb];
        if (bbAnalysis.in != nullptr)
        {
          auto inst = dyn_cast<Instruction>(bbAnalysis.in)->clone();
          inst->insertBefore(&(*(bb.getFirstInsertionPt())));
          pds.insert(dyn_cast<Instruction>(bbAnalysis.in));
        }
      }

      if (pds.empty())
      {
        return false;
      }

      for (auto i : pds)
      {
        i->eraseFromParent();
      }
      return true;
    }

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM)
    {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
      // Your core logic should reside here.

      // Step 1: Find all variables allocated by Alloca instruction
      std::vector<Value *> allocas;
      getAllocas(F, allocas);

      // Step 2: Assignment sinking analysis

      for (auto alloca : allocas)
      {
        errs() << "alloca: " << *(cast<Instruction>(alloca)) << "\n";

        std::unordered_map<BasicBlock *, bbSinkingAnalysis> analysis;

        while (true)
        {
          findGenKillInOut(F, alloca, analysis);

          if (!findPartialDeadStores(F, alloca, analysis))
          {
            break;
          }
        }

        for (auto i : analysis)
        {
          errs() << "BB: ";
          if (i.first != nullptr)
          {
            errs() << *i.first;
          }
          else
          {
            errs() << "null";
          }

          errs() << " GEN: ";
          if (i.second.gen != nullptr)
          {
            errs() << *i.second.gen;
          }
          else
          {
            errs() << "null";
          }

          errs() << " KILL: " << i.second.kill;

          errs() << " IN: ";
          if (i.second.in != nullptr)
          {
            errs() << *i.second.in;
          }
          else
          {
            errs() << "null";
          }

          errs() << " OUT: ";
          if (i.second.out != nullptr)
          {
            errs() << *i.second.out;
          }
          else
          {
            errs() << "null";
          }

          errs() << "\n";
        }
      }

      /* *******Implementation Ends Here******* */
      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::all();
    }
  };
  struct HW2PerformancePass : public PassInfoMixin<HW2PerformancePass>
  {
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM)
    {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
      // This is a bonus. You do not need to attempt this to receive full credit.
      /* *******Implementation Ends Here******* */

      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::all();
    }
  };
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo()
{
  return {
      LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
      [](PassBuilder &PB)
      {
        PB.registerPipelineParsingCallback(
            [](StringRef Name, FunctionPassManager &FPM,
               ArrayRef<PassBuilder::PipelineElement>)
            {
              if (Name == "fplicm-correctness")
              {
                FPM.addPass(HW2CorrectnessPass());
                return true;
              }
              if (Name == "fplicm-performance")
              {
                FPM.addPass(HW2PerformancePass());
                return true;
              }
              return false;
            });
      }};
}
