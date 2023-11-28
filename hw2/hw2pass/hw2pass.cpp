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

/* *******Implementation Starts Here******* */
// You can include more Header files here
/* *******Implementation Ends Here******* */

using namespace llvm;

namespace
{
  BasicBlock *getHotSuccessor(const llvm::BasicBlock &bb, const llvm::BranchProbabilityAnalysis::Result &bpi)
  {
    auto i = bb.getTerminator();

    auto prob = bpi.getEdgeProbability(&bb, i->getSuccessor(0));
    if (prob >= BranchProbability(4, 5))
    {
      return i->getSuccessor(0);
    }

    return i->getSuccessor(1);
  }

  bool isIn(const Instruction *i, const std::vector<BasicBlock *> &bbs)
  {
    auto bb = i->getParent();
    for (auto b : bbs)
    {
      if (bb == b)
      {
        return true;
      }
    }

    return false;
  }

  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass>
  {

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM)
    {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
      // Your core logic should reside here.

      for (auto l : li)
      {
        auto header = l->getHeader();
        auto latch = l->getLoopLatch();

        std::vector<BasicBlock *> freqBB = {};
        std::vector<LoadInst *> loads = {};

        for (auto bb = header;; bb = getHotSuccessor(*bb, bpi))
        {
          freqBB.push_back(bb);
          for (auto &i : *bb)
          {
            switch (i.getOpcode())
            {
            case Instruction::Load:
            {
              auto l = dyn_cast_or_null<LoadInst>(&i);
              if (l == nullptr)
              {
                break;
              }
              loads.push_back(l);
              break;
            }
            }
          }

          if (bb == latch)
          {
            break;
          }
        }

        std::vector<BasicBlock *> inFreqBB = l->getBlocksVector();
        inFreqBB.erase(std::remove_if(inFreqBB.begin(),
                                      inFreqBB.end(),
                                      [&](BasicBlock *bb)
                                      {
                                        return std::find(freqBB.begin(), freqBB.end(), bb) != freqBB.end();
                                      }),
                       inFreqBB.end());

        std::vector<LoadInst *> hoistable = {};
        for (auto load : loads)
        {
          auto ptrOp = load->getPointerOperand();

          bool hasInfreqStore = false;

          for (auto *u : ptrOp->users())
          {
            auto user = dyn_cast_or_null<Instruction>(u);
            if (user == nullptr)
            {
              continue;
            }

            if (!isIn(user, inFreqBB))
            {
              continue;
            }
            if (auto store = dyn_cast<llvm::StoreInst>(user))
            {
              if (store->getPointerOperand() == ptrOp)
              {
                hasInfreqStore = true;
                break;
              }
            }
          }

          if (!hasInfreqStore)
          {
            continue;
          }

          bool hasFreqStore = false;

          for (auto *u : ptrOp->users())
          {
            auto user = dyn_cast_or_null<Instruction>(u);
            if (user == nullptr)
            {
              continue;
            }

            if (!isIn(user, freqBB))
            {
              continue;
            }
            if (auto store = dyn_cast<llvm::StoreInst>(user))
            {
              if (store->getPointerOperand() == ptrOp)
              {
                hasFreqStore = true;
                break;
              }
            }
          }

          if (hasFreqStore)
          {
            continue;
          }

          hoistable.push_back(load);
        }

        auto preHeader = l->getLoopPreheader();

        std::unordered_map<Value *, AllocaInst *> stores = {};

        int numFixed = 0;

        for (auto load : hoistable)
        {
          auto ptrOp = load->getPointerOperand();
          // errs() << *ptrOp << "\n";

          if (stores.find(ptrOp) != stores.end())
          {
            auto allocaInst = stores[ptrOp];
            auto newLoad = new LoadInst(load->getType(), allocaInst, "loadFromAlloca", load);
            load->replaceAllUsesWith(newLoad);

            load->moveAfter(allocaInst);

            auto newStore = new StoreInst(load, allocaInst, preHeader->getTerminator());
            continue;
          }
          auto allocaInst = new AllocaInst(load->getType(), 0, "hoistedAlloca", preHeader->getTerminator());
          stores[ptrOp] = allocaInst;

          std::vector<StoreInst *> toFix = {};

          for (auto *u : ptrOp->users())
          {
            // errs() << *u << "\n";
            auto user = dyn_cast_or_null<Instruction>(u);
            if (user == nullptr)
            {
              continue;
            }

            if (!isIn(user, inFreqBB))
            {
              continue;
            }
            if (auto store = dyn_cast<llvm::StoreInst>(user))
            {
              if (store->getPointerOperand() == ptrOp)
              {
                // errs() << "fixed"
                //        << "\n";
                // store->setOperand(1, allocaInst);
                toFix.push_back(store);
                numFixed++;
                continue;
              }
            }
          }

          for (auto s : toFix)
          {
            s->setOperand(1, allocaInst);
          }

          auto newLoad = new LoadInst(load->getType(), allocaInst, "loadFromAlloca", load);
          load->replaceAllUsesWith(newLoad);

          load->moveBefore(preHeader->getTerminator());

          auto newStore = new StoreInst(load, allocaInst, preHeader->getTerminator());
        }

        // errs() << freqBB.size() << " : " << inFreqBB.size() << " : " << hoistable.size() << " : " << numFixed << "\n";
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
