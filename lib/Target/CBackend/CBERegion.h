#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/CFG.h"
#if LLVM_VERSION_MAJOR > 10
#include "llvm/IR/AbstractCallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectFileInfo.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Pass.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Transforms/Scalar.h"

#include <set>

// SUSAN ADDED LIBS
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <queue>


namespace llvm_cbe {

class CWriter;
class CBERegion2;
class LoopRegion;
class CBERegion2 {
  public:
  virtual ~CBERegion2(){};
  BasicBlock *getNextEntryBB(){
    return nextEntryBB;
  };
  CBERegion2 (LoopInfo* LI, PostDominatorTree *PDT, DominatorTree* DT, CWriter *cwriter)
    : LI(LI),
      PDT(PDT),
      DT(DT),
      cw(cwriter),
      entryBlock(nullptr),
      nextEntryBB(nullptr),
      parentRegion(nullptr){};

  CBERegion2 (LoopInfo* LI, PostDominatorTree *PDT, DominatorTree *DT, CBERegion2 *parentR, BasicBlock *entryBB, CWriter *cwriter)
    : LI(LI),
      PDT(PDT),
      DT(DT),
      entryBlock(entryBB),
      parentRegion(parentR),
      cw(cwriter){};

  void createCBERegionDAG(BasicBlock *entryBB, CBERegion2 *parentR, BasicBlock *endBB);
  virtual bool isaLoopRegion() {return false;};
  virtual bool isaLinearRegion() {return false;};
  virtual bool isaIfElseRegion() {return false;};
  CBERegion2* getParentRegion(){return parentRegion;};
  virtual void print();
  BasicBlock *getEntryBlock(){return entryBlock;};
  virtual void printRegionDAG();

  LoopRegion* getParentLoopRegion(){
    auto ancestorR = parentRegion;
    while(ancestorR){
      if(ancestorR->isaLoopRegion())
        break;
      ancestorR = ancestorR->getParentRegion();
    }
    return (LoopRegion*)ancestorR;
  }

  int whichRegion(BasicBlock *entryBB, LoopInfo *LI);

  protected:
  BasicBlock *entryBlock; //entryBlock itself should belong to parent region
  BasicBlock *nextEntryBB;
  CBERegion2 *parentRegion;
  //CBERegion2 *topRegion;
  LoopInfo *LI;
  PostDominatorTree *PDT;
  DominatorTree *DT;
  CBERegion2* createSubRegions(CBERegion2* parentR, BasicBlock* entryBB);
  CWriter *cw;

  private:
  std::vector<CBERegion2*>CBERegionDAG;
};

class LinearRegion : public CBERegion2{
  public:
  LinearRegion(BasicBlock *entryBB, CBERegion2 *parentR, LoopInfo *LI, PostDominatorTree *PDT, DominatorTree *DT, CWriter *cwriter);
  bool isaLoopRegion() override {return false;};
  bool isaLinearRegion() override {return true;};
  bool isaIfElseRegion() override {return false;};
  void print() override;
  void printRegionDAG() override;

  private:
  std::vector<BasicBlock*> BBs;
};

class LoopRegion : public CBERegion2{
  public:
  virtual ~LoopRegion() = default;
  LoopRegion (BasicBlock *entryBB, LoopInfo *LI, PostDominatorTree* PDT, DominatorTree *DT, CBERegion2 *parentR, CWriter *cwriter);
  bool isaLoopRegion() override {return true;};
  bool isaLinearRegion() override {return false;};
  bool isaIfElseRegion() override {return false;};
  void print() override;
  void printRegionDAG() override;

  Loop* getLoop(){ return loop; }
  void addBBToVisit(BasicBlock* bb){
    remainingBBsToVisit.insert(bb);
  }
  void removeBBToVisit(BasicBlock* bb){
    remainingBBsToVisit.erase(bb);
  }
  bool hasNoRemainingBBs(){
    return remainingBBsToVisit.empty();
  }

  void createCBERegionDAG(BasicBlock *entryBB);

  private:
  Loop *loop;
  CBERegion2 *parentRegion;
  std::vector<CBERegion2*>LoopBodyRegionDAG;
  std::set<BasicBlock*> remainingBBsToVisit;
  BasicBlock *latchBB;
  Value *ub, *lb, *incr;
  PHINode *IV;
  Instruction *IVInc;
  int nestlevel;
};

class IfElseRegion : public CBERegion2 {
  public:
  virtual ~IfElseRegion() = default;
  IfElseRegion (BasicBlock *entryBB, CBERegion2 *parentR, PostDominatorTree *PDT, DominatorTree *DT, LoopInfo* LI, CWriter *cwriter);
  bool isaLoopRegion() override {return false;};
  bool isaLinearRegion() override {return false;};
  bool isaIfElseRegion() override {return true;};
  void print() override;
  void printRegionDAG() override;

  private:
  BasicBlock* createSubIfElseRegions(BasicBlock* start, BasicBlock *brBlock, BasicBlock *otherStart, bool isElseBranch = false);
  void removeIfElseBlockFromLR(LoopRegion* lr, BasicBlock *brBB);

  int dominatedByReturn(BasicBlock* brBB){
    Function *F = brBB->getParent();
    auto br = dyn_cast<BranchInst>(brBB->getTerminator());
    if(br->isConditional()){
      auto succ0 = br->getSuccessor(0);
      auto succ1 = br->getSuccessor(1);
      auto singleSucc = succ0->getSingleSuccessor();
      if(singleSucc && isa<ReturnInst>(singleSucc->getTerminator()))
        return 0;
      singleSucc = succ1->getSingleSuccessor();
      if(singleSucc && isa<ReturnInst>(singleSucc->getTerminator()))
        return 1;
    }
    return -1;
  }

  BasicBlock* isExitingFunction(BasicBlock* bb){
    Instruction *term = bb->getTerminator();
    if(isa<ReturnInst>(term))
      return bb;

    if(term->getNumSuccessors() > 1)
      return nullptr;

    if(isa<UnreachableInst>(term))
      return bb;

    BasicBlock *succ = term->getSuccessor(0);
    Instruction *ret = succ->getTerminator();

    if(isa<ReturnInst>(ret)) return succ;
    else return nullptr;
  }

  bool noElseRegion(bool trueBranch);
  std::vector<CBERegion2*> thenSubRegions;
  std::vector<CBERegion2*> elseSubRegions;
  BasicBlock* brBB;
  BranchInst* brInst;
  BasicBlock* pdBB;
  BasicBlock* trueStartBB;
  BasicBlock* falseStartBB;
  std::set<BasicBlock*> trueBBs;
  std::set<BasicBlock*> falseBBs;
};

}
