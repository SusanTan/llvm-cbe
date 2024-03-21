#include "CBackend.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/CodeGen/TargetLowering.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/TargetRegistry.h"

#include "TopologicalSorter.h"

#include <algorithm>
#include <cstdio>

#include <iostream>

// SUSAN: added libs
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

namespace llvm_cbe {

using namespace llvm;

LinearRegion::LinearRegion(BasicBlock *entryBB, CBERegion2 *parentR, LoopInfo *LI, PostDominatorTree *PDT, DominatorTree *DT, CWriter *cwriter)
: CBERegion2{ LI, PDT, DT, parentR, entryBB, cwriter}{
  /*for return block*/
  Instruction *term = entryBB->getTerminator();
  if(isa<ReturnInst>(term) || isa<UnreachableInst>(term)){
    BBs.push_back(entryBB);
    nextEntryBB = nullptr;
    return;
  }

  BasicBlock *nextBB = entryBB;
  Loop *l = LI->getLoopFor(entryBB);
  LoopRegion* lr = getParentLoopRegion();
  while(true){
    if(lr)
      lr->removeBBToVisit(nextBB);
    BBs.push_back(nextBB);
    errs() << "CBERegion: including " << nextBB->getName() << " in a linear region\n";
    if(nextBB) errs() << "CBERegion: nextBB " << *nextBB << "\n";
    nextBB = nextBB->getSingleSuccessor();
    nextEntryBB = nextBB;
    if(!nextBB || nextBB->getSingleSuccessor() == nullptr) break;
    Loop *lNextBB = LI->getLoopFor(nextBB);
    if(lNextBB && lNextBB->getLoopLatch() == nextBB) break;
  }
}


bool IfElseRegion::noElseRegion(bool trueBranch){
  std::set<BasicBlock*> branchBBs = trueBranch ? falseBBs : trueBBs;
  bool NoElseRegion = true;
  for(auto bb : branchBBs){
    for(auto &I : *bb){
      if(!isa<BranchInst>(&I)){
        NoElseRegion = false;
        break;
      }
    }
  }
  errs() << NoElseRegion << "\n";
  return NoElseRegion;
}

IfElseRegion::IfElseRegion(BasicBlock *entryBB, CBERegion2 *parentR, PostDominatorTree *PDT, DominatorTree *DT, LoopInfo* LI, CWriter *cwriter) : CBERegion2{ LI, PDT, DT, parentR, entryBB, cwriter}{
    errs() << "creating if-else region for entryBB: " << entryBB->getName() << "\n";
    /*fetch branch related infos*/
    this->brBB = entryBB;
    this->brInst = dyn_cast<BranchInst>(entryBB->getTerminator());
    assert(this->brInst && "terminator is not branch inst 600!\n");
    BranchInst *br = dyn_cast<BranchInst>(entryBB->getTerminator());
    assert(br && "not a branch inst to start if else region\n");
    this->trueStartBB = br->getSuccessor(0);
    this->falseStartBB = br->getSuccessor(1);
    for(auto &BB : *(brBB->getParent()))
      if(PDT->dominates(&BB, brBB)){
        this->pdBB = &BB;
        break;
      }
    for(auto &BB : *(brBB->getParent())){
      if(DT->dominates(trueStartBB, &BB) && PDT->dominates(pdBB, &BB) && pdBB != &BB)
        trueBBs.insert(&BB);
      if(DT->dominates(falseStartBB, &BB) && PDT->dominates(pdBB, &BB) && pdBB != &BB)
        falseBBs.insert(&BB);
    }
    bool exitFunctionTrueBr = isExitingFunction(trueStartBB);
    bool exitFunctionFalseBr = isExitingFunction(falseStartBB);
    bool trueBrOnly = noElseRegion(true);
    bool falseBrOnly = noElseRegion(false);
    int returnDominated = dominatedByReturn(brBB);
    if(!trueBrOnly && !falseBrOnly && returnDominated == -1){
      trueBrOnly = (exitFunctionTrueBr && !exitFunctionFalseBr);
      falseBrOnly = (exitFunctionFalseBr && !exitFunctionTrueBr);
    }

    if(trueBrOnly && returnDominated == -1){
      errs() << "SUSAN: marking only true branch\n";
      if(auto lr = getParentLoopRegion())
        for(auto BB : falseBBs)
          lr->removeBBToVisit(BB);
      createSubIfElseRegions(trueStartBB, brBB, falseStartBB, false);
      nextEntryBB = falseStartBB;
    }
    else if(falseBrOnly && returnDominated == -1){
      errs() << "SUSAN: marking only false branch\n";
      if(auto lr = getParentLoopRegion())
        for(auto BB : trueBBs)
          lr->removeBBToVisit(BB);
      createSubIfElseRegions(falseStartBB, brBB, trueStartBB, true);
      nextEntryBB = trueStartBB;
    }
    else{
      errs() << "SUSAN: marking both branches\n";
      auto nextEntryBB1 = createSubIfElseRegions(trueStartBB, brBB, falseStartBB, false);
      auto nextEntryBB2 = createSubIfElseRegions(falseStartBB, brBB, trueStartBB, true);
      nextEntryBB = nextEntryBB1 ? nextEntryBB1 : nextEntryBB2;
      errs() << "CBERegion: nextEntryBB 121: " << nextEntryBB->getName() << "\n";
    }

    if(parentR && parentR->isaLoopRegion())
      removeIfElseBlockFromLR((LoopRegion*)parentR, brBB);
    errs() << "=================SUSAN: END OF marking region : " << br->getParent()->getName() << "==================\n";
}


BasicBlock* IfElseRegion::createSubIfElseRegions(BasicBlock* start, BasicBlock *brBlock, BasicBlock *otherStart, bool isElseBranch){
    LoopRegion* lr = getParentLoopRegion();
    if(lr)
      lr->removeBBToVisit(brBlock);

    BasicBlock *currBB = start;
    while (!PDT->dominates(currBB, brBlock) && currBB != otherStart){
      CBERegion2 *subR = createSubRegions(this, currBB);
      if(!isElseBranch) thenSubRegions.push_back(subR);
      else elseSubRegions.push_back(subR);
      if(isa<UnreachableInst>(currBB->getTerminator())) break;
      currBB = subR->getNextEntryBB();
      errs() << "SUSAN: currbb 562: " << currBB->getName() << "\n";
    }
    return currBB;
}

void LoopRegion::createCBERegionDAG(BasicBlock* entryBB){
  BasicBlock *nextRegionEntryBB = entryBB;
  while(!this->hasNoRemainingBBs()){
    errs() << "CBERegion: here? 149\n";
    CBERegion2 *entryR = createSubRegions(this, nextRegionEntryBB);
    LoopBodyRegionDAG.push_back(entryR);
    if(nextRegionEntryBB){
      nextRegionEntryBB = entryR->getNextEntryBB();
      errs() << "SUSAN: nextRegionEntryBB " << nextRegionEntryBB->getName() << "\n";
      errs() << "for region: " << *(this->loop) << "\n";
    }
  }
}

void CBERegion2::createCBERegionDAG(BasicBlock* entryBB, CBERegion2 *parentR, BasicBlock *endBB){
  CBERegion2 *entryR = createSubRegions(parentR, entryBB);
  CBERegionDAG.push_back(entryR);
  if(entryBB == endBB) return;

  BasicBlock *nextRegionEntryBB = entryR->getNextEntryBB();
  if(nextRegionEntryBB){
    errs() << "SUSAN: nextRegionEntryBB " << nextRegionEntryBB->getName() << "\n";
    createCBERegionDAG(nextRegionEntryBB, parentR, endBB);
  }
}

void LinearRegion::print(){
  errs() << "Linear Region with entry block: " << getEntryBlock()->getName() << "\n";
  for(auto BB : BBs)
    errs() << BB->getName() << "\n";
}
void IfElseRegion::print(){
  errs() << "IfElse Region with entry block: " << getEntryBlock()->getName() << "\n";
  errs() << "thenSubRegions : \n";
  for(auto R : thenSubRegions)
    R->print();
  errs() << "elseSubRegions : \n";
  for(auto R : elseSubRegions)
    R->print();
}
void LoopRegion::print(){
  errs() << "Loop Region with entry block: " << getEntryBlock()->getName() << "\n";
  for(auto R : LoopBodyRegionDAG)
    R->print();
}
void CBERegion2::print(){
  errs() << "======================Printing CBERegions================\n";
  errs() << "Top CBERegion\n";
  for(auto R : CBERegionDAG)
    R->print();
}

void LinearRegion::printRegionDAG(){
  errs() << "Linear Region with entry block: " << getEntryBlock()->getName() << "\n";
  for(auto BB : BBs){
    errs() << "SUSAN: printing bb:" << BB->getName() << "\n";
    cw->printBasicBlock(BB);
  }
}
void IfElseRegion::printRegionDAG(){
  errs() << "IfElse Region with entry block: " << getEntryBlock()->getName() << "\n";
  errs() << "thenSubRegions : \n";

  auto condInst = brInst->getCondition();
  //print instructions before the branch
  for(auto &I : *brBB){
    if(&I == condInst)
      break;
    if(cw->isSkipableInst(&I)) continue;
    cw->printInstruction(&I);
  }


  //print If branch
  cw->Out << "  if (";
  cw->writeOperand(condInst, cw->ContextCasted);
  cw->Out << ") {\n";
  for(auto R : thenSubRegions)
    R->printRegionDAG();

  //print else branch
  if(!elseSubRegions.empty()){
    errs() << "elseSubRegions : \n";
    cw->Out << "  } else {\n";
    for(auto R : elseSubRegions)
      R->printRegionDAG();
  }

  cw->Out << "  }\n";
}

void LoopRegion::printRegionDAG(){
  errs() << "Loop Region with entry block: " << getEntryBlock()->getName() << "\n";

  BasicBlock *header = loop->getHeader();
  bool negateCondition = false;
  Instruction *condInst = cw->findCondInst(loop, negateCondition);

  std::set<Instruction*> printedLiveins;
  std::set<Value*> condRelatedInsts;
  BasicBlock *condBlock = condInst->getParent();
  cw->findCondRelatedInsts(condBlock, condRelatedInsts);
  for(auto condRelatedInst : condRelatedInsts){
    Instruction *inst = cast<Instruction>(condRelatedInst);
    errs() << "SUSAN: condrelatedinst:" << *inst << "\n";
    if(cw->isIVIncrement(inst) ||isa<PHINode>(inst)
        || isa<BranchInst>(inst) || isa<CmpInst>(inst)
        || cw->isInlinableInst(*inst) || inst == this->incr)
      continue;
    errs() << "SUSAN: printing condRelatedInst: " << *inst << "\n";
    cw->printInstruction(inst);
  }

  auto headerBr = dyn_cast<BranchInst>(header->getTerminator());
  if(headerBr->getMetadata("tulip.doall.loop.grid.collapse"))
    cw->Out << "#pragma omp parallel for collapse(2)";
  else if(headerBr->getMetadata("tulip.doall.loop.grid")){
    bool printCollapse = false;
    for (BasicBlock *BB : loop->getBlocks()){
      if(BB->getTerminator()->getMetadata("tulip.doall.loop.block")){
        cw->Out << "#pragma omp parallel for collapse(2)";
        printCollapse = true;
        break;
      }
    }
    if(!printCollapse)
      cw->Out << "#pragma omp parallel for";
  }
  else if(headerBr->getMetadata("noelle.doall.loop")){
    bool printReduction = false;
    for (BasicBlock *BB : loop->getBlocks()){
      for(auto &I : *BB){
        if(I.getMetadata("tulip.reduce.add")){
          printReduction = true;
          cw->Out << "#pragma omp simd reduction(+:";
          cw->writeOperand(&I);
          cw->Out << ")";
        }
      }
    }
    if(!printReduction)
      cw->Out << "#pragma omp parallel for ";
  }

  //for (BasicBlock *BB : loop->getBlocks()){
  //  for(auto &I : *BB){
  //    if(I.getMetadata("tulip.reduce.add")){
  //      cw->Out << "#pragma omp simd reduction(+:";
  //      cw->writeOperand(&I);
  //      cw->Out << ")";
  //    }
  //    else if(I.getMetadata("tulip.arr.reduce.add")){
  //      cw->Out << "#pragma omp simd reduction(+:";
  //      GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&I);
  //      Value *ptr = gep->getPointerOperand();
  //      cw->Out<<cw->GetValueName(ptr);
  //      PointerType *ptrTy = dyn_cast<PointerType>(ptr->getType());
  //      cw->Out << "[0:";
  //      assert(ptrTy && "CBERegion: not a pointer type? 288\n");
  //      ArrayType* arrTy = dyn_cast<ArrayType>(ptrTy->getPointerElementType());
  //      assert(arrTy && "CBERegion: not an array type? 290\n");
  //      cw->Out << arrTy->getNumElements();
  //      cw->Out << "]";
  //      cw->Out << ")";
  //    }
  //  }
  //}

  cw->Out << "\nfor(";

  //initiation
  cw->printTypeName(cw->Out, IV->getType(), true);
  cw->Out << " ";
  cw->Out << cw->GetValueName(IV, true) << " = ";
  if(Instruction* lbInst = dyn_cast<Instruction>(lb))
    cw->writeInstComputationInline(*lbInst);
  else cw->writeOperand(lb);
  cw->Out << "; ";

  //exit condition
  cw->Out << cw->GetValueName(condInst->getOperand(0));
  if(ICmpInst *icmp = dyn_cast<ICmpInst>(condInst)){
    if(!negateCondition && (icmp->getPredicate() == ICmpInst::ICMP_NE))
      cw->Out << " < ";
    else if(negateCondition && (icmp->getPredicate() == ICmpInst::ICMP_EQ))
      cw->Out << " < ";
    else cw->printCmpOperator(icmp, negateCondition);
  }
  cw->writeOperandInternal(condInst->getOperand(1));
  cw->Out << "; ";

  //increment
  cw->printInstruction(cast<Instruction>(incr), false);
  cw->Out << "){\n";

  //print loop body
  for(auto R : LoopBodyRegionDAG)
    R->printRegionDAG();

  //print extra instructions in a latch other than incr and br
  errs() << "CBERegion: printing latchBB " << latchBB->getName() << "\n";
  for(auto &I : *latchBB){
    errs() << "CBERegion: I 316: " << I << "\n";
    if(!cw->isSkipableInst(&I) && incr != &I && latchBB->getTerminator() != &I)
      cw->printInstruction(&I);
  }

  cw->Out << "}\n";
}

void CBERegion2::printRegionDAG(){
  for(auto R : CBERegionDAG){
    R->printRegionDAG();
  }
}

void IfElseRegion::removeIfElseBlockFromLR(LoopRegion* lr, BasicBlock *brBB){
  for(auto &BB : *(brBB->getParent()))
    if(DT->dominates(brBB, &BB) && PDT->dominates(pdBB, &BB) && pdBB != &BB)
      lr->removeBBToVisit(&BB);
}

LoopRegion::LoopRegion(BasicBlock *entryBB, LoopInfo *LI, PostDominatorTree* PDT, DominatorTree *DT, CBERegion2 *parentR, CWriter *cwriter)
  : CBERegion2{ LI, PDT, DT, parentR, entryBB, cwriter}{
    //latch BB isn't considered a loop body;
    errs() << "creating loop region for entryBB: " << entryBB->getName() << "\n";

    parentRegion = parentR;
    loop = LI->getLoopFor(entryBB);
    latchBB = loop->getLoopLatch();
    errs() << "SUSAN: loop at 355 " << *loop << "\n";
    this->IV = cw->getInductionVariable(loop);
    this->IVInc = cw->getIVIncrement(loop, IV);
    if(LI->getLoopFor(IV->getIncomingBlock(0)) != loop)
      this->lb = IV->getIncomingValue(0);
    else if((LI->getLoopFor(IV->getIncomingBlock(0)) == loop))
      this->incr = IV->getIncomingValue(0);
    if(LI->getLoopFor(IV->getIncomingBlock(1)) != loop)
      this->lb = IV->getIncomingValue(1);
    else if((LI->getLoopFor(IV->getIncomingBlock(1)) == loop))
      this->incr = IV->getIncomingValue(1);
    bool negateCondition = false;
    Instruction *condInst = cw->findCondInst(loop, negateCondition);
    this->ub = condInst->getOperand(1);
    this->nestlevel = -1;

    assert(loop && "cannot find loop for a loop region\n");
    nextEntryBB = loop->getUniqueExitBlock();
    //errs() << "next entry BB: " << nextEntryBB->getName() << "\n";
    assert(nextEntryBB && "loop doesn't have unique exit block\n");

    auto loopBBs = loop->getBlocks();
    LoopRegion* lr = getParentLoopRegion();
    for( auto BB : loopBBs){
      if(lr)
        lr->removeBBToVisit(BB);
      if(BB != entryBB && BB != latchBB)
        remainingBBsToVisit.insert(BB);
    }

    BasicBlock* startBB = entryBB;
    auto br = dyn_cast<BranchInst>(entryBB->getTerminator());
    auto succ0 = br->getSuccessor(0);
    auto succ1 = br->getSuccessor(1);
    BasicBlock *bodyBB = nullptr;
    if(succ0 == nextEntryBB) startBB = succ1;
    else if(succ1 == nextEntryBB) startBB = succ0;
    else assert(0 && "exit block is not from header!\n");
    errs() << "CBERegion: startBB 393: " << *startBB << "\n";
    createCBERegionDAG(startBB);
}

CBERegion2* CBERegion2::createSubRegions(CBERegion2 *parentR, BasicBlock* entryBB){
  CBERegion2 *R = nullptr;
  switch (whichRegion(entryBB, LI)){
    case 0:
    {
      errs() << "SUSAN: entry block is a linear region! " << entryBB->getName() << "\n";
      R = new LinearRegion(entryBB, parentR, LI, PDT, DT, this->cw);
      break;
    }
    case 1:
    {
      errs() << "SUSAN: entry block is an if-else region! " << entryBB->getName() << "\n";
      R = new IfElseRegion(entryBB, parentR, PDT, DT, LI, this->cw);
      break;
    }
    case 2:
    {
      errs() << "SUSAN: entry block is a loop region! " << entryBB->getName() << "\n";
      R = new LoopRegion(entryBB, LI, PDT, DT, parentR, this->cw);
      break;
    }
  }
  return R;
}

}
