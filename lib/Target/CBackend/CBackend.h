#include "CTargetMachine.h"
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

#include "IDMap.h"

// SUSAN ADDED LIBS
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <queue>

namespace llvm_cbe {

using namespace llvm;

//utility functions
//SUSAN: added structs
typedef struct CBERegion{
  BasicBlock *entryBlock; //entryBlock itself should belong to parent region
  CBERegion *parentRegion;
  std::vector<BasicBlock*> thenBBs;
  std::vector<BasicBlock*> elseBBs;
  std::vector<struct CBERegion*> thenSubRegions;
  std::vector<struct CBERegion*> elseSubRegions;
  std::vector<std::pair<BasicBlock*, BasicBlock*>> thenEdges;
  std::vector<std::pair<BasicBlock*, BasicBlock*>> elseEdges;
} CBERegion;

typedef struct LoopProfile{
  Loop *L;
  Value *ub;
  int ubOffset;
  Value *lb;
  Value *incr;
  PHINode *IV;
  Instruction *IVInc;
  bool isOmpLoop;
  bool barrier;
  Value* lbAlloca;
  bool isForLoop;
  int nestlevel;
  int schedtype;
  int chunksize;
} LoopProfile;

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

/// CWriter - This class is the main chunk of code that converts an LLVM
/// module to a C translation unit.
class CWriter : public ModulePass, public InstVisitor<CWriter> {

  public:
  void printBasicBlock(BasicBlock *BB, std::set<Value*> skipInsts = std::set<Value*>());
  raw_string_ostream Out;
  enum OperandContext {
    ContextNormal,
    ContextCasted,
    ContextStatic
  };
  void writeOperandDeref(Value *Operand);
  void writeOperand(Value *Operand,
                    enum OperandContext Context = ContextNormal, bool startExpression = true);
  void writeInstComputationInline(Instruction &I, bool startExpression=true);
  void writeOperandInternal(Value *Operand,
                            enum OperandContext Context = ContextNormal, bool startExpression = true);
  void writeOperandWithCast(Value *Operand, unsigned Opcode, bool startExpression = true);
  void opcodeNeedsCast(unsigned Opcode, bool &shouldCast, bool &castIsSigned);

  void writeOperandWithCast(Value *Operand, ICmpInst &I);
  Instruction* findCondInst(Loop *L, bool &negateCondition);
  void findCondRelatedInsts(BasicBlock *skipBlock, std::set<Value*> &condRelatedInsts);
  bool isIVIncrement(Value* V);
  bool isInlinableInst(Instruction &I) const;
  void printInstruction(Instruction *I, bool printSemiColon = true);
  PHINode* getInductionVariable(Loop *L);
  Instruction *getIVIncrement(Loop *L, PHINode* IV);
  void printCmpOperator(ICmpInst *icmp, bool negateCondition = false);
  std::string GetValueName(Value *Operand, bool isDeclaration=false);
  bool isSkipableInst(Instruction* inst);


  private:
  //SUSAN: counters
  int cnt_totalVariables;
  int cnt_reconstructedVariables;

  //SUSAN: tables not need to be saved when inlining
  std::map<Value*, std::string> inlinedArgNames;
  std::set<LoadInst*> addressExposedLoads;
  std::set<Value*> valuesCast2Double;

  // SUSAN: tables for variable preservation
  std::set<std::pair<Value*, std::string>> IRNaming;
  std::set<std::string>allVars, phiVars;
  //std::set<BasicBlock*>printedBBs;
  std::map<BasicBlock*, int> times2bePrinted;
  //std::set<BasicBlock*> splittedBBs;
  //std::set<Instruction*> declaredInsts;
  std::set<std::pair<BasicBlock*, BasicBlock*>> irregularLoopExits;
  std::vector<Instruction*> ifBranches;
  std::set<GetElementPtrInst*> accessGEPMemory;
  std::set<GetElementPtrInst*> GEPPointers;
  std::set<GetElementPtrInst*> NoneArrayGEPs;
  std::map<Value*, int> Times2Dereference;
  std::pair<Value*,int> currValue2DerefCnt;
  std::set<BasicBlock*> printLabels;
  std::set<BranchInst*> gotoBranches;
  std::set<CallInst*> loopCondCalls;
  std::map<BasicBlock*, CBERegion*> CBERegionMap;
  std::map<CBERegion*, BasicBlock*> recordedRegionBBs;
  bool gepStart;
  std::set<std::pair<BasicBlock*, BasicBlock*>> backEdges;
  bool NATURAL_CONTROL_FLOW;
  std::set<Instruction*> signedInsts;
  std::map<SExtInst*, Instruction*> declareAsCastedType;
  //std::set<std::pair<BasicBlock*, PHINode*>> printedPHIValues;
  std::set<std::pair<BasicBlock*, PHINode*>> PHIValues2Print;
  std::map<CallInst*, Function*> ompFuncs;
  std::set<Value*> omp_SkipVals;
  bool IS_OPENMP_FUNCTION;
  std::set<LoopProfile*> LoopProfiles;
  std::set<GetElementPtrInst*> GEPNeedsReference;
  //std::set<Value*>skipInstsForPhis;
  //std::map<PHINode*, std::set<Value*>>phis2print;
  std::map<Value*, PHINode*>InstsToReplaceByPhi;
  std::map<Loop*, std::set<Instruction*>> omp_liveins;
  std::map<Instruction*, Value*> deleteAndReplaceInsts;
  std::map<BranchInst*, int> deadBranches;
  bool omp_declarePrivate;
  void EliminateDeadInsts(Function &F);
  int returnDominated;
  std::set<Instruction*> deadInsts;
  std::map<PHINode*, std::set<PHINode*>> IVMap;
  std::map<Instruction*, PHINode*> IVInc2IV;
  std::set<Value*> UpperBoundArgs;
  std::set<Instruction*> addParenthesis;
  std::set<std::string> declaredLocals;
  std::set<std::string> omp_declaredLocals;
  std::map<Value*, std::string> IV2Name;
  std::set<Instruction*> notInlinableBinOps;
  std::map<Value*, Type*> type2declare;
  std::map<Instruction*, Value*> doubleGeps;
  std::map<Value*, Type*> mallocType;
  std::map<Function*, int> FunctionTopLoopLevels;
  std::set<Instruction*>noneSkipAllocaInsts;

  CBERegion *topRegion;
  CBERegion2 *TopRegion;

  // SUSAN: added analyses
  PostDominatorTree *PDT = nullptr;
  DominatorTree *DT = nullptr;
  RegionInfo *RI = nullptr;
  ScalarEvolution *SE = nullptr;

  std::string _Out;
  std::string _OutHeaders;
  raw_string_ostream OutHeaders;
  raw_ostream &FileOut;
  IntrinsicLowering *IL = nullptr;
  LoopInfo *LI = nullptr;
  const Module *TheModule = nullptr;
  const MCAsmInfo *TAsm = nullptr;
  const MCRegisterInfo *MRI = nullptr;
  const MCObjectFileInfo *MOFI = nullptr;
  MCContext *TCtx = nullptr;
  const DataLayout *TD = nullptr;
  const Instruction *CurInstr = nullptr;
  const Loop *CurLoop = nullptr;

  IDMap<const ConstantFP *> FPConstantMap;
  std::set<const Argument *> ByValParams;

  IDMap<const Value *> AnonValueNumbers;

  /// UnnamedStructIDs - This contains a unique ID for each struct that is
  /// either anonymous or has no name.
  IDMap<StructType *> UnnamedStructIDs;

  std::set<Type *> TypedefDeclTypes;
  std::set<Type *> SelectDeclTypes;
  std::set<std::pair<CmpInst::Predicate, VectorType *>> CmpDeclTypes;
  std::set<std::pair<CastInst::CastOps, std::pair<Type *, Type *>>>
      CastOpDeclTypes;
  std::set<std::pair<unsigned, Type *>> InlineOpDeclTypes;
  std::set<Type *> CtorDeclTypes;

  IDMap<std::pair<FunctionType *, std::pair<AttributeList, CallingConv::ID>>>
      UnnamedFunctionIDs;

  // This is used to keep track of intrinsics that get generated to a lowered
  // function. We must generate the prototypes before the function body which
  // will only be expanded on first use
  std::vector<Function *> prototypesToGen;

  unsigned LastAnnotatedSourceLine = 0;

  struct {
    // Standard headers
    bool Stdarg : 1;
    bool Setjmp : 1;
    bool Limits : 1;
    bool Math : 1;

    // printModuleTypes()
    bool BitCastUnion : 1;

    // generateCompilerSpecificCode()
    bool BuiltinAlloca : 1;
    bool Unreachable : 1;
    bool NoReturn : 1;
    bool ExternalWeak : 1;
    bool AttributeWeak : 1;
    bool Hidden : 1;
    bool AttributeList : 1;
    bool UnalignedLoad : 1;
    bool MsAlign : 1;
    bool NanInf : 1;
    bool Int128 : 1;
    bool ThreadFence : 1;
    bool StackSaveRestore : 1;
    bool ConstantDoubleTy : 1;
    bool ConstantFloatTy : 1;
    bool ConstantFP80Ty : 1;
    bool ConstantFP128Ty : 1;
    bool ForceInline : 1;
  } UsedHeaders;

#define USED_HEADERS_FLAG(Name)                                                \
  void headerUse##Name() { UsedHeaders.Name = true; }                          \
  bool headerInc##Name() const { return UsedHeaders.Name; }

  // Standard headers
  USED_HEADERS_FLAG(Stdarg)
  USED_HEADERS_FLAG(Setjmp)
  USED_HEADERS_FLAG(Limits)
  USED_HEADERS_FLAG(Math)

  // printModuleTypes()
  USED_HEADERS_FLAG(BitCastUnion)

  // generateCompilerSpecificCode()
  USED_HEADERS_FLAG(BuiltinAlloca)
  USED_HEADERS_FLAG(Unreachable)
  USED_HEADERS_FLAG(NoReturn)
  USED_HEADERS_FLAG(ExternalWeak)
  USED_HEADERS_FLAG(AttributeWeak)
  USED_HEADERS_FLAG(Hidden)
  USED_HEADERS_FLAG(AttributeList)
  USED_HEADERS_FLAG(UnalignedLoad)
  USED_HEADERS_FLAG(MsAlign)
  USED_HEADERS_FLAG(NanInf)
  USED_HEADERS_FLAG(Int128)
  USED_HEADERS_FLAG(ThreadFence)
  USED_HEADERS_FLAG(StackSaveRestore)
  USED_HEADERS_FLAG(ConstantDoubleTy)
  USED_HEADERS_FLAG(ConstantFloatTy)
  USED_HEADERS_FLAG(ConstantFP80Ty)
  USED_HEADERS_FLAG(ConstantFP128Ty)
  USED_HEADERS_FLAG(ForceInline)

  llvm::SmallSet<CmpInst::Predicate, 26> FCmpOps;
  void headerUseFCmpOp(CmpInst::Predicate P);

  void generateCompilerSpecificCode(raw_ostream &Out, const DataLayout *) const;

public:
  static char ID;
  explicit CWriter(raw_ostream &o)
      : ModulePass(ID), OutHeaders(_OutHeaders), Out(_Out), FileOut(o) {
    memset(&UsedHeaders, 0, sizeof(UsedHeaders));
  }

  virtual StringRef getPassName() const { return "C backend"; }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<RegionInfoPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.setPreservesCFG();
  }

  virtual bool doInitialization(Module &M);
  virtual bool doFinalization(Module &M);
  //virtual bool runOnFunction(Function &F);
  virtual bool runOnModule(Module &M);

private:
  void generateHeader(Module &M);
  void declareOneGlobalVariable(GlobalVariable *I);

  void forwardDeclareStructs(raw_ostream &Out, Type *Ty,
                             std::set<Type *> &TypesPrinted);

  raw_ostream &printFunctionAttributes(raw_ostream &Out, AttributeList Attrs);

  bool isStandardMain(const FunctionType *FTy);
  raw_ostream &
  printFunctionProto(raw_ostream &Out, FunctionType *Ty,
                     std::pair<AttributeList, CallingConv::ID> Attrs,
                     const std::string &Name,
                     iterator_range<Function::arg_iterator> *ArgList, int skipArgSteps = 0);
  raw_ostream &printFunctionProto(raw_ostream &Out, Function *F, int skipArgSteps = 0) {
    return printFunctionProto(
        Out, F->getFunctionType(),
        std::make_pair(F->getAttributes(), F->getCallingConv()),
        GetValueName(F), nullptr, skipArgSteps);
  }

  raw_ostream &
  printFunctionDeclaration(raw_ostream &Out, FunctionType *Ty,
                           std::pair<AttributeList, CallingConv::ID> PAL =
                               std::make_pair(AttributeList(), CallingConv::C));
  raw_ostream &printStructDeclaration(raw_ostream &Out, StructType *Ty);
  raw_ostream &printArrayDeclaration(raw_ostream &Out, ArrayType *Ty);
  raw_ostream &printVectorDeclaration(raw_ostream &Out, VectorType *Ty);

  raw_ostream &printTypeName(raw_ostream &Out, Type *Ty, bool isSigned = false,
                             std::pair<AttributeList, CallingConv::ID> PAL =
                                 std::make_pair(AttributeList(),
                                                CallingConv::C));
  raw_ostream &printTypeNameForAddressableValue(raw_ostream &Out, Type *Ty,
                                                bool isSigned = false);
  raw_ostream &printTypeNameUnaligned(raw_ostream &Out, Type *Ty,
                                      bool isSigned = false);
  raw_ostream &printSimpleType(raw_ostream &Out, Type *Ty, bool isSigned);
  raw_ostream &printTypeString(raw_ostream &Out, Type *Ty, bool isSigned);

  std::string getStructName(StructType *ST);
  std::string getFunctionName(FunctionType *FT,
                              std::pair<AttributeList, CallingConv::ID> PAL =
                                  std::make_pair(AttributeList(),
                                                 CallingConv::C));
  std::string getArrayName(ArrayType *AT);
  std::string getVectorName(VectorType *VT, bool Aligned);


  // SUSAN: added functions
  void emitIfBlock(CBERegion *R, bool doNotPrintReturn=false, bool isElseBranch=false);
  void markLoopIrregularExits(Function &F);
  void NodeSplitting(Function &F);
  void markIfBranches(Function &F, std::set<BasicBlock*> *visitedBBs);
  void markGotoBranches(Function &F);
  void printPHICopiesForAllPhis(BasicBlock *CurBlock, unsigned Indent);
  void emitSwitchBlock(BasicBlock* start, BasicBlock *brBlockk);
  bool GEPAccessesMemory(GetElementPtrInst *I);
  void collectNoneArrayGEPs(Function &F);
  void collectVariables2Deref(Function &F);
  Value* findUnderlyingObject(Value *Ptr);
  void findVariableDepth(Type *Ty, Value *UO, int depths);
  void markBBwithNumOfVisits(Function &F);
  Instruction* headerIsExiting(Loop *L, bool &negateCondition, BranchInst* brInst = nullptr);
  void recordTimes2bePrintedForBranch(BasicBlock* start, BasicBlock *brBlock, BasicBlock *otherStart, CBERegion *R, bool isElseBranch = false);
  void CountTimes2bePrintedByRegionPath ();
  void markBranchRegion(Instruction* br, CBERegion* targetRegion);
  bool alreadyVisitedRegion (BasicBlock* bbUT);
  CBERegion* createNewRegion(BasicBlock* entryBB, CBERegion* parentR, bool isElseRegion);
  void createSubRegionOrRecordCurrentRegion(BasicBlock* predBB, BasicBlock* currBB, CBERegion *R, bool isElseBranch);
  BasicBlock* findFirstBrBlock(BasicBlock* entryBlock);
  void markBackEdges(Function &F);
  bool edgeBelongsToSubRegions(BasicBlock *fromBB, BasicBlock* toBB, CBERegion *R, bool isElseBranch);
  bool nodeBelongsToRegion(BasicBlock* BB, CBERegion *R, bool isElseBranch = false);
  void determineControlFlowTranslationMethod(Function &F);
  void naturalBranchTranslation(BranchInst &I);
  void naturalSwitchTranslation(SwitchInst &SI);
  std::set<BasicBlock*> findRegionEntriesOfBB (BasicBlock* BB);
  void findSignedInsts(Instruction* inst, Instruction* signedInst);
  void insertDeclaredInsts(Instruction* I);
  bool alreadyPrintedPHIVal(BasicBlock* predBB, PHINode* phi);
  void preprossesPHIs2Print(Function &F);
  void emitOmpFunction(Function &F);
  void omp_searchForUsesToDelete(std::set<Value*> values2delete, Function &F);
  void omp_preprossesing(Function &F);
  Loop* findLoopAccordingTo(Function &F, Value *bound);
  void CreateOmpLoops(Loop *L, Value* ub, Value *lb, Value *incr);
  LoopProfile* findLoopProfile(Loop *L);
  void printLoopBody(LoopProfile *LP, Instruction *condInst,  std::set<Value*> &skipInsts);
  bool isInductionVariable(Value* V);
  bool isExtraInductionVariable(Value* V);
  void initializeLoopPHIs(Loop *L);
  void printPHIsIfNecessary(BasicBlock* BB);
  void FindLiveInsFor(Loop *L, Value *val);
  void searchForBlocksToSkip(Loop *L, std::set<BasicBlock*> &skipBlocks);
  void DeclareLocalVariable(Instruction *I, bool &PrintedVar, bool &isDeclared, std::set<std::string> &declaredLocals);
  void OMP_RecordLiveIns(LoopProfile *LP);
  void keepIVUnrelatedInsts(BasicBlock *skipBB, Instruction *condInst, std::set<Instruction*> &InstsKeptFromSkipBlock);
  bool canSkipHeader(BasicBlock* header);
  void preprocessSkippableInsts(Function &F);
  void preprocessLoopProfiles(Function &F);
  void preprocessSkippableBranches(Function &F);
  Value* findOriginalValue(Value *val);
  CBERegion* findRegionOfBlock(BasicBlock* BB);
  int dominatedByReturn(BasicBlock* brBB);
  bool noElseRegion(bool trueBranch, BasicBlock *brBB);
  void removeBranchTarget(BranchInst *br, int destIdx);
  void FindInductionVariableRelationships();
  bool isExtraIVIncrement(Value* V);
  void findOMPFunctions(Module &M);
  void preprocessIVIncrements();
  Value* findOriginalUb(Function &F, Value *ub, CallInst *initCI, CallInst *prevFini, int &offset);
  void preprocessInsts2AddParenthesis(Function &F);
  bool hasHigherOrderOps(Instruction* I, std::set<unsigned> higherOrderOpcodes);
  bool RunAllAnalysis(Function &F);
  void omp_findInlinedStructInputs(Value* argInput, std::map<int, Value*> &argInputs);
  void omp_findCorrespondingUsesOfStruct(Value* arg, std::map<int, Value*> &args);
  void inlineNameForArg(Value* argInput, Value* arg);
  void buildIVNames();
  void buildInlinedArgsTable(Function &F);
  void collectNotInlinableBinOps(Function &F);
  void findDoubleGEP(Function &F);
  void findMallocType(Function &F);



  bool writeInstructionCast(Instruction &I);
  void writeMemoryAccess(Value *Operand, Type *OperandType, bool IsVolatile,
                         unsigned Alignment);

  std::string InterpretASMConstraint(InlineAsm::ConstraintInfo &c);

  bool lowerIntrinsics(Function &F);
  /// Prints the definition of the intrinsic function F. Supports the
  /// intrinsics which need to be explicitly defined in the CBackend.
  void printIntrinsicDefinition(Function &F, raw_ostream &Out);
  void printIntrinsicDefinition(FunctionType *funT, unsigned Opcode,
                                std::string OpName, raw_ostream &Out);

  void printModuleTypes(raw_ostream &Out);
  void printContainedTypes(raw_ostream &Out, Type *Ty, std::set<Type *> &);

  void printFloatingPointConstants(Function &F);
  void printFloatingPointConstants(const Constant *C);

  void printFunction(Function &F, bool inlineF=false);
  void printLoop(Loop *L);
  void printLoopNew(Loop *L);

  void printCast(unsigned opcode, Type *SrcTy, Type *DstTy);
  void printConstant(Constant *CPV, enum OperandContext Context);
  void printConstantWithCast(Constant *CPV, unsigned Opcode);
  bool printConstExprCast(ConstantExpr *CE);
  void printConstantArray(ConstantArray *CPA, enum OperandContext Context);
  void printConstantVector(ConstantVector *CV, enum OperandContext Context);
  void printConstantDataSequential(ConstantDataSequential *CDS,
                                   enum OperandContext Context);
  bool printConstantString(Constant *C, enum OperandContext Context);

  bool isEmptyType(Type *Ty) const;
  Type *skipEmptyArrayTypes(Type *Ty) const;
  bool isAddressExposed(Value *V) const;
  AllocaInst *isDirectAlloca(Value *V) const;
  bool isInlineAsm(Instruction &I) const;

  // Instruction visitation functions
  friend class InstVisitor<CWriter>;

  void visitReturnInst(ReturnInst &I);
  void visitBranchInst(BranchInst &I);
  void visitSwitchInst(SwitchInst &I);
  void visitIndirectBrInst(IndirectBrInst &I);
  void visitInvokeInst(InvokeInst &I) {
    llvm_unreachable("Lowerinvoke pass didn't work!");
  }
  void visitResumeInst(ResumeInst &I) {
    llvm_unreachable("DwarfEHPrepare pass didn't work!");
  }
  void visitUnreachableInst(UnreachableInst &I);

  void visitPHINode(PHINode &I);
  void visitUnaryOperator(UnaryOperator &I);
  void visitBinaryOperator(BinaryOperator &I);
  void visitICmpInst(ICmpInst &I);
  void visitFCmpInst(FCmpInst &I);

  void visitCastInst(CastInst &I);
  void visitSelectInst(SelectInst &I);
  void visitCallInst(CallInst &I);
  void visitInlineAsm(CallInst &I);
  bool visitBuiltinCall(CallInst &I, Intrinsic::ID ID);

  void visitAllocaInst(AllocaInst &I);
  void visitLoadInst(LoadInst &I);
  void visitStoreInst(StoreInst &I);
  void visitFenceInst(FenceInst &I);
  void visitGetElementPtrInst(GetElementPtrInst &I);
  void visitVAArgInst(VAArgInst &I);

  void visitInsertElementInst(InsertElementInst &I);
  void visitExtractElementInst(ExtractElementInst &I);
  void visitShuffleVectorInst(ShuffleVectorInst &SVI);

  void visitInsertValueInst(InsertValueInst &I);
  void visitExtractValueInst(ExtractValueInst &I);

  void visitInstruction(Instruction &I) {
    CurInstr = &I;
    errorWithMessage("unsupported LLVM instruction");
  }

  LLVM_ATTRIBUTE_NORETURN void errorWithMessage(const char *message);

  bool isGotoCodeNecessary(BasicBlock *From, BasicBlock *To);
  bool canDeclareLocalLate(Instruction &I);
  bool isNotDuplicatedDeclaration(Instruction *I, bool isPhi);
  void printPHICopiesForSuccessor(BasicBlock *CurBlock, BasicBlock *Successor,
                                  unsigned Indent);
  void printBranchToBlock(BasicBlock *CurBlock, BasicBlock *SuccBlock,
                          unsigned Indent);
  bool printGEPExpressionStruct(Value *Ptr, gep_type_iterator I, gep_type_iterator E, bool accessMemory = false, bool printReference = false);
  void printGEPExpressionArray(Value *Ptr, gep_type_iterator I, gep_type_iterator E, bool accessMemory=false);


  friend class CWriterTestHelper;
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


class CBEMCAsmInfo : public MCAsmInfo {
public:
  CBEMCAsmInfo() { PrivateGlobalPrefix = ""; }
};

} // namespace llvm_cbe
