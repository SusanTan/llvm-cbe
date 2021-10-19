//===-- CTargetMachine.cpp - TargetMachine for the C backend ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the TargetMachine that is used by the C backend.
//
//===----------------------------------------------------------------------===//

#include "CTargetMachine.h"
#include "CBackend.h"
#include "llvm/CodeGen/TargetPassConfig.h"

#if LLVM_VERSION_MAJOR >= 7
#include "llvm/Transforms/Utils.h"
#endif

namespace llvm {

bool CTargetMachine::addPassesToEmitFile(PassManagerBase &PM,
                                         raw_pwrite_stream &Out,
#if LLVM_VERSION_MAJOR >= 7
                                         raw_pwrite_stream *DwoOut,
#endif
                                         CodeGenFileType FileType,
                                         bool DisableVerify,
#if LLVM_VERSION_MAJOR >= 10
                                         MachineModuleInfoWrapperPass *MMI) {
#else
                                         MachineModuleInfo *MMI) {
#endif

#if LLVM_VERSION_MAJOR >= 10
  if (FileType != CodeGenFileType::CGFT_AssemblyFile)
#else
  if (FileType != TargetMachine::CGFT_AssemblyFile)
#endif
    return true;

  PM.add(new TargetPassConfig(*this, PM));
  PM.add(createGCLoweringPass());

  // Remove exception handling with LowerInvokePass. This would be done with
  // TargetPassConfig if TargetPassConfig supported TargetMachines that aren't
  // LLVMTargetMachines.
  PM.add(createLowerInvokePass());
  PM.add(createUnreachableBlockEliminationPass());

  // Lower atomic operations to libcalls
  PM.add(createAtomicExpandPass());

  // SUSAN: add PDT pass
  PM.add(createPostDomTree());
  PM.add(new llvm_cbe::CWriter(Out));
  return false;
}

const TargetSubtargetInfo *
CTargetMachine::getSubtargetImpl(const Function &) const {
  return &SubtargetInfo;
}

bool CTargetSubtargetInfo::enableAtomicExpand() const { return true; }

const TargetLowering *CTargetSubtargetInfo::getTargetLowering() const {
  return &Lowering;
}

} // namespace llvm
