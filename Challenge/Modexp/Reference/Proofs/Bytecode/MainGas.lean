import Challenge.Modexp.Reference.Proofs.Bytecode.MainTrampolinesLow
import Challenge.Modexp.Reference.Proofs.Bytecode.MainTrampolinesHigh
import Challenge.Modexp.Reference.Proofs.Bytecode.MainHeaderLoad
import Challenge.Modexp.Reference.Proofs.Bytecode.MainHeaderCheck
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_tramp0 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (trampolineState input 14) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp0Path rfl rfl (run_tramp0 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 14)
      (trampolineState input 53) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp1Path rfl rfl (run_tramp1 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 53)
      (trampolineState input 99) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp2Path rfl rfl (run_tramp2 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp3 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 99)
      (trampolineState input 305) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp3Path rfl rfl (run_tramp3 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp4 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 305)
      (trampolineState input 434) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp4Path rfl rfl (run_tramp4 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp5 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 434)
      (trampolineState input 512) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp5Path rfl rfl (run_tramp5 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp6 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 512)
      (trampolineState input 699) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka tramp6Path rfl rfl (run_tramp6 input)
      rfl deployAddress_not_precompile

private def gasSteps_tramp7 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 699)
      (headerEntryState input) := by
  apply Challenge.EvmProof.GasSteps.trans
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka tramp7JumpPath rfl rfl
        (run_tramp7Jump input) rfl deployAddress_not_precompile
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka tramp7DestPath rfl rfl
        (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_headerLoad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerEntryState input)
      (headerLoadedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka headerLoadPath rfl rfl (run_headerLoad input)
      rfl deployAddress_not_precompile

private def gasSteps_headerCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (headerLoadedState input) (headerState input) := by
  exact
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerModulusCheckPath rfl rfl
      (run_headerModulusCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerExponentCheckPath rfl rfl
      (run_headerExponentCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerBaseCheckPath rfl rfl
      (run_headerBaseCheck input hvalid) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerCheckOrPath rfl rfl
      (run_headerCheckOr input) rfl deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerCheckIsZeroPath rfl rfl
      (run_headerCheckIsZero input) rfl deployAddress_not_precompile).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka headerCheckJumpPath rfl rfl
      (run_headerCheckJump input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_tramp0_cost (input : ByteArray) :
    (gasSteps_tramp0 input).cost = 11 := by rfl

@[simp] private theorem gasSteps_tramp1_cost (input : ByteArray) :
    (gasSteps_tramp1 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp2_cost (input : ByteArray) :
    (gasSteps_tramp2 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp3_cost (input : ByteArray) :
    (gasSteps_tramp3 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp4_cost (input : ByteArray) :
    (gasSteps_tramp4 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp5_cost (input : ByteArray) :
    (gasSteps_tramp5 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp6_cost (input : ByteArray) :
    (gasSteps_tramp6 input).cost = 12 := by rfl

@[simp] private theorem gasSteps_tramp7_cost (input : ByteArray) :
    (gasSteps_tramp7 input).cost = 13 := by rfl

@[simp] private theorem gasSteps_headerLoad_cost (input : ByteArray) :
    (gasSteps_headerLoad input).cost = 17 := by rfl

@[simp] private theorem gasSteps_headerCheck_cost
    (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_headerCheck input hvalid).cost = 49 := by rfl

/-- Header parsing as a gas-parametric relational trace. -/
def gasSteps_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (headerState input) := by
  exact (gasSteps_tramp0 input).trans <|
    (gasSteps_tramp1 input).trans <|
    (gasSteps_tramp2 input).trans <|
    (gasSteps_tramp3 input).trans <|
    (gasSteps_tramp4 input).trans <|
    (gasSteps_tramp5 input).trans <|
    (gasSteps_tramp6 input).trans <|
    (gasSteps_tramp7 input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input hvalid)

/-- Exact, input-independent gas used by the compiler trampolines and the
three successful EIP-7823 size checks. -/
theorem gasSteps_header_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_header input hvalid).cost = 162 := by
  simp [gasSteps_header]


end Challenge.Modexp.Reference.Proofs.Bytecode.Main
