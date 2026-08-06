import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchCheck
import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchTail
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_bigTailFrame (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigCheckedState input)
      (bigTailFrameState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigTailFramePath rfl rfl
      (run_bigTailFrame input) rfl deployAddress_not_precompile

private def gasSteps_bigTailArgs (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigTailFrameState input)
      (bigTailArgsState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigTailArgsPath rfl rfl
      (run_bigTailArgs input) rfl deployAddress_not_precompile

private def gasSteps_bigTailJump (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigTailArgsState input) (bigEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigTailJumpPath rfl rfl
      (run_bigTailJump input) rfl deployAddress_not_precompile

private theorem gasSteps_bigTailFrame_cost (input : ByteArray) :
    (gasSteps_bigTailFrame input).cost = 10 := by rfl

private theorem gasSteps_bigTailArgs_cost (input : ByteArray) :
    (gasSteps_bigTailArgs input).cost = 12 := by rfl

private theorem gasSteps_bigTailJump_cost (input : ByteArray) :
    (gasSteps_bigTailJump input).cost = 11 := by rfl

def gasSteps_bigTail (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigCheckedState input) (bigEntryState input) :=
  (gasSteps_bigTailFrame input).trans <|
    (gasSteps_bigTailArgs input).trans (gasSteps_bigTailJump input)

theorem gasSteps_bigTail_cost (input : ByteArray) :
    (gasSteps_bigTail input).cost = 33 := by
  simp [gasSteps_bigTail, gasSteps_bigTailFrame_cost, gasSteps_bigTailArgs_cost,
    gasSteps_bigTailJump_cost]

private def gasSteps_bigCheckExp (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigExpOffsetState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigCheckExpPath rfl rfl
      (run_bigCheckExp input hvalid) rfl deployAddress_not_precompile

private def gasSteps_bigCheckMod (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (bigExpOffsetState input)
      (bigOffsetsState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigCheckModPath rfl rfl
      (run_bigCheckMod input hvalid) rfl deployAddress_not_precompile

private def gasSteps_bigCheckCompare (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (bigOffsetsState input)
      (bigComparedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigCheckComparePath rfl rfl
      (run_bigCheckCompare input hvalid hbig) rfl deployAddress_not_precompile

private def gasSteps_bigCheckJump (input : ByteArray) :
    Challenge.EvmProof.GasSteps (bigComparedState input)
      (bigCheckedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigCheckJumpPath rfl rfl
      (run_bigCheckJump input) rfl deployAddress_not_precompile

private theorem gasSteps_bigCheckExp_cost (input : ByteArray)
    (hvalid : ValidInput input) :
    (gasSteps_bigCheckExp input hvalid).cost = 10 := by rfl

private theorem gasSteps_bigCheckMod_cost (input : ByteArray)
    (hvalid : ValidInput input) :
    (gasSteps_bigCheckMod input hvalid).cost = 9 := by rfl

private theorem gasSteps_bigCheckCompare_cost (input : ByteArray)
    (hvalid : ValidInput input) (hbig : 32 < modulusSize input) :
    (gasSteps_bigCheckCompare input hvalid hbig).cost = 9 := by rfl

private theorem gasSteps_bigCheckJump_cost (input : ByteArray) :
    (gasSteps_bigCheckJump input).cost = 13 := by rfl

def gasSteps_bigCheck (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordDispatchState input)
      (bigCheckedState input) :=
  (gasSteps_bigCheckExp input hvalid).trans <|
    (gasSteps_bigCheckMod input hvalid).trans <|
      (gasSteps_bigCheckCompare input hvalid hbig).trans
        (gasSteps_bigCheckJump input)

theorem gasSteps_bigCheck_cost (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (gasSteps_bigCheck input hvalid hbig).cost = 41 := by
  simp [gasSteps_bigCheck, gasSteps_bigCheckExp_cost,
    gasSteps_bigCheckMod_cost, gasSteps_bigCheckCompare_cost,
    gasSteps_bigCheckJump_cost]

def gasSteps_bigJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (Dispatch.wordDispatchState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka Dispatch.wordJumpPath rfl rfl
      (Dispatch.run_wordJump input hvalid hpositive) rfl
      deployAddress_not_precompile

theorem gasSteps_bigJump_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    (gasSteps_bigJump input hvalid hpositive).cost = 17 := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    Dispatch.wordJumpPath 17 (Dispatch.run_wordJump input hvalid hpositive)
      (by rfl) (by decide) (by decide)
  have hactive : (Main.headerState input).activeWords =
      (Dispatch.wordDispatchState input).activeWords := by rfl
  rw [hactive] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost
      Dispatch.wordJumpPath (Main.headerState input) = 17 := by omega
  simpa [gasSteps_bigJump] using hcost

def gasSteps_bigEntry (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (Main.headerState input) (bigEntryState input) :=
  (gasSteps_bigJump input hvalid hpositive).trans <|
    (gasSteps_bigCheck input hvalid hbig).trans (gasSteps_bigTail input)

theorem gasSteps_bigEntry_cost (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hbig : 32 < modulusSize input) :
    (gasSteps_bigEntry input hvalid hpositive hbig).cost = 91 := by
  simp [gasSteps_bigEntry, gasSteps_bigJump_cost, gasSteps_bigCheck_cost,
    gasSteps_bigTail_cost]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
