import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigCheckMod (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckModPath
      (bigExpOffsetState input) = some (bigOffsetsState input) := by
  rcases hvalid with ⟨_, hb, he, _⟩
  have hexp : 96 + baseSize input < 2 ^ 256 := by omega
  have hmod : 96 + baseSize input + exponentSize input < 2 ^ 256 := by omega
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := baseSize input) hexp
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := exponentSize input) (b := 96 + baseSize input) (by omega)
  have hadd₂' : UInt256.ofNat (96 + baseSize input) +
      UInt256.ofNat (exponentSize input) =
        UInt256.ofNat (96 + baseSize input + exponentSize input) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hmod
  simp (config := { maxSteps := 100000 })
    [bigCheckModPath, opAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigExpOffsetState, bigOffsetsState, Main.headerState, initialState,
      hadd₁, hadd₂, hadd₂', hexp, hmod, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
