import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigCheckCompare (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckComparePath
      (bigOffsetsState input) = some (bigComparedState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have honeWord : UInt256.ofNat 1 = (1 : UInt256) := by decide
  have hgt : UInt256.gt (UInt256.ofNat (modulusSize input)) 32 = 1 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm', h32, if_pos hbig]
    exact honeWord
  simp (config := { maxSteps := 80000 })
    [bigCheckComparePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigOffsetsState, bigComparedState, Main.headerState, initialState,
      hgt, honeWord, hm',
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
