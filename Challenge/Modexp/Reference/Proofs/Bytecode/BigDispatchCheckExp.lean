import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigCheckExp (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckExpPath
      (Dispatch.wordDispatchState input) = some (bigExpOffsetState input) := by
  rcases hvalid with ⟨_, hb, _, _⟩
  have hb' : baseSize input < 2 ^ 256 := by omega
  have hexp : 96 + baseSize input < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := baseSize input) hexp
  simp (config := { maxSteps := 100000 })
    [bigCheckExpPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordDispatchState, bigExpOffsetState, Main.headerState,
      initialState, hadd, hb', hexp,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
