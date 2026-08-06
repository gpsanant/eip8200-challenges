import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigTailArgs (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigTailArgsPath
      (bigTailFrameState input) = some (bigTailArgsState input) := by
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  simp (config := { maxSteps := 80000 })
    [bigTailArgsPath, opAt, pushAt, wfOp, bigTailFrameState,
      bigTailArgsState, Main.headerState, initialState,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigTailPCs, h96Word,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
