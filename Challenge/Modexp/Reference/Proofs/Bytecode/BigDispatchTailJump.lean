import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigTailJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigTailJumpPath
      (bigTailArgsState input) = some (bigEntryState input) := by
  have h704 : (704 : UInt256).toNat = 704 := by decide
  have h704Word : (704 : UInt256) = UInt256.ofNat 704 := by decide
  simp (config := { maxSteps := 50000 })
    [bigTailJumpPath, opAt, pushAt, wfOp, bigTailArgsState,
      bigEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigTailPCs, h704, h704Word, jump704,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
