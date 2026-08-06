import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigCheckJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckJumpPath
      (bigComparedState input) = some (bigCheckedState input) := by
  have htrue : UInt256.isTrue 1 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have h1268 : (1268 : UInt256).toNat = 1268 := by decide
  have h1268Word : (1268 : UInt256) = UInt256.ofNat 1268 := by decide
  simp (config := { maxSteps := 50000 })
    [bigCheckJumpPath, pushAt, opAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigComparedState, bigCheckedState, Dispatch.wordCheckedState,
      Main.headerState, initialState, UInt256.isTrue, htrue, h1, h1268,
      h1268Word, jump1268,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
