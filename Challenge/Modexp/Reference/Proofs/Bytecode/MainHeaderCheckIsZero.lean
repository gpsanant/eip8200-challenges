import Challenge.Modexp.Reference.Proofs.Bytecode.MainHeaderFinishDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerCheckIsZero (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerCheckIsZeroPath
      (headerChecksCombinedState input) = some (headerCheckPassedState input) := by
  have hiz : UInt256.isZero 0 = 1 := by decide
  have hs1222 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1222) (by norm_num : 1222 + 1 < 2 ^ 256)
  simp (config := { maxSteps := 20000 })
    [headerCheckIsZeroPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerChecksCombinedState, headerCheckPassedState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, hiz, hs1222]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
