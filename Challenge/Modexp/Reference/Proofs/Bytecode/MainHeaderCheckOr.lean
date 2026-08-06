import Challenge.Modexp.Reference.Proofs.Bytecode.MainHeaderFinishDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerCheckOr (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerCheckOrPath
      (headerBaseCheckedState input) = some (headerChecksCombinedState input) := by
  have hlor : UInt256.lor 0 0 = 0 := by decide
  have hs1220 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1220) (by norm_num : 1220 + 1 < 2 ^ 256)
  have hs1221 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1221) (by norm_num : 1221 + 1 < 2 ^ 256)
  simp (config := { maxSteps := 40000 })
    [headerCheckOrPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerBaseCheckedState, headerChecksCombinedState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, hlor, hs1220, hs1221]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
