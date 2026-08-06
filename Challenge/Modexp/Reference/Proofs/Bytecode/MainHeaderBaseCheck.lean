import Challenge.Modexp.Reference.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerBaseCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerBaseCheckPath
      (headerExponentCheckedState input) = some (headerBaseCheckedState input) := by
  rcases hvalid with ⟨_, hb, _, _⟩
  have hb' := size_lt_word hb
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb'
  have hgtb := boundedSize_gt_1024_eq_zero hb
  have ha1215 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1215) (b := 3) (by norm_num : 1215 + 3 < 2 ^ 256)
  have hs1218 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1218) (by norm_num : 1218 + 1 < 2 ^ 256)
  have hs1219 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1219) (by norm_num : 1219 + 1 < 2 ^ 256)
  simp (config := { maxSteps := 80000 })
    [headerBaseCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerExponentCheckedState, headerBaseCheckedState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hb, hb', hbmod, hgtb, ha1215, hs1218, hs1219]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
