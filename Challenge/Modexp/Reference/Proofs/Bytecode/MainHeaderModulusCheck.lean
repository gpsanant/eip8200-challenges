import Challenge.Modexp.Reference.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerModulusCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerModulusCheckPath
      (headerLoadedState input) = some (headerModulusCheckedState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' := size_lt_word hm
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have hgtm := boundedSize_gt_1024_eq_zero hm
  have ha1205 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1205) (b := 3) (by norm_num : 1205 + 3 < 2 ^ 256)
  have hs1208 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1208) (by norm_num : 1208 + 1 < 2 ^ 256)
  have hs1209 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1209) (by norm_num : 1209 + 1 < 2 ^ 256)
  simp (config := { maxSteps := 80000 })
    [headerModulusCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerLoadedState, headerModulusCheckedState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hm, hm', hmmod, hgtm, ha1205, hs1208, hs1209]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
