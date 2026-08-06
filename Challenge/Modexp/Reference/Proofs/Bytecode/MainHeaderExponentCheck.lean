import Challenge.Modexp.Reference.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerExponentCheck (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerExponentCheckPath
      (headerModulusCheckedState input) =
        some (headerExponentCheckedState input) := by
  rcases hvalid with ⟨_, _, he, _⟩
  have he' := size_lt_word he
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he'
  have hgte := boundedSize_gt_1024_eq_zero he
  have ha1210 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1210) (b := 3) (by norm_num : 1210 + 3 < 2 ^ 256)
  have hs1213 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1213) (by norm_num : 1213 + 1 < 2 ^ 256)
  have hs1214 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1214) (by norm_num : 1214 + 1 < 2 ^ 256)
  simp (config := { maxSteps := 80000 })
    [headerExponentCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerModulusCheckedState, headerExponentCheckedState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    he, he', hemod, hgte, ha1210, hs1213, hs1214]

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
