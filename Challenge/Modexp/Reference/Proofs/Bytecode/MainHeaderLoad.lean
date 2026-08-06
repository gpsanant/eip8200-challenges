import Challenge.Modexp.Reference.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerLoad (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerLoadPath
      (headerEntryState input) = some (headerLoadedState input) := by
  have hs1197 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1197) (by norm_num : 1197 + 1 < 2 ^ 256)
  have hs1198 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1198) (by norm_num : 1198 + 1 < 2 ^ 256)
  have ha1199 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1199) (b := 2) (by norm_num : 1199 + 2 < 2 ^ 256)
  have hs1201 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1201) (by norm_num : 1201 + 1 < 2 ^ 256)
  have ha1202 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1202) (b := 2) (by norm_num : 1202 + 2 < 2 ^ 256)
  have hs1204 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1204) (by norm_num : 1204 + 1 < 2 ^ 256)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h64 : (64 : UInt256).toNat = 64 := by decide
  simp (config := { maxSteps := 200000 })
    [headerLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      headerEntryState, headerLoadedState, initialState, headerWord,
      baseSize, exponentSize, modulusSize,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hs1197, hs1198, ha1199, hs1201, ha1202, hs1204, h0, h32, h64]; rfl


end Challenge.Modexp.Reference.Proofs.Bytecode.Main
