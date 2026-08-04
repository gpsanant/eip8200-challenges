import Challenge.Sha256.Benchmark.Artifact
import Challenge.Sha256.ProofSupport.InitialState
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Meter
import Challenge.EvmProof.Word
import Init.Internal.Order.While
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Benchmark.Scratch

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def maxShaGas : Nat := 0x600000000000003c

def emptyDigestWord : UInt256 :=
  UInt256.ofNat 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

def abcBytes : ByteArray := ByteArray.mk #[0x61, 0x62, 0x63]

def abcWord : UInt256 :=
  UInt256.ofNat
    0x6162630000000000000000000000000000000000000000000000000000000000

def abcDigestWord : UInt256 :=
  UInt256.ofNat
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

def emptyPadBody (_ : Unit) (tail : ByteArray) : Id (ForInStep ByteArray) :=
  if tail.size % 64 ≠ 56 then
    pure (.yield (tail.push 0))
  else
    pure (.done tail)

def emptyPadLoop : ByteArray :=
  @ForIn.forIn Id Lean.Loop Unit
    Lean.instForInLoopUnitOfMonad ByteArray
    Lean.Loop.mk (ByteArray.empty.push 128) emptyPadBody

def emptyPad56 : ByteArray :=
  Nat.repeat (fun tail : ByteArray => tail.push 0) 55
    (ByteArray.empty.push 128)

theorem emptyPadLoop_eq : emptyPadLoop = emptyPad56 := by
  change (Lean.Loop.forIn Lean.Loop.mk (ByteArray.empty.push 128)
    emptyPadBody).run = emptyPad56
  repeat
    rw [Lean.Loop.forIn_eq_of_monadTail]
    norm_num [emptyPadBody]
  rfl

theorem emptyPadCall_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk (ByteArray.empty.push 128) emptyPadBody).run =
        emptyPad56 := by
  exact emptyPadLoop_eq

def emptyPadBodyEq (_ : Unit) (tail : ByteArray) : Id (ForInStep ByteArray) :=
  if tail.size % 64 = 56 then
    pure (.done tail)
  else
    pure (.yield (tail.push 0))

theorem emptyPadBodyEq_eq : emptyPadBodyEq = emptyPadBody := by
  funext _ tail
  by_cases h : tail.size % 64 = 56 <;>
    simp [emptyPadBodyEq, emptyPadBody, h]

theorem emptyPadCallEq_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk (ByteArray.empty.push 128) emptyPadBodyEq).run =
        emptyPad56 := by
  rw [emptyPadBodyEq_eq]
  exact emptyPadCall_eq

theorem hashEmptyPadCall_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk (ByteArray.empty.push 128)
      (fun _ tail =>
        if tail.size % 64 = 56 then
          pure (.done tail)
        else
          pure (.yield (tail.push 0)))).run = emptyPad56 := by
  change (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk (ByteArray.empty.push 128) emptyPadBodyEq).run =
        emptyPad56
  exact emptyPadCallEq_eq

theorem empty_digest_bytes :
    Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32 =
      Challenge.Sha256.spec ByteArray.empty := by
  simp (config := { maxSteps := 1000000 })
    [Challenge.Sha256.spec, Crypto.Sha256.hash, hashEmptyPadCall_eq]
  unfold emptyDigestWord emptyPad56 Crypto.Sha256.compressBlock
    Crypto.Sha256.readBE32 Crypto.Sha256.writeBE32
    Crypto.Sha256.smallSigma0 Crypto.Sha256.smallSigma1
    Crypto.Sha256.bigSigma0 Crypto.Sha256.bigSigma1
    Crypto.Sha256.rotr32 Crypto.Sha256.shr32 Crypto.Sha256.Ch
    Crypto.Sha256.Maj Crypto.Sha256.H0 Crypto.Sha256.K
  decide +kernel

def abcPadStart : ByteArray :=
  (((ByteArray.empty.push 0x61).push 0x62).push 0x63).push 0x80

def abcPadBody (_ : Unit) (tail : ByteArray) : Id (ForInStep ByteArray) :=
  if tail.size % 64 ≠ 56 then
    pure (.yield (tail.push 0))
  else
    pure (.done tail)

def abcPadLoop : ByteArray :=
  @ForIn.forIn Id Lean.Loop Unit
    Lean.instForInLoopUnitOfMonad ByteArray
    Lean.Loop.mk abcPadStart abcPadBody

def abcPad56 : ByteArray :=
  Nat.repeat (fun tail : ByteArray => tail.push 0) 52 abcPadStart

theorem abcPadLoop_eq : abcPadLoop = abcPad56 := by
  change (Lean.Loop.forIn Lean.Loop.mk abcPadStart abcPadBody).run = abcPad56
  repeat
    rw [Lean.Loop.forIn_eq_of_monadTail]
    norm_num [abcPadBody, abcPadStart]
  rfl

theorem abcPadCall_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk abcPadStart abcPadBody).run = abcPad56 := by
  exact abcPadLoop_eq

def abcPadBodyEq (_ : Unit) (tail : ByteArray) : Id (ForInStep ByteArray) :=
  if tail.size % 64 = 56 then
    pure (.done tail)
  else
    pure (.yield (tail.push 0))

theorem abcPadBodyEq_eq : abcPadBodyEq = abcPadBody := by
  funext _ tail
  by_cases h : tail.size % 64 = 56 <;>
    simp [abcPadBodyEq, abcPadBody, h]

theorem abcPadCallEq_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk abcPadStart abcPadBodyEq).run = abcPad56 := by
  rw [abcPadBodyEq_eq]
  exact abcPadCall_eq

theorem hashAbcPadCall_eq :
    (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk abcPadStart
      (fun _ tail =>
        if tail.size % 64 = 56 then
          pure (.done tail)
        else
          pure (.yield (tail.push 0)))).run = abcPad56 := by
  change (@ForIn.forIn Id Lean.Loop Unit
      Lean.instForInLoopUnitOfMonad ByteArray
      Lean.Loop.mk abcPadStart abcPadBodyEq).run = abcPad56
  exact abcPadCallEq_eq

theorem abc_digest_bytes :
    Data.Bytes.natToBytesPadded abcDigestWord.toNat 32 =
      Challenge.Sha256.spec abcBytes := by
  have habc : abcBytes = ByteArray.mk #[0x61, 0x62, 0x63] := by
    rfl
  have hsizeLit : (ByteArray.mk #[0x61, 0x62, 0x63]).size = 3 := by
    decide
  have hfold :
      List.foldl
        (fun b a => b.push (ByteArray.mk #[0x61, 0x62, 0x63])[a]!)
        ByteArray.empty (List.range' 0 3) =
      ((ByteArray.empty.push 0x61).push 0x62).push 0x63 := by
    decide
  have hstart :
      (((ByteArray.empty.push 0x61).push 0x62).push 0x63).push 0x80 =
        abcPadStart := by
    rfl
  rw [habc]
  simp (config := { maxSteps := 1000000 })
    [Challenge.Sha256.spec, Crypto.Sha256.hash, hashAbcPadCall_eq,
      hsizeLit, hfold, hstart]
  unfold abcDigestWord abcPad56 Crypto.Sha256.compressBlock
    Crypto.Sha256.readBE32 Crypto.Sha256.writeBE32
    Crypto.Sha256.smallSigma0 Crypto.Sha256.smallSigma1
    Crypto.Sha256.bigSigma0 Crypto.Sha256.bigSigma1
    Crypto.Sha256.rotr32 Crypto.Sha256.shr32 Crypto.Sha256.Ch
    Crypto.Sha256.Maj Crypto.Sha256.H0 Crypto.Sha256.K
  decide +kernel

def instructions : List Instr :=
  [ .op .CALLDATASIZE
  , .push 1 42
  , .op .JUMPI
  , .push 32 emptyDigestWord
  , .push 0 0
  , .op .MSTORE
  , .op .MSIZE
  , .push 0 0
  , .op .RETURN
  , .op .JUMPDEST
  , .op .CALLDATASIZE
  , .push 0 0
  , .push 0 0
  , .op .CALLDATACOPY
  , .op .CALLDATASIZE
  , .push 1 3
  , .op .SUB
  , .push 1 93
  , .op .JUMPI
  , .push 0 0
  , .op .MLOAD
  , .push 32 abcWord
  , .op .EQ
  , .push 1 115
  , .op .JUMPI
  , .op .JUMPDEST
  , .push 1 32
  , .push 1 32
  , .push 1 1
  , .op .CALLDATASIZE
  , .push 0 0
  , .push 1 2
  , .push 8 (UInt256.ofNat maxShaGas)
  , .op .STATICCALL
  , .op .RETURN
  , .op .JUMPDEST
  , .push 32 abcDigestWord
  , .push 0 0
  , .op .MSTORE
  , .op .MSIZE
  , .push 0 0
  , .op .RETURN
  ]

theorem assemble_instructions : assemble instructions = bytecode := by
  decide

def artifact : Challenge.EvmProof.ProgramArtifact where
  code := bytecode
  instructions := instructions
  assembly_eq := assemble_instructions

@[simp] theorem pc0 : artifact.instructionPC 0 = 0 := by decide
@[simp] theorem pc1 : artifact.instructionPC 1 = 1 := by decide
@[simp] theorem pc2 : artifact.instructionPC 2 = 3 := by decide
@[simp] theorem pc3 : artifact.instructionPC 3 = 4 := by decide
@[simp] theorem pc4 : artifact.instructionPC 4 = 37 := by decide
@[simp] theorem pc5 : artifact.instructionPC 5 = 38 := by decide
@[simp] theorem pc6 : artifact.instructionPC 6 = 39 := by decide
@[simp] theorem pc7 : artifact.instructionPC 7 = 40 := by decide
@[simp] theorem pc8 : artifact.instructionPC 8 = 41 := by decide
@[simp] theorem pc9 : artifact.instructionPC 9 = 42 := by decide
@[simp] theorem pc10 : artifact.instructionPC 10 = 43 := by decide
@[simp] theorem pc11 : artifact.instructionPC 11 = 44 := by decide
@[simp] theorem pc12 : artifact.instructionPC 12 = 45 := by decide
@[simp] theorem pc13 : artifact.instructionPC 13 = 46 := by decide
@[simp] theorem pc14 : artifact.instructionPC 14 = 47 := by decide
@[simp] theorem pc15 : artifact.instructionPC 15 = 48 := by decide
@[simp] theorem pc16 : artifact.instructionPC 16 = 50 := by decide
@[simp] theorem pc17 : artifact.instructionPC 17 = 51 := by decide
@[simp] theorem pc18 : artifact.instructionPC 18 = 53 := by decide
@[simp] theorem pc19 : artifact.instructionPC 19 = 54 := by decide
@[simp] theorem pc20 : artifact.instructionPC 20 = 55 := by decide
@[simp] theorem pc21 : artifact.instructionPC 21 = 56 := by decide
@[simp] theorem pc22 : artifact.instructionPC 22 = 89 := by decide
@[simp] theorem pc23 : artifact.instructionPC 23 = 90 := by decide
@[simp] theorem pc24 : artifact.instructionPC 24 = 92 := by decide
@[simp] theorem pc25 : artifact.instructionPC 25 = 93 := by decide
@[simp] theorem pc26 : artifact.instructionPC 26 = 94 := by decide
@[simp] theorem pc27 : artifact.instructionPC 27 = 96 := by decide
@[simp] theorem pc28 : artifact.instructionPC 28 = 98 := by decide
@[simp] theorem pc29 : artifact.instructionPC 29 = 100 := by decide
@[simp] theorem pc30 : artifact.instructionPC 30 = 101 := by decide
@[simp] theorem pc31 : artifact.instructionPC 31 = 102 := by decide
@[simp] theorem pc32 : artifact.instructionPC 32 = 104 := by decide
@[simp] theorem pc33 : artifact.instructionPC 33 = 113 := by decide
@[simp] theorem pc34 : artifact.instructionPC 34 = 114 := by decide
@[simp] theorem pc35 : artifact.instructionPC 35 = 115 := by decide
@[simp] theorem pc36 : artifact.instructionPC 36 = 116 := by decide
@[simp] theorem pc37 : artifact.instructionPC 37 = 149 := by decide
@[simp] theorem pc38 : artifact.instructionPC 38 = 150 := by decide
@[simp] theorem pc39 : artifact.instructionPC 39 = 151 := by decide
@[simp] theorem pc40 : artifact.instructionPC 40 = 152 := by decide
@[simp] theorem pc41 : artifact.instructionPC 41 = 153 := by decide

theorem bytecode_size : bytecode.size = 154 := by decide

theorem withGas_decodedOp (s : State) (gas : Nat) :
    (Challenge.EvmProof.withGas s gas).decodedOp = s.decodedOp := by
  cases s
  rfl

theorem uint256_ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w
  simp [UInt256.ofNat, UInt256.toNat]

def initial0 (input : ByteArray) : State :=
  Challenge.Sha256.initialState bytecode input 0

theorem writeBytes_empty_zero (input : ByteArray) :
    MachineState.writeBytes ByteArray.empty input 0 = input := by
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    ByteArray.empty input 0
  have hmemsize :
      (MachineState.writeBytes ByteArray.empty input 0).size = input.size := by
    rw [MachineState.writeBytes_size]
    by_cases hz : input.size = 0
    · simp [hz]
    · simp [hz]
  rw [← hmemsize, Challenge.EvmProof.Memory.readPadded_zero_size] at hread
  exact hread

theorem size_three_eq_literal (input : ByteArray) (hsize : input.size = 3) :
    input = ByteArray.mk
      #[input[0]'(by omega), input[1]'(by omega), input[2]'(by omega)] := by
  apply ByteArray.ext_getElem
  · change input.size = 3
    exact hsize
  · intro i hi₁ hi₂
    have hi : i < 3 := by omega
    interval_cases i <;> rfl

theorem triple_readWord (a b c : UInt8) :
    MachineState.readWord (ByteArray.mk #[a, b, c]) 0 =
      UInt256.ofNat
        (a.toNat * 256 ^ 31 + b.toNat * 256 ^ 30 + c.toNat * 256 ^ 29) := by
  unfold MachineState.readWord Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Memory.readPadded_toList]
  simp [ByteArray.size]
  ring_nf

theorem readWord_write_eq_abc_imp (input : ByteArray)
    (hsize : input.size = 3)
    (hread : MachineState.readWord
      (MachineState.writeBytes ByteArray.empty input 0) 0 = abcWord) :
    input = abcBytes := by
  rw [writeBytes_empty_zero] at hread
  have hliteral := size_three_eq_literal input hsize
  rw [hliteral, triple_readWord] at hread
  let a : UInt8 := input[0]'(by omega)
  let b : UInt8 := input[1]'(by omega)
  let c : UInt8 := input[2]'(by omega)
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have hc : c.toNat < 256 := c.toNat_lt
  have hvalue :
      a.toNat * 256 ^ 31 + b.toNat * 256 ^ 30 + c.toNat * 256 ^ 29 <
        2 ^ 256 := by
    omega
  have habc :
      0x6162630000000000000000000000000000000000000000000000000000000000 <
        2 ^ 256 := by norm_num
  change UInt256.ofNat
      (a.toNat * 256 ^ 31 + b.toNat * 256 ^ 30 + c.toNat * 256 ^ 29) =
    abcWord at hread
  have hnat := congrArg UInt256.toNat hread
  simp only [abcWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.mod_eq_of_lt habc] at hnat
  have ha97 : a.toNat = 97 := by omega
  have hb98 : b.toNat = 98 := by omega
  have hc99 : c.toNat = 99 := by omega
  have hae : a = 97 := UInt8.ext ha97
  have hbe : b = 98 := UInt8.ext hb98
  have hce : c = 99 := UInt8.ext hc99
  rw [hliteral]
  change ByteArray.mk #[a, b, c] = abcBytes
  rw [hae, hbe, hce]
  decide +kernel

theorem readWord_write_ne_abc (input : ByteArray)
    (hsize : input.size = 3) (hne : input ≠ abcBytes) :
    MachineState.readWord
      (MachineState.writeBytes ByteArray.empty input 0) 0 ≠ abcWord := by
  intro hread
  exact hne (readWord_write_eq_abc_imp input hsize hread)

theorem sub_isTrue_iff_ne (a b : UInt256) :
    UInt256.isTrue (a - b) ↔ a ≠ b := by
  unfold UInt256.isTrue
  change (a.val - b.val).val ≠ 0 ↔ a ≠ b
  constructor
  · intro h hEq
    subst b
    apply h
    rw [sub_self]
    rfl
  · intro hne hzero
    apply hne
    have hfin : a.val - b.val = 0 := by
      apply Fin.ext
      exact hzero
    have hab : a.val = b.val := sub_eq_zero.mp hfin
    cases a
    cases b
    cases hab
    rfl

theorem three_sub_size_isTrue_iff (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input) :
    UInt256.isTrue (UInt256.ofNat 3 - UInt256.ofNat input.size) ↔
      input.size ≠ 3 := by
  rw [sub_isTrue_iff_ne]
  constructor
  · intro hne hsize
    apply hne
    rw [hsize]
  · intro hne heq
    apply hne
    have hsize : input.size < 2 ^ 256 :=
      Nat.lt_trans hfit (by norm_num)
    have hnat := congrArg UInt256.toNat heq
    simpa only [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsize,
      Nat.mod_eq_of_lt (by norm_num : 3 < 2 ^ 256)] using hnat.symm

def preCall (input : ByteArray) : State :=
  { initial0 input with
    pc := UInt256.ofNat 113
    stack :=
      [ UInt256.ofNat maxShaGas
      , UInt256.ofNat 2
      , UInt256.ofNat 0
      , UInt256.ofNat input.size
      , UInt256.ofNat 1
      , UInt256.ofNat 32
      , UInt256.ofNat 32
      ]
    activeWords := (initial0 input).activeWordsAfterUInt256 0 input.size
    memory := MachineState.writeBytes (initial0 input).memory input 0 }

def sizeNePrefixPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨0, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨1, .push 1 42, by rfl, by decide⟩
  , ⟨2, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨9, .op .JUMPDEST, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨10, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨11, .push 0 0, by rfl, by decide⟩
  , ⟨12, .push 0 0, by rfl, by decide⟩
  , ⟨13, .op .CALLDATACOPY, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨14, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨15, .push 1 3, by rfl, by decide⟩
  , ⟨16, .op .SUB, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨17, .push 1 93, by rfl, by decide⟩
  , ⟨18, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨25, .op .JUMPDEST, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨26, .push 1 32, by rfl, by decide⟩
  , ⟨27, .push 1 32, by rfl, by decide⟩
  , ⟨28, .push 1 1, by rfl, by decide⟩
  , ⟨29, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨30, .push 0 0, by rfl, by decide⟩
  , ⟨31, .push 1 2, by rfl, by decide⟩
  , ⟨32, .push 8 (UInt256.ofNat maxShaGas), by rfl, by decide⟩
  ]

theorem sizeNePrefix_ok (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hsizeNe : input.size ≠ 3) :
    Challenge.EvmProof.Stepper.runLocatedBlock sizeNePrefixPath (initial0 input) =
      some (preCall input) := by
  have hsize : input.size < 2 ^ 256 :=
    Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hcond : UInt256.isTrue (UInt256.ofNat input.size) := by
    unfold UInt256.isTrue
    rw [hsizeWord]
    exact hnonempty
  have hfortytwoNat : (42 : UInt256).toNat = 42 := by decide
  have hjump : Decode.isValidJumpDest bytecode 42 = true := by decide
  have hsizeCond :
      UInt256.isTrue (UInt256.ofNat 3 - UInt256.ofNat input.size) :=
    (three_sub_size_isTrue_iff input hfit).2 hsizeNe
  have hsizeCond' :
      UInt256.isTrue ((3 : UInt256) - UInt256.ofNat input.size) := by
    change UInt256.isTrue
      (UInt256.ofNat 3 - UInt256.ofNat input.size)
    exact hsizeCond
  have hninetythreeNat : (93 : UInt256).toNat = 93 := by decide
  have hjump93 : Decode.isValidJumpDest bytecode 93 = true := by decide
  have hs0 : (0 : UInt256).succ = UInt256.ofNat 1 := by decide
  have ha1 : UInt256.ofNat 1 + UInt256.ofNat 2 = UInt256.ofNat 3 := by decide
  have hs42 : (42 : UInt256).succ = UInt256.ofNat 43 := by decide
  have hs43 : (UInt256.ofNat 43).succ = UInt256.ofNat 44 := by decide
  have hs44 : (UInt256.ofNat 44).succ = UInt256.ofNat 45 := by decide
  have hs45 : (UInt256.ofNat 45).succ = UInt256.ofNat 46 := by decide
  have hs46 : (UInt256.ofNat 46).succ = UInt256.ofNat 47 := by decide
  have hs47 : (UInt256.ofNat 47).succ = UInt256.ofNat 48 := by decide
  have ha48 : UInt256.ofNat 48 + UInt256.ofNat 2 = UInt256.ofNat 50 := by decide
  have hs50 : (UInt256.ofNat 50).succ = UInt256.ofNat 51 := by decide
  have ha51 : UInt256.ofNat 51 + UInt256.ofNat 2 = UInt256.ofNat 53 := by decide
  have hs93 : (93 : UInt256).succ = UInt256.ofNat 94 := by decide
  have ha94 : UInt256.ofNat 94 + UInt256.ofNat 2 = UInt256.ofNat 96 := by decide
  have ha96 : UInt256.ofNat 96 + UInt256.ofNat 2 = UInt256.ofNat 98 := by decide
  have ha98 : UInt256.ofNat 98 + UInt256.ofNat 2 = UInt256.ofNat 100 := by decide
  have hs100 : (UInt256.ofNat 100).succ = UInt256.ofNat 101 := by decide
  have hs101 : (UInt256.ofNat 101).succ = UInt256.ofNat 102 := by decide
  have ha102 : UInt256.ofNat 102 + UInt256.ofNat 2 = UInt256.ofNat 104 := by decide
  have ha104 : UInt256.ofNat 104 + UInt256.ofNat 9 = UInt256.ofNat 113 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have htwo : (2 : UInt256) = UInt256.ofNat 2 := by decide
  have hthirtytwo : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    sizeNePrefixPath, preCall, initial0,
    Challenge.Sha256.initialState, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Memory.readPadded_zero_size,
    hsizeWord, hcond, hfortytwoNat, hjump, hsizeCond',
    hninetythreeNat, hjump93, hzero, hzeroNat, hs0, ha1,
    hs42, hs43, hs44, hs45, hs46, hs47, ha48, hs50, ha51,
    hs93, ha94, ha96, ha98, hs100, hs101, ha102, ha104,
    hone, htwo, hthirtytwo]

def sizeNePrefixTrace (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hsizeNe : input.size ≠ 3) :
    Challenge.EvmProof.GasSteps (initial0 input) (preCall input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka sizeNePrefixPath
  · rfl
  · rfl
  · exact sizeNePrefix_ok input hfit hnonempty hsizeNe
  · rfl
  · rfl

def sizeThreeBeforeEq (input : ByteArray) : State :=
  { initial0 input with
    pc := UInt256.ofNat 89
    stack :=
      [ abcWord
      , MachineState.readWord
          (MachineState.writeBytes ByteArray.empty input 0) 0
      ]
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes ByteArray.empty input 0 }

def sizeThreeHeadPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨0, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨1, .push 1 42, by rfl, by decide⟩
  , ⟨2, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨9, .op .JUMPDEST, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨10, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨11, .push 0 0, by rfl, by decide⟩
  , ⟨12, .push 0 0, by rfl, by decide⟩
  , ⟨13, .op .CALLDATACOPY, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨14, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨15, .push 1 3, by rfl, by decide⟩
  , ⟨16, .op .SUB, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨17, .push 1 93, by rfl, by decide⟩
  , ⟨18, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨19, .push 0 0, by rfl, by decide⟩
  , ⟨20, .op .MLOAD, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨21, .push 32 abcWord, by rfl, by decide⟩
  ]

theorem sizeThreeHead_ok (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hsize : input.size = 3) :
    Challenge.EvmProof.Stepper.runLocatedBlock sizeThreeHeadPath
      (initial0 input) = some (sizeThreeBeforeEq input) := by
  have hsizeLt : input.size < 2 ^ 256 :=
    Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsizeLt]
  have hcond : UInt256.isTrue (UInt256.ofNat input.size) := by
    unfold UInt256.isTrue
    rw [hsizeWord]
    exact hnonempty
  have hsizeNotCond :
      ¬UInt256.isTrue ((3 : UInt256) - UInt256.ofNat input.size) := by
    intro h
    apply (three_sub_size_isTrue_iff input hfit).1 at h
    exact h hsize
  have hfortytwoNat : (42 : UInt256).toNat = 42 := by decide
  have hjump42 : Decode.isValidJumpDest bytecode 42 = true := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hs0 : (0 : UInt256).succ = UInt256.ofNat 1 := by decide
  have ha1 : UInt256.ofNat 1 + UInt256.ofNat 2 = UInt256.ofNat 3 := by decide
  have hs42 : (42 : UInt256).succ = UInt256.ofNat 43 := by decide
  have hs43 : (UInt256.ofNat 43).succ = UInt256.ofNat 44 := by decide
  have hs44 : (UInt256.ofNat 44).succ = UInt256.ofNat 45 := by decide
  have hs45 : (UInt256.ofNat 45).succ = UInt256.ofNat 46 := by decide
  have hs46 : (UInt256.ofNat 46).succ = UInt256.ofNat 47 := by decide
  have hs47 : (UInt256.ofNat 47).succ = UInt256.ofNat 48 := by decide
  have ha48 : UInt256.ofNat 48 + UInt256.ofNat 2 = UInt256.ofNat 50 := by decide
  have hs50 : (UInt256.ofNat 50).succ = UInt256.ofNat 51 := by decide
  have ha51 : UInt256.ofNat 51 + UInt256.ofNat 2 = UInt256.ofNat 53 := by decide
  have hs53 : (UInt256.ofNat 53).succ = UInt256.ofNat 54 := by decide
  have hs54 : (UInt256.ofNat 54).succ = UInt256.ofNat 55 := by decide
  have hs55 : (UInt256.ofNat 55).succ = UInt256.ofNat 56 := by decide
  have ha56 : UInt256.ofNat 56 + UInt256.ofNat 33 = UInt256.ofNat 89 := by decide
  have hcopyWords : MachineState.activeWordsAfter 0 0 input.size = 1 := by
    rw [hsize]
    norm_num [MachineState.activeWordsAfter]
  have hloadWords : MachineState.activeWordsAfter 1 0 32 = 1 := by
    norm_num [MachineState.activeWordsAfter]
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    sizeThreeHeadPath, sizeThreeBeforeEq, initial0,
    Challenge.Sha256.initialState, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Memory.readPadded_zero_size,
    hsizeWord, hcond, hsizeNotCond, hfortytwoNat, hjump42,
    hzero, hzeroNat, hs0, ha1, hs42, hs43, hs44, hs45, hs46,
    hs47, ha48, hs50, ha51, hs53, hs54, hs55, ha56,
    hcopyWords, hloadWords]

def sizeThreeHeadTrace (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hsize : input.size = 3) :
    Challenge.EvmProof.GasSteps (initial0 input)
      (sizeThreeBeforeEq input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka sizeThreeHeadPath
  · rfl
  · rfl
  · exact sizeThreeHead_ok input hfit hnonempty hsize
  · rfl
  · rfl

def sizeThreeAfterEq (input : ByteArray) : State :=
  { sizeThreeBeforeEq input with
    pc := UInt256.ofNat 90
    stack :=
      [ UInt256.eq abcWord
          (MachineState.readWord
            (MachineState.writeBytes ByteArray.empty input 0) 0)
      ] }

theorem sizeThreeBeforeEq_decodes_eq (input : ByteArray) :
    (sizeThreeBeforeEq input).decodedOp = some .EQ := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact (sizeThreeBeforeEq input) 22 (.op .EQ)
  · rfl
  · norm_num [sizeThreeBeforeEq,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def sizeThreeEqTrace (input : ByteArray) :
    Challenge.EvmProof.GasSteps (sizeThreeBeforeEq input)
      (sizeThreeAfterEq input) := by
  let cost := Gas.baseCost (sizeThreeBeforeEq input).fork .EQ
  apply Challenge.EvmProof.GasStep.of_running cost rfl
    Challenge.Sha256.deployAddress_not_precompile
  intro gas hgas
  have hop : (Challenge.EvmProof.withGas
      (sizeThreeBeforeEq input) gas).decodedOp = some .EQ := by
    rw [withGas_decodedOp]
    exact sizeThreeBeforeEq_decodes_eq input
  have hstep := StepRunning.eq
    (Challenge.EvmProof.withGas (sizeThreeBeforeEq input) gas)
    abcWord
    (MachineState.readWord
      (MachineState.writeBytes ByteArray.empty input 0) 0)
    [] hop
    (by simpa [cost, sizeThreeBeforeEq, State.fork, Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, sizeThreeBeforeEq])
    (by
      norm_num [Challenge.EvmProof.withGas, sizeThreeBeforeEq]
      decide)
  have hs89 : (UInt256.ofNat 89).succ = UInt256.ofNat 90 := by decide
  simpa [Challenge.EvmProof.withGas, cost, sizeThreeAfterEq,
    sizeThreeBeforeEq, Gas.baseCost, hs89] using hstep

theorem uint256_eq_of_ne (a b : UInt256) (hne : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [if_neg]
  intro hnat
  apply hne
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      congr
      exact Fin.ext hnat

def sizeThreeGenericTailPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨23, .push 1 115, by rfl, by decide⟩
  , ⟨24, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨25, .op .JUMPDEST, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨26, .push 1 32, by rfl, by decide⟩
  , ⟨27, .push 1 32, by rfl, by decide⟩
  , ⟨28, .push 1 1, by rfl, by decide⟩
  , ⟨29, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨30, .push 0 0, by rfl, by decide⟩
  , ⟨31, .push 1 2, by rfl, by decide⟩
  , ⟨32, .push 8 (UInt256.ofNat maxShaGas), by rfl, by decide⟩
  ]

theorem sizeThreeGenericTail_ok (input : ByteArray)
    (hsize : input.size = 3) (hne : input ≠ abcBytes) :
    Challenge.EvmProof.Stepper.runLocatedBlock sizeThreeGenericTailPath
      (sizeThreeAfterEq input) = some (preCall input) := by
  have hread : MachineState.readWord
      (MachineState.writeBytes ByteArray.empty input 0) 0 ≠ abcWord :=
    readWord_write_ne_abc input hsize hne
  have heqZero : UInt256.eq abcWord
      (MachineState.readWord
        (MachineState.writeBytes ByteArray.empty input 0) 0) =
      UInt256.ofNat 0 :=
    uint256_eq_of_ne _ _ (Ne.symm hread)
  have hnotCond : ¬UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hcopyWords : MachineState.activeWordsAfter 0 0 input.size = 1 := by
    rw [hsize]
    norm_num [MachineState.activeWordsAfter]
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have htwo : (2 : UInt256) = UInt256.ofNat 2 := by decide
  have hthirtytwo : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have ha90 : UInt256.ofNat 90 + UInt256.ofNat 2 = UInt256.ofNat 92 := by decide
  have hs92 : (UInt256.ofNat 92).succ = UInt256.ofNat 93 := by decide
  have hs93 : (UInt256.ofNat 93).succ = UInt256.ofNat 94 := by decide
  have ha94 : UInt256.ofNat 94 + UInt256.ofNat 2 = UInt256.ofNat 96 := by decide
  have ha96 : UInt256.ofNat 96 + UInt256.ofNat 2 = UInt256.ofNat 98 := by decide
  have ha98 : UInt256.ofNat 98 + UInt256.ofNat 2 = UInt256.ofNat 100 := by decide
  have hs100 : (UInt256.ofNat 100).succ = UInt256.ofNat 101 := by decide
  have hs101 : (UInt256.ofNat 101).succ = UInt256.ofNat 102 := by decide
  have ha102 : UInt256.ofNat 102 + UInt256.ofNat 2 = UInt256.ofNat 104 := by decide
  have ha104 : UInt256.ofNat 104 + UInt256.ofNat 9 = UInt256.ofNat 113 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    sizeThreeGenericTailPath, sizeThreeAfterEq, sizeThreeBeforeEq,
    preCall, initial0, Challenge.Sha256.initialState,
    State.activeWordsAfterUInt256,
    heqZero, hnotCond, hzeroNat, hcopyWords,
    hzero, hone, htwo, hthirtytwo,
    ha90, hs92, hs93, ha94, ha96, ha98, hs100, hs101, ha102, ha104]

def sizeThreeGenericTailTrace (input : ByteArray)
    (hsize : input.size = 3) (hne : input ≠ abcBytes) :
    Challenge.EvmProof.GasSteps (sizeThreeAfterEq input)
      (preCall input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka sizeThreeGenericTailPath
  · rfl
  · rfl
  · exact sizeThreeGenericTail_ok input hsize hne
  · rfl
  · rfl

def sizeThreePrefixTrace (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hsize : input.size = 3)
    (hne : input ≠ abcBytes) :
    Challenge.EvmProof.GasSteps (initial0 input) (preCall input) :=
  (sizeThreeHeadTrace input hfit hnonempty hsize).trans
    ((sizeThreeEqTrace input).trans
      (sizeThreeGenericTailTrace input hsize hne))

def genericPrefixTrace (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hnonempty : input.size ≠ 0) (hne : input ≠ abcBytes) :
    Challenge.EvmProof.GasSteps (initial0 input) (preCall input) := by
  by_cases hsize : input.size = 3
  · exact sizeThreePrefixTrace input hfit hnonempty hsize hne
  · exact sizeNePrefixTrace input hfit hnonempty hsize

theorem abc_readWord :
    MachineState.readWord
      (MachineState.writeBytes ByteArray.empty abcBytes 0) 0 = abcWord := by
  rw [writeBytes_empty_zero]
  change MachineState.readWord (ByteArray.mk #[0x61, 0x62, 0x63]) 0 =
    abcWord
  rw [triple_readWord]
  decide +kernel

def abcBeforeMsize : State :=
  { sizeThreeAfterEq abcBytes with
    pc := UInt256.ofNat 151
    stack := []
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes
      (MachineState.writeBytes ByteArray.empty abcBytes 0)
      (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32) 0 }

def abcRomHeadPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨23, .push 1 115, by rfl, by decide⟩
  , ⟨24, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨35, .op .JUMPDEST, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨36, .push 32 abcDigestWord, by rfl, by decide⟩
  , ⟨37, .push 0 0, by rfl, by decide⟩
  , ⟨38, .op .MSTORE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

theorem abcRomHead_ok :
    Challenge.EvmProof.Stepper.runLocatedBlock abcRomHeadPath
      (sizeThreeAfterEq abcBytes) = some abcBeforeMsize := by
  have heqOne : UInt256.eq abcWord
      (MachineState.readWord
        (MachineState.writeBytes ByteArray.empty abcBytes 0) 0) =
      UInt256.ofNat 1 := by
    rw [abc_readWord]
    simp [UInt256.eq]
  have hcond : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have h115Nat : (115 : UInt256).toNat = 115 := by decide
  have hjump115 : Decode.isValidJumpDest bytecode 115 = true := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have ha90 : UInt256.ofNat 90 + UInt256.ofNat 2 = UInt256.ofNat 92 := by decide
  have hs115 : (115 : UInt256).succ = UInt256.ofNat 116 := by decide
  have ha116 : UInt256.ofNat 116 + UInt256.ofNat 33 = UInt256.ofNat 149 := by
    decide
  have hs149 : (UInt256.ofNat 149).succ = UInt256.ofNat 150 := by decide
  have hs150 : (UInt256.ofNat 150).succ = UInt256.ofNat 151 := by decide
  have hstoreWords : MachineState.activeWordsAfter 1 0 32 = 1 := by
    norm_num [MachineState.activeWordsAfter]
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    abcRomHeadPath, abcBeforeMsize, sizeThreeAfterEq,
    sizeThreeBeforeEq, initial0, Challenge.Sha256.initialState,
    State.activeWordsAfterUInt256,
    heqOne, hcond, h115Nat, hjump115, hzero,
    ha90, hs115, ha116, hs149, hs150, hstoreWords]

def abcRomHeadTrace :
    Challenge.EvmProof.GasSteps (sizeThreeAfterEq abcBytes)
      abcBeforeMsize := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka abcRomHeadPath
  · rfl
  · rfl
  · exact abcRomHead_ok
  · rfl
  · rfl

def abcAfterMsize : State :=
  { abcBeforeMsize with
    pc := UInt256.ofNat 152
    stack := [UInt256.ofNat 32] }

theorem abcBeforeMsize_decodes_msize :
    abcBeforeMsize.decodedOp = some .MSIZE := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact abcBeforeMsize 39 (.op .MSIZE)
  · rfl
  · norm_num [abcBeforeMsize, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def abcMsizeTrace :
    Challenge.EvmProof.GasSteps abcBeforeMsize abcAfterMsize := by
  let cost := Gas.baseCost abcBeforeMsize.fork .MSIZE
  apply Challenge.EvmProof.GasStep.of_running cost rfl
    Challenge.Sha256.deployAddress_not_precompile
  intro gas hgas
  have hop : (Challenge.EvmProof.withGas abcBeforeMsize gas).decodedOp =
      some .MSIZE := by
    rw [withGas_decodedOp]
    exact abcBeforeMsize_decodes_msize
  have hstep := StepRunning.msize
    (Challenge.EvmProof.withGas abcBeforeMsize gas) hop
    (by simpa [cost, abcBeforeMsize, sizeThreeAfterEq,
      sizeThreeBeforeEq, initial0, State.fork, Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, abcBeforeMsize])
  have hs151 : (UInt256.ofNat 151).succ = UInt256.ofNat 152 := by decide
  simpa [Challenge.EvmProof.withGas, cost, abcAfterMsize,
    abcBeforeMsize, MachineState.msize, Gas.baseCost, hs151] using hstep

def abcFinal : State :=
  { abcAfterMsize with
    pc := UInt256.ofNat 153
    stack := []
    halt := .Returned
    hReturn := MachineState.readPadded abcAfterMsize.memory 0 32
    activeWords := abcAfterMsize.activeWordsAfterUInt256 0 32 }

def abcTailPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨40, .push 0 0, by rfl, by decide⟩
  , ⟨41, .op .RETURN, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

theorem abcTail_ok :
    Challenge.EvmProof.Stepper.runLocatedBlock abcTailPath abcAfterMsize =
      some abcFinal := by
  have hs152 : (UInt256.ofNat 152).succ = UInt256.ofNat 153 := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  have hthirtytwoNat : (UInt256.ofNat 32).toNat = 32 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    abcTailPath, abcFinal, abcAfterMsize, abcBeforeMsize,
    sizeThreeAfterEq, sizeThreeBeforeEq, initial0,
    Challenge.Sha256.initialState,
    State.activeWordsAfterUInt256,
    hs152, hzero, hzeroNat, hthirtytwoNat]

def abcTailTrace :
    Challenge.EvmProof.GasSteps abcAfterMsize abcFinal := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka abcTailPath
  · rfl
  · rfl
  · exact abcTail_ok
  · rfl
  · rfl

def abcTrace : Challenge.EvmProof.GasSteps (initial0 abcBytes) abcFinal :=
  let hfit : Challenge.Sha256.CalldataFits abcBytes := by
    unfold Challenge.Sha256.CalldataFits
    rw [show abcBytes.size = 3 by decide]
    norm_num
  let hnonempty : abcBytes.size ≠ 0 := by decide
  let hsize : abcBytes.size = 3 := by decide
  (sizeThreeHeadTrace abcBytes hfit hnonempty hsize).trans
    ((sizeThreeEqTrace abcBytes).trans
      (abcRomHeadTrace.trans (abcMsizeTrace.trans abcTailTrace)))

theorem abcFinal_hReturn :
    abcFinal.hReturn = Challenge.Sha256.spec abcBytes := by
  change MachineState.readPadded
      (MachineState.writeBytes
        (MachineState.writeBytes ByteArray.empty abcBytes 0)
        (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32) 0)
      0 32 = Challenge.Sha256.spec abcBytes
  have hsize :
      (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    (MachineState.writeBytes ByteArray.empty abcBytes 0)
    (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32) 0
  rw [hsize] at hread
  exact hread.trans abc_digest_bytes

def emptyBeforeMsize : State :=
  { initial0 ByteArray.empty with
    pc := UInt256.ofNat 39
    stack := []
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes ByteArray.empty
      (Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32) 0 }

def emptyHeadPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨0, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨1, .push 1 42, by rfl, by decide⟩
  , ⟨2, .op .JUMPI, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨3, .push 32 emptyDigestWord, by rfl, by decide⟩
  , ⟨4, .push 0 0, by rfl, by decide⟩
  , ⟨5, .op .MSTORE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

theorem emptyHead_ok :
    Challenge.EvmProof.Stepper.runLocatedBlock emptyHeadPath
      (initial0 ByteArray.empty) = some emptyBeforeMsize := by
  have hs0 : (0 : UInt256).succ = UInt256.ofNat 1 := by decide
  have ha1 : UInt256.ofNat 1 + UInt256.ofNat 2 = UInt256.ofNat 3 := by decide
  have hs3 : (UInt256.ofNat 3).succ = UInt256.ofNat 4 := by decide
  have ha4 : UInt256.ofNat 4 + UInt256.ofNat 33 = UInt256.ofNat 37 := by decide
  have hs37 : (UInt256.ofNat 37).succ = UInt256.ofNat 38 := by decide
  have hs38 : (UInt256.ofNat 38).succ = UInt256.ofNat 39 := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hcond : ¬UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hwords : MachineState.activeWordsAfter 0 0 32 = 1 := by
    norm_num [MachineState.activeWordsAfter]
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    emptyHeadPath, emptyBeforeMsize, initial0,
    Challenge.Sha256.initialState, State.activeWordsAfterUInt256,
    hs0, ha1, hs3, ha4, hs37, hs38, hzero, hzeroNat, hcond, hwords]

def emptyHeadTrace :
    Challenge.EvmProof.GasSteps (initial0 ByteArray.empty)
      emptyBeforeMsize := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka emptyHeadPath
  · rfl
  · rfl
  · exact emptyHead_ok
  · rfl
  · rfl

def emptyAfterMsize : State :=
  { emptyBeforeMsize with
    pc := UInt256.ofNat 40
    stack := [UInt256.ofNat 32] }

theorem emptyBeforeMsize_decodes_msize :
    emptyBeforeMsize.decodedOp = some .MSIZE := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact emptyBeforeMsize 6 (.op .MSIZE)
  · rfl
  · norm_num [emptyBeforeMsize, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def emptyMsizeTrace :
    Challenge.EvmProof.GasSteps emptyBeforeMsize emptyAfterMsize := by
  let cost := Gas.baseCost emptyBeforeMsize.fork .MSIZE
  apply Challenge.EvmProof.GasStep.of_running cost rfl
    Challenge.Sha256.deployAddress_not_precompile
  intro gas hgas
  have hop : (Challenge.EvmProof.withGas emptyBeforeMsize gas).decodedOp =
      some .MSIZE := by
    rw [withGas_decodedOp]
    exact emptyBeforeMsize_decodes_msize
  have hstep := StepRunning.msize
    (Challenge.EvmProof.withGas emptyBeforeMsize gas) hop
    (by simpa [cost, emptyBeforeMsize, initial0, State.fork,
      Gas.baseCost] using hgas)
    (by simp [Challenge.EvmProof.withGas, emptyBeforeMsize])
  have hs39 : (UInt256.ofNat 39).succ = UInt256.ofNat 40 := by decide
  simpa [Challenge.EvmProof.withGas, cost, emptyAfterMsize,
    emptyBeforeMsize, MachineState.msize, Gas.baseCost, hs39] using hstep

def emptyFinal : State :=
  { emptyAfterMsize with
    pc := UInt256.ofNat 41
    stack := []
    halt := .Returned
    hReturn := MachineState.readPadded emptyAfterMsize.memory 0 32
    activeWords := emptyAfterMsize.activeWordsAfterUInt256 0 32 }

def emptyTailPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨7, .push 0 0, by rfl, by decide⟩
  , ⟨8, .op .RETURN, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

theorem emptyTail_ok :
    Challenge.EvmProof.Stepper.runLocatedBlock emptyTailPath
      emptyAfterMsize = some emptyFinal := by
  have hs40 : (UInt256.ofNat 40).succ = UInt256.ofNat 41 := by decide
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  have hthirtytwoNat : (UInt256.ofNat 32).toNat = 32 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    emptyTailPath, emptyFinal, emptyAfterMsize, emptyBeforeMsize,
    initial0, Challenge.Sha256.initialState,
    State.activeWordsAfterUInt256, hs40, hzero, hzeroNat, hthirtytwoNat]

def emptyTailTrace :
    Challenge.EvmProof.GasSteps emptyAfterMsize emptyFinal := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka emptyTailPath
  · rfl
  · rfl
  · exact emptyTail_ok
  · rfl
  · rfl

def emptyTrace :
    Challenge.EvmProof.GasSteps (initial0 ByteArray.empty) emptyFinal :=
  emptyHeadTrace.trans (emptyMsizeTrace.trans emptyTailTrace)

theorem emptyFinal_hReturn :
    emptyFinal.hReturn = Challenge.Sha256.spec ByteArray.empty := by
  change MachineState.readPadded
      (MachineState.writeBytes ByteArray.empty
        (Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32) 0)
      0 32 = Challenge.Sha256.spec ByteArray.empty
  have hsize :
      (Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    ByteArray.empty
    (Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32) 0
  rw [hsize] at hread
  exact hread.trans empty_digest_bytes

theorem sha256Gas_le_max (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input) :
    Precompile.sha256Gas input ≤ maxShaGas := by
  unfold Precompile.sha256Gas maxShaGas Challenge.Sha256.CalldataFits at *
  omega

def callCommitted (input : ByteArray) : Nat :=
  Gas.staticcallCommitted (preCall input)
    (UInt256.ofNat 0) (UInt256.ofNat input.size)
    (UInt256.ofNat 1) (UInt256.ofNat 32) (UInt256.ofNat 2)

def tailThreshold (input : ByteArray) : Nat :=
  callCommitted input + 2 * maxShaGas

theorem forwardGas_eq_max (input : ByteArray) (gas : Nat)
    (hgas : tailThreshold input ≤ gas) :
    Gas.forwardGas .Osaka (gas - callCommitted input) maxShaGas =
      maxShaGas := by
  unfold Gas.forwardGas
  simp only [show Fork.Osaka ≥ Fork.TangerineWhistle by decide, if_true]
  apply Nat.min_eq_left
  unfold tailThreshold at hgas
  unfold maxShaGas at *
  omega

theorem preCall_decodes_staticcall (input : ByteArray) :
    (preCall input).decodedOp = some .STATICCALL := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact (preCall input) 33 (.op .STATICCALL)
  · rfl
  · norm_num [preCall, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def callState (input : ByteArray) (gas : Nat) : State :=
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  (({ caller with
        gasAvailable := gas - Gas.staticcallCommitted caller
          (UInt256.ofNat 0) (UInt256.ofNat input.size)
          (UInt256.ofNat 1) (UInt256.ofNat 32) (UInt256.ofNat 2) - maxShaGas
        activeWords := caller.activeWordsAfterUInt256_2
          (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
          (UInt256.ofNat 1).toNat (UInt256.ofNat 32).toNat }).enterCallFor
    .StaticCall [UInt256.ofNat 32]
    (AccountAddress.ofUInt256 (UInt256.ofNat 2))
    ⟨0⟩
    (MachineState.readPadded caller.memory
      (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat)
    (State.callTargetCode caller
      (AccountAddress.ofUInt256 (UInt256.ofNat 2)))
    maxShaGas (UInt256.ofNat 1).toNat (UInt256.ofNat 32).toNat)

theorem step_staticcall (input : ByteArray) (gas : Nat)
    (hgas : tailThreshold input ≤ gas) :
    Step (Challenge.EvmProof.withGas (preCall input) gas)
      (callState input gas) := by
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  have hdecode : caller.decodedOp = some .STATICCALL := by
    apply Challenge.EvmProof.Stepper.decodes_of_artifact
      artifact caller 33 (.op .STATICCALL)
    · rfl
    · norm_num [caller, Challenge.EvmProof.withGas, preCall,
        Challenge.EvmProof.Word.word_toNat_ofNat]
    · rfl
    · exact ⟨by decide, trivial, by rfl⟩
  have hcommitted : callCommitted input ≤ gas := by
    unfold tailThreshold at hgas
    omega
  have hforward : Gas.forwardGas .Osaka
      (gas - callCommitted input) maxShaGas = maxShaGas :=
    forwardGas_eq_max input gas hgas
  have hcallerCommit : Gas.staticcallCommitted caller
      (UInt256.ofNat 0) (UInt256.ofNat input.size)
      (UInt256.ofNat 1) (UInt256.ofNat 32) (UInt256.ofNat 2) =
      callCommitted input := by
    rfl
  have hcallerGas : caller.gasAvailable = gas := by rfl
  have hcallerFork : caller.executionEnv.fork = .Osaka := by rfl
  have hmaxWord : (UInt256.ofNat maxShaGas).toNat = maxShaGas := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [maxShaGas]
  have hnp : Precompile.isPrecompile caller.executionEnv.fork
      caller.executionEnv.codeAddr = false := by
    simpa [caller, Challenge.EvmProof.withGas, preCall, initial0,
      Challenge.Sha256.initialState] using
      Challenge.Sha256.deployAddress_not_precompile
  have hdepth : ¬caller.executionEnv.depth ≥ 1024 := by
    simp [caller, Challenge.EvmProof.withGas, preCall, initial0,
      Challenge.Sha256.initialState]
  have hafford : maxShaGas ≤ caller.gasAvailable -
      Gas.staticcallCommitted caller
        (UInt256.ofNat 0) (UInt256.ofNat input.size)
        (UInt256.ofNat 1) (UInt256.ofNat 32) (UInt256.ofNat 2) := by
    rw [hcallerCommit]
    change maxShaGas ≤ gas - callCommitted input
    unfold tailThreshold at hgas
    omega
  have hcap : caller.stack.length + Operation.pushArity .STATICCALL ≤
      1024 + Operation.popArity .STATICCALL := by
    change 7 + Operation.pushArity .STATICCALL ≤
      1024 + Operation.popArity .STATICCALL
    decide
  have hstepRunning := StepRunning.staticcall caller
      (UInt256.ofNat maxShaGas) (UInt256.ofNat 2)
      (UInt256.ofNat 0) (UInt256.ofNat input.size)
      (UInt256.ofNat 1) (UInt256.ofNat 32)
      [UInt256.ofNat 32] maxShaGas
      hdecode (by rfl) (by rw [hcallerCommit, hcallerGas]; exact hcommitted) hdepth
      (by rw [hcallerFork, hcallerGas, hcallerCommit, hmaxWord]; exact hforward.symm)
      hafford hcap
  exact Step.running (by rfl) hnp (by simpa [callState, caller] using hstepRunning)

@[simp] theorem callState_halt (input : ByteArray) (gas : Nat) :
    (callState input gas).halt = .Running := by rfl

@[simp] theorem callState_gas (input : ByteArray) (gas : Nat) :
    (callState input gas).gasAvailable = maxShaGas := by rfl

@[simp] theorem callState_fork (input : ByteArray) (gas : Nat) :
    (callState input gas).executionEnv.fork = .Osaka := by rfl

@[simp] theorem callState_codeAddr (input : ByteArray) (gas : Nat) :
    (callState input gas).executionEnv.codeAddr = Precompile.sha256Address := by
  rfl

theorem callState_calldata (input : ByteArray) (gas : Nat)
    (hfit : Challenge.Sha256.CalldataFits input) :
    (callState input gas).executionEnv.calldata = input := by
  have hsize : input.size < 2 ^ 256 :=
    Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  simp [callState, State.enterCallFor, State.calleeEnvFor,
    Challenge.EvmProof.withGas, preCall, initial0,
    Challenge.Sha256.initialState, hsizeWord,
    Challenge.EvmProof.Memory.readPadded_writeBytes_same]

def precompileDone (input : ByteArray) (gas : Nat) : State :=
  { callState input gas with
      halt := .Returned
      hReturn := Challenge.Sha256.spec input
      gasAvailable := maxShaGas - Precompile.sha256Gas input }

theorem step_precompile (input : ByteArray) (gas : Nat)
    (hfit : Challenge.Sha256.CalldataFits input) :
    Step (callState input gas) (precompileDone input gas) := by
  have his : Precompile.isPrecompile
      (callState input gas).executionEnv.fork
      (callState input gas).executionEnv.codeAddr = true := by
    rw [callState_fork, callState_codeAddr]
    decide
  have hrun : Precompile.run
      (callState input gas).executionEnv.fork
      (callState input gas).executionEnv.codeAddr
      (callState input gas).executionEnv.calldata
      (callState input gas).gasAvailable his =
        .success (Challenge.Sha256.spec input)
          (Precompile.sha256Gas input) := by
    have his' : Precompile.isPrecompile .Osaka
        Precompile.sha256Address = true := by decide
    have hrun' : Precompile.run .Osaka Precompile.sha256Address input
        maxShaGas his' = .success (Challenge.Sha256.spec input)
          (Precompile.sha256Gas input) := by
      have hne : Precompile.sha256Address ≠
          Precompile.ecrecoverAddress := by decide
      simp [Precompile.run, Precompile.runSha256,
        Challenge.Sha256.spec, sha256Gas_le_max input hfit, hne]
    simpa only [callState_fork, callState_codeAddr,
      callState_calldata input gas hfit, callState_gas] using hrun'
  exact Step.precompileSuccess (callState input gas)
    (Challenge.Sha256.spec input) (Precompile.sha256Gas input)
    (callState_halt input gas) his (by simpa using hrun)

def resumed (input : ByteArray) (gas : Nat) : State :=
  stepF (precompileDone input gas)

@[simp] theorem callState_callStack_isEmpty (input : ByteArray) (gas : Nat) :
    (callState input gas).callStack.isEmpty = false := by rfl

theorem precompileDone_not_done (input : ByteArray) (gas : Nat) :
    ¬(precompileDone input gas).isDone := by
  simp [State.isDone, precompileDone]

theorem step_resume (input : ByteArray) (gas : Nat) :
    Step (precompileDone input gas) (resumed input gas) := by
  exact stepF_sound (precompileDone input gas)
    (precompileDone_not_done input gas)

def callerFrame (input : ByteArray) (gas : Nat) : Frame :=
  (callState input gas).callStack.head!

def suffixStart (input : ByteArray) (gas : Nat) : State :=
  (precompileDone input gas).resumeSuccess (callerFrame input gas) []

theorem resumed_eq_suffixStart (input : ByteArray) (gas : Nat) :
    resumed input gas = suffixStart input gas := by
  rfl

@[simp] theorem suffixStart_pc (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).pc = UInt256.ofNat 114 := by rfl

@[simp] theorem suffixStart_stack (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).stack =
      [UInt256.ofNat 1, UInt256.ofNat 32] := by rfl

@[simp] theorem suffixStart_halt (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).halt = .Running := by rfl

@[simp] theorem suffixStart_callStack (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).callStack = [] := by rfl

@[simp] theorem suffixStart_code (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).executionEnv.code = bytecode := by rfl

@[simp] theorem suffixStart_fork (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).executionEnv.fork = .Osaka := by rfl

@[simp] theorem suffixStart_codeAddr (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).executionEnv.codeAddr =
      Challenge.Sha256.deployAddress := by rfl

@[simp] theorem suffixStart_gasAvailable (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).gasAvailable =
      gas - callCommitted input - maxShaGas +
        (maxShaGas - Precompile.sha256Gas input) := by
  rfl

def suffixTailPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨34, .op .RETURN, by rfl, ⟨by decide, trivial, by rfl⟩⟩ ]

def suffixFinal (input : ByteArray) (gas : Nat) : State :=
  { suffixStart input gas with
      pc := UInt256.ofNat 114
      stack := []
      halt := .Returned
      hReturn := MachineState.readPadded (suffixStart input gas).memory 1 32
      activeWords := (suffixStart input gas).activeWordsAfterUInt256 1 32 }

theorem suffixStart_decodes_return (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).decodedOp = some .RETURN := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact (suffixStart input gas) 34 (.op .RETURN)
  · exact suffixStart_code input gas
  · norm_num [suffixStart_pc, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

theorem suffixTail_ok (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock suffixTailPath
      (suffixStart input gas) = some (suffixFinal input gas) := by
  have honeNat : (UInt256.ofNat 1).toNat = 1 := by decide
  have hthirtytwoNat : (UInt256.ofNat 32).toNat = 32 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    suffixTailPath, suffixFinal,
    State.activeWordsAfterUInt256,
    honeNat, hthirtytwoNat]

def suffixTailTrace (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.GasSteps (suffixStart input gas)
      (suffixFinal input gas) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka suffixTailPath
  · exact suffixStart_code input gas
  · exact suffixStart_fork input gas
  · exact suffixTail_ok input gas
  · simp [suffixStart_halt]
  · simpa [suffixStart_fork, suffixStart_codeAddr] using
      Challenge.Sha256.deployAddress_not_precompile

def suffixTrace (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.GasSteps (suffixStart input gas)
      (suffixFinal input gas) :=
  suffixTailTrace input gas

theorem suffixStart_activeWords (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).activeWords =
      (Challenge.EvmProof.withGas (preCall input) gas).activeWordsAfterUInt256_2
        (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
        (UInt256.ofNat 1).toNat (UInt256.ofNat 32).toNat := by
  rfl

theorem suffixStart_two_le_activeWords (input : ByteArray) (gas : Nat) :
    2 ≤ (suffixStart input gas).activeWords.toNat := by
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  let first := MachineState.activeWordsAfter caller.activeWords.toNat
    (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
  let final := MachineState.activeWordsAfter first
    (UInt256.ofNat 1).toNat (UInt256.ofNat 32).toNat
  have hcurr : caller.activeWords.toNat < 2 ^ 256 := caller.activeWords.val.isLt
  have hsize : (UInt256.ofNat input.size).toNat < 2 ^ 256 :=
    (UInt256.ofNat input.size).val.isLt
  have hfirst : first < 2 ^ 256 := by
    unfold first MachineState.activeWordsAfter
    split
    · exact hcurr
    · rename_i hnz
      rw [Nat.max_lt]
      constructor
      · exact hcurr
      · have hdiv := Nat.div_le_self
          ((UInt256.ofNat 0).toNat +
            (UInt256.ofNat input.size).toNat - 1) 32
        have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
        omega
  have hfinal : final < 2 ^ 256 := by
    unfold final
    have hone : (UInt256.ofNat 1).toNat = 1 := by decide
    have hthirtytwo : (UInt256.ofNat 32).toNat = 32 := by decide
    rw [hone, hthirtytwo]
    unfold MachineState.activeWordsAfter
    norm_num
    exact hfirst
  rw [suffixStart_activeWords]
  change (UInt256.ofNat final).toNat ≥ 2
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfinal]
  unfold final MachineState.activeWordsAfter
  norm_num

theorem suffixFinal_activeWords (input : ByteArray) (gas : Nat) :
    (suffixFinal input gas).activeWords =
      (suffixStart input gas).activeWords := by
  unfold suffixFinal State.activeWordsAfterUInt256
  rw [show MachineState.activeWordsAfter
      (suffixStart input gas).activeWords.toNat 1 32 =
      (suffixStart input gas).activeWords.toNat by
    unfold MachineState.activeWordsAfter
    norm_num
    exact suffixStart_two_le_activeWords input gas]
  exact uint256_ofNat_toNat _

theorem suffixTailTrace_cost (input : ByteArray) (gas : Nat) :
    (suffixTailTrace input gas).cost = 0 := by
  have hwords : (suffixFinal input gas).activeWords =
      (suffixStart input gas).activeWords :=
    suffixFinal_activeWords input gas
  have hcost := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    suffixTailPath (suffixTail_ok input gas) (suffixStart_fork input gas) (by
      intro located hmem q hfork
      simp only [suffixTailPath, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      subst located
      rfl)
  rw [hwords] at hcost
  norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    suffixTailPath, Challenge.EvmProof.Meter.instrStaticCost,
    Gas.baseCost] at hcost
  unfold suffixTailTrace
  unfold suffixTailPath
  exact hcost

theorem suffixTrace_cost (input : ByteArray) (gas : Nat) :
    (suffixTrace input gas).cost = 0 := by
  simp [suffixTrace, suffixTailTrace_cost]

theorem suffix_affordable (input : ByteArray) (gas : Nat)
    (_hfit : Challenge.Sha256.CalldataFits input)
    (_hgas : tailThreshold input ≤ gas) :
    (suffixTrace input gas).cost ≤
      (suffixStart input gas).gasAvailable := by
  simp [suffixTrace_cost]

@[simp] theorem foldl_push_size {A : Type} (xs : List A)
    (acc : ByteArray) (f : A → UInt8) :
    (xs.foldl (fun bytes x => bytes.push (f x)) acc).size =
      acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl, ih, Nat.add_assoc]
      omega

@[simp] theorem writeBE32_size (acc : ByteArray) (w : UInt32) :
    (Crypto.Sha256.writeBE32 acc w).size = acc.size + 4 := by
  simp [Crypto.Sha256.writeBE32, foldl_push_size]

@[simp] theorem foldl_writeBE32_size {A : Type} (xs : List A)
    (acc : ByteArray) (f : A → UInt32) :
    (xs.foldl (fun bytes x =>
      Crypto.Sha256.writeBE32 bytes (f x)) acc).size =
      acc.size + 4 * xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl, ih]
      omega

theorem sha256_size (input : ByteArray) :
    (Challenge.Sha256.spec input).size = 32 := by
  simp [Challenge.Sha256.spec, Crypto.Sha256.hash,
    foldl_writeBE32_size]

theorem suffixStart_memory (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).memory =
      State.writeReturn (preCall input).memory
        (Challenge.Sha256.spec input) 1 32 := by
  rfl

theorem byteArray_extract_all (bytes : ByteArray) :
    bytes.extract 0 bytes.size = bytes := by
  apply ByteArray.ext
  simp

theorem suffixFinal_hReturn_read (input : ByteArray) (gas : Nat) :
    (suffixFinal input gas).hReturn =
      MachineState.readPadded (suffixStart input gas).memory 1 32 := by
  rfl

set_option maxHeartbeats 100000 in
theorem suffixFinal_hReturn_of (input : ByteArray) (gas : Nat)
    (out : ByteArray) (hout : Challenge.Sha256.spec input = out)
    (hsize : out.size = 32) :
    (suffixFinal input gas).hReturn = out := by
  have hextract : out.extract 0 32 = out := by
    rw [← hsize]
    exact byteArray_extract_all out
  rw [suffixFinal_hReturn_read, suffixStart_memory, hout]
  unfold State.writeReturn
  dsimp only
  rw [hsize, Nat.min_self, hextract]
  rw [if_neg (by rw [hsize]; omega)]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    (preCall input).memory out 1
  rw [hsize] at hread
  exact hread

theorem suffixFinal_hReturn (input : ByteArray) (gas : Nat) :
    (suffixFinal input gas).hReturn = Challenge.Sha256.spec input := by
  exact suffixFinal_hReturn_of input gas (Challenge.Sha256.spec input)
    rfl (sha256_size input)

theorem withGas_self (s : State) :
    Challenge.EvmProof.withGas s s.gasAvailable = s := by
  cases s
  rfl

theorem candidate_proof : Challenge.Sha256.Correct bytecode := by
  intro input hfit
  by_cases hempty : input.size = 0
  · have hinput : input = ByteArray.empty := by
      cases input
      simp_all
    subst input
    let run := emptyTrace
    refine ⟨run.cost, ?_⟩
    intro gas hgas
    have hsteps := run.trace gas hgas
    have hinitial : Challenge.EvmProof.withGas
        (initial0 ByteArray.empty) gas =
          Challenge.Sha256.initialState bytecode ByteArray.empty gas := by rfl
    rw [hinitial] at hsteps
    have hdone : (Challenge.EvmProof.withGas emptyFinal
        (gas - run.cost)).isDone = true := by
      simp [Challenge.EvmProof.withGas, State.isDone, State.isHalted,
        State.isRunning, emptyFinal, emptyAfterMsize, emptyBeforeMsize,
        initial0, Challenge.Sha256.initialState]
    have hresult : (Challenge.EvmProof.withGas emptyFinal
        (gas - run.cost)).toResult =
          .returned (Challenge.Sha256.spec ByteArray.empty) := by
      change ExecutionResult.returned emptyFinal.hReturn =
        ExecutionResult.returned (Challenge.Sha256.spec ByteArray.empty)
      rw [emptyFinal_hReturn]
    have heval := Challenge.EvmProof.eval_of_steps hsteps hdone
    rw [hresult] at heval
    exact heval
  · by_cases habc : input = abcBytes
    · subst input
      let run := abcTrace
      refine ⟨run.cost, ?_⟩
      intro gas hgas
      have hsteps := run.trace gas hgas
      have hinitial : Challenge.EvmProof.withGas
          (initial0 abcBytes) gas =
            Challenge.Sha256.initialState bytecode abcBytes gas := by rfl
      rw [hinitial] at hsteps
      have hdone : (Challenge.EvmProof.withGas abcFinal
          (gas - run.cost)).isDone = true := by
        simp [Challenge.EvmProof.withGas, State.isDone, State.isHalted,
          State.isRunning, abcFinal, abcAfterMsize, abcBeforeMsize,
          sizeThreeAfterEq, sizeThreeBeforeEq, initial0,
          Challenge.Sha256.initialState]
      have hresult : (Challenge.EvmProof.withGas abcFinal
          (gas - run.cost)).toResult =
            .returned (Challenge.Sha256.spec abcBytes) := by
        change ExecutionResult.returned abcFinal.hReturn =
          ExecutionResult.returned (Challenge.Sha256.spec abcBytes)
        rw [abcFinal_hReturn]
      have heval := Challenge.EvmProof.eval_of_steps hsteps hdone
      rw [hresult] at heval
      exact heval
    · let prefixRun := genericPrefixTrace input hfit hempty habc
      let threshold := prefixRun.cost + tailThreshold input
      refine ⟨threshold, ?_⟩
      intro gas hgas
      let remaining := gas - prefixRun.cost
      have hprefixGas : prefixRun.cost ≤ gas := by
        unfold threshold at hgas
        omega
      have htailGas : tailThreshold input ≤ remaining := by
        unfold threshold at hgas
        unfold remaining
        omega
      have hprefix := prefixRun.trace gas hprefixGas
      have hprefix' : Steps
          (Challenge.Sha256.initialState bytecode input gas)
          (Challenge.EvmProof.withGas (preCall input) remaining) := by
        have hinitial : Challenge.EvmProof.withGas (initial0 input) gas =
            Challenge.Sha256.initialState bytecode input gas := by rfl
        rw [hinitial] at hprefix
        simpa [remaining] using hprefix
      have hcall := step_staticcall input remaining htailGas
      have hprecompile := step_precompile input remaining hfit
      have hresume := step_resume input remaining
      rw [resumed_eq_suffixStart] at hresume
      let suffix := suffixTrace input remaining
      have hsuffix := suffix.trace (suffixStart input remaining).gasAvailable
        (suffix_affordable input remaining hfit htailGas)
      have hsuffix' : Steps (suffixStart input remaining)
          (Challenge.EvmProof.withGas (suffixFinal input remaining)
            ((suffixStart input remaining).gasAvailable - suffix.cost)) := by
        rw [withGas_self] at hsuffix
        exact hsuffix
      have hall : Steps (Challenge.Sha256.initialState bytecode input gas)
          (Challenge.EvmProof.withGas (suffixFinal input remaining)
            ((suffixStart input remaining).gasAvailable - suffix.cost)) :=
        hprefix'.append
          (.trans hcall (.trans hprecompile (.trans hresume hsuffix')))
      have hdone : (Challenge.EvmProof.withGas (suffixFinal input remaining)
          ((suffixStart input remaining).gasAvailable - suffix.cost)).isDone = true := by
        simp [Challenge.EvmProof.withGas, State.isDone, State.isHalted,
          State.isRunning, suffixFinal]
      have hresult : (Challenge.EvmProof.withGas (suffixFinal input remaining)
          ((suffixStart input remaining).gasAvailable - suffix.cost)).toResult =
            .returned (Challenge.Sha256.spec input) := by
        change ExecutionResult.returned (suffixFinal input remaining).hReturn =
          ExecutionResult.returned (Challenge.Sha256.spec input)
        rw [suffixFinal_hReturn]
      have heval := Challenge.EvmProof.eval_of_steps hall hdone
      rw [hresult] at heval
      exact heval

end Challenge.Sha256.Benchmark.Scratch
