import Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def bigJumpPath := Dispatch.wordJumpPath

def bigCheckExpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 928 .JUMPDEST, opAt 929 (.Dup ⟨2, by decide⟩),
   pushAt 930 1 96, opAt 931 .ADD]

def bigCheckModPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 932 (.Dup ⟨2, by decide⟩), opAt 933 (.Dup ⟨1, by decide⟩),
   opAt 934 .ADD]

def bigCheckComparePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 935 1 32, opAt 936 (.Dup ⟨3, by decide⟩), opAt 937 .GT]

def bigCheckJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 938 2 1268, opAt 939 .JUMPI]

def bigCheckPath := bigCheckExpPath ++ bigCheckModPath ++
  bigCheckComparePath ++ bigCheckJumpPath

def bigTailFramePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 950 .JUMPDEST, pushAt 951 2 1283,
   opAt 952 (.Dup ⟨1, by decide⟩), opAt 953 (.Dup ⟨3, by decide⟩)]

def bigTailArgsPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 954 1 96, opAt 955 (.Dup ⟨6, by decide⟩),
   opAt 956 (.Dup ⟨8, by decide⟩), opAt 957 (.Dup ⟨10, by decide⟩)]

def bigTailJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 958 2 704, opAt 959 .JUMP]

def bigTailPath := bigTailFramePath ++ bigTailArgsPath ++ bigTailJumpPath

def bigExpOffsetState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1242
    stack := [UInt256.ofNat (96 + baseSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def bigOffsetsState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1245
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigComparedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1249
    stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigCheckedState (input : ByteArray) : State :=
  { Dispatch.wordCheckedState input with pc := UInt256.ofNat 1268 }

def bigTailFrameState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 1274
    stack := [UInt256.ofNat expOff, UInt256.ofNat modOff, UInt256.ofNat 1283,
      UInt256.ofNat modOff, UInt256.ofNat expOff, UInt256.ofNat m,
      UInt256.ofNat e, UInt256.ofNat b] }

def bigTailArgsState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 1279
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1283, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

/-- Calling-convention state at the first instruction of `modexpBig`. -/
def bigEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 704
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1283, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

@[simp] theorem bigTailPCs (i : Nat) (hi : 950 ≤ i) (hii : i ≤ 959) :
    Artifact.referenceArtifact.instructionPC i =
      [1268,1269,1272,1273,1274,1276,1277,1278,1279,1282][i - 950]! := by
  interval_cases i <;> decide

theorem jump704 : Decode.isValidJumpDest referenceBytecode 704 = true :=
  Artifact.isValidJumpDest_index 563 (by rfl)

theorem jump1268 : Decode.isValidJumpDest referenceBytecode 1268 = true :=
  Artifact.isValidJumpDest_index 950 (by rfl)

end Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
