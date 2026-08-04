import Challenge.Sha256.Benchmark.Artifact
import Challenge.Sha256.ProofSupport.InitialState
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Meter
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Benchmark.Scratch

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def maxShaGas : Nat := 0x600000000000003c

def instructions : List Instr :=
  [ .op .CALLDATASIZE
  , .push 0 0
  , .push 0 0
  , .op .CALLDATACOPY
  , .op .CODESIZE
  , .push 0 0
  , .op .CALLDATASIZE
  , .push 0 0
  , .push 1 2
  , .push 8 (UInt256.ofNat maxShaGas)
  , .op .STATICCALL
  , .op .CODESIZE
  , .push 0 0
  , .op .RETURN
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  , .op .STOP
  ]

theorem assemble_instructions : assemble instructions = bytecode := by
  decide

def artifact : Challenge.EvmProof.ProgramArtifact where
  code := bytecode
  instructions := instructions
  assembly_eq := assemble_instructions

@[simp] theorem pc0 : artifact.instructionPC 0 = 0 := by decide
@[simp] theorem pc1 : artifact.instructionPC 1 = 1 := by decide
@[simp] theorem pc2 : artifact.instructionPC 2 = 2 := by decide
@[simp] theorem pc3 : artifact.instructionPC 3 = 3 := by decide
@[simp] theorem pc4 : artifact.instructionPC 4 = 4 := by decide
@[simp] theorem pc5 : artifact.instructionPC 5 = 5 := by decide
@[simp] theorem pc6 : artifact.instructionPC 6 = 6 := by decide
@[simp] theorem pc7 : artifact.instructionPC 7 = 7 := by decide
@[simp] theorem pc8 : artifact.instructionPC 8 = 8 := by decide
@[simp] theorem pc9 : artifact.instructionPC 9 = 10 := by decide
@[simp] theorem pc10 : artifact.instructionPC 10 = 19 := by decide
@[simp] theorem pc11 : artifact.instructionPC 11 = 20 := by decide
@[simp] theorem pc12 : artifact.instructionPC 12 = 21 := by decide
@[simp] theorem pc13 : artifact.instructionPC 13 = 22 := by decide

theorem bytecode_size : bytecode.size = 32 := by decide

def codesizeOut (s : State) : State :=
  { s with
      stack := UInt256.ofNat s.executionEnv.code.size :: s.stack
      pc := s.pc.succ }

theorem withGas_decodedOp (s : State) (gas : Nat) :
    (Challenge.EvmProof.withGas s gas).decodedOp = s.decodedOp := by
  cases s
  rfl

def gasSteps_codesize {s : State}
    (hdecode : s.decodedOp = some .CODESIZE)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcap : s.stack.length < 1024) :
    Challenge.EvmProof.GasSteps s (codesizeOut s) := by
  let cost := Gas.baseCost s.fork .CODESIZE
  apply Challenge.EvmProof.GasStep.of_running cost hrun hnp
  intro gas hgas
  have hdecodeGas :
      (Challenge.EvmProof.withGas s gas).decodedOp = some .CODESIZE := by
    rw [withGas_decodedOp]
    exact hdecode
  simpa [codesizeOut, Challenge.EvmProof.withGas, cost] using
    StepRunning.codesize (Challenge.EvmProof.withGas s gas)
      hdecodeGas
      (by simpa [cost, Challenge.EvmProof.withGas] using hgas)
      (by simpa [Challenge.EvmProof.withGas] using hcap)

def initial0 (input : ByteArray) : State :=
  Challenge.Sha256.initialState bytecode input 0

def preCall (input : ByteArray) : State :=
  { initial0 input with
    pc := UInt256.ofNat 19
    stack :=
      [ UInt256.ofNat maxShaGas
      , UInt256.ofNat 2
      , UInt256.ofNat 0
      , UInt256.ofNat input.size
      , UInt256.ofNat 0
      , UInt256.ofNat 32
      ]
    activeWords := (initial0 input).activeWordsAfterUInt256 0 input.size
    memory := MachineState.writeBytes (initial0 input).memory input 0 }

def afterCopy (input : ByteArray) : State :=
  { initial0 input with
      pc := UInt256.ofNat 4
      activeWords := (initial0 input).activeWordsAfterUInt256 0 input.size
      memory := MachineState.writeBytes (initial0 input).memory input 0 }

def afterCodeSize (input : ByteArray) : State :=
  codesizeOut (afterCopy input)

def prefixHeadPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨0, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨1, .push 0 0, by rfl, by decide⟩
  , ⟨2, .push 0 0, by rfl, by decide⟩
  , ⟨3, .op .CALLDATACOPY, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

def prefixTailPath : List
    (Challenge.EvmProof.Stepper.Located artifact .Osaka) :=
  [ ⟨5, .push 0 0, by rfl, by decide⟩
  , ⟨6, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  , ⟨7, .push 0 0, by rfl, by decide⟩
  , ⟨8, .push 1 2, by rfl, by decide⟩
  , ⟨9, .push 8 (UInt256.ofNat maxShaGas), by rfl, by decide⟩
  ]

theorem prefixHead_ok (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixHeadPath (initial0 input) =
      some (afterCopy input) := by
  have hsize : input.size < 2 ^ 256 :=
    Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hs0 : (0 : UInt256).succ = UInt256.ofNat 1 := by decide
  have hs1 : (UInt256.ofNat 1).succ = UInt256.ofNat 2 := by decide
  have hs2 : (UInt256.ofNat 2).succ = UInt256.ofNat 3 := by decide
  have hs3 : (UInt256.ofNat 3).succ = UInt256.ofNat 4 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    prefixHeadPath, afterCopy, initial0,
    Challenge.Sha256.initialState, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Memory.readPadded_zero_size,
    hsizeWord, hzero, hzeroNat, hs0, hs1, hs2, hs3]

def prefixHeadTrace (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input) :
    Challenge.EvmProof.GasSteps (initial0 input) (afterCopy input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka prefixHeadPath
  · rfl
  · rfl
  · exact prefixHead_ok input hfit
  · rfl
  · rfl

theorem afterCopy_decodes_codesize (input : ByteArray) :
    (afterCopy input).decodedOp = some .CODESIZE := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact (afterCopy input) 4 (.op .CODESIZE)
  · rfl
  · norm_num [afterCopy, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def prefixCodeSizeTrace (input : ByteArray) :
    Challenge.EvmProof.GasSteps (afterCopy input) (afterCodeSize input) := by
  exact gasSteps_codesize (afterCopy_decodes_codesize input) (by rfl)
    (by
      change Precompile.isPrecompile .Osaka
        Challenge.Sha256.deployAddress = false
      exact Challenge.Sha256.deployAddress_not_precompile)
    (by change 0 < 1024; decide)

theorem prefixTail_ok (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixTailPath
      (afterCodeSize input) = some (preCall input) := by
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  have hs4 : (UInt256.ofNat 4).succ = UInt256.ofNat 5 := by decide
  have hs5 : (UInt256.ofNat 5).succ = UInt256.ofNat 6 := by decide
  have hs6 : (UInt256.ofNat 6).succ = UInt256.ofNat 7 := by decide
  have hs7 : (UInt256.ofNat 7).succ = UInt256.ofNat 8 := by decide
  have ha8 : UInt256.ofNat 8 + UInt256.ofNat 2 = UInt256.ofNat 10 := by decide
  have ha10 : UInt256.ofNat 10 + UInt256.ofNat 9 = UInt256.ofNat 19 := by decide
  have htwo : (2 : UInt256) = UInt256.ofNat 2 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    prefixTailPath, afterCodeSize, afterCopy, preCall, initial0,
    Challenge.Sha256.initialState,
    codesizeOut, bytecode_size,
    hzero, hs4, hs5, hs6, hs7, ha8, ha10, htwo]

def prefixTailTrace (input : ByteArray) :
    Challenge.EvmProof.GasSteps (afterCodeSize input) (preCall input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka prefixTailPath
  · rfl
  · rfl
  · exact prefixTail_ok input
  · rfl
  · rfl

def prefixTrace (input : ByteArray) (hfit : Challenge.Sha256.CalldataFits input) :
    Challenge.EvmProof.GasSteps (initial0 input) (preCall input) :=
  (prefixHeadTrace input hfit).trans
    ((prefixCodeSizeTrace input).trans (prefixTailTrace input))

theorem sha256Gas_le_max (input : ByteArray)
    (hfit : Challenge.Sha256.CalldataFits input) :
    Precompile.sha256Gas input ≤ maxShaGas := by
  unfold Precompile.sha256Gas maxShaGas Challenge.Sha256.CalldataFits at *
  omega

def callCommitted (input : ByteArray) : Nat :=
  Gas.staticcallCommitted (preCall input)
    (UInt256.ofNat 0) (UInt256.ofNat input.size)
    (UInt256.ofNat 0) (UInt256.ofNat 32) (UInt256.ofNat 2)

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
    artifact (preCall input) 10 (.op .STATICCALL)
  · rfl
  · norm_num [preCall, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def callState (input : ByteArray) (gas : Nat) : State :=
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  (({ caller with
        gasAvailable := gas - Gas.staticcallCommitted caller
          (UInt256.ofNat 0) (UInt256.ofNat input.size)
          (UInt256.ofNat 0) (UInt256.ofNat 32) (UInt256.ofNat 2) - maxShaGas
        activeWords := caller.activeWordsAfterUInt256_2
          (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
          (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat }).enterCallFor
    .StaticCall [] (AccountAddress.ofUInt256 (UInt256.ofNat 2))
    ⟨0⟩
    (MachineState.readPadded caller.memory
      (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat)
    (State.callTargetCode caller
      (AccountAddress.ofUInt256 (UInt256.ofNat 2)))
    maxShaGas (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat)

theorem step_staticcall (input : ByteArray) (gas : Nat)
    (hgas : tailThreshold input ≤ gas) :
    Step (Challenge.EvmProof.withGas (preCall input) gas)
      (callState input gas) := by
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  have hdecode : caller.decodedOp = some .STATICCALL := by
    apply Challenge.EvmProof.Stepper.decodes_of_artifact
      artifact caller 10 (.op .STATICCALL)
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
      (UInt256.ofNat 0) (UInt256.ofNat 32) (UInt256.ofNat 2) =
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
        (UInt256.ofNat 0) (UInt256.ofNat 32) (UInt256.ofNat 2) := by
    rw [hcallerCommit]
    change maxShaGas ≤ gas - callCommitted input
    unfold tailThreshold at hgas
    omega
  have hcap : caller.stack.length + Operation.pushArity .STATICCALL ≤
      1024 + Operation.popArity .STATICCALL := by
    change 6 + Operation.pushArity .STATICCALL ≤
      1024 + Operation.popArity .STATICCALL
    decide
  have hstepRunning := StepRunning.staticcall caller
      (UInt256.ofNat maxShaGas) (UInt256.ofNat 2)
      (UInt256.ofNat 0) (UInt256.ofNat input.size)
      (UInt256.ofNat 0) (UInt256.ofNat 32) [] maxShaGas
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
    (suffixStart input gas).pc = UInt256.ofNat 20 := by rfl

@[simp] theorem suffixStart_stack (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).stack = [UInt256.ofNat 1] := by rfl

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
  [ ⟨12, .push 0 0, by rfl, by decide⟩
  , ⟨13, .op .RETURN, by rfl, ⟨by decide, trivial, by rfl⟩⟩
  ]

def suffixFinal (input : ByteArray) (gas : Nat) : State :=
  { suffixStart input gas with
      pc := UInt256.ofNat 22
      stack := [UInt256.ofNat 1]
      halt := .Returned
      hReturn := MachineState.readPadded (suffixStart input gas).memory 0 32
      activeWords := (suffixStart input gas).activeWordsAfterUInt256 0 32 }

theorem suffixStart_decodes_codesize (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).decodedOp = some .CODESIZE := by
  apply Challenge.EvmProof.Stepper.decodes_of_artifact
    artifact (suffixStart input gas) 11 (.op .CODESIZE)
  · exact suffixStart_code input gas
  · norm_num [suffixStart_pc, Challenge.EvmProof.Word.word_toNat_ofNat]
  · rfl
  · exact ⟨by decide, trivial, by rfl⟩

def suffixCodeSizeTrace (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.GasSteps (suffixStart input gas)
      (codesizeOut (suffixStart input gas)) :=
  gasSteps_codesize (suffixStart_decodes_codesize input gas)
    (suffixStart_halt input gas)
    (by simpa [suffixStart_fork, suffixStart_codeAddr] using
      Challenge.Sha256.deployAddress_not_precompile)
    (by simp [suffixStart_stack])

theorem suffixTail_ok (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock suffixTailPath
      (codesizeOut (suffixStart input gas)) = some (suffixFinal input gas) := by
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := by decide
  have hs20 : (UInt256.ofNat 20).succ = UInt256.ofNat 21 := by decide
  have hs21 : (UInt256.ofNat 21).succ = UInt256.ofNat 22 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    suffixTailPath, suffixFinal, codesizeOut, bytecode_size,
    State.activeWordsAfterUInt256,
    hzeroNat, hs20, hs21]

def suffixTailTrace (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.GasSteps (codesizeOut (suffixStart input gas))
      (suffixFinal input gas) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    artifact .Osaka suffixTailPath
  · exact suffixStart_code input gas
  · exact suffixStart_fork input gas
  · exact suffixTail_ok input gas
  · simp [codesizeOut, suffixStart_halt]
  · simpa [codesizeOut, suffixStart_fork, suffixStart_codeAddr] using
      Challenge.Sha256.deployAddress_not_precompile

def suffixTrace (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.GasSteps (suffixStart input gas)
      (suffixFinal input gas) :=
  (suffixCodeSizeTrace input gas).trans (suffixTailTrace input gas)

theorem uint256_ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w
  simp [UInt256.ofNat, UInt256.toNat]

theorem suffixStart_activeWords (input : ByteArray) (gas : Nat) :
    (suffixStart input gas).activeWords =
      (Challenge.EvmProof.withGas (preCall input) gas).activeWordsAfterUInt256_2
        (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
        (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat := by
  rfl

theorem suffixStart_one_le_activeWords (input : ByteArray) (gas : Nat) :
    1 ≤ (suffixStart input gas).activeWords.toNat := by
  let caller := Challenge.EvmProof.withGas (preCall input) gas
  let first := MachineState.activeWordsAfter caller.activeWords.toNat
    (UInt256.ofNat 0).toNat (UInt256.ofNat input.size).toNat
  let final := MachineState.activeWordsAfter first
    (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat
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
    have hzero : (UInt256.ofNat 0).toNat = 0 := by decide
    have hthirtytwo : (UInt256.ofNat 32).toNat = 32 := by decide
    rw [hzero, hthirtytwo]
    unfold MachineState.activeWordsAfter
    norm_num
    exact hfirst
  rw [suffixStart_activeWords]
  change (UInt256.ofNat final).toNat ≥ 1
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfinal]
  unfold final MachineState.activeWordsAfter
  norm_num

theorem suffixFinal_activeWords (input : ByteArray) (gas : Nat) :
    (suffixFinal input gas).activeWords =
      (suffixStart input gas).activeWords := by
  unfold suffixFinal State.activeWordsAfterUInt256
  rw [show MachineState.activeWordsAfter
      (suffixStart input gas).activeWords.toNat 0 32 =
      (suffixStart input gas).activeWords.toNat by
    unfold MachineState.activeWordsAfter
    norm_num
    exact suffixStart_one_le_activeWords input gas]
  exact uint256_ofNat_toNat _

theorem suffixCodeSizeTrace_cost (input : ByteArray) (gas : Nat) :
    (suffixCodeSizeTrace input gas).cost = 2 := by
  rfl

theorem suffixTailTrace_cost (input : ByteArray) (gas : Nat) :
    (suffixTailTrace input gas).cost = 2 := by
  have hwords : (suffixFinal input gas).activeWords =
      (codesizeOut (suffixStart input gas)).activeWords := by
    simpa [codesizeOut] using suffixFinal_activeWords input gas
  have hcost := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    suffixTailPath (suffixTail_ok input gas) (suffixStart_fork input gas) (by
      intro located hmem q hfork
      simp only [suffixTailPath, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with h | h
      · subst located
        rfl
      · subst located
        rfl)
  rw [hwords] at hcost
  norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    suffixTailPath, Challenge.EvmProof.Meter.instrStaticCost,
    Gas.baseCost] at hcost
  unfold suffixTailTrace
  unfold suffixTailPath
  exact hcost

theorem suffixTrace_cost (input : ByteArray) (gas : Nat) :
    (suffixTrace input gas).cost = 4 := by
  simp [suffixTrace, suffixCodeSizeTrace_cost, suffixTailTrace_cost]

theorem suffix_affordable (input : ByteArray) (gas : Nat)
    (hfit : Challenge.Sha256.CalldataFits input)
    (hgas : tailThreshold input ≤ gas) :
    (suffixTrace input gas).cost ≤
      (suffixStart input gas).gasAvailable := by
  rw [suffixTrace_cost, suffixStart_gasAvailable]
  have hsha := sha256Gas_le_max input hfit
  unfold tailThreshold at hgas
  unfold maxShaGas at *
  omega

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
        (Challenge.Sha256.spec input) 0 32 := by
  rfl

theorem byteArray_extract_all (bytes : ByteArray) :
    bytes.extract 0 bytes.size = bytes := by
  apply ByteArray.ext
  simp

theorem suffixFinal_hReturn_read (input : ByteArray) (gas : Nat) :
    (suffixFinal input gas).hReturn =
      MachineState.readPadded (suffixStart input gas).memory 0 32 := by
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
    (preCall input).memory out 0
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
  let prefixRun := prefixTrace input hfit
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
