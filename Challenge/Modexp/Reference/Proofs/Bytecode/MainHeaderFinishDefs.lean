import Challenge.Modexp.Reference.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

def headerCheckOrPath := [opAt 915 .OR, opAt 916 .OR]
def headerCheckIsZeroPath := [opAt 917 .ISZERO]
def headerCheckJumpPath := [pushAt 918 2 1228, opAt 919 .JUMPI]

def headerChecksCombinedState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 1222
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerCheckPassedState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 1223
    stack := [1, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
