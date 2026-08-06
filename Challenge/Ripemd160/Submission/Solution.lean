import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Baseline proof for the bundled RIPEMD-160 reference bytecode. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode := by
  change Challenge.Ripemd160.Correct Challenge.Ripemd160.referenceBytecode
  exact Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

end Challenge.Ripemd160.Benchmark
