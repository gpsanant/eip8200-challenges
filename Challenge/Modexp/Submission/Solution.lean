import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Baseline proof for the bundled MODEXP reference bytecode. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.referenceBytecode
  exact Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

end Challenge.Modexp.Benchmark
