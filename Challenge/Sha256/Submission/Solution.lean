import Challenge.Sha256.Benchmark.Artifact
import Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Baseline Yukon solution

The benchmark generates Benchmark.Artifact from the protected copy of
bytecode.hex. This baseline discharges correctness with the bundled proof.
-/

namespace Challenge.Sha256.Benchmark

/-- The submitted bytecode implements the SHA-256 precompile interface. -/
theorem candidate : Challenge.Sha256.Correct bytecode := by
  change Challenge.Sha256.Correct Challenge.Sha256.referenceBytecode
  exact Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

end Challenge.Sha256.Benchmark
