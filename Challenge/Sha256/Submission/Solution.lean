import Challenge.Sha256.Submission.Scratch

set_option warningAsError true

namespace Challenge.Sha256.Benchmark

/-- The 26-byte wrapper delegates SHA-256 to the pinned Osaka precompile. -/
theorem candidate : Challenge.Sha256.Correct bytecode :=
  Scratch.candidate_proof

end Challenge.Sha256.Benchmark
