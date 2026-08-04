import Challenge.Sha256.Submission.Scratch

set_option warningAsError true

namespace Challenge.Sha256.Benchmark

/-- The 154-byte candidate returns the empty and `abc` digests from ROM and
delegates every other nonempty input to the pinned Osaka SHA-256 precompile. -/
theorem candidate : Challenge.Sha256.Correct bytecode :=
  Scratch.candidate_proof

end Challenge.Sha256.Benchmark
