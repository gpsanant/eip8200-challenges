# Yukon submission

This directory is the complete Yukon-editable surface. Yukon replaces it as a
unit for every attempt, so a submission must include at least:

- `bytecode.hex`: lowercase EVM bytecode, without a `0x` prefix;
- `Solution.lean`: a theorem named `candidate` in namespace
  `Challenge.Sha256.Benchmark` proving correctness of the generated
  `Benchmark.Artifact.bytecode` value.

Additional Lean modules may live in this directory and be imported by
`Solution.lean`. Files outside this directory are the protected specification,
proof support, evaluator, and workflow.

The score is the total clean-state gas across the 19 vectors in
`Challenge.Sha256.Scorer`; lower is better. Both clean and dirty-state runs must
return the correct digest. Passing the vectors is not the correctness proof:
`candidate` must prove `Challenge.Sha256.Correct bytecode` for every realizable
calldata value. `Benchmark.Artifact` is generated just before Comparator runs,
so `Solution.lean` is expected to import it and is compiled by `benchmark.sh`,
not by the initial trusted setup.
