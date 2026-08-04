import Challenge.Sha256.Spec
import EvmSemantics.Data.Hex

set_option warningAsError true

/-!
# SHA-256 Yukon benchmark target

The benchmark converts the protected submitted hex into a generated, trusted
`Benchmark.Artifact` module. The generated `Challenge` and editable
`Submission.Solution` then state the same `candidate` theorem for those exact
bytes.

`leanprover/comparator` checks the submitted declarations against the generated
trusted declarations and replays the proof through its independent kernel.
-/

namespace Challenge.Sha256.Benchmark

end Challenge.Sha256.Benchmark
