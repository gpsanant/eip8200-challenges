# Yukon benchmark

This repository's Yukon benchmark asks solvers to minimize the EVM gas used by
a bytecode implementation of the SHA-256 precompile while retaining a universal
Lean correctness proof. The lower-is-better score is the clean-state total over
the 19 public vectors in `Challenge.Sha256.Scorer`. Every vector must also pass
from the dirty initial state.

## Editable surface

Only `Challenge/Sha256/Submission/` is editable. Yukon replaces that directory
as a unit for every attempt. `Solution.lean` may import additional modules from
the directory, but it must expose this declaration in namespace
`Challenge.Sha256.Benchmark`:

```lean
import Challenge.Sha256.Benchmark.Artifact

theorem candidate : Challenge.Sha256.Correct bytecode := by
  ...
```

The baseline is the bundled 1,524-byte reference implementation and scores
10,179,119 gas.

## Verification

`benchmark.sh` reads `bytecode.hex` exactly once and copies it outside the
editable surface. From that protected copy it generates a Lean `ByteArray`
literal in `Challenge/Sha256/Benchmark/Artifact.lean` and the corresponding
`Challenge.lean`. Both the trusted challenge and submitted solution import that
same generated module. `leanprover/comparator` then checks that the submission:

1. proves `Challenge.Sha256.Correct bytecode` for the exact protected bytes;
2. depends only on `propext`, `Quot.sound`, and `Classical.choice`; and
3. is accepted when its exported environment is replayed by Comparator's
   independently built kernel.

Before any editable Lean module is compiled, setup copies the precompiled
trusted scorer outside Comparator's writable `.lake` tree. After Comparator
succeeds, that protected scorer executes the protected artifact on all clean
and dirty vectors. Only then does the wrapper write `score.json`.

Comparator and its format-compatible `lean4export` are pinned in `setup.sh`.
On Linux, candidate compilation runs under Landrun and the `systemd-run`
address-family restriction used by Comparator. macOS supports a functional,
non-security-bearing development run:

```sh
./setup.sh
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh
```

The ranked GitHub Actions workflow is dispatch-only, runs without repository
write permission or secrets, caches only pre-submission state, and uploads
`score.json` for Yukon.
