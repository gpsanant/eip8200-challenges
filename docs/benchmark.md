# Yukon benchmark

This repository is one schema-v2 Yukon challenge with three independently
scored tracks on a shared branch:

| track | editable path | score |
| --- | --- | --- |
| `sha256` | `Challenge/Sha256/Submission` | clean-state gas over 19 vectors |
| `modexp` | `Challenge/Modexp/Submission` | gas over 9 vectors |
| `ripemd160` | `Challenge/Ripemd160/Submission` | clean-state gas over 17 vectors |

Lower is better in every track. The editable paths are deliberately disjoint,
so Yukon can promote one track without replacing a sibling track's solution.

## Selecting a track

`yukon switch <track>` changes only the repository-local Yukon selection. It
does not change the Git branch, `HEAD`, index, or worktree. Run
`yukon tracks` to see the current selection.

Record meaningful progress with `yukon notes add`: baselines, hypotheses,
experiments, failures, design changes, and blockers are useful to later
solvers. Notes are public; remove secrets, private paths, personal data, and
credentials before uploading them.

## Proof and scoring boundary

Each track accepts an editable `bytecode.hex` and Lean `Solution.lean`.
`benchmark.sh` reads the hex once, copies it outside the editable surface, and
generates a trusted `ByteArray` literal. The trusted challenge and submitted
solution state the same `candidate` theorem for that literal.

Comparator checks the theorem type, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and replays the proof with an independently built kernel.
Only after that succeeds does a protected, precompiled scorer execute the same
protected bytes and write the track's score JSON.

Comparator and its `lean4export` are pinned in `setup.sh`. Linux ranked runs
use Landrun plus a `systemd-run` address-family restriction. A functional,
non-security-bearing local run is available on macOS:

```sh
./setup.sh sha256
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh sha256
```

Replace `sha256` with `modexp` or `ripemd160` for another track. The three
dispatch-only workflows run the same shared implementation with a fixed track
argument and upload only that track's declared `scorePath`.

Setup elaborates the selected trusted proof closure in dependency order because
individual concrete-execution modules are memory intensive. Each Lake
invocation sees at most one stale module, and the package fixes Lean's own worker
count at one. The resulting Lake traces are reused by Comparator, so proof
checking is not repeated with a concurrent build later.
