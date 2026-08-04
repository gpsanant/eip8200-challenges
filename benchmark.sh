#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

readonly submitted_hex="${root}/Challenge/Sha256/Submission/bytecode.hex"
readonly trusted_hex="${root}/benchmark-results/verified-bytecode.hex"
readonly scorer_csv="${root}/benchmark-results/scorer.csv"
readonly artifact_path="${root}/Challenge/Sha256/Benchmark/Artifact.lean"
readonly challenge_path="${root}/Challenge/Sha256/Benchmark/Challenge.lean"
readonly comparator_dir="${root}/.benchmark-tools/comparator"
readonly comparator_bin="${comparator_dir}/.lake/build/bin/comparator"
readonly lean4export_bin="${comparator_dir}/.lake/packages/lean4export/.lake/build/bin/lean4export"
readonly scorer_bin="${root}/.benchmark-tools/trusted/sha256challenge"

rm -f "${root}/score.json" "${root}/benchmark-results/summary.md" \
  "${trusted_hex}" "${scorer_csv}" "${challenge_path}"
rm -f "${artifact_path}"

[[ -f "${submitted_hex}" ]] || {
  echo "missing ${submitted_hex}" >&2
  exit 1
}

python3 scripts/yukon_benchmark.py prepare \
  "${submitted_hex}" "${trusted_hex}" "${artifact_path}" "${challenge_path}"
trap 'rm -f "${artifact_path}" "${challenge_path}"' EXIT

[[ -x "${comparator_bin}" && -x "${lean4export_bin}" ]] || {
  echo "benchmark tools are missing; run ./setup.sh first" >&2
  exit 1
}
[[ -x "${scorer_bin}" ]] || {
  echo "protected scorer is missing; run ./setup.sh first" >&2
  exit 1
}

export COMPARATOR_LEAN4EXPORT="${lean4export_bin}"

if [[ "$(uname -s)" == Linux && "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  readonly landrun_bin="${root}/.benchmark-tools/landrun/landrun"
  [[ -x "${landrun_bin}" ]] || {
    echo "landrun is missing; run ./setup.sh first" >&2
    exit 1
  }
  command -v systemd-run >/dev/null 2>&1 || {
    echo "systemd-run is required for the ranked benchmark" >&2
    exit 1
  }
  export COMPARATOR_LANDRUN="${landrun_bin}"
  systemd-run --user --wait --pipe \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --setenv=PATH="${PATH}" \
    --setenv=HOME="${HOME}" \
    --setenv=COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN}" \
    --setenv=COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT}" \
    --working-directory="${root}" \
    -- lake env "${comparator_bin}" benchmark/comparator.json
else
  [[ "${BENCHMARK_INSECURE_LOCAL:-0}" == 1 ]] || {
    echo "set BENCHMARK_INSECURE_LOCAL=1 for a non-ranked local run on $(uname -s)" >&2
    exit 1
  }
  echo "WARNING: using Comparator's fake sandbox; this run is not trusted" >&2
  export COMPARATOR_LANDRUN="${comparator_dir}/scripts/fake-landrun.sh"
  lake env "${comparator_bin}" benchmark/comparator.json
fi

# Only trusted code runs after Comparator accepts the universal correctness
# theorem for the artifact generated from the same protected bytes.
"${scorer_bin}" --hex="${trusted_hex}" --csv > "${scorer_csv}"
rm -f "${root}/score.json"
python3 scripts/yukon_benchmark.py score "${trusted_hex}" "${scorer_csv}"
cat "${root}/benchmark-results/summary.md"
