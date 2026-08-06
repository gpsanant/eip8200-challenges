#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

readonly track="${1:-}"
case "${track}" in
  sha256)
    readonly challenge_dir="Sha256"
    readonly scorer_exe="sha256challenge"
    ;;
  modexp)
    readonly challenge_dir="Modexp"
    readonly scorer_exe="modexpchallenge"
    ;;
  ripemd160)
    readonly challenge_dir="Ripemd160"
    readonly scorer_exe="ripemd160challenge"
    ;;
  *)
    echo "usage: $0 {sha256|modexp|ripemd160}" >&2
    exit 64
    ;;
esac

readonly result_dir="${root}/benchmark-results/${track}"
readonly submitted_hex="${root}/Challenge/${challenge_dir}/Submission/bytecode.hex"
readonly trusted_hex="${result_dir}/verified-bytecode.hex"
readonly scorer_csv="${result_dir}/scorer.csv"
readonly score_path="${result_dir}/score.json"
readonly summary_path="${result_dir}/summary.md"
readonly artifact_path="${root}/Challenge/${challenge_dir}/Benchmark/Artifact.lean"
readonly challenge_path="${root}/Challenge/${challenge_dir}/Benchmark/Challenge.lean"
readonly comparator_dir="${root}/.benchmark-tools/comparator"
readonly comparator_bin="${comparator_dir}/.lake/build/bin/comparator"
readonly lean4export_bin="${comparator_dir}/.lake/packages/lean4export/.lake/build/bin/lean4export"
readonly scorer_bin="${root}/.benchmark-tools/trusted/${scorer_exe}"
readonly comparator_config="${root}/benchmark/comparator-${track}.json"

rm -f "${score_path}" "${summary_path}" "${trusted_hex}" "${scorer_csv}" \
  "${artifact_path}" "${challenge_path}"

[[ -f "${submitted_hex}" ]] || {
  echo "missing ${submitted_hex}" >&2
  exit 1
}

python3 scripts/yukon_benchmark.py prepare "${track}" \
  "${submitted_hex}" "${trusted_hex}" "${artifact_path}" "${challenge_path}"
trap 'rm -f "${artifact_path}" "${challenge_path}"' EXIT

[[ -x "${comparator_bin}" && -x "${lean4export_bin}" ]] || {
  echo "benchmark tools are missing; run ./setup.sh ${track} first" >&2
  exit 1
}
[[ -x "${scorer_bin}" ]] || {
  echo "protected scorer is missing; run ./setup.sh ${track} first" >&2
  exit 1
}

export COMPARATOR_LEAN4EXPORT="${lean4export_bin}"

if [[ "$(uname -s)" == Linux && "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  readonly landrun_bin="${root}/.benchmark-tools/landrun/landrun"
  [[ -x "${landrun_bin}" ]] || {
    echo "landrun is missing; run ./setup.sh ${track} first" >&2
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
    -- lake env "${comparator_bin}" "${comparator_config}"
else
  [[ "${BENCHMARK_INSECURE_LOCAL:-0}" == 1 ]] || {
    echo "set BENCHMARK_INSECURE_LOCAL=1 for a non-ranked local run on $(uname -s)" >&2
    exit 1
  }
  echo "WARNING: using Comparator's fake sandbox; this run is not trusted" >&2
  export COMPARATOR_LANDRUN="${comparator_dir}/scripts/fake-landrun.sh"
  lake env "${comparator_bin}" "${comparator_config}"
fi

# Score only the protected bytes, and only after Comparator accepts the
# universal correctness theorem for those same bytes.
"${scorer_bin}" --hex="${trusted_hex}" --csv > "${scorer_csv}"
python3 scripts/yukon_benchmark.py score "${track}" \
  "${trusted_hex}" "${scorer_csv}" "${score_path}" "${summary_path}"
cat "${summary_path}"
