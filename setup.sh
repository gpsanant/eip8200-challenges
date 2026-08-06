#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

readonly track="${1:-}"
case "${track}" in
  sha256)
    readonly target_module="Challenge.Sha256.Benchmark.Target"
    readonly reference_module="Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect"
    readonly scorer_module="Sha256Main"
    readonly scorer_exe="sha256challenge"
    ;;
  modexp)
    readonly target_module="Challenge.Modexp.Benchmark.Target"
    readonly reference_module="Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect"
    readonly scorer_module="ModexpMain"
    readonly scorer_exe="modexpchallenge"
    ;;
  ripemd160)
    readonly target_module="Challenge.Ripemd160.Benchmark.Target"
    readonly reference_module="Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect"
    readonly scorer_module="Ripemd160Main"
    readonly scorer_exe="ripemd160challenge"
    ;;
  *)
    echo "usage: $0 {sha256|modexp|ripemd160}" >&2
    exit 64
    ;;
esac

readonly comparator_rev="51491237b1d2f96cca203af9c34bced6fe38e0d8"
readonly exporter_toolchain="leanprover/lean4:v4.31.0"
readonly verifier_toolchain="leanprover/lean4:v4.32.2"
readonly landrun_rev="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
readonly tools_dir="${root}/.benchmark-tools"
readonly comparator_dir="${tools_dir}/comparator"
readonly landrun_dir="${tools_dir}/landrun"
readonly exporter_bin="${comparator_dir}/.lake/packages/lean4export/.lake/build/bin/lean4export"
readonly comparator_bin="${comparator_dir}/.lake/build/bin/comparator"
readonly landrun_bin="${landrun_dir}/landrun"
readonly built_scorer_bin="${root}/.lake/build/bin/${scorer_exe}"
readonly trusted_scorer_bin="${tools_dir}/trusted/${scorer_exe}"

if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

clone_at() {
  local url="$1"
  local revision="$2"
  local destination="$3"
  if [[ ! -d "${destination}/.git" ]]; then
    git clone --filter=blob:none --no-checkout "${url}" "${destination}"
  fi
  git -C "${destination}" fetch --depth=1 origin "${revision}"
  git -C "${destination}" checkout --detach --force "${revision}"
  [[ "$(git -C "${destination}" rev-parse HEAD)" == "${revision}" ]]
  [[ -z "$(git -C "${destination}" status --porcelain --untracked-files=no)" ]]
}

mkdir -p "${tools_dir}"
if [[ "${BENCHMARK_TOOLS_CACHE_RESTORED:-}" == true ]]; then
  [[ "$(git -C "${comparator_dir}" rev-parse HEAD)" == "${comparator_rev}" ]]
  [[ -z "$(git -C "${comparator_dir}" status --porcelain --untracked-files=no)" ]]
  [[ -x "${exporter_bin}" && -x "${comparator_bin}" ]]
  if [[ "$(uname -s)" == Linux ]]; then
    [[ "$(git -C "${landrun_dir}" rev-parse HEAD)" == "${landrun_rev}" ]]
    [[ -z "$(git -C "${landrun_dir}" status --porcelain --untracked-files=no)" ]]
    [[ -x "${landrun_bin}" ]]
  fi
else
  clone_at https://github.com/leanprover/comparator.git "${comparator_rev}" "${comparator_dir}"
  elan run "${exporter_toolchain}" lake -d "${comparator_dir}" build lean4export
  elan run "${verifier_toolchain}" lake -d "${comparator_dir}" build comparator

  if [[ "$(uname -s)" == Linux ]]; then
    command -v go >/dev/null 2>&1 || {
      echo "Go 1.24 or newer is required to build landrun" >&2
      exit 1
    }
    clone_at https://github.com/Zouuup/landrun.git "${landrun_rev}" "${landrun_dir}"
    (
      cd "${landrun_dir}"
      go build -trimpath -o landrun ./cmd/landrun
    )
  fi
fi

if [[ "${BENCHMARK_LAKE_CACHE_RESTORED:-}" != 1 ]]; then
  lake exe cache get
fi

mkdir -p "${tools_dir}/trusted"

# Build the selected trusted closure in dependency order, one Lake process per
# module. This bounds peak memory and leaves valid trace metadata after every
# completed module.
scripts/build-lean-serial.sh \
  "${target_module}" "${reference_module}" "${scorer_module}"

# The scorer module and proof closure are already traced. Lake's remaining work
# is native compilation and linking rather than parallel Lean elaboration.
lake build "${scorer_exe}"
install -m 0755 "${built_scorer_bin}" "${trusted_scorer_bin}"

echo "${track} benchmark setup complete"
