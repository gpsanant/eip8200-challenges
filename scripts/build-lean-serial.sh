#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

if [[ "$#" -eq 0 ]]; then
  echo "usage: $0 MODULE..." >&2
  exit 64
fi

# Lake may elaborate independent modules concurrently. The reference proofs
# are individually large enough that this can exhaust a standard runner, so
# walk local imports first and give each module its own Lake process.
built_modules=""
build_module() {
  local module="$1"
  case " ${built_modules} " in
    *" ${module} "*) return ;;
  esac

  local source="${module//.//}.lean"
  [[ -f "${source}" ]] || {
    echo "missing local Lean source for ${module}" >&2
    return 1
  }

  local dependency
  while IFS= read -r dependency; do
    case "${dependency}" in
      Challenge.*|Checks.*) build_module "${dependency}" ;;
    esac
  done < <(sed -n 's/^import //p' "${source}")

  echo "checking local module ${module} (serial)"
  lake build "${module}"
  built_modules="${built_modules} ${module}"
}

for module in "$@"; do
  build_module "${module}"
done
