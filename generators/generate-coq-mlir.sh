#!/usr/bin/env bash
# Build the state-machine exporter and check CoreSoc against Semantics.v.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
: "${CIRCT_ROOT:?Set CIRCT_ROOT to the CIRCT SDK (tested: firtool-1.62.0)}"
CIRCT_ROOT=$(realpath -- "$CIRCT_ROOT")
if [[ $# -gt 1 ]]; then
  echo "Usage: $0 [CoreSoc.fir]" >&2
  exit 2
fi
for tool in firtool circt-opt; do
  [[ -x "$CIRCT_ROOT/bin/$tool" ]] || { echo "Missing $CIRCT_ROOT/bin/$tool" >&2; exit 1; }
done
command -v coqc >/dev/null
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
if [[ $# -eq 1 ]]; then
  input=$(realpath -- "$1")
else
  cd "$repo"
  if [[ ! -f riscv-spec-core/build.sbt ]]; then
    git submodule update --init --recursive riscv-spec-core
  fi
  mill --no-server chiselModule.runMain mini.CoqMain \
    --target-dir "$work/chisel" --no-run-firrtl
  input="$work/chisel/CoreSoc.fir"
fi
build="$repo/out/coq-mlir"
cmake -S "$repo/mlir-to-coq" -B "$build" -G Ninja \
  -DCMAKE_PREFIX_PATH="$CIRCT_ROOT" -DCMAKE_BUILD_TYPE=Release
cmake --build "$build" -j"${JOBS:-2}"
cat > "$work/flatten.json" <<'JSON'
[{"class":"firrtl.transforms.FlattenAnnotation","target":"~CoreSoc|CoreSoc"}]
JSON
"$CIRCT_ROOT/bin/firtool" "$input" --parse-only \
  --annotation-file="$work/flatten.json" -o "$work/Parsed.mlir"
"$CIRCT_ROOT/bin/circt-opt" "$work/Parsed.mlir" \
  --pass-pipeline='builtin.module(firrtl.circuit(firrtl.module(firrtl-lower-chirrtl),firrtl-infer-widths,firrtl-infer-resets,firrtl-lower-types,firrtl-inliner,firrtl.module(firrtl-expand-whens)))' \
  -o "$work/CoreSoc.mlir"
options=()
case "${COQ_NAMED_NODES:-1}" in
  1) options+=(--named-nodes) ;;
  0) ;;
  *) echo "COQ_NAMED_NODES must be 0 or 1" >&2; exit 2 ;;
esac
"$build/firrtl-to-coq" "$work/CoreSoc.mlir" CoreSoc "$work/CoreSoc.v" "${options[@]}"
cp "$repo/mlir-to-coq/Semantics.v" "$work/Semantics.v"
(
  cd "$work"
  coqc Semantics.v
  coqc CoreSoc.v
)
mkdir -p "$repo/formal/mlir"
cp "$work/CoreSoc.mlir" "$work/CoreSoc.v" "$work/Semantics.v" "$repo/formal/mlir/"
echo "Verified: formal/mlir/CoreSoc.v (state-machine model; assertions are not proved)."
