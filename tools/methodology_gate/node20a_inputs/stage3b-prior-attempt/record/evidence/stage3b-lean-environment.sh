#!/bin/bash
set -eu
export LEAN_PATH=/output/build:/runtime/erdos-build/lib/lean:/runtime/hypostructure-build/lib/lean
for pkg in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  export LEAN_PATH="$LEAN_PATH:/runtime/erdos-packages/$pkg/.lake/build/lib/lean"
done
exec /runtime/lean/bin/lean "$@"
