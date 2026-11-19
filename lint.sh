#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"

nested_setups=$(find LongTails/Setups -mindepth 2 -type f -name '*.lean')
if [ -n "$nested_setups" ]; then
  printf '%s\n' "$nested_setups" >&2
  echo "Setup files must be directly in LongTails/Setups/, not in subdirectories." >&2
  exit 1
fi

if grep -REn --include='*.lean' '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+LongTails\.(Algorithms|Proofs)(\.|[[:space:]]|$)' LongTails/Setups; then
  echo "Setups must not import LongTails.Algorithms or LongTails.Proofs." >&2
  exit 1
fi

ruff check .
ruff format --check .

# mk_all returns nonzero when it creates or updates the import index.
lake exe mk_all --lib LongTails || lake exe mk_all --lib LongTails --check
lake --wfail build LongTails BudgetLatex Tutorial
lake exe lint-style
lake exe runLinterNoDocString
