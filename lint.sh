#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"

if grep -REn --include='*.lean' '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+LongTails\.(Algorithms|Proofs)(\.|[[:space:]]|$)' LongTails/Setups; then
  echo "Setups must not import LongTails.Algorithms or LongTails.Proofs." >&2
  exit 1
fi

ruff check .
ruff format --check .

# mk_all returns nonzero when it creates or updates the import index.
lake exe mk_all --lib LongTails || lake exe mk_all --lib LongTails --check
lake --wfail build LongTails BudgetLatex
lake exe lint-style
lake exe runLinterNoDocString
