#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"

ruff check .
ruff format --check .

# mk_all returns nonzero when it creates or updates the import index.
lake exe mk_all --lib LongTails || lake exe mk_all --lib LongTails --check
lake exe mk_all --lib LongTailsOnline || lake exe mk_all --lib LongTailsOnline --check
lake --wfail build LongTails LongTailsOnline BudgetLatex
lake exe lint-style
lake exe runLinterNoDocString
