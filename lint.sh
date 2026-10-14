#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"

ruff check .
ruff format --check .

lake exe mk_all --lib LongTails --check
lake --wfail build LongTails BudgetLatex
lake exe lint-style
lake exe runLinterNoDocString
