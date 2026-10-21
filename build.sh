#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

lake exe cache get
# mk_all returns nonzero when it creates or updates the import index.
lake exe mk_all --lib LongTails || lake exe mk_all --lib LongTails --check
lake exe mk_all --lib LongTailsOnline || lake exe mk_all --lib LongTailsOnline --check
exec lake build "$@"
