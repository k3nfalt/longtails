#!/usr/bin/env bash
set -euo pipefail

# Run from, or pass, the existing LongTails checkout. No project source is changed.
repo_arg=${1:-.}
repo=$(cd "$repo_arg" && pwd)
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source_file="$repo/LongTails/Proofs/ProximalEf21Geometry.lean"
candidate_file="$script_dir/replacement/LongTails/Proofs/ProximalEf21Geometry.lean"
limit=${EF21_LIMIT_SECONDS:-180}
heartbeats=${EF21_HEARTBEATS:-200000}
memory=${EF21_MEMORY_MB:-2048}

for value in "$limit" "$heartbeats" "$memory"; do
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    printf 'Limits must be positive integers.\n' >&2
    exit 2
  fi
done
for tool in lake timeout awk tee; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Required command not found: %s\n' "$tool" >&2
    exit 2
  fi
done
if [[ ! -f "$source_file" || ! -f "$repo/lean-toolchain" ]]; then
  printf 'Expected a LongTails checkout containing %s and lean-toolchain.\n' "$source_file" >&2
  exit 2
fi

stamp=$(date -u +%Y%m%dT%H%M%SZ)
run_dir=$(mktemp -d "$repo/Ef21Diagnostic_${stamp}_XXXXXX")
summary="$run_dir/Summary.tsv"
printf 'phase\texit_status\twall_seconds\n' > "$summary"
cp -- "$source_file" "$run_dir/OriginalGeometrySource.lean"
if [[ -f "$candidate_file" ]]; then
  cp -- "$candidate_file" "$run_dir/CandidateGeometrySource.lean"
fi

{
  printf 'UTC: '; date -u
  printf 'Repository: %s\nLimits per run: %s seconds, %s heartbeats per command, %s MB Lean memory\n' \
    "$repo" "$limit" "$heartbeats" "$memory"
  printf '\nPinned toolchain:\n'; cat "$repo/lean-toolchain"
  printf '\nGit revision and EF21 source status:\n'
  git -C "$repo" rev-parse HEAD 2>&1 || true
  git -C "$repo" status --short -- LongTails/Proofs/ProximalEf21Geometry.lean 2>&1 || true
  printf '\nCPU count:\n'; getconf _NPROCESSORS_ONLN 2>&1 || true
  printf '\nMemory:\n'; free -m 2>&1 || true
  printf '\nDisk:\n'; df -h "$repo" 2>&1 || true
  printf '\nCgroup memory limits:\n'
  for p in /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.current /sys/fs/cgroup/memory.events; do
    if [[ -f "$p" ]]; then printf '%s\n' "$p"; cat "$p"; fi
  done
  printf '\nAlready-running Lean/Lake-related processes (stop the old build first):\n'
  ps -eo pid,ppid,etime,pcpu,pmem,rss,stat,args | \
    grep -E '(lean|lake|run_comparator|build\.sh)' | grep -v 'grep -E' || true
  printf '\nLake version:\n'
  (cd "$repo" && timeout --kill-after=5s 20s lake --version) 2>&1 || true
  printf '\nLean version:\n'
  (cd "$repo" && timeout --kill-after=5s 20s lake env lean --version) 2>&1 || true
  printf '\nSource checksums:\n'
  sha256sum "$run_dir/OriginalGeometrySource.lean" "$candidate_file" 2>&1 || true
} > "$run_dir/Environment.txt"

# This instrumenter targets the supplied Geometry module's simple top-level layout.
# Checkpoints are printed to stderr and are not used in any proof.
instrument() {
  local input=$1 output=$2 label=$3
  local last_import
  last_import=$(awk '/^import[[:space:]]/{n=NR} END{print n+0}' "$input")
  if [[ "$last_import" == 0 ]]; then
    printf 'No imports found in %s\n' "$input" >&2
    return 2
  fi
  awk -v last="$last_import" -v hb="$heartbeats" -v label="$label" '
    /^set_option (maxHeartbeats|Elab.async|profiler|profiler.threshold|diagnostics) / {next}
    /^(noncomputable[[:space:]]+)?(lemma|theorem|def)[[:space:]]/ {
      name=$2
      if ($1 == "noncomputable") name=$3
      printf "#eval IO.eprintln \"EF21 BEGIN %s source-line=%d declaration=%s\"\n", label, NR, name
    }
    {print}
    NR == last {
      print "set_option Elab.async false"
      printf "set_option maxHeartbeats %s\n", hb
      print "set_option profiler true"
      print "set_option profiler.threshold 100"
      print "set_option diagnostics true"
      printf "#eval IO.eprintln \"EF21 IMPORTS_READY %s\"\n", label
    }
    END {printf "\n#eval IO.eprintln \"EF21 END_OF_FILE %s\"\n", label}
  ' "$input" > "$output"
}

awk '/^import[[:space:]]/{print}' "$source_file" > "$run_dir/ImportOnly.lean"
printf '\n#eval IO.eprintln "EF21 IMPORTS_ONLY_FINISHED"\n' >> "$run_dir/ImportOnly.lean"
instrument "$source_file" "$run_dir/OriginalGeometryTrace.lean" original
if [[ -f "$candidate_file" ]]; then
  instrument "$candidate_file" "$run_dir/CandidateGeometryTrace.lean" candidate
fi

printf '\nDiagnostic directory: %s\n' "$run_dir"
printf 'Each check has a %s-second wall-clock cutoff, plus up to 10 seconds for termination.\n' "$limit"
printf 'These are diagnostic cutoffs, NOT estimates of theorem-verification time.\n'
printf 'The original sources, toolchain, manifest, and cache will not be modified.\n\n'

last_status=0
run_check() {
  local label=$1 input=$2
  local started elapsed status
  local -a clock=()
  if [[ -x /usr/bin/time ]]; then clock=(/usr/bin/time -v); fi
  printf '\n===== %s =====\n' "$label"
  started=$SECONDS
  set +e
  (
    cd "$repo"
    "${clock[@]}" timeout --signal=TERM --kill-after=10s "${limit}s" \
      env LEAN_NUM_THREADS=1 lake env lean -j1 "-M${memory}" \
        -DElab.async=false "-DmaxHeartbeats=${heartbeats}" "$input"
  ) 2>&1 | tee "$run_dir/${label}.log"
  status=${PIPESTATUS[0]}
  set -e
  elapsed=$((SECONDS - started))
  printf '%s\t%s\t%s\n' "$label" "$status" "$elapsed" >> "$summary"
  printf '\n%s: exit=%s wall=%ss\n' "$label" "$status" "$elapsed"
  if [[ "$status" == 124 || "$status" == 137 ]]; then
    printf 'Stopped by the diagnostic timeout or a kill signal; this is not a successful proof check.\n'
  elif [[ "$status" != 0 ]]; then
    printf 'Check failed. Inspect the FIRST error before later cascading errors.\n'
  fi
  grep -E 'EF21 BEGIN|EF21 IMPORTS_READY|EF21 END_OF_FILE|error:' \
    "$run_dir/${label}.log" | tail -n 12 || true
  last_status=$status
}

run_check imports "$run_dir/ImportOnly.lean"
if [[ "$last_status" == 0 ]]; then
  run_check original "$run_dir/OriginalGeometryTrace.lean"
  if [[ -f "$run_dir/CandidateGeometryTrace.lean" ]]; then
    run_check candidate "$run_dir/CandidateGeometryTrace.lean"
  fi
else
  printf '\nImport-only check failed or timed out. Skipping proof checks; inspect imports.log.\n'
fi

printf '\n===== SUMMARY =====\n'
cat "$summary"
printf '\nExit 0 is required; reaching END_OF_FILE is not enough if errors appeared earlier.\n'
printf 'The candidate is not installed automatically. Do not replace the original unless its check succeeds.\n'
printf 'These checks concern Geometry only, not the complete convergence theorem or Comparator.\n'
printf 'Logs and both checked source snapshots: %s\n' "$run_dir"
archive="${run_dir}.tar.gz"
tar -czf "$archive" -C "$(dirname "$run_dir")" "$(basename "$run_dir")"
printf 'Diagnostic report archive: %s\n' "$archive"
