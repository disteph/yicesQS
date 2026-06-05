#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/run_nra_wide_stats.sh [options]

Run yicesQS on NRA SMT-LIB benchmarks with Yices wide-projection stats enabled.

Options:
  --bench-dir DIR     Benchmark root (default: ../SMTLib/NRA)
  --file-list FILE    Newline-separated benchmark list; overrides --bench-dir scan
  --out-dir DIR       Output directory (default: experiments/nra-wide-stats/<timestamp>)
  --budgets LIST      Space-separated wide projection budgets (default: "1 10 0")
  --timeout SECONDS   Per file/budget timeout; 0 disables timeout (default: 5)
  --max-files N       Limit to first N benchmark files after sorting (default: all)
  --main PATH         yicesQS executable (default: ./main.exe)
  --no-build          Do not run make build before the experiment
  --dry-run           Write the file list and exit without running benchmarks
  -h, --help          Show this help

Outputs:
  files.txt                 Benchmarks selected for the run
  runs.tsv                  One row per file/budget invocation
  projection_calls.tsv      One row per [yices-wide-projection] stats line
  summary.tsv               Aggregate counts by budget
  logs/<budget>/<n>.out     Raw stdout for each invocation
  logs/<budget>/<n>.err     Raw stderr for each invocation

Environment overrides:
  BENCH_DIR, FILE_LIST, OUT_DIR, BUDGETS, TIMEOUT_SECS, MAX_FILES, MAIN_EXE, BUILD
EOF
}

BENCH_DIR="${BENCH_DIR:-../SMTLib/NRA}"
FILE_LIST="${FILE_LIST:-}"
BUDGETS="${BUDGETS:-1 10 0}"
TIMEOUT_SECS="${TIMEOUT_SECS:-5}"
MAX_FILES="${MAX_FILES:-0}"
MAIN_EXE="${MAIN_EXE:-./main.exe}"
BUILD="${BUILD:-1}"
DRY_RUN=0
OUT_DIR="${OUT_DIR:-}"

while [ $# -gt 0 ]; do
  case "$1" in
    --bench-dir)
      BENCH_DIR="$2"
      shift 2
      ;;
    --file-list)
      FILE_LIST="$2"
      shift 2
      ;;
    --out-dir)
      OUT_DIR="$2"
      shift 2
      ;;
    --budgets)
      BUDGETS="$2"
      shift 2
      ;;
    --timeout)
      TIMEOUT_SECS="$2"
      shift 2
      ;;
    --max-files)
      MAX_FILES="$2"
      shift 2
      ;;
    --main)
      MAIN_EXE="$2"
      shift 2
      ;;
    --no-build)
      BUILD=0
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [ -z "$OUT_DIR" ]; then
  OUT_DIR="experiments/nra-wide-stats/$(date +%Y%m%d-%H%M%S)"
fi

if [ -n "$FILE_LIST" ] && [ ! -f "$FILE_LIST" ]; then
  echo "File list not found: $FILE_LIST" >&2
  exit 2
fi

if [ -z "$FILE_LIST" ] && [ ! -d "$BENCH_DIR" ]; then
  echo "Benchmark directory not found: $BENCH_DIR" >&2
  exit 2
fi

if ! [[ "$MAX_FILES" =~ ^[0-9]+$ ]]; then
  echo "--max-files must be a non-negative integer" >&2
  exit 2
fi

if ! [[ "$TIMEOUT_SECS" =~ ^[0-9]+$ ]]; then
  echo "--timeout must be a non-negative integer number of seconds" >&2
  exit 2
fi

mkdir -p "$OUT_DIR/logs"

if [ "$BUILD" = "1" ]; then
  make build
fi

if [ ! -x "$MAIN_EXE" ]; then
  echo "Executable not found or not executable: $MAIN_EXE" >&2
  exit 2
fi

all_files="$OUT_DIR/files.all"
files="$OUT_DIR/files.txt"
if [ -n "$FILE_LIST" ]; then
  grep -v '^[[:space:]]*$' "$FILE_LIST" > "$all_files"
else
  find "$BENCH_DIR" -follow -name '*.smt2' | sort > "$all_files"
fi
if [ "$MAX_FILES" -gt 0 ]; then
  head -n "$MAX_FILES" "$all_files" > "$files"
else
  cp "$all_files" "$files"
fi
rm -f "$all_files"

file_count="$(wc -l < "$files" | tr -d ' ')"
echo "Selected $file_count NRA benchmark files"
echo "Output directory: $OUT_DIR"
echo "Budgets: $BUDGETS"
echo "Timeout: ${TIMEOUT_SECS}s"

if [ "$DRY_RUN" = "1" ]; then
  echo "Dry run complete"
  exit 0
fi

runs_tsv="$OUT_DIR/runs.tsv"
calls_tsv="$OUT_DIR/projection_calls.tsv"
summary_tsv="$OUT_DIR/summary.tsv"

printf 'file\tbudget\trun_index\texit_code\ttimed_out\telapsed_s\tresult\tstat_lines\tstdout_log\tstderr_log\n' > "$runs_tsv"
printf 'file\tbudget\trun_index\tcall_index\tstatus\tinput_terms\telim_vars\tatoms\tattempted_cubes\tprojected_cubes\tskipped_cubes\tsat_exhausted\tfallback\tresult_terms\tcode\traw\n' > "$calls_tsv"

opam_libdir="$(opam var lib 2>/dev/null || true)"
opam_stublibs="$(opam var stublibs 2>/dev/null || true)"
vendor_lib="../yices2_ocaml_bindings/_build/default/vendor_install/lib"
runtime_paths="$vendor_lib"
if [ -n "$opam_libdir" ]; then
  runtime_paths="$runtime_paths:$opam_libdir"
fi
if [ -n "$opam_stublibs" ]; then
  runtime_paths="$runtime_paths:$opam_stublibs"
fi
runtime_paths="$runtime_paths:/usr/local/lib"

export LD_LIBRARY_PATH="$runtime_paths${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export DYLD_LIBRARY_PATH="$runtime_paths${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

current_pid=""
watchdog_pid=""

stop_current_run() {
  if [ -n "$watchdog_pid" ]; then
    kill "$watchdog_pid" 2>/dev/null || true
    wait "$watchdog_pid" 2>/dev/null || true
    watchdog_pid=""
  fi

  if [ -n "$current_pid" ]; then
    kill -INT "$current_pid" 2>/dev/null || true
    sleep 1
    kill -TERM "$current_pid" 2>/dev/null || true
    sleep 1
    kill -KILL "$current_pid" 2>/dev/null || true
    wait "$current_pid" 2>/dev/null || true
    current_pid=""
  fi
}

on_interrupt() {
  echo "Interrupted; stopping current benchmark run" >&2
  stop_current_run
  exit 130
}

trap on_interrupt INT TERM

run_index=0
total_runs=$(( file_count * $(printf '%s\n' $BUDGETS | wc -l | tr -d ' ') ))

while IFS= read -r file; do
  [ -n "$file" ] || continue
  for budget in $BUDGETS; do
    run_index=$((run_index + 1))
    budget_log_dir="$OUT_DIR/logs/budget-$budget"
    mkdir -p "$budget_log_dir"
    stdout_log="$budget_log_dir/$run_index.out"
    stderr_log="$budget_log_dir/$run_index.err"
    timeout_marker="$budget_log_dir/$run_index.timeout"
    rm -f "$timeout_marker"

    printf '[%d/%d] budget=%s %s\n' "$run_index" "$total_runs" "$budget" "$file"

    start_s="$(date +%s)"
    YICES_WIDE_PROJECTION_STATS=1 "$MAIN_EXE" -wide-projection "$budget" "$file" \
      > "$stdout_log" 2> "$stderr_log" &
    current_pid=$!

    watchdog_pid=""
    if [ "$TIMEOUT_SECS" -gt 0 ]; then
      (
        sleep "$TIMEOUT_SECS"
        if kill -0 "$current_pid" 2>/dev/null; then
          : > "$timeout_marker"
          kill -TERM "$current_pid" 2>/dev/null || true
          sleep 1
          kill -KILL "$current_pid" 2>/dev/null || true
        fi
      ) &
      watchdog_pid=$!
    fi

    set +e
    wait "$current_pid"
    exit_code=$?
    set -e

    if [ -n "$watchdog_pid" ]; then
      kill "$watchdog_pid" 2>/dev/null || true
      wait "$watchdog_pid" 2>/dev/null || true
      watchdog_pid=""
    fi
    current_pid=""

    end_s="$(date +%s)"
    elapsed_s=$((end_s - start_s))

    timed_out=0
    if [ -f "$timeout_marker" ]; then
      timed_out=1
      exit_code=124
      rm -f "$timeout_marker"
    fi

    result="$(awk 'NF { last=$0 } END { print last }' "$stdout_log")"
    stat_lines="$(grep -c '^\[yices-wide-projection\]' "$stderr_log" 2>/dev/null || true)"

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$file" "$budget" "$run_index" "$exit_code" "$timed_out" "$elapsed_s" \
      "$result" "$stat_lines" "$stdout_log" "$stderr_log" >> "$runs_tsv"

    awk -v file="$file" -v budget="$budget" -v run_index="$run_index" '
      BEGIN { call_index = 0 }
      /^\[yices-wide-projection\]/ {
        call_index++
        raw = $0
        status = input_terms = elim_vars = atoms = attempted_cubes = ""
        projected_cubes = skipped_cubes = sat_exhausted = fallback = ""
        result_terms = code = ""
        for (i = 2; i <= NF; i++) {
          split($i, kv, "=")
          if (kv[1] == "status") status = kv[2]
          else if (kv[1] == "input_terms") input_terms = kv[2]
          else if (kv[1] == "elim_vars") elim_vars = kv[2]
          else if (kv[1] == "atoms") atoms = kv[2]
          else if (kv[1] == "attempted_cubes") attempted_cubes = kv[2]
          else if (kv[1] == "projected_cubes") projected_cubes = kv[2]
          else if (kv[1] == "skipped_cubes") skipped_cubes = kv[2]
          else if (kv[1] == "sat_exhausted") sat_exhausted = kv[2]
          else if (kv[1] == "fallback") fallback = kv[2]
          else if (kv[1] == "result_terms") result_terms = kv[2]
          else if (kv[1] == "code") code = kv[2]
        }
        gsub(/\t/, " ", raw)
        printf "%s\t%s\t%s\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", \
          file, budget, run_index, call_index, status, input_terms, elim_vars, \
          atoms, attempted_cubes, projected_cubes, skipped_cubes, sat_exhausted, \
          fallback, result_terms, code, raw
      }
    ' "$stderr_log" >> "$calls_tsv"
  done
done < "$files"

awk '
  BEGIN {
    FS = "\t"; OFS = "\t"
    print "budget", "runs", "sat", "unsat", "unknown", "timeouts", "errors", \
      "runs_with_stats", "projection_calls", "attempted_cubes", "projected_cubes", \
      "skipped_cubes", "fallback_calls"
  }
  FNR == 1 && NR == FNR { next }
  NR == FNR {
    budget = $2
    runs[budget]++
    if ($5 == "1") timeouts[budget]++
    else if ($4 != "0") errors[budget]++
    if ($7 == "sat") sat[budget]++
    else if ($7 == "unsat") unsat[budget]++
    else if ($7 != "") unknown[budget]++
    if ($8 + 0 > 0) runs_with_stats[budget]++
    seen[budget] = 1
    next
  }
  FNR == 1 { next }
  {
    budget = $2
    calls[budget]++
    attempted[budget] += $9
    projected[budget] += $10
    skipped[budget] += $11
    fallback[budget] += $13
    seen[budget] = 1
  }
  END {
    for (budget in seen) {
      print budget, runs[budget] + 0, sat[budget] + 0, unsat[budget] + 0, \
        unknown[budget] + 0, timeouts[budget] + 0, errors[budget] + 0, \
        runs_with_stats[budget] + 0, calls[budget] + 0, attempted[budget] + 0, \
        projected[budget] + 0, skipped[budget] + 0, fallback[budget] + 0
    }
  }
' "$runs_tsv" "$calls_tsv" > "$summary_tsv"

echo "Done"
echo "Runs: $runs_tsv"
echo "Projection calls: $calls_tsv"
echo "Summary: $summary_tsv"
