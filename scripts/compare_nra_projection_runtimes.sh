#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C
export LANG=C

usage() {
  cat <<'EOF'
Usage: scripts/compare_nra_projection_runtimes.sh [options]

Compare regular Yices projection against wide projection on a TSV list of
benchmarks. The input TSV must have:
  file<TAB>avg_cubes_per_call<TAB>max_cubes_per_call<TAB>wide_call_count

Options:
  --instances FILE    Input TSV (required)
  --out-dir DIR       Output directory (default: experiments/nra-wide-runtime/<timestamp>)
  --timeout SECONDS   Per run timeout; 0 disables timeout (default: 5)
  --main PATH         yicesQS executable (default: ./main.exe)
  --no-build          Do not run make build before the experiment
  -h, --help          Show this help
EOF
}

INSTANCES=""
OUT_DIR=""
TIMEOUT_SECS=5
MAIN_EXE="./main.exe"
BUILD=1

while [ $# -gt 0 ]; do
  case "$1" in
    --instances)
      INSTANCES="$2"
      shift 2
      ;;
    --out-dir)
      OUT_DIR="$2"
      shift 2
      ;;
    --timeout)
      TIMEOUT_SECS="$2"
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

if [ -z "$INSTANCES" ] || [ ! -f "$INSTANCES" ]; then
  echo "--instances is required and must name an existing file" >&2
  exit 2
fi

if ! [[ "$TIMEOUT_SECS" =~ ^[0-9]+$ ]]; then
  echo "--timeout must be a non-negative integer number of seconds" >&2
  exit 2
fi

if [ -z "$OUT_DIR" ]; then
  OUT_DIR="experiments/nra-wide-runtime/$(date +%Y%m%d-%H%M%S)"
fi

mkdir -p "$OUT_DIR/logs"

if [ "$BUILD" = "1" ]; then
  make build
fi

if [ ! -x "$MAIN_EXE" ]; then
  echo "Executable not found or not executable: $MAIN_EXE" >&2
  exit 2
fi

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

now_s() {
  perl -MTime::HiRes=time -e 'printf "%.6f\n", time'
}

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

run_tsv="$OUT_DIR/runs.tsv"
table_tsv="$OUT_DIR/comparison.tsv"

printf 'file\tavg_cubes_per_call\tmax_cubes_per_call\twide_call_count\tmode\texit_code\ttimed_out\telapsed_s\tresult\tstat_lines\tstdout_log\tstderr_log\n' > "$run_tsv"

instance_count="$(wc -l < "$INSTANCES" | tr -d ' ')"
total_runs=$((instance_count * 2))
run_index=0

while IFS=$'\t' read -r file avg_cubes max_cubes wide_call_count; do
  [ -n "$file" ] || continue
  for mode in regular wide0; do
    run_index=$((run_index + 1))
    mode_dir="$OUT_DIR/logs/$mode"
    mkdir -p "$mode_dir"
    stdout_log="$mode_dir/$run_index.out"
    stderr_log="$mode_dir/$run_index.err"
    timeout_marker="$mode_dir/$run_index.timeout"
    rm -f "$timeout_marker"

    printf '[%d/%d] mode=%s avg_cubes=%s %s\n' "$run_index" "$total_runs" "$mode" "$avg_cubes" "$file"

    start="$(now_s)"
    if [ "$mode" = "wide0" ]; then
      YICES_WIDE_PROJECTION_STATS=1 "$MAIN_EXE" -wide-projection 0 "$file" > "$stdout_log" 2> "$stderr_log" &
    else
      YICES_WIDE_PROJECTION_STATS=1 "$MAIN_EXE" "$file" > "$stdout_log" 2> "$stderr_log" &
    fi
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

    end="$(now_s)"
    elapsed="$(awk -v s="$start" -v e="$end" 'BEGIN { printf "%.6f", e - s }')"
    timed_out=0
    if [ -f "$timeout_marker" ]; then
      timed_out=1
      exit_code=124
      rm -f "$timeout_marker"
    fi

    result="$(awk 'NF { last=$0 } END { print last }' "$stdout_log")"
    stat_lines="$(grep -c '^\[yices-wide-projection\]' "$stderr_log" 2>/dev/null || true)"

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$file" "$avg_cubes" "$max_cubes" "$wide_call_count" "$mode" \
      "$exit_code" "$timed_out" "$elapsed" "$result" "$stat_lines" \
      "$stdout_log" "$stderr_log" >> "$run_tsv"
  done
done < "$INSTANCES"

{
  printf 'file\tavg_cubes_per_call\tmax_cubes_per_call\twide_call_count\tregular_s\twide0_s\tdelta_s\tpct_change\tspeedup\tregular_timeout\twide0_timeout\tregular_result\twide0_result\n'
  awk -F '\t' '
  NR == 1 { next }
  {
    file = $1
    avg[file] = $2
    max[file] = $3
    calls[file] = $4
    result[file, $5] = $9
    timeout[file, $5] = $7
    elapsed[file, $5] = $8
    seen[file] = 1
  }
  END {
    for (file in seen) {
      r = elapsed[file, "regular"] + 0
      w = elapsed[file, "wide0"] + 0
      delta = r - w
      if (r > 0) {
        pct = 100.0 * (w - r) / r
        speedup = r / w
      } else {
        pct = 0
        speedup = 0
      }
      printf "%s\t%s\t%s\t%s\t%.6f\t%.6f\t%.6f\t%.2f\t%.3f\t%s\t%s\t%s\t%s\n", \
        file, avg[file], max[file], calls[file], r, w, delta, pct, speedup, \
        timeout[file, "regular"], timeout[file, "wide0"], \
        result[file, "regular"], result[file, "wide0"]
    }
  }
  ' "$run_tsv" | sort -t $'\t' -k2,2nr -k1,1
} > "$table_tsv"

echo "Done"
echo "Runs: $run_tsv"
echo "Comparison: $table_tsv"
