#!/usr/bin/env bash

set -u

freqhorn_bin="${FREQHORN_BIN:-build/tools/deep/freqhorn}"
timeout_seconds="${BV_BENCH_TIMEOUT:-30}"
timestamp="$(date +%Y%m%d-%H%M%S)"
out_dir="${BV_BENCH_OUT_DIR:-/tmp/aeval-bv-benchmarks/${timestamp}-$$}"

benchmarks=(
  "bench_horn_bv/bv_small_01.smt2|solved-smoke|solved"
  "bench_horn_bv/bv_simp_01.smt2|solved-smoke|solved"
  "bench_horn_bv/bv_cmp_01.smt2|comparison-hard|unsolved-or-timeout"
  "bench_horn_bv/bv_add_01.smt2|add-hard|unsolved-or-timeout"
  "bench_horn_bv/bv_add_02.smt2|add-hard|unsolved-or-timeout"
  "bench_horn_bv/bv_neg_01.smt2|overflow-diagnostic|unsolved"
  "bench_horn_bv/bv_mul_01.smt2|template-win|unsolved by default, solved with --bv-bitmask-templates=basic"
  "bench_horn_bv/bv_mod_01.smt2|arithmetic-hard|unsolved"
)

if [[ ! -x "${freqhorn_bin}" ]]; then
  echo "error: freqhorn binary not found or not executable: ${freqhorn_bin}" >&2
  echo "hint: build it with 'cmake --build build --target freqhorn -j2'" >&2
  exit 2
fi

mkdir -p "${out_dir}"

base_args=(--v5 --skip-sampling)
if [[ "${BV_BENCH_DEBUG_GUARDS:-}" == "1" ]]; then
  base_args+=(--debug 5)
fi

printf "benchmark\tgroup\texpectation\tstatus\texit_code\tseconds\tguard_hints\tlog\n"

for entry in "${benchmarks[@]}"; do
  IFS='|' read -r benchmark group expectation <<< "${entry}"
  log_name="$(basename "${benchmark}" .smt2).log"
  log_path="${out_dir}/${log_name}"
  start_time="$(date +%s)"

  timeout "${timeout_seconds}s" "${freqhorn_bin}" "${base_args[@]}" "$@" "${benchmark}" >"${log_path}" 2>&1
  exit_code="$?"

  end_time="$(date +%s)"
  seconds="$((end_time - start_time))"

  if [[ "${exit_code}" == "124" ]]; then
    status="timeout"
  elif [[ "${exit_code}" == "0" ]] && grep -Eq "Success after|Success with BV bitmask templates" "${log_path}"; then
    status="solved"
  else
    status="unsolved"
  fi

  if grep -q "No-overflow guard:" "${log_path}"; then
    guard_hints="yes"
  else
    guard_hints="no"
  fi

  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "${benchmark}" "${group}" "${expectation}" "${status}" \
    "${exit_code}" "${seconds}" "${guard_hints}" "${log_path}"
done
