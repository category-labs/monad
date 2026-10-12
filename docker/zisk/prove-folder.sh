#!/usr/bin/env bash
set -euo pipefail
usage() {
    echo 'Usage: prove-folder.sh [--cpu] INPUT_DIRECTORY [RUN_DIRECTORY]'
    echo 'Inputs must be framed ZiskStdin files named BLOCK_NUMBER.bin.'
    echo 'Optional BLOCK_NUMBER.hash files hold expected Ethereum block hashes.'
    echo 'Default run directory: /workspace/runs/<timestamp>. Logs and proofs are retained.'
}
mode=gpu
if [[ ${1:-} == --help || ${1:-} == -h ]]; then usage; exit 0; fi
if [[ ${1:-} == --cpu ]]; then mode=cpu; shift; fi
[[ $# -ge 1 && $# -le 2 ]] || { usage >&2; exit 2; }
inputs=$(realpath "$1")
run_dir=${2:-/workspace/runs/$(date -u +%Y%m%dT%H%M%SZ)}
[[ -d "$inputs" ]] || { echo "Missing input directory: $inputs" >&2; exit 1; }
shopt -s nullglob
files=("$inputs"/*.bin)
(( ${#files[@]} > 0 )) || { echo 'No .bin inputs found' >&2; exit 1; }
for file in "${files[@]}"; do
    [[ $(basename "$file") =~ ^(0|[1-9][0-9]*)\.bin$ ]] || { echo "Expected BLOCK_NUMBER.bin: $file" >&2; exit 1; }
    witness.py validate "$file"
done
# The ASM emulator shares ROM, RAM and input buffers through /dev/shm.
# Docker's default 64 MiB causes SIGBUS even during guest setup.
shm_available=$(df -B1 --output=avail /dev/shm | tail -n 1)
if (( shm_available < 1024 * 1024 * 1024 )); then
    echo 'At least 1 GiB of free /dev/shm is required; provision 8 GiB or more (Docker: --shm-size=8g).' >&2
    exit 1
fi
if [[ $mode == gpu ]]; then nvidia-smi; fi
[[ ! -e "$run_dir" ]] || { echo "Run directory already exists: $run_dir" >&2; exit 1; }
mkdir -p "$run_dir" /workspace
run_dir=$(realpath "$run_dir")
exec 9>/workspace/.cluster.lock
flock -n 9 || { echo 'Another cluster launcher is running' >&2; exit 1; }
for port in 7000 50051 9090; do
    if ss -H -ltn "sport = :$port" | grep -q .; then
        echo "Port $port is already in use" >&2; exit 1
    fi
done
# Check optional expected hashes before spending time on proving.
for file in "${files[@]}"; do
    if [[ -f ${file%.bin}.hash ]]; then
        witness.py check "$file" "$(tr -d '[:space:]' < "${file%.bin}.hash")"
    fi
done
key=${PROVING_KEY:-${KEY_ROOT:-/workspace/keys}/provingKey}
if [[ -z ${PROVING_KEY:-} ]]; then setup-key.sh; fi
[[ -f "$key/zisk/vadcop_final/vadcop_final.verkey.json" ]] || { echo "Incomplete proving key: $key" >&2; exit 1; }
worker="/opt/zisk/bin/zisk-worker-$mode"
worker_args=(--coordinator-url http://127.0.0.1:50051 --proving-key "$key" --unlock-mapped-memory)
if [[ $mode == gpu ]]; then worker_args+=(--gpu); fi
pids=()
cleanup() {
    trap '' INT TERM HUP
    for pid in "${pids[@]}"; do kill -TERM -- "-$pid" 2>/dev/null || true; done
    sleep 2
    for pid in "${pids[@]}"; do kill -KILL -- "-$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; done
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM HUP
# Independent process groups let cleanup stop emulator/compiler children too.
setsid zisk-coordinator --api-port 7000 --cluster-port 50051 --metrics-port 9090 >"$run_dir/coordinator.log" 2>&1 &
coordinator=$!; pids+=("$coordinator")
metrics() { curl -fsS --max-time 2 http://127.0.0.1:9090/metrics 2>/dev/null; }
for ((i=0; i<60; i++)); do
    kill -0 "$coordinator" 2>/dev/null || { echo "Coordinator failed: $run_dir/coordinator.log" >&2; exit 1; }
    if metrics >/dev/null; then break; fi
    sleep 1
done
metrics >/dev/null || { echo 'Coordinator readiness timed out' >&2; exit 1; }
setsid "$worker" "${worker_args[@]}" >"$run_dir/worker.log" 2>&1 &
worker_pid=$!; pids+=("$worker_pid")
echo "Waiting for worker setup; logs: $run_dir"
ready=0
for ((i=0; i<${WORKER_TIMEOUT:-1800}; i++)); do
    kill -0 "$worker_pid" 2>/dev/null && kill -0 "$coordinator" 2>/dev/null || { echo 'Cluster process failed; see logs' >&2; exit 1; }
    if metrics | awk '$1 == "coordinator_workers_connected" && $2 >= 1 { ready=1 } END { exit !ready }'; then ready=1; break; fi
    sleep 1
done
(( ready == 1 )) || { echo 'Worker readiness timed out' >&2; exit 1; }
mkdir -p "$run_dir/spool" "$run_dir/proofs"
cp /opt/monad/versions.json "$run_dir/versions.json"
setsid ethproofs-client --client monad --guest /opt/monad/monad-zkvm-zisk \
    --coordinator-url http://127.0.0.1:7000 --input.mode folder --folder.path "$inputs" \
    --input.folder "$run_dir/spool" --proof.save --proof.folder "$run_dir/proofs" \
    --proof.csv "$run_dir/proofs.csv" --prove-timeout "${PROVE_TIMEOUT:-14400}" --exit-on-error \
    >"$run_dir/ethproofs-client.log" 2>&1 &
client=$!; pids+=("$client")
while kill -0 "$client" 2>/dev/null; do
    kill -0 "$worker_pid" 2>/dev/null && kill -0 "$coordinator" 2>/dev/null || { echo 'Cluster process failed; see logs' >&2; exit 1; }
    sleep 1
done
wait "$client"
for file in "${files[@]}"; do
    block=$(basename "$file" .bin)
    cargo-zisk verify --proof "$run_dir/proofs/${block}_proof.zisk" \
        --setup-vk "$key/zisk/vadcop_final/vadcop_final.verkey.json"
    if [[ -f ${file%.bin}.hash ]]; then
        witness.py publics "$run_dir/proofs/${block}_publics.bin" "$(tr -d '[:space:]' < "${file%.bin}.hash")"
    fi
done
echo "Verified ${#files[@]} proof(s). Results: $run_dir"
