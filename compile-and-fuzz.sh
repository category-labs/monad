#! /bin/sh
set -e

./scripts/vm/tmux-fuzzer.sh kill
cmake --build build -j$(nproc)
./scripts/vm/tmux-fuzzer.sh start

# Every second, for 5 seconds, call ./scripts/vm/tmux-fuzzer.sh status
for i in $(seq 1 5); do
  sleep 1
  if ./scripts/vm/tmux-fuzzer.sh status | grep -q "TERMINATED"; then
    echo "Fuzzer has found a bug!"
    ./scripts/vm/tmux-fuzzer.sh status
    exit 1
  fi
done

echo "All good after 5 seconds of fuzzing, probably good to go!"
