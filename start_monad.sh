#!/bin/bash

DATE=$(date +%Y%m%d%H%M%S)
LOG="logs/monad.${DATE}.log"

echo "log = ${LOG}"

echo "${@}" >> "${LOG}"

git log | head -20 >> "${LOG}"

rm -f test.db

#dd if=/dev/zero of=/dev/nvme1n1p1 bs=1M count=10

#blkdiscard /dev/nvme1n1p1
#build/libs/db/monad_mpt --storage /dev/nvme1n1p1 --create

build/libs/db/monad_mpt --storage /dev/nvme1n1p1 --truncate --yes

#LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libmimalloc.so.2 \
export LD_PRELOAD=/home/jhunsaker/git/ro/rpmalloc/bin/linux/release/x86-64/librpmallocwrap.so

#  --genesis test/common/genesis/ethereum/mainnet.json \
#  --snapshot /space/jhunsaker/snapshots/12000000 \

#LD_BIND_NOW=1 \
#taskset -c 1-6 \
gdb --args \
build/cmd/monad \
  --snapshot /space/jhunsaker/snapshots/3000000 \
  --chain ethereum_mainnet \
  --block_db "/space/jhunsaker/block_db" \
  --nblocks 10000 \
  --nfibers 128 \
  --nthreads 4 \
  --db /dev/nvme1n1p1 \
  --no-compaction \
  2>&1 | tee -a "${LOG}"

