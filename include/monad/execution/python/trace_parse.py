#!/usr/bin/env python3

import argparse
import numpy as np
import os
import pandas as pd
from collections import defaultdict
from enum import IntEnum
from functools import partial
from struct import unpack


class TraceType(IntEnum):
    StartBlock = 0
    EndBlock = 1
    StartTxn = 2
    EndTxn = 3
    StartSenderRecovery = 4
    EndSenderRecovery = 5
    StartExecution = 6
    EndExecution = 7
    StartStall = 8
    EndStall = 9
    StartRetry = 10
    EndRetry = 11
    StartReadAccount = 12
    EndReadAccount = 13
    StartReadStorage = 14
    EndReadStorage = 15
    StartReadCode = 16
    EndReadCode = 17
    StartCommit = 18
    EndCommit = 19


# Quill writes a \n after every log (see first line of
# PatternFormatter::_set_pattern), hence the +1;
read_size = 21 + 1
struct = "=ciQQx"


def summary(f):
    timing = defaultdict(list)
    start = defaultdict(lambda: defaultdict(list))

    for chunk in iter(partial(f.read, read_size), b""):
        type, tid, time, value = unpack(struct, chunk)
        trace_type = TraceType(ord(type))

        if trace_type.name.startswith("Start"):
            start[trace_type.name[5:]][value].append(time)
        else:
            assert trace_type.name.startswith("End")
            key = trace_type.name[3:]
            assert value in start[key]
            assert len(start[key][value]) > 0
            timing[key].append(time - start[key][value].pop())
            if len(start[key][value]) == 0:
                del start[key][value]

    assert all(len(l) == 0 for l in start.values())

    pctls = [0, 1, 25, 50, 75, 99, 100]
    print(
        pd.DataFrame(
            data=[
                np.append(
                    [key, len(val), np.round(np.average(val) / 1000, 2)],
                    np.round(np.percentile(val, pctls) / 1000, 2),
                )
                for key, val in sorted(timing.items())
            ],
            columns=["Event", "n", "avg(us)"] + list(map(lambda x: f"{x}%(us)", pctls)),
        ).to_string(index=False)
    )


def dump(f, number, txn):
    events = defaultdict(tuple)
    started = False

    for chunk in iter(partial(f.read, read_size), b""):
        type, tid, time, value = unpack(struct, chunk)
        trace_type = TraceType(ord(type))
        if trace_type == TraceType.StartBlock and number == value:
            assert started == False
            started = True
        elif trace_type == TraceType.EndBlock and started:
            assert number == value
            break
        elif started and (txn == None or txn == value):
            events[time] = (trace_type, tid, value)

    if not started:
        assert len(events) == 0
        print("Block not found")
    elif len(events) == 0:
        print("Txn events not found")
    else:
        print(
            pd.DataFrame(
                data=[
                    [time, event[1], event[2], event[0].name]
                    for time, event in sorted(events.items())
                ],
                columns=["Time(ns)", "Tid", "Txn", "Event"],
            ).to_string(index=False)
        )


def main():
    parser = argparse.ArgumentParser(prog="trace_parse", description="Trace log parser")
    parser.add_argument(
        "--log", required=True, help="path to log file", type=os.path.abspath
    )
    subparsers = parser.add_subparsers(help="actions")
    dump_parser = subparsers.add_parser(
        "dump",
        help="print trace events",
    )
    dump_parser.add_argument(
        "--block",
        required=True,
        help="block number",
        type=int,
    )
    dump_parser.add_argument(
        "--txn",
        required=False,
        help="txn number within block",
        type=int,
    )
    args = parser.parse_args()
    with open(args.log, "rb") as f:
        if hasattr(args, "block"):
            dump(f, args.block, args.txn)
        else:
            summary(f)


if __name__ == "__main__":
    main()
