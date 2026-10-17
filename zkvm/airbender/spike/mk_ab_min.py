#!/usr/bin/env python3
"""Airbender inputs from minimal witnesses: what the block reads and nothing else, the way
ZKsync OS's oracle hands its guest only the preimages it asks for.

work/minw/min_witness.py drops the 255 ancestor headers past the parent and the EIP-2935 ring
slots the block does not touch (it keeps the slot the system call writes and the slots BLOCKHASH
reads, from work/minw/results.json's "extra"; 26002408 reads many, so it keeps all 256 recent
ones). mk_ab_input.py's builder then lays the witness out as the ABIN=1 input.

usage: PYTHONPATH=work/minw/shim mk_ab_min.py <block>...   -> work/airbender/out/abin_min/rpc_<b>.in
(the shim stands in for pycryptodome's keccak)"""
import json, os, subprocess, sys, tempfile
# MONAD_ZKVM_WORK holds airbender/ (stack/, out/, build-rv32/) and run/w/
# (the witnesses); by default the directory two above this checkout (from
# argv[0]: the scripts that exec this file's helpers sit beside it).
W = os.environ.get("MONAD_ZKVM_WORK") or os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), *[".."] * 5))
MK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mk_ab_input.py")
OUT = os.environ.get("ABIN_MIN_OUT", f"{W}/airbender/out/abin_min")
res = json.load(open(f"{W}/minw/results.json"))


def extra(b):
    if b == "26002408":
        return [k % 8191 for k in range(int(b) - 256, int(b))]
    return res.get(b, {}).get("extra") or []


def main():
    os.makedirs(OUT, exist_ok=True)
    src = open(f"{W}/minw/min_witness.py").read().replace("    os.remove(wit)\n", "")
    with tempfile.TemporaryDirectory() as tmp:
        keep = f"{tmp}/min_witness_keep.py"
        open(keep, "w").write(src)
        ns = {"__name__": "mk", "__file__": MK}
        exec(compile(open(MK).read(), MK, "exec"), ns)
        for b in sys.argv[1:]:
            subprocess.run([sys.executable, keep, tmp, b] + [str(x) for x in extra(b)], check=True,
                           capture_output=True)
            cw, _ = ns["build"](f"{tmp}/rpc_{b}.witness", False)
            fr = len(cw).to_bytes(8, "little") + cw
            open(f"{OUT}/rpc_{b}.in", "wb").write(fr + b"\0" * ((8 - len(fr) % 8) % 8))
            print(b, os.path.getsize(f"{OUT}/rpc_{b}.in"))


if __name__ == "__main__":
    main()
