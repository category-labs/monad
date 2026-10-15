#!/usr/bin/env python3
"""Run the precompile golden vectors in the Airbender VM and decode the report.
usage: ab_pt.py <elf> <vectors.bin>"""
import os, re, struct, subprocess, sys, collections
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "ab_run.py")).read().split("\ndef main():")[0]
ns = {}; exec(src, ns)
W, TC, runner_cmd = ns["W"], ns["TC"], ns["runner_cmd"]
elf, vec = sys.argv[1], sys.argv[2]
only = [int(a, 16) for a in sys.argv[3].split(",")] if len(sys.argv) > 3 else None
out = os.path.splitext(elf)[0]
subprocess.run([f"{TC}-objcopy", "-O", "binary", elf, out + ".bin"], check=True)
subprocess.run([f"{TC}-objcopy", "-O", "binary", "--only-section=.text", elf, out + ".text"], check=True)
data = open(vec, "rb").read()
if only:  # keep the cases of these precompile addresses
    n = struct.unpack("<I", data[4:8])[0]; i = 8; keep = []
    for _ in range(n):
        j = i
        addr, ilen = struct.unpack("<HI", data[i:i+6]); i += 6 + ilen
        olen = struct.unpack("<I", data[i+1:i+5])[0]; i += 5 + olen
        if addr in only: keep.append(data[j:i])
    data = b"PT01" + struct.pack("<I", len(keep)) + b"".join(keep)
payload = data + b"\0" * (-len(data) % 4)
words = [len(data)] + list(struct.unpack(f"<{len(payload)//4}I", payload))
hp = f"{W}/airbender/out/pt_input.hex"
open(hp, "w").write("".join(f"{w:08x}" for w in words))
r = subprocess.run(runner_cmd("run") + [out + ".bin", "--input", hp, "--text-path", out + ".text"], capture_output=True, text=True)
uart = re.findall(r"UART: `([^`]*)`", r.stdout)
cyc = re.search(r"cycles: (\d+)", r.stdout)
rep = bytes.fromhex("".join(u for u in uart if re.fullmatch(r"[0-9a-f]+", u)))
if not rep.startswith(b"PR01"):
    print("no report", uart[-3:], r.stderr[-600:]); sys.exit(1)
total, passed, failed, logged = struct.unpack("<4I", rep[4:20])
hints = re.search(r"hints: (.*)", r.stdout)
print(f"cases {total}: passed {passed}, failed {failed}; cycles {cyc.group(1) if cyc else '?'}"
      + (f"; {hints.group(1)}" if hints else ""))
# per-address failure counts from the logged entries (capped at 32)
cases = []
blob = data; n = struct.unpack("<I", blob[4:8])[0]; i = 8
for _ in range(n):
    addr, ilen = struct.unpack("<HI", blob[i:i+6]); i += 6 + ilen
    kind = blob[i]; olen = struct.unpack("<I", blob[i+1:i+5])[0]; i += 5 + olen
    cases.append((addr, kind))
c = collections.Counter(); per = collections.Counter(a for a, k in cases)
for j in range(logged):
    idx, addr, st = struct.unpack("<IHB", rep[20 + 7*j: 27 + 7*j]); c[addr] += 1
print("logged failures by address (first 32):", {hex(a): v for a, v in c.items()})
print("cases by address:", {hex(a): v for a, v in sorted(per.items())})
