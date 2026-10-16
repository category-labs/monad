# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import json
import os
import pathlib
import re
import shutil
import string
import subprocess
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from typing import Any, Callable

DATA = pathlib.Path(__file__).resolve().parents[5] / "test" / "vm" / "data"
MCE = "cmd/vm/mce/mce"
MICRO = "test/vm/micro_benchmarks/vm-micro-benchmarks"
CORE = (
    r"^micro/[^/]+/(BASIC_UNA_MATH|BASIC_BIN_MATH|BASIC_TERN_MATH|SHIFT|BYTE/SIGNEXTEND|EXP|LOAD|DUP2; MSTORE; MLOAD"
    r"|PUSH 23; SIGNEXTEND|PUSH 1; XOR; PUSH 23; SIGNEXTEND|CREATE|CALL|store forwarding stall), "
)
COMPILE_OPTIONS = ["--toggle-collect=*native::compile_basic_blocks<*"]
MICRO_OPTIONS = [
    "--toggle-collect=*VM::execute_native_entrypoint_raw*",
    "--toggle-collect=*VM::execute_intercode_raw*",
    "--dump-before=BlockchainTestVM::execute_compiler*",
    "--dump-before=BlockchainTestVM::execute_interpreter*",
]

Report = dict[str, Any]
Case = tuple[str, str, str]


def tool(name: str) -> str:
    path = shutil.which(name)
    if path is None:
        raise RuntimeError(f"{name} not found")
    return path


def callgrind(tmp: pathlib.Path, out: str, options: list[str], program: list[str]) -> None:
    cmd = [tool("setarch"), "-R", tool("valgrind"), "-q", "--tool=callgrind", "--collect-atstart=no"]
    cmd += ["--compress-strings=no", "--compress-pos=no", *options, f"--callgrind-out-file={out}", *program]
    subprocess.run(cmd, cwd=tmp, env={}, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def profile(path: pathlib.Path) -> Report:
    functions: Counter[str] = Counter()
    total = 0
    skip = False
    for line in path.read_text().splitlines():
        if line.startswith("fn="):
            function = "JIT code" if line.startswith("fn=0x") else line[3:]
        elif line.startswith("calls="):
            skip = True
        elif line[:1].isdigit():
            if not skip:
                functions[function] += int(line.split()[1])
            skip = False
        elif line.startswith("summary:"):
            total = int(line.split()[1])
    return {"total": total, "functions": dict(sorted(functions.items()))}


def compile_case(tmp: pathlib.Path, i: int) -> Report | None:
    callgrind(tmp, f"{i}.out", COMPILE_OPTIONS, ["./mce", "--rev", "prague", f"{i}.hex"])
    result = profile(tmp / f"{i}.out")
    return result if result["total"] else None


def micro_case(binary: pathlib.Path, case: Case) -> Report | None:
    impl, title, seq = case
    with tempfile.TemporaryDirectory(dir="/tmp") as tmp_dir:
        tmp = pathlib.Path(tmp_dir)
        shutil.copy(binary, tmp / "micro")
        filters = ["--impl-filter", f"^{impl}$", "--title-filter", f"^{re.escape(title)}$"]
        filters += ["--seq-filter", "^" + re.escape(seq).replace("\\\n", "\n") + "$"]
        callgrind(tmp, "cg", MICRO_OPTIONS, ["./micro", *filters])
        parts = sorted(tmp.glob("cg.*"), key=lambda p: int(p.suffix[1:]))
        if not parts:
            return None
        base = profile(parts[-1])["total"]
        subject = profile(tmp / "cg")
    return {"total": subject["total"] - base, "baseline": base, "functions": subject["functions"]}


def parse_results(out: str) -> list[tuple[str, str, str, float]]:
    rows: list[tuple[str, str, str, float]] = []
    name: list[str] = []
    impl = title = seq = ""
    lines = out.splitlines()
    for i, line in enumerate(lines):
        if line in ("interpreter", "compiler") and i + 1 < len(lines):
            impl, title, name = line, lines[i + 1].strip(), []
        elif line.startswith("\tbaseline:"):
            seq, name = "\n".join(name).replace(";", "\n"), []
        elif line.startswith("\tbest:"):
            rows.append((impl, title, seq, float(line.split()[1])))
        elif line == "Results" or line.startswith("\t"):
            name = []
        elif line:
            name.append(line)
    return rows


def list_micro_cases(binary: pathlib.Path) -> list[Case]:
    def run(group: str) -> str:
        cmd = [str(binary), "--impl-filter", "^interpreter$", "--title-filter", f"^{group}"]
        return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout

    cases = []
    with ThreadPoolExecutor(26) as pool:
        for out in pool.map(run, string.ascii_uppercase):
            for _, title, seq, _ in parse_results(out):
                cases += [(impl, title, seq) for impl in ("interpreter", "compiler")]
    return sorted(set(cases))


def micro_name(case: Case) -> str:
    return f"micro/{case[0]}/{case[1]}/{case[2].strip().replace(chr(10), '; ')}"


def measure_build(build: pathlib.Path, cases_file: pathlib.Path, micro: str) -> Report:
    if not cases_file.exists():
        cases_file.write_text(json.dumps(list_micro_cases(build / MICRO)))
    cases: list[Case] = [(c[0], c[1], c[2]) for c in json.loads(cases_file.read_text())]
    cases = [c for c in cases if re.search(micro, micro_name(c))]
    with tempfile.TemporaryDirectory(dir="/tmp") as tmp_dir:
        tmp = pathlib.Path(tmp_dir)
        shutil.copy(build / MCE, tmp / "mce")
        contracts = sorted((DATA / "compile_benchmarks").iterdir())
        for i, p in enumerate(contracts):
            (tmp / f"{i}.hex").write_text(p.read_text().strip())
        jobs: list[tuple[str, Callable[[], Report | None]]] = [
            (f"compile/{p.name}", partial(compile_case, tmp, i)) for i, p in enumerate(contracts)
        ]
        jobs += [(micro_name(c), partial(micro_case, build / MICRO, c)) for c in cases]
        with ThreadPoolExecutor(os.cpu_count()) as pool:
            results = list(pool.map(lambda job: job[1](), jobs))
    return {name: r for (name, _), r in zip(jobs, results) if r is not None}
