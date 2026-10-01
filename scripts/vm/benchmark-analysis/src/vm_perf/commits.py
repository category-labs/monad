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

import argparse
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys

from vm_perf.compare import cost
from vm_perf.suites import MCE, MICRO, Report, measure_build, tool

EVMONE = "https://github.com/category-labs/evmone"
VM_PATHS = ["category/vm", "cmd/vm/mce", "test/vm/micro_benchmarks", "third_party/asmjit"]
PLOT = """<!doctype html><meta charset="utf-8"><title>vm-perf history</title>
<script src="https://cdn.plot.ly/plotly-2.35.2.min.js"></script><div id="plot" style="height:95vh"></div>
<script>Plotly.newPlot("plot", TRACES, {yaxis: {title: "Instructions vs first commit (%)"}})</script>
"""


def git(source: pathlib.Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(source), *args], capture_output=True, text=True, check=True).stdout


def prepare(source: pathlib.Path, commit: str, cache: pathlib.Path) -> None:
    for step in (["clean", "-q", "-ffd"], ["checkout", "-q", "--detach", commit], ["clean", "-q", "-ffd"]):
        git(source, *step)
    git(source, "submodule", "sync", "-q", "--recursive")
    git(source, "submodule", "update", "-q", "--init", "--recursive", "--force")
    if not (source / "cmake/evmone.cmake").exists() or git(source, "ls-files", "--stage", "third_party/evmone"):
        return
    workflow = (source / ".github/workflows/test-vm.yml").read_text()
    ref = re.search(r"repository: category-labs/evmone(?:(?!uses:).)*?ref: (\S+)", workflow, re.S)
    if ref is None:
        raise RuntimeError(f"no evmone ref at {commit}")
    if not cache.exists():
        subprocess.run(["git", "clone", "-q", "--bare", EVMONE, str(cache)], check=True)
    (source / "third_party/evmone").mkdir(parents=True, exist_ok=True)
    date = git(source, "log", "-1", "--format=%cI", "HEAD").strip()
    at = subprocess.run(
        ["git", "-C", str(cache), "rev-list", "-1", f"--before={date}", ref.group(1)], capture_output=True
    )
    archive = subprocess.run(
        ["git", "-C", str(cache), "archive", at.stdout.decode().strip() or ref.group(1)],
        capture_output=True,
        check=True,
    )
    subprocess.run(["tar", "-x", "-C", str(source / "third_party/evmone")], input=archive.stdout, check=True)


def build(source: pathlib.Path, build: pathlib.Path) -> None:
    toolchain = source.resolve() / "category/core/toolchains/gcc-avx2.cmake"
    configure = ["cmake", "-G", "Ninja", f"-S{source}", f"-B{build}", f"-DCMAKE_TOOLCHAIN_FILE={toolchain}"]
    configure += ["-DCMAKE_BUILD_TYPE=RelWithDebInfo", "-DMONAD_COMPILER_BENCHMARKS=ON"]
    configure += ["-DCMAKE_POLICY_VERSION_MINIMUM=3.5"]
    micro = (source / "test/vm/micro_benchmarks/main.cpp").read_text()
    if "LLVM" in micro and "MONAD_COMPILER_LLVM" not in micro:
        cmakedir = subprocess.run([tool("llvm-config-19"), "--cmakedir"], capture_output=True, text=True, check=True)
        configure += ["-DMONAD_COMPILER_LLVM=ON", f"-DLLVM_DIR={cmakedir.stdout.strip()}"]
    for attempt in range(2):
        if attempt:
            shutil.rmtree(build, ignore_errors=True)
        steps = [configure, ["cmake", "--build", str(build), "-t", "mce", "vm-micro-benchmarks"]]
        if all(subprocess.run(step, capture_output=True).returncode == 0 for step in steps):
            return
    raise RuntimeError(f"mce or vm-micro-benchmarks does not build in {source}")


def measure_commit(args: argparse.Namespace, commit: str) -> Report:
    tag = hashlib.sha1(args.micro.encode()).hexdigest()[:8]
    path = args.output / f"{commit}-{tag}.json"
    if not path.exists():
        print(commit[:9], git(args.source, "log", "-1", "--format=%s", commit).strip(), file=sys.stderr)
        try:
            prepare(args.source, commit, args.output / "evmone.git")
            build(args.source, args.build)
            binaries = args.output / "bin" / commit
            binaries.mkdir(parents=True, exist_ok=True)
            for binary in (MCE, MICRO):
                shutil.copy(args.build / binary, binaries / pathlib.Path(binary).name)
            report = measure_build(args.build, args.cases or args.output / "cases.json", args.micro)
        except (RuntimeError, subprocess.CalledProcessError) as error:
            print(error, file=sys.stderr)
            report = {}
        path.write_text(json.dumps(report))
    result: Report = json.loads(path.read_text())
    return result


def history_plot(commits: list[list[str]], reports: list[Report], names: list[str]) -> str:
    traces = [
        {
            "name": name,
            "x": [f"{c[0][:9]} {c[1]}" for c in commits],
            "y": [100 * (cost(r[name]) / max(cost(reports[0][name]), 1) - 1) for r in reports],
            "text": [c[2] for c in commits],
            "hovertemplate": "%{x}<br>%{text}<br>%{y:.2f}%",
        }
        for name in names
    ]
    return PLOT.replace("TRACES", json.dumps(traces).replace("</", "<\\/"))
