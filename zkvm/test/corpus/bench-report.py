#!/usr/bin/env python3
"""Tables and fits from bench.py's CSVs.

    bench-report.py --l2 L2.csv [...] --plain PLAIN.csv [...] [--mainnet M.csv]

Rows are paired across the arms on (corpus, number): both arms are generated
from one seed and one preset on the same L2 chain, so block n executes the same
transactions on the same state in both, and only the cipher suite differs --
the plaintext arm is the L2 built with MONAD_ZKVM_L2_CIPHER=plaintext.

`base` is ZisK's fixed ROM-and-tables cost, the same on every run, so the fits
are taken on COST - base: the part of the cost that depends on the block.
"""
import argparse
import csv
import math
import re
import statistics as st

PRESETS = ('wholesale', 'payouts', 'wholesale-cbdc', 'worker-payouts')
# A transaction of these is one transfer, so a cost per transaction is a
# property of the mix; on the token presets a transaction is a contract call of
# any size, and gas is what measures it.
TRANSFER_PRESETS = ('wholesale', 'payouts')


def load(paths, workload_only=True):
    rows = []
    for p in paths:
        for r in csv.DictReader(open(p)):
            if r.get('verdict') != 'PASS':
                raise SystemExit(f'{p}: {r["corpus"]}/{r["number"]} is {r["verdict"]}')
            rows.append(r)
    if not workload_only:
        return rows
    # Only the presets are workloads. The small scenarios (transfers, evm,
    # spoke) exercise the rules and are checked for correctness by bench.py,
    # but they are not a load and their blocks are not comparable.
    rows = [r for r in rows if r['scenario'] in PRESETS]
    # Drop a first-block spoke deployment from benchmark samples, not a
    # workload block. L2 corpora seed the spoke at genesis and need no such
    # drop.
    first = {}
    for r in rows:
        c = r['corpus']
        first[c] = min(first.get(c, int(r['number'])), int(r['number']))
    return [r for r in rows
            if not (int(r['number']) == first[r['corpus']] and r['txs'] == '1')]


def f(r, k):
    v = r.get(k)
    return float(v) if v not in (None, '') else math.nan


def med(v):
    v = [x for x in v if not math.isnan(x)]
    return st.median(v) if v else math.nan


def var(r):
    return f(r, 'cost') - f(r, 'base')


def group(rows):
    g = {}
    for r in rows:
        g.setdefault(r['corpus'], []).append(r)
    return g


def per_corpus(title, rows):
    print(f'\n### {title}\n')
    print('| corpus | n | witness KB | txs | Mgas | M steps | G COST | G COST - base | '
          'precompile share | keccak calls |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for c, rs in sorted(group(rows).items(), key=lambda kv: med([f(r, 'cost') for r in kv[1]])):
        print(f"| {c} | {len(rs)} | {med([f(r, 'witness_bytes') for r in rs]) / 1e3:,.0f} | "
              f"{med([f(r, 'txs') for r in rs]):,.0f} | {med([f(r, 'gas_used') for r in rs]) / 1e6:.2f} | "
              f"{med([f(r, 'steps') for r in rs]) / 1e6:.2f} | "
              f"{med([f(r, 'cost') for r in rs]) / 1e9:.3f} | {med([var(r) for r in rs]) / 1e9:.3f} | "
              f"{med([f(r, 'precompiles') / var(r) for r in rs]):.0%} | "
              f"{med([f(r, 'kec_calls') for r in rs]):,.0f} |")


def paired(l2, plain):
    key = lambda r: (r['corpus'], r['number'])
    p = {key(r): r for r in plain}
    pairs = [(r, p[key(r)]) for r in l2 if key(r) in p]
    print(f'\n### L2 over plaintext, {len(pairs)} paired blocks\n')
    print('The last six columns split the extra COST: category deltas, then three precompiles.\n')
    print('| corpus | n | steps | COST | COST - base | main | precompiles | memory | '
          'poseidon2 | secp256k1 | keccak |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    by = {}
    for a, b in pairs:
        by.setdefault(a['corpus'], []).append((a, b))
    z = lambda x: 0.0 if math.isnan(x) else x   # an op one arm never calls
    for c, ps in sorted(by.items()):
        ratio = lambda k: med([f(a, k) / f(b, k) for a, b in ps])
        dtot = med([f(a, 'cost') - f(b, 'cost') for a, b in ps])
        share = lambda k: med([z(f(a, k)) - z(f(b, k)) for a, b in ps]) / dtot
        print(f"| {c} | {len(ps)} | {ratio('steps'):.3f}x | {ratio('cost'):.3f}x | "
              f"{med([var(a) / var(b) for a, b in ps]):.3f}x | "
              f"{share('main'):.0%} | {share('precompiles'):.0%} | {share('memory'):.0%} | "
              f"{share('poseidon2_cost'):.0%} | {share('secp256k1_cost'):.0%} | "
              f"{share('kec_cost'):.0%} |")


def fit_power(xs, ys):
    lx, ly = [math.log(x) for x in xs], [math.log(y) for y in ys]
    mx, my = st.mean(lx), st.mean(ly)
    b = sum((a - mx) * (c - my) for a, c in zip(lx, ly)) / sum((a - mx) ** 2 for a in lx)
    a = math.exp(my - b * mx)
    ss = sum((c - (math.log(a) + b * x)) ** 2 for x, c in zip(lx, ly))
    tot = sum((c - my) ** 2 for c in ly)
    return a, b, 1 - ss / tot


def fit_origin(xs, ys):
    k = sum(x * y for x, y in zip(xs, ys)) / sum(x * x for x in xs)
    my = st.mean(ys)
    ss = sum((y - k * x) ** 2 for x, y in zip(xs, ys))
    tot = sum((y - my) ** 2 for y in ys)
    return k, 1 - ss / tot


def least_squares(A, y):
    """y ~ A x: the normal equations, solved by Gauss-Jordan with partial
    pivoting. Three unknowns, so nothing heavier is warranted."""
    n = len(A[0])
    M = [[sum(a[i] * a[j] for a in A) for j in range(n)] for i in range(n)]
    v = [sum(a[i] * b for a, b in zip(A, y)) for i in range(n)]
    for i in range(n):
        piv = max(range(i, n), key=lambda k: abs(M[k][i]))
        M[i], M[piv], v[i], v[piv] = M[piv], M[i], v[piv], v[i]
        for k in range(n):
            if k != i:
                t = M[k][i] / M[i][i]
                M[k] = [x - t * w for x, w in zip(M[k], M[i])]
                v[k] -= t * v[i]
    return [v[i] / M[i][i] for i in range(n)]


def fit_two(rows, x, w):
    """COST - base ~ a x + b w + c, with R2 and the worst relative miss."""
    ys = [var(r) for r in rows]
    A = [[f(r, x), f(r, w), 1.0] for r in rows]
    a, b, c = least_squares(A, ys)
    ps = [a * p[0] + b * p[1] + c for p in A]
    my = st.mean(ys)
    ss = sum((y - p) ** 2 for y, p in zip(ys, ps))
    tot = sum((y - my) ** 2 for y in ys)
    return a, b, c, 1 - ss / tot, max(abs(p - y) / y for y, p in zip(ys, ps))


def signed(c):
    return f"{'+' if c >= 0 else '-'} {abs(c) / 1e6:,.1f} M"


def laws(title, rows):
    transfers = [r for r in rows if r['scenario'] in TRANSFER_PRESETS]
    if transfers:
        a, b, c, r2, worst = fit_two(transfers, 'txs', 'witness_bytes')
        print(f'- {title}, the {len(transfers)} blocks of the transfer presets: '
              f'`COST - base = {a:,.0f} x txs + {b:,.0f} x witness_bytes {signed(c)}`, '
              f'R2 {r2:.7f}, worst miss {worst:.1%}')
    a, b, c, r2, worst = fit_two(rows, 'gas_used', 'witness_bytes')
    print(f'- {title}, all {len(rows)} workload blocks: `COST - base = {a:,.1f} x gas + '
          f'{b:,.1f} x witness_bytes {signed(c)}`, R2 {r2:.7f}, worst miss {worst:.1%}')


def sweep(title, rows):
    point = lambda c: re.search(r'-d(\d+)$', c)
    rs = [r for r in rows if point(r['corpus'])]
    if not rs:
        return
    print(f'\n### {title}: the dispersion sweep\n')
    print('| distinct | n | witness KB | Mgas | M steps | G COST | G COST - base | COST/gas |')
    print('|---:|---:|---:|---:|---:|---:|---:|---:|')
    pts = []
    for c, g in sorted(group(rs).items(), key=lambda kv: int(point(kv[0]).group(1))):
        print(f"| {int(point(c).group(1)):,} | {len(g)} | "
              f"{med([f(r, 'witness_bytes') for r in g]) / 1e3:,.0f} | "
              f"{med([f(r, 'gas_used') for r in g]) / 1e6:.2f} | "
              f"{med([f(r, 'steps') for r in g]) / 1e6:.2f} | "
              f"{med([f(r, 'cost') for r in g]) / 1e9:.3f} | {med([var(r) for r in g]) / 1e9:.3f} | "
              f"{med([f(r, 'cost') / f(r, 'gas_used') for r in g]):.0f} |")
        pts += [(f(r, 'intended_distinct'), f(r, 'witness_bytes'), var(r), f(r, 'gas_used'))
                for r in g]
    a, b, r2 = fit_power([p[0] for p in pts], [p[2] for p in pts])
    k, r2k = fit_origin([p[1] for p in pts], [p[2] for p in pts])
    kg, r2g = fit_origin([p[3] for p in pts], [p[2] for p in pts])
    print(f'\n- `COST - base = {a:,.0f} x distinct^{b:.3f}`, R2 {r2:.4f}')
    print(f'- `COST - base = {k:,.0f} x witness_bytes`, R2 {r2k:.4f}')
    print(f'- `COST - base = {kg:,.0f} x gas`, R2 {r2g:.4f}')


def mainnet(rows):
    c = sorted(f(r, 'cost') for r in rows)
    q = lambda p: c[int(p * (len(c) - 1))]
    print(f'\n### Mainnet reference, {len(rows)} blocks\n')
    print(f"- COST median {med(c) / 1e9:.2f} G (p10 {q(.1) / 1e9:.2f}, p90 {q(.9) / 1e9:.2f})")
    print(f"- steps median {med([f(r, 'steps') for r in rows]) / 1e6:.1f} M, "
          f"witness median {med([f(r, 'witness_bytes') for r in rows]) / 1e6:.2f} MB")
    print(f"- COST - base per witness byte, median "
          f"{med([var(r) / f(r, 'witness_bytes') for r in rows]):,.0f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l2', nargs='+', required=True)
    ap.add_argument('--plain', nargs='+', required=True)
    ap.add_argument('--mainnet', help='a bench.py CSV of mainnet witnesses, taken whole')
    a = ap.parse_args()
    l2, plain = load(a.l2), load(a.plain)
    per_corpus('L2 arm', l2)
    per_corpus('Plaintext arm', plain)
    paired(l2, plain)
    sweep('L2 arm', l2)
    sweep('Plaintext arm', plain)
    print('\n### The cost laws\n')
    laws('L2 arm', l2)
    laws('Plaintext arm', plain)
    if a.mainnet:
        mainnet(load([a.mainnet], workload_only=False))


if __name__ == '__main__':
    main()
