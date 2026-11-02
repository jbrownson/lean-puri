#!/usr/bin/env python3
"""Sums up the per-frame callgrind dumps that `bench --callgrind` makes.

Each frame of each path dumps two parts, in order (the Lean part, then the
drawing part), named "<path> <part> <kind>". This prints, per path and kind
of frame, the median and 90th percentile of each part's instructions and of
their total per frame.

Usage: callgrind-summary.py DIR, where DIR holds the callgrind.out files.
"""
import os
import re
import sys
from collections import defaultdict


def parts(directory):
    """(dump number, name, instructions) for each client-request dump."""
    out = []
    for f in os.listdir(directory):
        m = re.search(r"\.(\d+)$", f)
        if not m:
            continue
        name = total = None
        with open(os.path.join(directory, f)) as h:
            for line in h:
                if line.startswith("desc: Trigger: Client Request: "):
                    name = line[len("desc: Trigger: Client Request: "):].strip()
                elif line.startswith("totals: "):
                    total = int(line.split()[1])
        if name and total is not None:
            out.append((int(m.group(1)), name, total))
    return sorted(out)


def quantile(q, xs):
    s = sorted(xs)
    return s[min(len(s) - 1, int(q * len(s)))] if s else 0


def main():
    rows = parts(sys.argv[1])
    frames = []  # (path, kind, {part: instructions})
    for _, name, total in rows:
        path, part, kind = name.split(" ")
        if not frames or frames[-1][0] != path or part in frames[-1][2]:
            frames.append((path, kind, {}))
        frames[-1][2][part] = total
    table = defaultdict(lambda: defaultdict(list))
    for path, kind, ps in frames:
        for k in ("all", kind):
            for part, n in ps.items():
                table[(path, k)][part].append(n)
            table[(path, k)]["total"].append(sum(ps.values()))
    print(f"{'instructions per frame':40}{'median':>14}{'p90':>14}")
    for path in ("incremental", "whole"):
        for kind in ("all", "scroll", "jump", "edit"):
            t = table.get((path, kind))
            if not t:
                continue
            print(f"{path}, {kind} frames ({len(t['total'])}):")
            for part in ["total"] + [p for p in t if p != "total"]:
                xs = t[part]
                print(f"  {part:38}{quantile(0.5, xs):>14,}{quantile(0.9, xs):>14,}")


if __name__ == "__main__":
    main()
