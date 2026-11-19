#!/usr/bin/env python3
# Path: leanasm/scripts/inspect_build_history.py
# Inspect and sort module build timings from .lake/build-history.json
# Max Column: 80 Columns

import argparse
import json
import sys
from pathlib import Path


def inspect_history(history_path: Path, limit: int, metric: str) -> int:
    if not history_path.exists():
        print(f"Error: {history_path} does not exist.", file=sys.stderr)
        return 1

    with open(history_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    items = data.get("modules", data) if isinstance(data, dict) else data
    if not isinstance(items, dict):
        print(f"Error: Unexpected format in {history_path}", file=sys.stderr)
        return 1

    rows = []
    for name, val in items.items():
        if isinstance(val, list) and val:
            last_sec = val[-1]
            avg_sec = sum(val) / len(val)
            max_sec = max(val)
        elif isinstance(val, (int, float)):
            last_sec = float(val)
            avg_sec = float(val)
            max_sec = float(val)
        elif isinstance(val, dict):
            sec = float(val.get("duration_secs", 0.0))
            last_sec = sec
            avg_sec = sec
            max_sec = sec
        else:
            continue

        rows.append((name, last_sec, avg_sec, max_sec))

    if not rows:
        print("No timing data found.")
        return 0

    metric_idx = {"last": 1, "avg": 2, "max": 3}.get(metric, 1)
    rows.sort(key=lambda r: -r[metric_idx])

    hdr = f"{'MODULE':<52} {'LAST':>8} {'AVG':>8} {'MAX':>8}"
    print(hdr)
    print("-" * len(hdr))
    for name, last_sec, avg_sec, max_sec in rows[:limit]:
        print(f"{name:<52} {last_sec:7.2f}s {avg_sec:7.2f}s {max_sec:7.2f}s")

    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Inspect and rank module build durations from build history"
    )
    parser.add_argument(
        "--file",
        "-f",
        type=Path,
        default=Path(".lake/build-history.json"),
        help="Path to build history JSON (default: .lake/build-history.json)",
    )
    parser.add_argument(
        "--limit",
        "-n",
        type=int,
        default=15,
        help="Number of modules to display (default: 15)",
    )
    parser.add_argument(
        "--sort-by",
        "-s",
        choices=["last", "avg", "max"],
        default="last",
        help="Metric to sort by: last, avg, max (default: last)",
    )
    args = parser.parse_args()
    return inspect_history(args.file, args.limit, args.sort_by)


if __name__ == "__main__":
    sys.exit(main())

# end of file: leanasm/scripts/inspect_build_history.py
