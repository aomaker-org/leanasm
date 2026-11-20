#!/usr/bin/env python3
# Path: leanasm/scripts/inspect_build_history.py
# Inspect and sort module build timings from .lake/build-history.json
# Max Column: 80 Columns

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# Import discover_modules from tools.incremental_build if available
try:
    from tools.incremental_build import discover_modules
except ImportError:
    repo_root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(repo_root))
    from tools.incremental_build import discover_modules


def get_active_modules(repo_root: Path) -> Set[str]:
    """Return set of active module names discovered in workspace."""
    try:
        modules = discover_modules(repo_root)
        return {mod for mod, _ in modules}
    except Exception as exc:
        print(
            f"Warning: Could not discover active modules: {exc}",
            file=sys.stderr,
        )
        return set()


def load_history(history_path: Path) -> Optional[dict]:
    """Load JSON data from history_path."""
    if not history_path.exists():
        print(f"Error: {history_path} does not exist.", file=sys.stderr)
        return None
    try:
        with open(history_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as exc:
        print(f"Error: Failed to read {history_path}: {exc}", file=sys.stderr)
        return None


def save_history(history_path: Path, data: dict) -> bool:
    """Save JSON data to history_path."""
    try:
        history_path.parent.mkdir(parents=True, exist_ok=True)
        with open(history_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
            f.write("\n")
        return True
    except Exception as exc:
        print(f"Error: Failed to write {history_path}: {exc}", file=sys.stderr)
        return False


def handle_clear(history_path: Path) -> int:
    """Reset build history JSON cleanly to a fresh empty state."""
    if save_history(history_path, {}):
        print(f"Cleared build history in {history_path}.")
        return 0
    return 1


def handle_prune(history_path: Path, repo_root: Path) -> int:
    """Prune stale/retired module entries from build history in place."""
    data = load_history(history_path)
    if data is None:
        return 1

    is_wrapped = isinstance(data, dict) and "modules" in data
    items = data.get("modules", data) if is_wrapped else data
    if not isinstance(items, dict):
        print(f"Error: Unexpected format in {history_path}", file=sys.stderr)
        return 1

    active = get_active_modules(repo_root)
    if not active:
        print(
            "Error: No active modules discovered; aborting prune.",
            file=sys.stderr,
        )
        return 1

    original_count = len(items)
    pruned_items = {k: v for k, v in items.items() if k in active}
    pruned_count = original_count - len(pruned_items)

    if is_wrapped:
        data["modules"] = pruned_items
        new_data = data
    else:
        new_data = pruned_items

    if save_history(history_path, new_data):
        print(
            f"Pruned {pruned_count} retired modules; "
            f"{len(pruned_items)} active modules remaining in {history_path}."
        )
        return 0
    return 1


def inspect_history(
    history_path: Path,
    repo_root: Path,
    limit: Optional[int],
    metric: str,
    show_all: bool,
    filter_substr: Optional[str],
    active_only: bool,
) -> int:
    data = load_history(history_path)
    if data is None:
        return 1

    items = data.get("modules", data) if isinstance(data, dict) else data
    if not isinstance(items, dict):
        print(f"Error: Unexpected format in {history_path}", file=sys.stderr)
        return 1

    active_modules: Optional[Set[str]] = None
    if active_only:
        active_modules = get_active_modules(repo_root)

    rows: List[Tuple[str, float, float, float]] = []
    for name, val in items.items():
        if active_modules is not None and name not in active_modules:
            continue
        if filter_substr and filter_substr.lower() not in name.lower():
            continue

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

    display_rows = rows if show_all or limit is None else rows[:limit]

    hdr = f"{'MODULE':<52} {'LAST':>8} {'AVG':>8} {'MAX':>8}"
    print(hdr)
    print("-" * len(hdr))
    for name, last_sec, avg_sec, max_sec in display_rows:
        print(f"{name:<52} {last_sec:7.2f}s {avg_sec:7.2f}s {max_sec:7.2f}s")

    # Summary total line across displayed modules
    tot_last = sum(r[1] for r in display_rows)
    tot_avg = sum(r[2] for r in display_rows)
    tot_max = sum(r[3] for r in display_rows)
    print("-" * len(hdr))
    print(f"{'TOTAL':<52} {tot_last:7.2f}s {tot_avg:7.2f}s {tot_max:7.2f}s")

    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Inspect and rank module build durations from build history"
    )
    parser.add_argument(
        "--file",
        type=Path,
        default=Path(".lake/build-history.json"),
        help="Path to build history JSON (default: .lake/build-history.json)",
    )
    parser.add_argument(
        "--all",
        "-a",
        action="store_true",
        help="Display every recorded module instead of truncating to limit",
    )
    parser.add_argument(
        "--limit",
        "-n",
        type=int,
        default=15,
        help="Max rows displayed when --all is omitted (default: 15)",
    )
    parser.add_argument(
        "--filter",
        "-f",
        dest="filter_substr",
        type=str,
        default=None,
        help="Case-insensitive substring filter on module names",
    )
    parser.add_argument(
        "--sort",
        "-s",
        dest="sort_by",
        choices=["last", "avg", "max"],
        default="last",
        help="Metric to sort by: last, avg, max (default: last)",
    )
    parser.add_argument(
        "--active-only",
        action="store_true",
        help="Filter or hide retired/non-existent module targets from reports",
    )
    parser.add_argument(
        "--prune",
        action="store_true",
        help="Prune stale / retired module entries from history file in place",
    )
    parser.add_argument(
        "--clear",
        action="store_true",
        help="Reset or truncate history file cleanly to a fresh empty state",
    )

    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parent.parent

    if args.clear:
        return handle_clear(args.file)

    if args.prune:
        return handle_prune(args.file, repo_root)

    return inspect_history(
        history_path=args.file,
        repo_root=repo_root,
        limit=args.limit,
        metric=args.sort_by,
        show_all=args.all,
        filter_substr=args.filter_substr,
        active_only=args.active_only,
    )


if __name__ == "__main__":
    sys.exit(main())

# end of file: leanasm/scripts/inspect_build_history.py
