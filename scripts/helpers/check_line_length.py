#!/usr/bin/env python3
# Path: leanasm/scripts/helpers/check_line_length.py
# Check that lines in target files do not exceed maximum column limits
# Max Column: 100 Columns

import argparse
import sys

def check_file(path, max_len=100):
    exceeded = False
    with open(path, "r", encoding="utf-8") as f:
        for i, line in enumerate(f, start=1):
            line = line.rstrip("\r\n")
            if len(line) > max_len:
                print(f"{path}:{i}: length {len(line)} exceeds {max_len}: {line[:80]}...")
                exceeded = True
    return not exceeded

def main():
    parser = argparse.ArgumentParser(description="Check line length in source and markdown files.")
    parser.add_argument("files", nargs="+", help="Files to inspect")
    parser.add_argument("--max-len", type=int, default=100, help="Maximum allowed column width")
    args = parser.parse_args()

    all_ok = True
    for file_path in args.files:
        if not check_file(file_path, args.max_len):
            all_ok = False

    return 0 if all_ok else 1

if __name__ == "__main__":
    sys.exit(main())
# end of file: leanasm/scripts/helpers/check_line_length.py
