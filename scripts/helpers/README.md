<!-- Path: leanasm/scripts/helpers/README.md -->
# In-Tree Helper & Side-Quest Scripts
<!-- Max Column: 80 Columns -->

This directory contains standalone helper utilities, verification scripts, and
historical logs from trial explorations and side quests.

## Directives & Conventions

Per `AI.md` (`[Directive 02]` & `[Directive 04]`):
1. **Trial Helper Logging**: When creating or executing non-trivial helper
   scripts, log records may be appended to `/tmp/agy_helper_scripts.log` and
   periodically consolidated into `scripts/helpers/agy_helper_scripts.log`.
2. **Column Limits**: Maximum 80 columns for Markdown text and target 80
   columns (maximum 120 characters) for code files.
3. **Headers & Footers**: Every file in this directory must have the proper path
   header and footer comment.

## Inventory

- `check_line_length.py`: Column width inspector ensuring text/code conforms to
  repository column rules.
- `agy_helper_scripts.log`: Archived log record of trial script executions and
  offline witness runs.

<!-- end of file: leanasm/scripts/helpers/README.md -->
