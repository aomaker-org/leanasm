# Path: leanasm/docs/environment_tools.md
# Environment Tools, Virtual Environment, & Text Pipeline
# Max Column: 80 Columns

## 1. Overview & Toolchain Standards

Per `AI.md` Directive 01, `leanasm` mandates strict toolchain hygiene:
- Lean package builds, verifications, and executions rely on `elan`, `lake`,
  and `lean`.
- Auxiliary tools, LLM interface scripts, and workflow utilities run under
  Python 3 within a repository-local virtual environment (`.venv`) managed
  by `uv`.
- All text processing and clipboard operations must enforce strict UTF-8
  encoding without mojibake or corrupt character encodings.

---

## 2. Virtual Environment Setup (`.venv` via `uv`)

The local virtual environment is initialized and synchronized via
`local/setup.sh` and pinned dependencies in `local/requirements.txt`:

```bash
# Initialize or update virtual environment packages
./local/setup.sh

# Activate virtual environment in current shell session
source config_env
```

### 2.1 Managed Packages in `.venv`

- **`google-antigravity`**: Antigravity Python SDK for agentic execution.
- **`ftfy`**: Fixes mojibake, mixed encoding artifacts, and broken Unicode
  sequences.
- **`pyperclip`**: Cross-platform clipboard dispatch fallback (supporting
  Linux X11/Wayland and WSL2 pipes).
- **`charset-normalizer`**: Character encoding autodetection and fallback for
  non-UTF-8 source text.

---

## 3. Context Bundling & Text Tooling (`scripts/files2clip`)

The `scripts/files2clip` utility packs targeted repository files into a
symmetrical bundle copied directly to the clipboard or archived into
`scratch/` if exceeding the safety limit (250 KB).

### 3.1 Encoding & Mojibake Prevention Pipeline

1. **Binary Ingestion**: Files are read in binary mode
   (`read(MAX_TRUNCATE_SIZE)`).
2. **UTF-8 Decoding with Normalization**:
   - Primary decoding via standard UTF-8.
   - On `UnicodeDecodeError`, fallback to `charset_normalizer` best-match
     detection, or UTF-8 replacement chars.
3. **Mojibake Remediation**:
   - Post-processed through `ftfy.fix_text` to repair encoding anomalies,
     curly quote mojibake, or double-encoded entities.
4. **Clipboard Multiplexing**:
   - Direct `pyperclip.copy()` integration.
   - WSL pipe fallback (`/mnt/c/Windows/System32/clip.exe` and `clip.exe`).
   - Native Linux clipboard utilities (`xclip -selection clipboard`,
     `wl-copy`).

---

## 4. Environment Verification & Diagnostic Checks

Assistants and developers verify toolchain and clipboard integrity using:

```bash
# Verify Python virtual environment and core text packages
python3 -c "import ftfy, pyperclip; print('Text tools ready')"

# Pack explicit target files into clipboard
python3 scripts/files2clip local/requirements.txt local/setup.sh

# Verify Lean axioms and sequential build
make axioms
LEAN_OPTS="-M4096" make build-seq
make sync
```

<!-- end of file: leanasm/docs/environment_tools.md -->
