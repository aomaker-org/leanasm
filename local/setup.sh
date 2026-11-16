#!/usr/bin/env bash
# Path: leanasm/local/setup.sh
# Install local Antigravity Python SDK dependencies into repo .venv via uv.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
VENV_DIR="${REPO_ROOT}/.venv"

if ! command -v uv; then
    echo "[!] Error: 'uv' is required (AI.md Directive 01) but not in PATH." >&2
    exit 1
fi

if [ ! -d "${VENV_DIR}" ]; then
    echo "[*] Creating virtual environment at ${VENV_DIR}..."
    uv venv "${VENV_DIR}"
fi

echo "[*] Installing google-antigravity SDK into ${VENV_DIR}..."
uv pip install --python "${VENV_DIR}/bin/python" -r "${SCRIPT_DIR}/requirements.txt"

echo "[+] Local SDK environment ready."
echo "    Re-source 'source config_env' to auto-activate .venv."

# end of file: leanasm/local/setup.sh
