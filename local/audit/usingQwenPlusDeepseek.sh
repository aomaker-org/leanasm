#!/usr/bin/env bash
# Path: leanasm/local/audit/usingQwenPlusDeepseek.sh
# Launch Qwen + DeepSeek codebase audit & profiler with Directive 02 logging.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

show_help() {
    cat <<'EOF'
Usage: ./local/audit/usingQwenPlusDeepseek.sh [WRAPPER_OPTS] [AUDITOR_OPTS...]

Wrapper Options:
  --no-build-each    Do not automatically pass --build-each to auditor.py
  --no-check-axioms  Do not automatically pass --check-axioms to auditor.py
  --sdk              Use Antigravity SDK tool-calling instead of --direct
  --no-log           Run directly without tools/run_with_logging.py wrapper
  -h, --help         Show this help and auditor.py options

Default behavior passes --direct, --build-each, and --check-axioms to
local/auditor.py and records full stdout/stderr via tools/run_with_logging.py.
EOF
}

_use_log=1
_add_build_each=1
_add_check_axioms=1
_add_direct=1
_det_only=0
_pass_args=()

while [ "$#" -gt 0 ]; do
    case "$1" in
        -h|--help)
            show_help
            echo ""
            "${REPO_ROOT}/.venv/bin/python" "${REPO_ROOT}/local/auditor.py" --help
            exit 0
            ;;
        --no-log)
            _use_log=0
            ;;
        --no-build-each)
            _add_build_each=0
            ;;
        --no-check-axioms)
            _add_check_axioms=0
            ;;
        --sdk)
            _add_direct=0
            ;;
        --direct)
            _add_direct=1
            ;;
        --deterministic-only)
            _det_only=1
            _pass_args+=("$1")
            ;;
        --build-each)
            _add_build_each=0
            _pass_args+=("$1")
            ;;
        --check-axioms)
            _add_check_axioms=0
            _pass_args+=("$1")
            ;;
        *)
            _pass_args+=("$1")
            ;;
    esac
    shift
done

if [ ! -x "${REPO_ROOT}/.venv/bin/python" ]; then
    echo "[!] Missing ${REPO_ROOT}/.venv/bin/python. Run ./local/setup.sh first." >&2
    exit 1
fi

export LEANASM_USE_OLLAMA=1
# shellcheck disable=SC1091
. "${REPO_ROOT}/config_env" audit

if [ "${_det_only}" -eq 0 ]; then
    _base="${AGY_OLLAMA_BASE_URL:-http://localhost:11434}"
    _tags_url="${_base%/}/api/tags"
    echo "[*] Checking Ollama connectivity at ${_tags_url}..."
    if ! curl -fsS "${_tags_url}"; then
        echo "" >&2
        echo "[!] Cannot reach Ollama at ${_tags_url}." >&2
        echo "    Start Windows Ollama and verify WSL2 mirrored networking." >&2
        exit 1
    fi
    echo ""
fi

_cmd=("${REPO_ROOT}/.venv/bin/python" "${REPO_ROOT}/local/auditor.py")
if [ "${_add_direct}" -eq 1 ] && [ "${_det_only}" -eq 0 ]; then
    _cmd+=("--direct")
fi
if [ "${_add_build_each}" -eq 1 ]; then
    _cmd+=("--build-each")
fi
if [ "${_add_check_axioms}" -eq 1 ]; then
    _cmd+=("--check-axioms")
fi
if [ "${#_pass_args[@]}" -gt 0 ]; then
    _cmd+=("${_pass_args[@]}")
fi

cd "${REPO_ROOT}"
if [ "${_use_log}" -eq 1 ]; then
    _quoted=""
    for _arg in "${_cmd[@]}"; do
        _quoted+=" $(printf '%q' "${_arg}")"
    done
    exec python3 "${REPO_ROOT}/tools/run_with_logging.py" \
        -l qwen-deepseek-audit \
        "${_quoted# }"
else
    exec "${_cmd[@]}"
fi

# end of file: leanasm/local/audit/usingQwenPlusDeepseek.sh
