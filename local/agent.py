#!/usr/bin/env python3
# Path: leanasm/local/agent.py
"""Quota-free local Ollama runner for leanasm using Antigravity SDK or HTTP."""

import argparse
import asyncio
import json
import os
from pathlib import Path
import sys
import urllib.error
import urllib.request
from typing import List, Optional


DEFAULT_MODEL = "deepseek-prover:7b"
DEFAULT_BASE_URL = "http://localhost:11434"
DEFAULT_SYSTEM_PROMPT = (
    "You are a Lean 4 (v4.35.0) formal verification assistant for leanasm. "
    "All core proofs must be constructive (zero sorryAx, zero Classical.choice). "
    "Verify candidate proofs with lake build +LeanAsm.<Module>."
)


def resolve_ollama_settings(
    model_arg: Optional[str],
    base_url_arg: Optional[str],
) -> tuple[str, str]:
    """Resolve model name and OpenAI-compatible /v1 base URL."""
    model = model_arg or os.environ.get("AGY_MODEL") or DEFAULT_MODEL
    raw_url = (
        base_url_arg
        or os.environ.get("AGY_OLLAMA_BASE_URL")
        or os.environ.get("OLLAMA_HOST")
        or DEFAULT_BASE_URL
    )
    cleaned = raw_url.rstrip("/")
    v1_url = cleaned if cleaned.endswith("/v1") else f"{cleaned}/v1"
    return model, v1_url


def read_system_instructions(prompt_file: Optional[str]) -> str:
    """Load system instructions from prompt_file or fallback to default."""
    if not prompt_file:
        return DEFAULT_SYSTEM_PROMPT
    path = Path(prompt_file)
    if not path.is_file():
        raise FileNotFoundError(f"System prompt file not found: {path}")
    return path.read_text(encoding="utf-8")


async def run_sdk_mode(
    model: str,
    v1_url: str,
    system_prompt: str,
    prompt: Optional[str],
    enable_write: bool,
    lightweight: bool,
) -> int:
    """Run interactive or one-shot agent via google-antigravity SDK."""
    from google.antigravity import Agent, CapabilitiesConfig
    from google.antigravity.connections.local.local_openai_connection_config import (
        LocalOpenAIAgentConfig,
    )
    from google.antigravity.utils.interactive import run_interactive_loop

    kwargs = {
        "model": model,
        "base_url": v1_url,
    }
    if enable_write:
        kwargs["capabilities"] = CapabilitiesConfig()

    config = LocalOpenAIAgentConfig(**kwargs)
    if lightweight:
        config = config.lightweight()

    print(
        f"[+] Starting Antigravity SDK local agent "
        f"(model={model}, base_url={v1_url}, write={enable_write})"
    )
    print(f"[*] System context loaded ({len(system_prompt)} chars).")

    async with Agent(config) as agent:
        if prompt:
            full_prompt = f"{system_prompt}\n\nTask:\n{prompt}"
            response = await agent.chat(full_prompt)
            async for token in response:
                sys.stdout.write(token)
                sys.stdout.flush()
            print()
        else:
            await run_interactive_loop(agent)
    return 0


def post_chat_completion(
    v1_url: str,
    model: str,
    messages: List[dict],
    timeout_secs: int = 300,
) -> str:
    """Send a synchronous OpenAI-compatible chat request to Ollama."""
    endpoint = f"{v1_url}/chat/completions"
    payload = json.dumps(
        {
            "model": model,
            "messages": messages,
            "stream": False,
        }
    ).encode("utf-8")
    req = urllib.request.Request(
        endpoint,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_secs) as resp:
            body = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Ollama HTTP {exc.code} from {endpoint}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(
            f"Cannot reach Ollama at {endpoint}: {exc.reason}. "
            "Check Windows Ollama service and WSL2 mirrored networking."
        ) from exc

    choices = body.get("choices", [])
    if not choices:
        raise RuntimeError(f"Empty choices in Ollama response: {body}")
    return choices[0].get("message", {}).get("content", "")


def run_http_mode(
    model: str,
    v1_url: str,
    system_prompt: str,
    prompt: Optional[str],
) -> int:
    """Run zero-dependency OpenAI-compatible chat against local Ollama."""
    messages: List[dict] = [{"role": "system", "content": system_prompt}]
    print(f"[+] Starting Ollama HTTP chat (model={model}, base_url={v1_url})")

    if prompt:
        messages.append({"role": "user", "content": prompt})
        reply = post_chat_completion(v1_url, model, messages)
        print(reply)
        return 0

    print("[*] Interactive HTTP loop ready. Type '/exit' or Ctrl+D to quit.")
    while True:
        try:
            user_text = input("\nlocal> ").strip()
        except EOFError:
            print()
            break
        if not user_text:
            continue
        if user_text in ("/exit", "/quit"):
            break
        messages.append({"role": "user", "content": user_text})
        reply = post_chat_completion(v1_url, model, messages)
        messages.append({"role": "assistant", "content": reply})
        print(f"\n{reply}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    """Build CLI argument parser for local Ollama agent runner."""
    parser = argparse.ArgumentParser(
        description="Run a quota-free local Ollama agent or chat loop for leanasm."
    )
    parser.add_argument(
        "-p",
        "--prompt",
        default=None,
        help="Run a single non-interactive prompt and exit.",
    )
    parser.add_argument(
        "--model",
        default=None,
        help="Override Ollama model (default: $AGY_MODEL or deepseek-prover:7b).",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override Ollama URL (default: $AGY_OLLAMA_BASE_URL or $OLLAMA_HOST).",
    )
    parser.add_argument(
        "--system-file",
        default=None,
        help="Optional markdown/text file for system instructions.",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Enable SDK workspace write/command tools (CapabilitiesConfig).",
    )
    parser.add_argument(
        "--no-lightweight",
        action="store_true",
        help="Disable SDK .lightweight() prompt/tool compression.",
    )
    parser.add_argument(
        "--http",
        action="store_true",
        help="Force zero-dependency HTTP /v1/chat/completions mode instead of SDK.",
    )
    return parser


def main() -> int:
    """CLI entrypoint."""
    args = build_parser().parse_args()
    model, v1_url = resolve_ollama_settings(args.model, args.base_url)
    system_prompt = read_system_instructions(args.system_file)

    if args.http:
        return run_http_mode(model, v1_url, system_prompt, args.prompt)

    try:
        import google.antigravity  # noqa: F401
    except ImportError as exc:
        print(
            f"[!] google-antigravity SDK is not installed in this Python env ({exc}).\n"
            "    Run './local/setup.sh' (or use '--http' for dependency-free mode).",
            file=sys.stderr,
        )
        return 1

    return asyncio.run(
        run_sdk_mode(
            model=model,
            v1_url=v1_url,
            system_prompt=system_prompt,
            prompt=args.prompt,
            enable_write=args.write,
            lightweight=not args.no_lightweight,
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())

# end of file: leanasm/local/agent.py
