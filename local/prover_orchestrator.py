#!/usr/bin/env python3
# Path: leanasm/local/prover_orchestrator.py
"""Hierarchical Qwen + DeepSeek-Prover orchestrator for leanasm via Antigravity SDK."""

import argparse
import asyncio
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.request
from typing import List, Optional

from google.antigravity import Agent, BuiltinTools, CapabilitiesConfig
from google.antigravity.connections.local.local_openai_connection_config import (
    LocalOpenAIAgentConfig,
)
from google.antigravity.utils.interactive import run_interactive_loop


DEFAULT_ORCHESTRATOR_MODEL = "qwen2.5-coder:7b"
DEFAULT_PROVER_MODEL = "deepseek-prover:7b"
DEFAULT_BASE_URL = "http://localhost:11434"
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]*$")

ORCHESTRATOR_INSTRUCTIONS = (
    "You are the leanasm Lean 4 (v4.35.0) verification orchestrator.\n"
    "Workflow:\n"
    "1. Inspect target .lean files with view_file / search_directory.\n"
    "2. When you need Lean 4 proof tactics or lemma synthesis, call "
    "synthesize_lean_prover_tactic with the exact theorem signature and "
    "surrounding definitions.\n"
    "3. When --write is enabled and you edit a .lean file, ensure zero "
    "'sorry' and zero Classical.choice (audit [propext, Quot.sound]).\n"
    "4. Always verify changes with verify_lean_module before concluding."
)


def normalize_v1_url(raw_url: Optional[str]) -> str:
    """Resolve and normalize the Ollama OpenAI-compatible /v1 base URL."""
    base = (
        raw_url
        or os.environ.get("AGY_OLLAMA_BASE_URL")
        or os.environ.get("OLLAMA_HOST")
        or DEFAULT_BASE_URL
    ).rstrip("/")
    return base if base.endswith("/v1") else f"{base}/v1"


def make_prover_tool(v1_url: str, prover_model: str, timeout_secs: int = 300):
    """Build a tool function that delegates Lean 4 tactic synthesis to DeepSeek-Prover."""

    def synthesize_lean_prover_tactic(
        theorem_context: str,
        goal_description: str = "",
    ) -> str:
        """Query DeepSeek-Prover on Ollama to synthesize Lean 4 proof tactics.

        Args:
            theorem_context: Exact Lean 4 theorem signature and local definitions.
            goal_description: Optional note on target lemma or compiler error.
        """
        endpoint = f"{v1_url}/chat/completions"
        user_msg = f"Complete or synthesize Lean 4 tactics for:\n\n{theorem_context}"
        if goal_description.strip():
            user_msg += f"\n\nNotes / compiler feedback:\n{goal_description.strip()}"

        payload = json.dumps(
            {
                "model": prover_model,
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "You are an expert Lean 4 (v4.35.0) theorem prover. "
                            "Produce constructive Lean 4 tactics without sorry or "
                            "Classical.choice."
                        ),
                    },
                    {"role": "user", "content": user_msg},
                ],
                "temperature": 0.2,
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
            return f"Error: Ollama HTTP {exc.code} querying {prover_model}: {detail}"
        except urllib.error.URLError as exc:
            return f"Error: Cannot reach Ollama at {endpoint}: {exc.reason}"

        choices = body.get("choices", [])
        if not choices:
            return f"Error: Empty choices from {prover_model}: {body}"
        return choices[0].get("message", {}).get("content", "")

    return synthesize_lean_prover_tactic


def make_verify_tool(repo_root: Path):
    """Build a safe Lean 4 module build and axiom-audit verification tool."""

    def verify_lean_module(module_name: str, check_axioms: bool = False) -> str:
        """Build a Lean 4 module with lake and optionally run TestAxioms.lean.

        Args:
            module_name: Dotted Lean module, e.g. LeanAsm.QuasiRiemann.MollifierVariationalBridge.
            check_axioms: If true, also run lake env lean tests/TestAxioms.lean.
        """
        if not MODULE_RE.match(module_name):
            return (
                f"Error: Invalid Lean module name '{module_name}'. "
                "Expected dotted identifier like LeanAsm.MiniVM."
            )

        elan_bin = str(Path.home() / ".elan" / "bin")
        env = dict(os.environ)
        if elan_bin not in env.get("PATH", ""):
            env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

        target = f"+{module_name}"
        proc = subprocess.run(
            ["lake", "build", target],
            cwd=str(repo_root),
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        output = [f"$ lake build {target} -> exit={proc.returncode}", proc.stdout.strip()]

        if proc.returncode == 0 and check_axioms:
            ax_proc = subprocess.run(
                ["lake", "env", "lean", "tests/TestAxioms.lean"],
                cwd=str(repo_root),
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
            )
            output.append(
                f"$ lake env lean tests/TestAxioms.lean -> exit={ax_proc.returncode}"
            )
            output.append(ax_proc.stdout.strip())

        return "\n".join(part for part in output if part)

    return verify_lean_module


def build_capabilities(enable_write: bool) -> CapabilitiesConfig:
    """Select focused builtin tools so 7B orchestrators stay reliable."""
    tools: List[BuiltinTools] = [
        BuiltinTools.LIST_DIR,
        BuiltinTools.SEARCH_DIR,
        BuiltinTools.FIND_FILE,
        BuiltinTools.VIEW_FILE,
        BuiltinTools.FINISH,
    ]
    if enable_write:
        tools.extend(
            [
                BuiltinTools.EDIT_FILE,
                BuiltinTools.CREATE_FILE,
                BuiltinTools.RUN_COMMAND,
            ]
        )
    return CapabilitiesConfig(
        enable_subagents=False,
        enabled_tools=tools,
    )


def build_agent_config(
    repo_root: Path,
    orchestrator_model: str,
    prover_model: str,
    v1_url: str,
    enable_write: bool,
    lightweight: bool,
) -> LocalOpenAIAgentConfig:
    """Construct LocalOpenAIAgentConfig wired with Qwen + DeepSeek + Lake tools."""
    prover_tool = make_prover_tool(v1_url, prover_model)
    verify_tool = make_verify_tool(repo_root)
    config = LocalOpenAIAgentConfig(
        model=orchestrator_model,
        base_url=v1_url,
        system_instructions=ORCHESTRATOR_INSTRUCTIONS,
        capabilities=build_capabilities(enable_write),
        tools=[prover_tool, verify_tool],
        workspaces=[str(repo_root)],
    )
    return config.lightweight() if lightweight else config


async def run_orchestrator(
    config: LocalOpenAIAgentConfig,
    prompt: Optional[str],
) -> int:
    """Run one-shot or interactive orchestration loop."""
    async with Agent(config) as agent:
        if prompt:
            response = await agent.chat(prompt)
            async for token in response:
                sys.stdout.write(token)
                sys.stdout.flush()
            print()
        else:
            await run_interactive_loop(agent)
    return 0


def build_parser() -> argparse.ArgumentParser:
    """Build CLI argument parser."""
    parser = argparse.ArgumentParser(
        description="Qwen orchestrator + DeepSeek-Prover + Lake verification loop."
    )
    parser.add_argument(
        "-p",
        "--prompt",
        default=None,
        help="Run a single non-interactive prompt and exit.",
    )
    parser.add_argument(
        "--orchestrator-model",
        default=DEFAULT_ORCHESTRATOR_MODEL,
        help=f"Tool-calling orchestrator model (default: {DEFAULT_ORCHESTRATOR_MODEL}).",
    )
    parser.add_argument(
        "--prover-model",
        default=DEFAULT_PROVER_MODEL,
        help=f"Lean 4 proof-synthesis model (default: {DEFAULT_PROVER_MODEL}).",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override Ollama base URL (default: $AGY_OLLAMA_BASE_URL or $OLLAMA_HOST).",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Allow edit_file, create_file, and run_command in addition to verify_lean_module.",
    )
    parser.add_argument(
        "--no-lightweight",
        action="store_true",
        help="Disable SDK .lightweight() presets.",
    )
    return parser


def main() -> int:
    """CLI entrypoint."""
    args = build_parser().parse_args()
    repo_root = Path(__file__).resolve().parent.parent
    v1_url = normalize_v1_url(args.base_url)

    print(
        f"[+] Starting Qwen+DeepSeek orchestrator "
        f"(orchestrator={args.orchestrator_model}, prover={args.prover_model}, "
        f"base_url={v1_url}, write={args.write})"
    )
    config = build_agent_config(
        repo_root=repo_root,
        orchestrator_model=args.orchestrator_model,
        prover_model=args.prover_model,
        v1_url=v1_url,
        enable_write=args.write,
        lightweight=not args.no_lightweight,
    )
    return asyncio.run(run_orchestrator(config, args.prompt))


if __name__ == "__main__":
    raise SystemExit(main())

# end of file: leanasm/local/prover_orchestrator.py
