#!/usr/bin/env python3
# Path: leanasm/scripts/scan_openai_submission.py
"""Zero-dependency scanner for subrepos/YM/submissions/openai-20261028.

Pass A: Deterministic file manifest (MANIFEST.json, MANIFEST.md).
Pass B: Lean 4 table of contents and hygiene audit (LEAN_TOC.json, LEAN_TOC.md).
Pass C: QRH 7/8 relevance scan and portability map (QRH_7_8_CANDIDATES.md).
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import json
import logging
from pathlib import Path
import re
import sys
import textwrap
import tomllib
from typing import Any

LOG = logging.getLogger("scan_openai_submission")

MD_MAX_COL = 80
DECL_KINDS = (
    "axiom",
    "opaque",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "lemma",
    "theorem",
)

IMPORT_RE = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.]+)")
NONCOMP_SEC_RE = re.compile(r"^\s*noncomputable\s+section\b")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+([A-Za-z0-9_.]+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")
ATTR_PREFIX_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)+")
DECL_RE = re.compile(
    r"^(?P<indent>\s*)"
    r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>axiom|opaque|def|abbrev|structure|inductive|class|instance|"
    r"lemma|theorem)\b"
    r"(?P<rest>.*)$"
)
IDENT_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_.']*|\u00ab[^\u00bb]+\u00bb)")

SORRY_RE = re.compile(r"(?<!\.)\bsorry\b(?!\s*(?::|\())")
ADMIT_RE = re.compile(r"(?<!\.)\badmit\b(?!\s*(?::|\())")
CLASSICAL_RE = re.compile(r"\bClassical\b")
CLASSICAL_CHOICE_RE = re.compile(r"\bClassical\.choice\b")
NONCOMP_RE = re.compile(r"\bnoncomputable\b")
REAL_RE = re.compile(r"\bReal\b|\u211d")
COMPLEX_RE = re.compile(r"\bComplex\b|\u2102")
FILTER_RE = re.compile(r"\bFilter\b|\batTop\b|\U0001d4dd|\u2135")
ASYMPTOTICS_RE = re.compile(r"\bAsymptotics\b|\bIsBigO\b|\bIsLittleO\b")
MATHLIB_MOD_PREFIXES = ("Mathlib", "Aesop", "Batteries", "Qq", "Plausible")

CONCEPT_WEIGHTS: dict[str, int] = {
    "QuasiRiemann": 12,
    "QRH": 12,
    "zeroFree": 10,
    "zeroDensity": 10,
    "vonMangoldt": 10,
    "shortInterval": 10,
    "primeGap": 10,
    "EulerMaclaurin": 10,
    "Perron": 10,
    "criticalStrip": 10,
    "zeta": 8,
    "Chebyshev": 8,
    "mollifier": 8,
    "Mellin": 8,
    "Lipschitz": 6,
    "7/8": 7,
    "7 / 8": 7,
    "Dirichlet": 5,
    "Euler": 5,
    "3/4": 4,
    "psi": 3,
    "theta": 3,
}

WORD_TOKEN_CONCEPTS = {"psi", "theta", "zeta", "QRH"}
FRAC_PATTERNS = {
    "7/8": re.compile(r"(?:^|[^\d])7/8(?:[^\d]|$)"),
    "7 / 8": re.compile(r"(?:^|[^\d])7\s+/\s+8(?:[^\d]|$)"),
    "3/4": re.compile(r"(?:^|[^\d])3/4(?:[^\d]|$)"),
}
CAMEL_SPLIT_RE = re.compile(
    r"[A-Z]?[a-z]+|[A-Z]+(?=[A-Z][a-z]|[^A-Za-z]|$)|[0-9]+"
)

TARGET_MODULE_PRIORITY = [
    (
        "QuasiRiemann/UltraDeep72.lean",
        {"Lipschitz", "zeroFree", "7/8", "7 / 8"},
    ),
    (
        "EulerFactorNonVanishing.lean",
        {"Euler", "Dirichlet", "zeta", "EulerMaclaurin", "Perron", "Mellin"},
    ),
    (
        "QuasiRiemann/ZeroDensityBridge.lean",
        {"zeroDensity", "mollifier", "criticalStrip", "3/4"},
    ),
    (
        "QuasiRiemann/ShortIntervalPrimes.lean",
        {"shortInterval", "primeGap", "Chebyshev", "vonMangoldt", "psi", "theta"},
    ),
    (
        "QuasiRiemann.lean",
        {"QuasiRiemann", "QRH"},
    ),
]


@dataclass
class DocComment:
    """Represents a Lean 4 `/-- ... -/` docstring block."""

    start_line: int
    end_line: int
    summary: str


def categorize_file(path: Path) -> str:
    """Classify a file path into a coarse manifest category."""
    name = path.name
    ext = path.suffix.lower()
    if ext == ".lean":
        return "lean"
    if ext in {".md", ".tex", ".pdf"}:
        return "docs"
    if ext == ".txt":
        return "text"
    if ext in {".json", ".tsv"}:
        return "data"
    if ext == ".log":
        return "log"
    if ext == ".py":
        return "script"
    if ext in {".toml", ".gitignore"} or name == "lean-toolchain":
        return "config"
    if ext == ".sha256":
        return "checksum"
    if name in {"LICENSE", "NOTICE"}:
        return "license"
    if ext == ".pyc":
        return "bytecode"
    return "other"


def count_lines_bytes(data: bytes, category: str) -> int | None:
    """Count lines for text files; return None for binary files."""
    if category == "bytecode" or b"\x00" in data:
        return None
    if not data:
        return 0
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def parse_lakefile_toml(path: Path, rel_path: str) -> dict[str, Any]:
    """Parse a lakefile.toml into structured package and dependency metadata."""
    parsed = tomllib.loads(path.read_text(encoding="utf-8", errors="replace"))
    libs = [
        {
            "name": lib.get("name", ""),
            "roots": lib.get("roots", []),
        }
        for lib in parsed.get("lean_lib", [])
    ]
    reqs = [
        {
            "name": req.get("name", ""),
            "git": req.get("git", ""),
            "path": req.get("path", ""),
            "rev": req.get("rev", ""),
        }
        for req in parsed.get("require", [])
    ]
    return {
        "path": rel_path,
        "format": "toml",
        "name": parsed.get("name", ""),
        "version": parsed.get("version", ""),
        "defaultTargets": parsed.get("defaultTargets", []),
        "lean_libs": libs,
        "dependencies": reqs,
    }


def parse_lake_manifest(path: Path, rel_path: str) -> dict[str, Any]:
    """Parse a lake-manifest.json into resolved dependency entries."""
    parsed = json.loads(path.read_text(encoding="utf-8", errors="replace"))
    pkgs = [
        {
            "name": pkg.get("name", ""),
            "url": pkg.get("url", ""),
            "rev": pkg.get("rev", ""),
            "inputRev": pkg.get("inputRev", ""),
            "inherited": bool(pkg.get("inherited", False)),
        }
        for pkg in parsed.get("packages", [])
    ]
    return {
        "path": rel_path,
        "name": parsed.get("name", ""),
        "packages": pkgs,
    }


def run_pass_a(root: Path) -> dict[str, Any]:
    """Execute Pass A: deterministic manifest, toolchains, and lakefiles."""
    LOG.info("Pass A: scanning files under %s", root)
    all_files = sorted(
        (p for p in root.rglob("*") if p.is_file()),
        key=lambda p: p.relative_to(root).as_posix(),
    )
    entries: list[dict[str, Any]] = []
    toolchains: list[dict[str, str]] = []
    lakefiles: list[dict[str, Any]] = []
    lake_manifests: list[dict[str, Any]] = []
    cat_counts: Counter[str] = Counter()
    ext_counts: Counter[str] = Counter()
    top_stats: dict[str, dict[str, int]] = defaultdict(
        lambda: {"files": 0, "lean_files": 0, "bytes": 0, "lines": 0}
    )
    ym_subpkg_stats: dict[str, dict[str, int]] = defaultdict(
        lambda: {"files": 0, "lean_files": 0, "bytes": 0, "lines": 0}
    )

    total_bytes = 0
    total_lines = 0

    for path in all_files:
        rel_path = path.relative_to(root).as_posix()
        data = path.read_bytes()
        size_bytes = len(data)
        ext = path.suffix.lower()
        cat = categorize_file(path)
        line_count = count_lines_bytes(data, cat)
        sha256 = hashlib.sha256(data).hexdigest()

        top_dir = rel_path.split("/", 1)[0] if "/" in rel_path else "(root)"
        entries.append(
            {
                "path": rel_path,
                "extension": ext,
                "category": cat,
                "top_dir": top_dir,
                "size_bytes": size_bytes,
                "line_count": line_count,
                "sha256": sha256,
            }
        )

        cat_counts[cat] += 1
        ext_counts[ext or "(none)"] += 1
        total_bytes += size_bytes
        if line_count is not None:
            total_lines += line_count

        ts = top_stats[top_dir]
        ts["files"] += 1
        ts["bytes"] += size_bytes
        ts["lines"] += line_count or 0
        if cat == "lean":
            ts["lean_files"] += 1

        if rel_path.startswith("submission/YM/"):
            parts = rel_path.split("/")
            subpkg = parts[2] if len(parts) > 3 else "(YM-root)"
            ys = ym_subpkg_stats[subpkg]
            ys["files"] += 1
            ys["bytes"] += size_bytes
            ys["lines"] += line_count or 0
            if cat == "lean":
                ys["lean_files"] += 1

        if path.name == "lean-toolchain":
            ver = data.decode("utf-8", errors="replace").strip()
            toolchains.append({"path": rel_path, "version": ver})
        elif path.name == "lakefile.toml":
            lakefiles.append(parse_lakefile_toml(path, rel_path))
        elif path.name == "lakefile.lean":
            lakefiles.append({"path": rel_path, "format": "lean"})
        elif path.name == "lake-manifest.json":
            lake_manifests.append(parse_lake_manifest(path, rel_path))

    LOG.info("Pass A complete: %d files (%d bytes)", len(entries), total_bytes)
    return {
        "root": root.as_posix(),
        "total_files": len(entries),
        "total_bytes": total_bytes,
        "total_lines": total_lines,
        "toolchains": toolchains,
        "lakefiles": lakefiles,
        "lake_manifests": lake_manifests,
        "counts_by_category": dict(sorted(cat_counts.items())),
        "counts_by_extension": dict(sorted(ext_counts.items())),
        "top_dir_summary": {k: top_stats[k] for k in sorted(top_stats)},
        "submission_ym_summary": {
            k: ym_subpkg_stats[k] for k in sorted(ym_subpkg_stats)
        },
        "files": entries,
    }


def strip_lean_comments_and_strings(
    text: str,
) -> tuple[str, str, list[DocComment]]:
    """Strip Lean 4 `--` and nested `/- ... -/` comments preserving newlines.

    Returns (code_with_strings, code_no_strings, doc_comments).
    """
    n = len(text)
    with_str: list[str] = []
    no_str: list[str] = []
    docs: list[DocComment] = []

    i = 0
    line = 1
    while i < n:
        ch = text[i]
        # Line comment `--`
        if ch == "-" and i + 1 < n and text[i + 1] == "-":
            while i < n and text[i] != "\n":
                with_str.append(" ")
                no_str.append(" ")
                i += 1
            continue

        # Block comment `/- ... -/` (supports nesting)
        if ch == "/" and i + 1 < n and text[i + 1] == "-":
            is_doc = (
                i + 2 < n and text[i + 2] == "-" and (i + 3 >= n or text[i + 3] != "-")
            )
            start_line = line
            doc_chars: list[str] = []
            depth = 1
            with_str.extend((" ", " "))
            no_str.extend((" ", " "))
            i += 2
            if is_doc and i < n and text[i] == "-":
                with_str.append(" ")
                no_str.append(" ")
                i += 1
            while i < n and depth > 0:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    with_str.extend((" ", " "))
                    no_str.extend((" ", " "))
                    if is_doc:
                        doc_chars.append("/-")
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    with_str.extend((" ", " "))
                    no_str.extend((" ", " "))
                    if is_doc and depth > 0:
                        doc_chars.append("-/")
                    i += 2
                else:
                    c = text[i]
                    if c == "\n":
                        line += 1
                        with_str.append("\n")
                        no_str.append("\n")
                    else:
                        with_str.append(" ")
                        no_str.append(" ")
                    if is_doc:
                        doc_chars.append(c)
                    i += 1
            if is_doc:
                raw_doc = "".join(doc_chars)
                cleaned = re.sub(r"\s+", " ", raw_doc).strip(" -*\t")
                if len(cleaned) > 160:
                    cleaned = cleaned[:157].rstrip() + "..."
                docs.append(DocComment(start_line, line, cleaned))
            continue

        # String literal `"..."`
        if ch == '"':
            with_str.append('"')
            no_str.append('"')
            i += 1
            while i < n:
                c = text[i]
                with_str.append(c)
                if c == "\n":
                    line += 1
                    no_str.append("\n")
                else:
                    no_str.append(" ")
                i += 1
                if c == "\\" and i < n:
                    esc = text[i]
                    with_str.append(esc)
                    if esc == "\n":
                        line += 1
                        no_str.append("\n")
                    else:
                        no_str.append(" ")
                    i += 1
                    continue
                if c == '"':
                    break
            continue

        # Char literal `'x'` or `'\n'` only when not a prime on identifier
        if ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")
        ):
            if i + 2 < n and text[i + 1] != "\\" and text[i + 2] == "'" and text[i + 1] != "\n":
                with_str.extend(("'", text[i + 1], "'"))
                no_str.extend(("'", " ", "'"))
                i += 3
                continue
            if i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'" and text[i + 2] != "\n":
                with_str.extend(("'", "\\", text[i + 2], "'"))
                no_str.extend(("'", " ", " ", "'"))
                i += 4
                continue

        with_str.append(ch)
        no_str.append(ch)
        if ch == "\n":
            line += 1
        i += 1

    return "".join(with_str), "".join(no_str), docs


def split_top_level_assign(sig: str) -> str:
    """Split signature at top-level `:=` or `where`, ignoring `(n:=n)` args."""
    depth = 0
    n = len(sig)
    i = 0
    while i < n:
        ch = sig[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}" and depth > 0:
            depth -= 1
        elif depth == 0:
            if sig[i : i + 2] == ":=":
                return sig[:i].strip()
            if (
                sig[i : i + 5] == "where"
                and (i == 0 or not sig[i - 1].isalnum())
                and (i + 5 == n or not sig[i + 5].isalnum())
            ):
                return sig[:i].strip()
        i += 1
    return sig.strip()


def extract_signature(lines_with_str: list[str], start_idx: int) -> str:
    """Extract a concise single-line declaration signature header."""
    chunks: list[str] = []
    limit = min(start_idx + 6, len(lines_with_str))
    for j in range(start_idx, limit):
        ln = lines_with_str[j].strip()
        if not ln and j > start_idx:
            break
        if j > start_idx and DECL_RE.match(ATTR_PREFIX_RE.sub("", lines_with_str[j])):
            break
        chunks.append(ln)
        joined_so_far = " ".join(chunks)
        if split_top_level_assign(joined_so_far) != joined_so_far.strip():
            break
    joined = re.sub(r"\s+", " ", " ".join(chunks)).strip()
    joined = split_top_level_assign(joined)
    if len(joined) > 220:
        joined = joined[:217].rstrip() + "..."
    return joined


def find_preceding_doc(
    docs: list[DocComment],
    lines_no_str: list[str],
    decl_line: int,
    last_boundary_line: int,
) -> str | None:
    """Return docstring summary immediately preceding decl_line if valid."""
    for doc in reversed(docs):
        if doc.end_line >= decl_line:
            continue
        if doc.end_line <= last_boundary_line:
            return None
        gap_ok = True
        for ln_no in range(doc.end_line + 1, decl_line):
            stripped = lines_no_str[ln_no - 1].strip()
            if not stripped:
                continue
            if stripped.startswith("@[") and stripped.endswith("]"):
                continue
            gap_ok = False
            break
        if gap_ok and doc.summary:
            return doc.summary
        return None
    return None


def parse_lean_file(path: Path, rel_path: str) -> dict[str, Any]:
    """Parse one Lean file for imports, scopes, declarations, and hygiene."""
    text = path.read_text(encoding="utf-8", errors="replace")
    code_with_str, code_no_str, docs = strip_lean_comments_and_strings(text)
    lines_ws = code_with_str.splitlines()
    lines_ns = code_no_str.splitlines()

    imports: list[str] = []
    scopes_seen: list[str] = []
    scope_stack: list[tuple[str, str]] = []
    declarations: list[dict[str, Any]] = []

    has_noncomp_section = False
    last_boundary_line = 0
    in_attr_block = False

    for idx, line_ns in enumerate(lines_ns):
        line_no = idx + 1
        stripped = line_ns.strip()
        if not stripped:
            continue

        imp_m = IMPORT_RE.match(line_ns)
        if imp_m:
            imports.append(imp_m.group(1))
            last_boundary_line = line_no
            continue

        if NONCOMP_SEC_RE.match(line_ns):
            has_noncomp_section = True
            last_boundary_line = line_no
            continue

        ns_m = NAMESPACE_RE.match(line_ns)
        if ns_m:
            ns_name = ns_m.group(1)
            scope_stack.append(("namespace", ns_name))
            scopes_seen.append(f"namespace {ns_name}")
            last_boundary_line = line_no
            continue

        sec_m = SECTION_RE.match(line_ns)
        if sec_m:
            sec_name = sec_m.group(1) or "<anon>"
            scope_stack.append(("section", sec_name))
            scopes_seen.append(f"section {sec_name}")
            last_boundary_line = line_no
            continue

        end_m = END_RE.match(line_ns)
        if end_m:
            target = end_m.group(1)
            if scope_stack:
                if target is None:
                    scope_stack.pop()
                else:
                    for k in range(len(scope_stack) - 1, -1, -1):
                        if scope_stack[k][1] == target:
                            del scope_stack[k:]
                            break
            last_boundary_line = line_no
            continue

        # Track multi-line @[...] attributes
        if in_attr_block:
            if "]" in stripped:
                in_attr_block = False
            continue
        if stripped.startswith("@[") and "]" not in stripped:
            in_attr_block = True
            continue

        candidate = ATTR_PREFIX_RE.sub("", line_ns)
        decl_m = DECL_RE.match(candidate)
        if not decl_m:
            continue

        indent = len(decl_m.group("indent"))
        if indent > 6:
            continue

        mods = decl_m.group("mods").strip().split()
        kind = decl_m.group("kind")
        rest = decl_m.group("rest")

        if kind == "instance":
            rest_strip = rest.lstrip()
            if rest_strip and rest_strip[0] in ":({[":
                decl_name = "<anonymous_instance>"
            else:
                id_m = IDENT_RE.match(rest)
                decl_name = id_m.group(1) if id_m else "<anonymous_instance>"
        else:
            id_m = IDENT_RE.match(rest)
            if not id_m:
                continue
            decl_name = id_m.group(1)

        ns_parts = [name for stype, name in scope_stack if stype == "namespace"]
        ns_path = ".".join(ns_parts) if ns_parts else "(root)"
        full_name = f"{ns_path}.{decl_name}" if ns_parts else decl_name
        sig = extract_signature(lines_ws, idx)
        doc_summary = find_preceding_doc(docs, lines_ns, line_no, last_boundary_line)

        declarations.append(
            {
                "kind": kind,
                "name": decl_name,
                "full_name": full_name,
                "namespace": ns_path,
                "line": line_no,
                "end_line": len(lines_ns),
                "modifiers": mods,
                "signature": sig,
                "docstring": doc_summary,
            }
        )
        last_boundary_line = line_no

    # Fill end_line of each declaration up to next declaration
    for i in range(len(declarations) - 1):
        declarations[i]["end_line"] = max(
            declarations[i]["line"], declarations[i + 1]["line"] - 1
        )

    # Hygiene audit on code_no_strings
    sorry_lines: list[int] = []
    admit_lines: list[int] = []
    for idx, ln in enumerate(lines_ns, start=1):
        if SORRY_RE.search(ln):
            sorry_lines.append(idx)
        if ADMIT_RE.search(ln):
            admit_lines.append(idx)

    custom_axioms = [
        {"name": d["full_name"], "line": d["line"]}
        for d in declarations
        if d["kind"] == "axiom"
    ]
    noncomp_decls = [
        d["full_name"] for d in declarations if "noncomputable" in d["modifiers"]
    ]
    uses_classical = bool(CLASSICAL_RE.search(code_no_str))
    uses_classical_choice = bool(CLASSICAL_CHOICE_RE.search(code_no_str))
    uses_noncomp = has_noncomp_section or bool(NONCOMP_RE.search(code_no_str))
    uses_real = bool(REAL_RE.search(code_no_str))
    uses_complex = bool(COMPLEX_RE.search(code_no_str))
    uses_filter = bool(FILTER_RE.search(code_no_str))
    uses_asymptotics = bool(ASYMPTOTICS_RE.search(code_no_str))
    mathlib_imports = [
        imp for imp in imports if imp.split(".", 1)[0] in MATHLIB_MOD_PREFIXES
    ]

    pure_constructive = (
        not custom_axioms
        and not sorry_lines
        and not admit_lines
        and not uses_classical
        and not uses_noncomp
        and not uses_real
        and not uses_complex
        and not uses_filter
        and not uses_asymptotics
        and not mathlib_imports
    )

    # Per-declaration body snippet analysis (kept transient or lightweight)
    for d in declarations:
        s_idx = d["line"] - 1
        e_idx = d["end_line"]
        d_body = "\n".join(lines_ns[s_idx:e_idx])
        d["_has_sorry_or_admit"] = bool(
            SORRY_RE.search(d_body) or ADMIT_RE.search(d_body)
        )
        d["_uses_analysis"] = bool(
            REAL_RE.search(d_body)
            or COMPLEX_RE.search(d_body)
            or FILTER_RE.search(d_body)
            or ASYMPTOTICS_RE.search(d_body)
            or NONCOMP_RE.search(d_body)
            or CLASSICAL_RE.search(d_body)
        )
        d["_body_text"] = "\n".join(lines_ws[s_idx:e_idx])

    hygiene = {
        "custom_axioms": custom_axioms,
        "sorry_lines": sorry_lines,
        "admit_lines": admit_lines,
        "has_noncomputable_section": has_noncomp_section,
        "noncomputable_decls": noncomp_decls,
        "uses_noncomputable": uses_noncomp,
        "uses_classical": uses_classical,
        "uses_classical_choice": uses_classical_choice,
        "uses_real": uses_real,
        "uses_complex": uses_complex,
        "uses_filter": uses_filter,
        "uses_asymptotics": uses_asymptotics,
        "mathlib_imports": mathlib_imports,
        "leanasm_pure_constructive": pure_constructive,
    }

    return {
        "path": rel_path,
        "line_count": len(lines_ns),
        "imports": imports,
        "scopes": scopes_seen,
        "declarations": declarations,
        "hygiene": hygiene,
    }


def run_pass_b(root: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    """Execute Pass B across all `.lean` files in the manifest."""
    lean_entries = [f for f in manifest["files"] if f["category"] == "lean"]
    LOG.info("Pass B: parsing %d Lean files", len(lean_entries))
    files_data: list[dict[str, Any]] = []
    decl_kind_counts: Counter[str] = Counter()
    blocker_counts: Counter[str] = Counter()

    for idx, entry in enumerate(lean_entries, start=1):
        rel_path = entry["path"]
        parsed = parse_lean_file(root / rel_path, rel_path)
        files_data.append(parsed)
        for d in parsed["declarations"]:
            decl_kind_counts[d["kind"]] += 1
        hyg = parsed["hygiene"]
        if hyg["custom_axioms"]:
            blocker_counts["files_with_custom_axioms"] += 1
        if hyg["sorry_lines"]:
            blocker_counts["files_with_sorry"] += 1
        if hyg["admit_lines"]:
            blocker_counts["files_with_admit"] += 1
        if hyg["uses_classical"] or hyg["uses_noncomputable"]:
            blocker_counts["files_with_classical_or_noncomputable"] += 1
        if hyg["uses_classical_choice"]:
            blocker_counts["files_with_classical_choice"] += 1
        if (
            hyg["uses_real"]
            or hyg["uses_complex"]
            or hyg["uses_filter"]
            or hyg["uses_asymptotics"]
        ):
            blocker_counts["files_with_real_complex_filter_asymptotics"] += 1
        if hyg["mathlib_imports"]:
            blocker_counts["files_with_mathlib_imports"] += 1
        if hyg["leanasm_pure_constructive"]:
            blocker_counts["files_pure_constructive"] += 1
        if idx % 2000 == 0:
            LOG.info("Pass B progress: %d / %d files", idx, len(lean_entries))

    LOG.info(
        "Pass B complete: %d files, %d declarations",
        len(files_data),
        sum(decl_kind_counts.values()),
    )
    return {
        "total_lean_files": len(files_data),
        "total_declarations": sum(decl_kind_counts.values()),
        "declaration_counts_by_kind": dict(sorted(decl_kind_counts.items())),
        "hygiene_summary": dict(sorted(blocker_counts.items())),
        "files": files_data,
    }


def match_concepts(text: str) -> set[str]:
    """Return matched QRH 7/8 concepts in text without substring false hits."""
    if not text:
        return set()
    matched: set[str] = set()
    lower = text.lower()

    for frac, pat in FRAC_PATTERNS.items():
        if pat.search(text):
            matched.add(frac)

    tokens = {tok.lower() for tok in CAMEL_SPLIT_RE.findall(text)}
    for concept in CONCEPT_WEIGHTS:
        if concept in FRAC_PATTERNS:
            continue
        c_low = concept.lower()
        if concept in WORD_TOKEN_CONCEPTS:
            if c_low in tokens:
                matched.add(concept)
        else:
            if c_low in lower:
                matched.add(concept)
    return matched


def map_target_module(concepts: set[str]) -> str:
    """Map matched QRH concepts to the best target module in leanasm."""
    best_mod = "QuasiRiemann.lean"
    best_score = -1
    for mod, mod_concepts in TARGET_MODULE_PRIORITY:
        overlap = concepts & mod_concepts
        score = sum(CONCEPT_WEIGHTS[c] for c in overlap)
        if score > best_score:
            best_score = score
            best_mod = mod
    return best_mod


def classify_portability(
    decl: dict[str, Any], file_hyg: dict[str, Any]
) -> str:
    """Classify declaration into direct port, cleared-denom, or blocked."""
    if (
        decl["kind"] == "axiom"
        or decl.get("_has_sorry_or_admit")
        or file_hyg["custom_axioms"]
        or file_hyg["sorry_lines"]
        or file_hyg["admit_lines"]
    ):
        return "AXIOM_OR_SORRY_BLOCKED"
    if file_hyg["leanasm_pure_constructive"] or (
        not decl.get("_uses_analysis")
        and not file_hyg["uses_real"]
        and not file_hyg["uses_complex"]
        and not file_hyg["uses_filter"]
        and not file_hyg["uses_asymptotics"]
        and not file_hyg["uses_classical"]
        and not file_hyg["uses_noncomputable"]
        and not file_hyg["mathlib_imports"]
    ):
        return "DIRECT_CONSTRUCTIVE_PORT"
    return "CLEARED_DENOMINATOR_ADAPTATION"


def run_pass_c(toc: dict[str, Any]) -> dict[str, Any]:
    """Execute Pass C: score, map, and classify QRH 7/8 candidate declarations."""
    LOG.info("Pass C: scoring QRH 7/8 candidate declarations")
    candidates: list[dict[str, Any]] = []
    class_counts: Counter[str] = Counter()
    target_counts: Counter[str] = Counter()

    for fdata in toc["files"]:
        rel_path = fdata["path"]
        hyg = fdata["hygiene"]
        for d in fdata["declarations"]:
            name_hits = match_concepts(d["full_name"])
            doc_hits = match_concepts(d.get("docstring") or "")
            sig_hits = match_concepts(d["signature"])
            body_hits = match_concepts(d.get("_body_text") or "")

            all_hits = name_hits | doc_hits | sig_hits | body_hits
            if not all_hits:
                continue

            score = (
                sum(CONCEPT_WEIGHTS[c] * 3 for c in name_hits)
                + sum(CONCEPT_WEIGHTS[c] * 2 for c in doc_hits)
                + sum(CONCEPT_WEIGHTS[c] * 2 for c in sig_hits)
                + sum(CONCEPT_WEIGHTS[c] for c in body_hits)
            )
            if d["kind"] in ("theorem", "lemma"):
                score += 4
            elif d["kind"] in ("def", "structure"):
                score += 2

            portability = classify_portability(d, hyg)
            target_mod = map_target_module(all_hits)

            class_counts[portability] += 1
            target_counts[target_mod] += 1

            candidates.append(
                {
                    "score": score,
                    "path": rel_path,
                    "line": d["line"],
                    "kind": d["kind"],
                    "full_name": d["full_name"],
                    "target_module": target_mod,
                    "classification": portability,
                    "concepts": sorted(all_hits),
                    "name_concepts": sorted(name_hits),
                    "signature": d["signature"],
                    "docstring": d.get("docstring"),
                }
            )

    candidates.sort(
        key=lambda c: (-c["score"], c["path"], c["line"], c["full_name"])
    )
    LOG.info("Pass C complete: %d matching declarations", len(candidates))
    return {
        "total_candidates": len(candidates),
        "classification_counts": dict(sorted(class_counts.items())),
        "target_module_counts": dict(sorted(target_counts.items())),
        "candidates": candidates,
    }


def strip_transient_fields(toc: dict[str, Any]) -> dict[str, Any]:
    """Remove transient body text fields before serializing LEAN_TOC.json."""
    cleaned_files = []
    for fdata in toc["files"]:
        decls = []
        for d in fdata["declarations"]:
            decls.append(
                {k: v for k, v in d.items() if not k.startswith("_")}
            )
        cleaned_files.append(
            {
                "path": fdata["path"],
                "line_count": fdata["line_count"],
                "imports": fdata["imports"],
                "scopes": fdata["scopes"],
                "declarations": decls,
                "hygiene": fdata["hygiene"],
            }
        )
    out = dict(toc)
    out["files"] = cleaned_files
    return out


def wrap_text_lines(
    text: str,
    width: int = MD_MAX_COL,
    indent: str = "",
    sub_indent: str | None = None,
) -> list[str]:
    """Wrap prose to at most `width` columns, breaking overlong tokens at `/`."""
    sub = indent if sub_indent is None else sub_indent
    wrapper = textwrap.TextWrapper(
        width=width,
        initial_indent=indent,
        subsequent_indent=sub,
        break_long_words=False,
        break_on_hyphens=False,
    )
    out: list[str] = []
    for raw_line in wrapper.wrap(text):
        if len(raw_line) <= width:
            out.append(raw_line)
        else:
            out.extend(_force_wrap_long_line(raw_line, width, sub))
    return out or [indent.rstrip()]


def _force_wrap_long_line(line: str, width: int, indent: str) -> list[str]:
    """Split a line exceeding `width` cleanly at `/` or hard boundaries."""
    res: list[str] = []
    cur = line
    while len(cur) > width:
        cut = cur.rfind(" ", 0, width + 1)
        if cut <= len(indent):
            cut = cur.rfind("/", 0, width)
            if cut > len(indent):
                cut += 1
        if cut <= len(indent):
            cut = width
        res.append(cur[:cut].rstrip())
        cur = indent + cur[cut:].lstrip()
    if cur:
        res.append(cur)
    return res


def format_kv_bullets(items: list[tuple[str, str]], width: int = MD_MAX_COL) -> list[str]:
    """Format `- **Key**: Value` lines wrapped cleanly within `width`."""
    lines: list[str] = []
    for key, val in items:
        prefix = f"- **{key}**: "
        sub = "  "
        wrapper = textwrap.TextWrapper(
            width=width,
            initial_indent=prefix,
            subsequent_indent=sub,
            break_long_words=False,
            break_on_hyphens=False,
        )
        wrapped = wrapper.wrap(val)
        if not wrapped:
            lines.append(prefix.rstrip())
        else:
            for w in wrapped:
                if len(w) <= width:
                    lines.append(w)
                else:
                    lines.extend(_force_wrap_long_line(w, width, sub))
    return lines


def format_md_table(
    headers: list[str], rows: list[list[str]], max_col: int = MD_MAX_COL
) -> list[str]:
    """Render a compact Markdown table guaranteed <= `max_col` chars per line."""
    ncols = len(headers)
    # Budget: `| ` + cols joined by ` | ` + ` |` => overhead = 3*ncols + 1
    overhead = 3 * ncols + 1
    avail = max(ncols * 4, max_col - overhead)
    widths = [len(h) for h in headers]
    for r in rows:
        for i, cell in enumerate(r):
            widths[i] = max(widths[i], len(cell))
    total = sum(widths)
    if total > avail:
        # Shrink widest columns proportionally while keeping min width 4
        while sum(widths) > avail:
            idx = max(range(ncols), key=lambda i: widths[i])
            if widths[idx] <= 4:
                break
            widths[idx] -= 1

    def clip(val: str, w: int) -> str:
        if len(val) <= w:
            return val.ljust(w)
        return (val[: max(1, w - 3)] + "...")[:w].ljust(w)

    lines = [
        "| " + " | ".join(clip(h, widths[i]) for i, h in enumerate(headers)) + " |",
        "| " + " | ".join("-" * widths[i] for i in range(ncols)) + " |",
    ]
    for r in rows:
        lines.append(
            "| " + " | ".join(clip(r[i], widths[i]) for i in range(ncols)) + " |"
        )
    return lines


def write_checked_markdown(path: Path, rel_repo_path: str, body_lines: list[str]) -> None:
    """Write Markdown with AI.md headers/footers and verify <= 80 columns."""
    header = [
        f"<!-- Path: {rel_repo_path} -->",
        f"<!-- Max Column: {MD_MAX_COL} Columns -->",
        "",
    ]
    footer = [
        "",
        f"<!-- end of file: {rel_repo_path} -->",
    ]
    all_lines = header + body_lines + footer
    final_lines: list[str] = []
    for ln in all_lines:
        if len(ln) <= MD_MAX_COL:
            final_lines.append(ln)
        else:
            final_lines.extend(_force_wrap_long_line(ln, MD_MAX_COL, ""))

    for idx, ln in enumerate(final_lines, start=1):
        if len(ln) > MD_MAX_COL:
            raise ValueError(
                f"{rel_repo_path}:{idx} exceeds {MD_MAX_COL} cols ({len(ln)})"
            )
    path.write_text("\n".join(final_lines) + "\n", encoding="utf-8")


def render_manifest_md(manifest: dict[str, Any]) -> list[str]:
    """Render Pass A MANIFEST.md body lines."""
    lines: list[str] = [
        "# OpenAI 2026-10-28 YM Submission Manifest",
        "",
        "## 1. Corpus Overview",
        "",
    ]
    lines.extend(
        format_kv_bullets(
            [
                ("Root", manifest["root"]),
                ("Total Files", f"{manifest['total_files']:,}"),
                ("Total Bytes", f"{manifest['total_bytes']:,}"),
                ("Total Lines", f"{manifest['total_lines']:,}"),
                ("Full Digests", "See `MANIFEST.json` for all SHA-256 hashes."),
            ]
        )
    )
    lines.extend(["", "## 2. Lean Toolchains & Lake Dependencies", ""])
    for tc in manifest["toolchains"]:
        lines.extend(
            wrap_text_lines(
                f"- `{tc['path']}`: `{tc['version']}`", sub_indent="  "
            )
        )
    for lf in manifest["lakefiles"]:
        if lf.get("format") == "toml":
            targets = ", ".join(lf.get("defaultTargets", [])) or "(none)"
            lines.extend(
                format_kv_bullets(
                    [(lf["path"], f"{lf['name']} v{lf['version']}; targets: {targets}")]
                )
            )
            for dep in lf.get("dependencies", []):
                lines.extend(
                    format_kv_bullets(
                        [
                            (
                                f"dep `{dep['name']}`",
                                f"{dep.get('git') or dep.get('path')} "
                                f"@ {dep.get('rev', '')[:12]}",
                            )
                        ]
                    )
                )
    for lm in manifest["lake_manifests"]:
        lines.extend(["", f"### Lake Manifest: `{lm['path']}`", ""])
        pkg_rows = [
            [p["name"], p["inputRev"], p["rev"][:12]]
            for p in lm.get("packages", [])
        ]
        lines.extend(format_md_table(["Package", "InputRev", "RevPrefix"], pkg_rows))

    lines.extend(["", "## 3. Counts by Category & Top Directory", ""])
    cat_rows = [[k, str(v)] for k, v in manifest["counts_by_category"].items()]
    lines.extend(format_md_table(["Category", "Files"], cat_rows))
    lines.append("")
    top_rows = [
        [
            k,
            str(v["files"]),
            str(v["lean_files"]),
            f"{v['bytes']:,}",
            f"{v['lines']:,}",
        ]
        for k, v in manifest["top_dir_summary"].items()
    ]
    lines.extend(
        format_md_table(["TopDir", "Files", "Lean", "Bytes", "Lines"], top_rows)
    )

    lines.extend(["", "## 4. `submission/YM` Subpackage Breakdown", ""])
    ym_rows = [
        [k, str(v["files"]), str(v["lean_files"]), f"{v['lines']:,}"]
        for k, v in manifest["submission_ym_summary"].items()
    ]
    lines.extend(format_md_table(["Subpkg", "Files", "Lean", "Lines"], ym_rows))

    lines.extend(["", "## 5. Non-`submission/YM` File Digest Sample", ""])
    lines.extend(
        wrap_text_lines(
            "All files outside `submission/YM/` (and root `submission/*.lean` "
            "files) are listed below with size, lines, and 12-char SHA-256 "
            "prefixes. Full 64-char digests for all files reside in `MANIFEST.json`."
        )
    )
    lines.append("")
    key_files = [
        f
        for f in manifest["files"]
        if not f["path"].startswith("submission/YM/")
        and not f["path"].startswith("evidence/historical/")
    ]
    for f in key_files:
        lc = str(f["line_count"]) if f["line_count"] is not None else "bin"
        lines.extend(
            wrap_text_lines(
                f"- `{f['path']}` ({f['category']}, {f['size_bytes']} B, "
                f"{lc} L, sha256:{f['sha256'][:12]})",
                indent="",
            )
        )
    return lines


def render_lean_toc_md(toc: dict[str, Any]) -> list[str]:
    """Render Pass B LEAN_TOC.md body lines."""
    hyg = toc["hygiene_summary"]
    lines: list[str] = [
        "# OpenAI 2026-10-28 Lean 4 Proof Table of Contents & Hygiene Audit",
        "",
        "## 1. Corpus & Declaration Totals",
        "",
    ]
    lines.extend(
        format_kv_bullets(
            [
                ("Total Lean Files", f"{toc['total_lean_files']:,}"),
                ("Total Declarations", f"{toc['total_declarations']:,}"),
                (
                    "Full AST/TOC JSON",
                    "See `LEAN_TOC.json` for every file, import, scope, and decl.",
                ),
            ]
        )
    )
    lines.extend(["", "### Declarations by Kind", ""])
    kind_rows = [
        [k, f"{v:,}"] for k, v in toc["declaration_counts_by_kind"].items()
    ]
    lines.extend(format_md_table(["Kind", "Count"], kind_rows))

    lines.extend(["", "## 2. `leanasm` Compatibility Hygiene Audit", ""])
    hyg_rows = [
        ["Custom `axiom` decls", str(hyg.get("files_with_custom_axioms", 0))],
        ["Uses `sorry`", str(hyg.get("files_with_sorry", 0))],
        ["Uses `admit`", str(hyg.get("files_with_admit", 0))],
        [
            "Classical / noncomputable",
            str(hyg.get("files_with_classical_or_noncomputable", 0)),
        ],
        ["Explicit `Classical.choice`", str(hyg.get("files_with_classical_choice", 0))],
        [
            "Real/Complex/Filter/Asymp",
            str(hyg.get("files_with_real_complex_filter_asymptotics", 0)),
        ],
        ["Mathlib/Std-ext imports", str(hyg.get("files_with_mathlib_imports", 0))],
        ["Pure constructive files", str(hyg.get("files_pure_constructive", 0))],
    ]
    lines.extend(format_md_table(["Audit Check", "Files"], hyg_rows))

    # Enumerate exact axiom & sorry files
    axiom_files = [f for f in toc["files"] if f["hygiene"]["custom_axioms"]]
    sorry_files = [f for f in toc["files"] if f["hygiene"]["sorry_lines"]]
    admit_files = [f for f in toc["files"] if f["hygiene"]["admit_lines"]]
    pure_files = [
        f for f in toc["files"] if f["hygiene"]["leanasm_pure_constructive"]
    ]

    lines.extend(["", "### Files with Custom Axioms", ""])
    if axiom_files:
        for f in axiom_files:
            axs = ", ".join(
                f"{a['name']}@L{a['line']}" for a in f["hygiene"]["custom_axioms"]
            )
            lines.extend(wrap_text_lines(f"- `{f['path']}`: {axs}"))
    else:
        lines.append("- None detected.")

    lines.extend(["", "### Files with `sorry` or `admit`", ""])
    if sorry_files or admit_files:
        for f in sorry_files:
            lns = ",".join(str(x) for x in f["hygiene"]["sorry_lines"])
            lines.extend(wrap_text_lines(f"- `{f['path']}` sorry @ L{lns}"))
        for f in admit_files:
            lns = ",".join(str(x) for x in f["hygiene"]["admit_lines"])
            lines.extend(wrap_text_lines(f"- `{f['path']}` admit @ L{lns}"))
    else:
        lines.append("- None detected.")

    lines.extend(["", "### Pure Constructive Files (Zero Mathlib/Real/Complex/Sorry)", ""])
    if pure_files:
        for f in pure_files[:40]:
            lines.extend(
                wrap_text_lines(
                    f"- `{f['path']}` ({len(f['declarations'])} decls)"
                )
            )
        if len(pure_files) > 40:
            lines.append(f"- ... and {len(pure_files) - 40} more in `LEAN_TOC.json`.")
    else:
        lines.append("- None detected.")

    lines.extend(["", "## 3. Root, Checks, Docs & Verification TOC", ""])
    key_lean = [
        f
        for f in toc["files"]
        if not f["path"].startswith("submission/YM/")
    ]
    for f in key_lean:
        hyg_tags: list[str] = []
        fh = f["hygiene"]
        if fh["custom_axioms"]:
            hyg_tags.append("AXIOM")
        if fh["sorry_lines"]:
            hyg_tags.append("SORRY")
        if fh["uses_noncomputable"] or fh["uses_classical"]:
            hyg_tags.append("noncomp/Classical")
        if fh["uses_real"] or fh["uses_complex"]:
            hyg_tags.append("Real/Complex")
        if fh["leanasm_pure_constructive"]:
            hyg_tags.append("PURE")
        tag_str = ", ".join(hyg_tags) if hyg_tags else "clean-types"
        decls = f["declarations"]
        imps = ", ".join(f["imports"][:4])
        if len(f["imports"]) > 4:
            imps += f" (+{len(f['imports']) - 4})"
        lines.extend(
            wrap_text_lines(
                f"- `{f['path']}` ({f['line_count']}L, {len(decls)} decls, "
                f"[{tag_str}]) imports: {imps or '(none)'}"
            )
        )
        for d in decls[:5]:
            doc = f" -- {d['docstring']}" if d.get("docstring") else ""
            lines.extend(
                wrap_text_lines(
                    f"  - L{d['line']} `{d['kind']} {d['full_name']}`{doc}",
                    indent="  ",
                )
            )
        if len(decls) > 5:
            lines.append(f"  - ... ({len(decls) - 5} more decls in `LEAN_TOC.json`)")

    lines.extend(["", "## 4. `submission/YM` Subpackage TOC Summary", ""])
    ym_agg: dict[str, dict[str, int]] = defaultdict(
        lambda: {"files": 0, "thms": 0, "defs": 0, "sorry": 0, "pure": 0}
    )
    for f in toc["files"]:
        if not f["path"].startswith("submission/YM/"):
            continue
        parts = f["path"].split("/")
        sub = parts[2] if len(parts) > 3 else "(YM-root)"
        agg = ym_agg[sub]
        agg["files"] += 1
        for d in f["declarations"]:
            if d["kind"] in ("theorem", "lemma"):
                agg["thms"] += 1
            else:
                agg["defs"] += 1
        if f["hygiene"]["sorry_lines"] or f["hygiene"]["admit_lines"]:
            agg["sorry"] += 1
        if f["hygiene"]["leanasm_pure_constructive"]:
            agg["pure"] += 1

    ym_rows = [
        [
            k,
            str(v["files"]),
            str(v["thms"]),
            str(v["defs"]),
            str(v["sorry"]),
            str(v["pure"]),
        ]
        for k, v in sorted(ym_agg.items())
    ]
    lines.extend(
        format_md_table(
            ["Subpkg", "Files", "Thm/Lem", "Other", "Sorry", "Pure"], ym_rows
        )
    )
    return lines


def render_qrh_candidates_md(report: dict[str, Any]) -> list[str]:
    """Render Pass C QRH_7_8_CANDIDATES.md body lines."""
    lines: list[str] = [
        "# QRH 7/8 Relevance Scan & Portability Candidates",
        "",
        "## 1. Summary & Classification Breakdown",
        "",
    ]
    lines.extend(
        format_kv_bullets(
            [
                ("Total Matched Decls", f"{report['total_candidates']:,}"),
                (
                    "Concepts Scanned",
                    ", ".join(sorted(CONCEPT_WEIGHTS.keys())),
                ),
            ]
        )
    )
    lines.extend(["", "### By Portability Classification", ""])
    cls_rows = [
        [k, f"{v:,}"] for k, v in report["classification_counts"].items()
    ]
    lines.extend(format_md_table(["Classification", "Count"], cls_rows))

    lines.extend(["", "### By Target `leanasm` Module", ""])
    tgt_rows = [
        [k, f"{v:,}"] for k, v in report["target_module_counts"].items()
    ]
    lines.extend(format_md_table(["Target Module", "Count"], tgt_rows))

    cands = report["candidates"]
    direct = [c for c in cands if c["classification"] == "DIRECT_CONSTRUCTIVE_PORT"]
    cleared = [
        c for c in cands if c["classification"] == "CLEARED_DENOMINATOR_ADAPTATION"
    ]
    blocked = [c for c in cands if c["classification"] == "AXIOM_OR_SORRY_BLOCKED"]

    sections = [
        ("2. Top Overall QRH 7/8 Candidates (Top 60)", cands[:60]),
        ("3. Direct Constructive Port Candidates (Top 30)", direct[:30]),
        ("4. Cleared-Denominator Adaptation Candidates (Top 40)", cleared[:40]),
        ("5. Axiom- or Sorry-Blocked Candidates (Top 20)", blocked[:20]),
    ]
    for heading, subset in sections:
        lines.extend(["", f"## {heading}", ""])
        if not subset:
            lines.append("- None found.")
            continue
        for rank, c in enumerate(subset, start=1):
            concepts = ", ".join(c["concepts"])
            lines.extend(
                wrap_text_lines(
                    f"{rank}. **[score={c['score']}]** `{c['kind']} {c['full_name']}` "
                    f"(`{c['path']}:{c['line']}`)"
                )
            )
            lines.extend(
                format_kv_bullets(
                    [
                        ("Class", c["classification"]),
                        ("Target", f"`src/LeanAsm/{c['target_module']}`"),
                        ("Concepts", concepts),
                        ("Signature", f"`{c['signature']}`"),
                    ]
                )
            )
            if c.get("docstring"):
                lines.extend(
                    format_kv_bullets([("Docstring", c["docstring"])])
                )

    lines.extend(["", "## 6. Target-Module & 7/8 Exponent Highlights", ""])
    for target_mod, _ in TARGET_MODULE_PRIORITY:
        mod_cands = [c for c in cands if c["target_module"] == target_mod][:10]
        if not mod_cands:
            continue
        lines.extend([f"### `src/LeanAsm/{target_mod}` (Top 10)", ""])
        for c in mod_cands:
            concepts = ", ".join(c["concepts"])
            lines.extend(
                wrap_text_lines(
                    f"- **[score={c['score']}]** `{c['kind']} {c['full_name']}` "
                    f"(`{c['path']}:{c['line']}`) [{concepts}]",
                    sub_indent="  ",
                )
            )
        lines.append("")
    return lines


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Scan OpenAI 2026-10-28 YM submission for leanasm."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("subrepos/YM/submissions/openai-20261028"),
        help="Path to openai-20261028 submission root.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/openai-20261028"),
        help="Output directory for generated reports.",
    )
    parser.add_argument(
        "--log-level",
        default="INFO",
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="Logging verbosity.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run Passes A, B, and C and write verified JSON/Markdown outputs."""
    args = parse_args(argv)
    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="[%(levelname)s] %(name)s: %(message)s",
    )
    root = args.root
    if not root.exists() or not root.is_dir():
        LOG.error("Submission root does not exist or is not a directory: %s", root)
        return 1

    out_dir = args.out
    out_dir.mkdir(parents=True, exist_ok=True)
    out_rel = out_dir.as_posix().rstrip("/")
    repo_prefix = f"leanasm/{out_rel}"

    manifest = run_pass_a(root)
    (out_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
    )
    write_checked_markdown(
        out_dir / "MANIFEST.md",
        f"{repo_prefix}/MANIFEST.md",
        render_manifest_md(manifest),
    )

    toc = run_pass_b(root, manifest)
    toc_serializable = strip_transient_fields(toc)
    (out_dir / "LEAN_TOC.json").write_text(
        json.dumps(toc_serializable, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    write_checked_markdown(
        out_dir / "LEAN_TOC.md",
        f"{repo_prefix}/LEAN_TOC.md",
        render_lean_toc_md(toc),
    )

    qrh_report = run_pass_c(toc)
    write_checked_markdown(
        out_dir / "QRH_7_8_CANDIDATES.md",
        f"{repo_prefix}/QRH_7_8_CANDIDATES.md",
        render_qrh_candidates_md(qrh_report),
    )
    LOG.info("All reports written to %s", out_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# end of file: leanasm/scripts/scan_openai_submission.py
