#!/usr/bin/env python3
"""Audit owned Lean source, root imports, and manuscript/ledger coverage.

This complements (and does not replace) Lean's kernel and audit_lean.lean.
Only the standard library is required. Dependencies under .lake are excluded.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
PROJECT = "EntropyConstrainedMissingMass"


def lean_code(source: str) -> str:
    """Remove nested block comments, line comments and escaped string literals."""
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif pair == "/-":
            result.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            result.append(" ")
            quoted = True
            i += 1
        else:
            result.append(source[i])
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment/string")
    return "".join(result)


def check_lean() -> None:
    # Include any future project-owned Lean files outside the library too.
    files = sorted(p for p in ROOT.rglob("*.lean")
                   if not any(part.startswith(".") for part in p.relative_to(ROOT).parts))
    code = {}
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")
    for path in files:
        relative = path.relative_to(ROOT)
        body = lean_code(path.read_text())
        match = forbidden.search(body)
        if match:
            line = body[:match.start()].count("\n") + 1
            raise ValueError(f"Forbidden proof escape {match[0]}: {relative}:{line}")
        code[str(relative.with_suffix("")).replace("/", ".")] = body
    seen = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        if module not in code:
            raise ValueError(f"Missing owned module: {module}")
        seen.add(module)
        for imported in re.findall(r"^\s*import\s+(\S+)", code[module], re.M):
            if imported == PROJECT or imported.startswith(PROJECT + "."):
                visit(imported)

    visit(PROJECT)
    owned = {name for name in code if name == PROJECT or name.startswith(PROJECT + ".")}
    if owned != seen:
        raise ValueError(f"Library modules absent from root imports: {sorted(owned - seen)}")
    print(f"Source audit: {len(files)} owned Lean files; {len(seen)} modules in root closure; no proof escapes.")


def check_ledger() -> None:
    ledger = (ROOT / "FORMALIZATION_STATUS.md").read_text()
    parts = re.split(r"^### `([^`]+)`\s*$", ledger, flags=re.M)
    entries = dict(zip(parts[1::2], parts[2::2]))
    if len(entries) != len(parts[1::2]):
        raise ValueError("Duplicate ledger identifiers")
    graph = {}
    for name, body in entries.items():
        status = re.search(r"^- Status: \*\*([^*]+)\*\*", body, re.M)
        correspondence = re.search(r"^- Lean correspondence: `([^`]+)`", body, re.M)
        dependencies = re.search(r"^- Dependencies: (.*)$", body, re.M)
        if not status or status[1] != "PROVED" or not correspondence or not dependencies:
            raise ValueError(f"Incomplete ledger entry: {name}")
        graph[name] = re.findall(r"`([^`]+)`", dependencies[1])
    done, active = set(), set()

    def visit(name: str) -> None:
        if name in active:
            raise ValueError(f"Circular ledger dependency: {name}")
        if name not in graph:
            raise ValueError(f"Unknown ledger dependency: {name}")
        if name in done:
            return
        active.add(name)
        for dependency in graph[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)

    for name in graph:
        visit(name)
    tex = (ROOT / "missing_mass_extremizers.tex").read_text()
    # All current named environments are labelled; reject an unlabelled addition.
    results = re.findall(
        r"\\begin\{(theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}",
        tex, re.S)
    labels = []
    for kind, body in results:
        label = re.search(r"\\label\{((?:thm|lem|cor|prop):[^}]+)\}", body)
        if not label or label[1] not in entries:
            raise ValueError(f"Named {kind} lacks a ledger counterpart: {body[:100]}")
        labels.append(label[1])
    ledger_named = {key for key in entries if key.startswith(("thm:", "lem:", "cor:", "prop:"))}
    if ledger_named != set(labels) or len(labels) != len(set(labels)):
        raise ValueError("Manuscript and ledger named-result inventories differ")
    print(f"Ledger audit: {len(entries)} proved entries, acyclic dependencies; all {len(labels)} named results covered.")


if __name__ == "__main__":
    check_lean()
    check_ledger()
