#!/usr/bin/env python3
"""Consistency guard for the coverage ledgers and the module manifests.

These are structural checks, not verification that a theorem matches the book:

1. Ledger rows must cover an independently recorded result inventory, and
   summary counts must agree with those rows. New ledgers require enrollment.

2. Markdown links in the ledgers must resolve to files that exist.  A row
   citing a module that was never written is worse than a row marked
   `Missing`, because it reads as evidence.

3. Every project import must resolve to a source file, and every substantive
   source module must be reachable from the top-level project import.

Exits non-zero and prints one line per problem.  Standard library only.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

LEDGERS = {
    1: ROOT / "CHAPTER1_COVERAGE.md",
    2: ROOT / "CHAPTER2_COVERAGE.md",
    3: ROOT / "CHAPTER3_COVERAGE.md",
    4: ROOT / "CHAPTER4_COVERAGE.md",
    5: ROOT / "CHAPTER5_COVERAGE.md",
    6: ROOT / "CHAPTER6_COVERAGE.md",
    7: ROOT / "CHAPTER7_COVERAGE.md",
    8: ROOT / "CHAPTER8_COVERAGE.md",
    9: ROOT / "CHAPTER9_COVERAGE.md",
    10: ROOT / "CHAPTER10_COVERAGE.md",
    11: ROOT / "CHAPTER11_COVERAGE.md",
    12: ROOT / "CHAPTER12_COVERAGE.md",
    13: ROOT / "CHAPTER13_COVERAGE.md",
    14: ROOT / "CHAPTER14_COVERAGE.md",
}

# Reviewed book inventories, deliberately independent of the ledger contents.
# Enroll a new chapter here and in LEDGERS, including rows marked Missing for
# results whose formalization is still pending.
EXPECTED_ENDPOINTS = {1: 46, 2: 57, 3: 55, 4: 48, 5: 59, 6: 49, 7: 69, 8: 54, 9: 69, 10: 59, 11: 67, 12: 68, 13: 68, 14: 62}
ALLOWED_STATUSES = frozenset({"Exact", "Adapted", "Partial", "Missing"})

# `| Exact | 43 |` in the summary table.
SUMMARY_ROW = re.compile(r"^\|\s*(?:\*\*)?([A-Za-z][A-Za-z ]*?)(?:\*\*)?\s*\|\s*(?:\*\*)?(\d+)(?:\*\*)?\s*\|\s*$")
# `| 4.12 Limits of connected sets | **Exact** | ... |` or `| 3.1 | **Exact** | ... |`
RESULT_ROW = re.compile(r"^\|\s*(\d+)\.(\d+)[^|]*\|\s*([^|]*?)\s*\|")
MD_LINK = re.compile(r"\]\(([^)]+)\)")
LEAN_IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$")
PROJECT_MODULE = re.compile(r"RockafellarWets(?:\.[A-Za-z0-9_']+)*\Z")


def split_cells(line: str) -> list[str]:
    return [c.strip() for c in line.strip().strip("|").split("|")]


def check_ledger(chapter: int, path: Path, expected_end: int | None = None) -> list[str]:
    """Check the expected result inventory, statuses, and summary counts."""
    problems: list[str] = []
    if not path.is_file():
        return [f"{path.name}: ledger file not found"]
    if expected_end is None:
        expected_end = EXPECTED_ENDPOINTS.get(chapter)
    if expected_end is None:
        problems.append(f"{path.name}: add Chapter {chapter}'s reviewed result endpoint to EXPECTED_ENDPOINTS in scripts/check_ledgers.py")

    lines = path.read_text(encoding="utf-8").splitlines()

    summary: dict[str, int] = {}
    declared_total: int | None = None
    in_summary = False
    seen_labels: set[str] = set()
    for number, line in enumerate(lines, start=1):
        cells = split_cells(line)
        if len(cells) == 2 and cells[0].lower() == "status" and cells[1].lower() == "count":
            in_summary = True
            continue
        if in_summary:
            match = SUMMARY_ROW.match(line)
            if not match:
                # Separator row `| --- | ---: |` keeps the table open; anything
                # else ends it.
                if set(line.replace("|", "").replace(" ", "")) <= {"-", ":"} and "|" in line:
                    continue
                in_summary = False
                continue
            label, count = match.group(1).strip(), int(match.group(2))
            if label.lower() in seen_labels:
                problems.append(f"{path.name}:{number}: duplicate summary label '{label}'")
                continue
            seen_labels.add(label.lower())
            if label.lower() == "total":
                declared_total = count
            else:
                if label not in ALLOWED_STATUSES:
                    problems.append(f"{path.name}:{number}: unknown summary status '{label}'; allowed: {', '.join(sorted(ALLOWED_STATUSES))}")
                summary[label] = count

    rows: dict[int, str] = {}
    for number, line in enumerate(lines, start=1):
        match = RESULT_ROW.match(line)
        if not match:
            continue
        row_chapter = int(match.group(1))
        result = int(match.group(2))
        if row_chapter != chapter:
            problems.append(f"{path.name}:{number}: wrong-chapter row {row_chapter}.{result}; expected Chapter {chapter}")
            continue
        status = match.group(3).removeprefix("**").removesuffix("**").strip()
        if status not in ALLOWED_STATUSES:
            problems.append(f"{path.name}:{number}: unknown result status '{status}'; allowed: {', '.join(sorted(ALLOWED_STATUSES))}")
        if result in rows:
            problems.append(f"{path.name}:{number}: duplicate row for {chapter}.{result}")
            continue
        rows[result] = status

    if not rows:
        problems.append(f"{path.name}: no result rows matched; the row format may have changed")

    tallied: dict[str, int] = {}
    for status in rows.values():
        tallied[status] = tallied.get(status, 0) + 1

    for status in sorted(set(summary) | set(tallied)):
        want, got = summary.get(status), tallied.get(status, 0)
        if want is None:
            problems.append(
                f"{path.name}: {got} row(s) marked '{status}' but the summary table has no '{status}' line"
            )
        elif want != got:
            problems.append(f"{path.name}: summary claims {want} '{status}' but {got} row(s) are marked '{status}'")

    if declared_total is None:
        problems.append(f"{path.name}: summary table has no Total row")
    else:
        if declared_total != len(rows):
            problems.append(f"{path.name}: summary Total is {declared_total} but there are {len(rows)} result rows")
        summed = sum(summary.values())
        if summed != declared_total:
            problems.append(f"{path.name}: summary status counts sum to {summed} but Total says {declared_total}")

    if expected_end is not None:
        expected = set(range(1, expected_end + 1))
        missing = sorted(expected - rows.keys())
        extra = sorted(rows.keys() - expected)
        if missing:
            listed = ", ".join(f"{chapter}.{n}" for n in missing)
            problems.append(f"{path.name}: no row for {listed}")
        if extra:
            listed = ", ".join(f"{chapter}.{n}" for n in extra)
            problems.append(f"{path.name}: unexpected result row(s): {listed}; expected {chapter}.1 through {chapter}.{expected_end}")

    return problems


def check_ledger_links(path: Path, root: Path | None = None) -> list[str]:
    """Every repository-relative link in a ledger must point at a real file."""
    problems: list[str] = []
    root = ROOT if root is None else root
    if not path.is_file():
        return problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for target in MD_LINK.findall(line):
            if target.startswith(("http://", "https://", "#", "mailto:")):
                continue
            relative = target.split("#", 1)[0]
            if not relative:
                continue
            if not (root / relative).is_file():
                problems.append(f"{path.name}:{number}: link target is not a file: {relative}")
    return problems


def check_ledger_enrollment(
    root: Path | None = None,
    ledgers: dict[int, Path] | None = None,
    expected_endpoints: dict[int, int] | None = None,
) -> list[str]:
    """Ensure new chapter ledgers cannot silently escape these checks."""
    root = ROOT if root is None else root
    ledgers = LEDGERS if ledgers is None else ledgers
    expected_endpoints = EXPECTED_ENDPOINTS if expected_endpoints is None else expected_endpoints
    problems: list[str] = []
    for path in sorted(root.glob("CHAPTER*_COVERAGE.md")):
        match = re.fullmatch(r"CHAPTER(\d+)_COVERAGE\.md", path.name)
        if not match:
            problems.append(f"{path.name}: expected a numeric chapter in CHAPTER<number>_COVERAGE.md")
            continue
        chapter = int(match.group(1))
        if chapter not in ledgers or ledgers[chapter] != path:
            problems.append(f"{path.name}: unenrolled ledger; add Chapter {chapter} to LEDGERS and EXPECTED_ENDPOINTS in scripts/check_ledgers.py")
    for chapter in sorted(set(ledgers) | set(expected_endpoints)):
        if chapter not in ledgers:
            problems.append(f"Chapter {chapter}: expected inventory has no LEDGERS entry in scripts/check_ledgers.py")
        if chapter not in expected_endpoints:
            problems.append(f"Chapter {chapter}: add a reviewed result endpoint to EXPECTED_ENDPOINTS in scripts/check_ledgers.py")
    return problems


def strip_lean_comments(source: str, *, mask_strings: bool = False) -> str:
    """Mask line and nested block comments, preserving positions and newlines.

    String literals protect comment delimiters. Import scanning additionally
    masks their contents so a multiline string cannot introduce fake imports.
    This is a small lexical helper, not a Lean parser or proof-integrity check.
    """
    result = list(source)
    i, depth = 0, 0
    in_string = False

    def mask(start: int, end: int) -> None:
        for position in range(start, end):
            if source[position] != "\n":
                result[position] = " "

    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                mask(i, i + 2)
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                mask(i, i + 2)
                depth -= 1
                i += 2
            else:
                mask(i, i + 1)
                i += 1
        elif in_string:
            width = 2 if source[i] == "\\" and i + 1 < len(source) else 1
            if mask_strings:
                mask(i, i + width)
            if source[i] == '"':
                in_string = False
            i += width
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            mask(i, end)
            i = end
        elif source.startswith("/-", i):
            mask(i, i + 2)
            depth = 1
            i += 2
        else:
            if source[i] == '"':
                in_string = True
                if mask_strings:
                    mask(i, i + 1)
            i += 1
    return "".join(result)


def project_imports(source: str) -> list[tuple[int, str]]:
    """Return project imports with their original one-based source lines.

    Recognizes ordinary single-line imports with ASCII project module names,
    including multiple modules on a line. It does not parse arbitrary Lean
    syntax, escaped module identifiers, or imports split across physical lines.
    """
    imports: list[tuple[int, str]] = []
    for number, line in enumerate(strip_lean_comments(source, mask_strings=True).splitlines(), start=1):
        match = LEAN_IMPORT.match(line)
        if match:
            imports.extend((number, module) for module in match.group(1).split() if PROJECT_MODULE.fullmatch(module))
    return imports


def check_imports(root: Path | None = None) -> list[str]:
    """Check import targets and reachability through the public umbrella."""
    root = ROOT if root is None else root
    problems: list[str] = []
    umbrella = root / "RockafellarWets.lean"
    sources = sorted(root.glob("RockafellarWets/**/*.lean")) + [umbrella]
    graph: dict[str, list[str]] = {}
    contents: dict[str, str] = {}
    for source in sources:
        if not source.is_file():
            continue
        module = source.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        contents[module] = source.read_text(encoding="utf-8")
        imports = project_imports(contents[module])
        graph[module] = [target for _, target in imports]
        for number, target_module in imports:
            target = root / (target_module.replace(".", "/") + ".lean")
            if not target.is_file():
                origin = source.relative_to(root)
                problems.append(f"{origin}:{number}: import does not resolve: {target_module}")
    if not umbrella.is_file():
        problems.append("RockafellarWets.lean: top-level umbrella file not found; cannot check module reachability")
        return problems
    reachable: set[str] = set()
    pending = ["RockafellarWets"]
    while pending:
        module = pending.pop()
        if module not in reachable:
            reachable.add(module)
            pending.extend(graph.get(module, []))
    for module in sorted(graph.keys() - reachable):
        # The template Basic file is intentionally comments-only. Do not exempt
        # it if it starts containing declarations or imports.
        if module == "RockafellarWets.Basic" and not strip_lean_comments(contents[module]).strip():
            continue
        origin = module.replace(".", "/") + ".lean"
        problems.append(f"{origin}: module is not reachable from RockafellarWets.lean; add it to the appropriate umbrella imports")
    return problems


def main() -> int:
    problems = check_ledger_enrollment()
    for chapter, path in sorted(LEDGERS.items()):
        problems += check_ledger(chapter, path)
        problems += check_ledger_links(path)
    problems += check_imports()

    if problems:
        print(f"{len(problems)} problem(s) found:\n", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    print("Ledgers match their expected inventories and summaries; all links are files, and project imports resolve and export all substantive modules.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
