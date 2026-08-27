#!/usr/bin/env python3
"""Consistency guard for the coverage ledgers and the module manifests.

Three checks, each of which has caught real drift in this repository:

1. Ledger summary tables must agree with their own result rows.  A status
   count in the `| Status | Count |` table is derivable from the rows below
   it, so an edit that updates one and not the other is a machine-detectable
   error rather than something a reader has to notice.

2. Markdown links in the ledgers must resolve to files that exist.  A row
   citing a module that was never written is worse than a row marked
   `Missing`, because it reads as evidence.

3. Every `import RockafellarWets.*` must resolve to a `.lean` file.  Lake
   reports this only after scheduling the whole build; here it costs
   milliseconds.

Exits non-zero and prints one line per problem.  Standard library only.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

LEDGERS = {
    3: ROOT / "CHAPTER3_COVERAGE.md",
    4: ROOT / "CHAPTER4_COVERAGE.md",
    5: ROOT / "CHAPTER5_COVERAGE.md",
}

# `| Exact | 43 |` in the summary table.
SUMMARY_ROW = re.compile(r"^\|\s*(?:\*\*)?([A-Za-z][A-Za-z ]*?)(?:\*\*)?\s*\|\s*(?:\*\*)?(\d+)(?:\*\*)?\s*\|\s*$")
# `| 4.12 Limits of connected sets | **Exact** | ... |` or `| 3.1 | **Exact** | ... |`
RESULT_ROW = re.compile(r"^\|\s*(\d+)\.(\d+)[^|]*\|\s*(?:\*\*)?([A-Za-z]+)(?:\*\*)?\s*\|")
MD_LINK = re.compile(r"\]\(([^)]+)\)")
LEAN_IMPORT = re.compile(r"^import\s+(RockafellarWets(?:\.[A-Za-z0-9_']+)*)\s*$")


def split_cells(line: str) -> list[str]:
    return [c.strip() for c in line.strip().strip("|").split("|")]


def check_ledger(chapter: int, path: Path) -> list[str]:
    """Compare a ledger's summary table against the result rows it summarizes."""
    problems: list[str] = []
    if not path.exists():
        return [f"{path.name}: file not found"]

    lines = path.read_text(encoding="utf-8").splitlines()

    summary: dict[str, int] = {}
    declared_total: int | None = None
    in_summary = False
    for line in lines:
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
            if label.lower() == "total":
                declared_total = count
            else:
                summary[label] = count

    rows: dict[int, str] = {}
    for number, line in enumerate(lines, start=1):
        match = RESULT_ROW.match(line)
        if not match or int(match.group(1)) != chapter:
            continue
        result = int(match.group(2))
        if result in rows:
            problems.append(f"{path.name}:{number}: duplicate row for {chapter}.{result}")
            continue
        rows[result] = match.group(3)

    if not rows:
        return [f"{path.name}: no result rows matched; the row format may have changed"]

    tallied: dict[str, int] = {}
    for status in rows.values():
        tallied[status] = tallied.get(status, 0) + 1

    for status in sorted(set(summary) | set(tallied)):
        want, got = summary.get(status), tallied.get(status)
        if want is None:
            problems.append(
                f"{path.name}: {got} row(s) marked '{status}' but the summary table has no '{status}' line"
            )
        elif got is None:
            problems.append(f"{path.name}: summary claims {want} '{status}' but no row is marked '{status}'")
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

    # A gap means a result silently lost its row; a pure count check misses this
    # whenever another row was added in the same edit.
    missing = sorted(set(range(1, max(rows) + 1)) - set(rows))
    if missing:
        listed = ", ".join(f"{chapter}.{n}" for n in missing)
        problems.append(f"{path.name}: no row for {listed}")

    return problems


def check_ledger_links(path: Path) -> list[str]:
    """Every repository-relative link in a ledger must point at a real file."""
    problems: list[str] = []
    if not path.exists():
        return problems
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for target in MD_LINK.findall(line):
            if target.startswith(("http://", "https://", "#", "mailto:")):
                continue
            relative = target.split("#", 1)[0]
            if not relative:
                continue
            if not (ROOT / relative).exists():
                problems.append(f"{path.name}:{number}: link target does not exist: {relative}")
    return problems


def check_imports() -> list[str]:
    """Every `import RockafellarWets.*` must resolve to a file on disk."""
    problems: list[str] = []
    sources = sorted(ROOT.glob("RockafellarWets/**/*.lean")) + [ROOT / "RockafellarWets.lean"]
    for source in sources:
        if not source.exists():
            continue
        for number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), start=1):
            match = LEAN_IMPORT.match(line)
            if not match:
                continue
            target = ROOT / (match.group(1).replace(".", "/") + ".lean")
            if not target.exists():
                origin = source.relative_to(ROOT)
                problems.append(f"{origin}:{number}: import does not resolve: {match.group(1)}")
    return problems


def main() -> int:
    problems: list[str] = []
    for chapter, path in sorted(LEDGERS.items()):
        problems += check_ledger(chapter, path)
        problems += check_ledger_links(path)
    problems += check_imports()

    if problems:
        print(f"{len(problems)} problem(s) found:\n", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    print("Ledgers agree with their rows; all ledger links and module imports resolve.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
