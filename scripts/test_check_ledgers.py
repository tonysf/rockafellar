#!/usr/bin/env python3
"""Regression fixtures for structural coverage and import checks.

Run with: python3 -m unittest discover -s scripts -p 'test_*.py'
All fixtures live in temporary directories; repository files are never changed.
"""

from __future__ import annotations

import tempfile
import unittest
from collections import Counter
from pathlib import Path

import check_ledgers as checker


class FixtureTest(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def write(self, relative: str, text: str = "") -> Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def assert_problem(self, problems: list[str], fragment: str) -> None:
        self.assertTrue(any(fragment in problem for problem in problems), problems)


class LedgerTests(FixtureTest):
    def ledger(
        self,
        rows: list[tuple[int, str]] | None = None,
        summary: list[tuple[str, int]] | None = None,
        total: int | None = None,
        extra: str = "",
    ) -> Path:
        if rows is None:
            rows = [(1, "Exact"), (2, "Adapted"), (3, "Missing")]
        if summary is None:
            summary = list(Counter(status for _, status in rows).items())
        if total is None:
            total = len(rows)
        lines = ["| Status | Count |", "| --- | ---: |"]
        lines.extend(f"| {status} | {count} |" for status, count in summary)
        lines.extend([f"| **Total** | **{total}** |", "", "| Result | Status | Evidence |", "| --- | --- | --- |"])
        lines.extend(f"| 3.{number} A result | **{status}** | evidence |" for number, status in rows)
        return self.write("CHAPTER3_COVERAGE.md", "\n".join(lines) + "\n" + extra)

    def test_valid_mixed_statuses(self) -> None:
        self.assertEqual(checker.check_ledger(3, self.ledger(), expected_end=3), [])

    def test_valid_zero_status_counts(self) -> None:
        path = self.ledger(
            rows=[(1, "Exact"), (2, "Exact"), (3, "Exact")],
            summary=[("Exact", 3), ("Adapted", 0), ("Partial", 0), ("Missing", 0)],
        )
        self.assertEqual(checker.check_ledger(3, path, expected_end=3), [])

    def test_truncated_tail_with_consistent_counts(self) -> None:
        # This formerly passed: all present rows and both summary counts agree.
        path = self.ledger(rows=[(number, "Exact") for number in range(1, 55)])
        self.assert_problem(checker.check_ledger(3, path), "no row for 3.55")

    def test_interior_gap_and_extra_id_do_not_cancel(self) -> None:
        path = self.ledger(rows=[(1, "Exact"), (3, "Exact"), (4, "Exact")])
        problems = checker.check_ledger(3, path, expected_end=3)
        self.assert_problem(problems, "no row for 3.2")
        self.assert_problem(problems, "unexpected result row(s): 3.4")

    def test_extra_ids_including_zero(self) -> None:
        path = self.ledger(rows=[(number, "Exact") for number in range(5)])
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "unexpected result row(s): 3.0, 3.4")

    def test_duplicate_result_row(self) -> None:
        path = self.ledger(extra="| 3.1 Again | Exact | evidence |\n")
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "duplicate row for 3.1")

    def test_duplicate_summary_status(self) -> None:
        path = self.ledger(summary=[("Exact", 1), ("Exact", 1), ("Adapted", 1), ("Missing", 1)])
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "duplicate summary label 'Exact'")

    def test_duplicate_total(self) -> None:
        path = self.ledger()
        path.write_text(path.read_text().replace("| **Total** | **3** |", "| Total | 3 |\n| **Total** | **3** |"))
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "duplicate summary label 'Total'")

    def test_unknown_status_even_when_counts_agree(self) -> None:
        path = self.ledger(rows=[(1, "Unreviewed"), (2, "Exact"), (3, "Exact")])
        problems = checker.check_ledger(3, path, expected_end=3)
        self.assert_problem(problems, "unknown summary status 'Unreviewed'")
        self.assert_problem(problems, "unknown result status 'Unreviewed'")

    def test_wrong_chapter_row(self) -> None:
        path = self.ledger(extra="| 4.1 Wrong chapter | Exact | evidence |\n")
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "wrong-chapter row 4.1")

    def test_mismatched_summary(self) -> None:
        path = self.ledger(summary=[("Exact", 2), ("Adapted", 1), ("Missing", 0)])
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "summary claims 2 'Exact' but 1")

    def test_missing_summary_status(self) -> None:
        path = self.ledger(summary=[("Exact", 1), ("Missing", 1)])
        self.assert_problem(checker.check_ledger(3, path, expected_end=3), "summary table has no 'Adapted' line")

    def test_missing_ledger(self) -> None:
        self.assert_problem(checker.check_ledger(3, self.root / "absent.md"), "ledger file not found")

    def test_empty_ledger_does_not_lose_other_errors(self) -> None:
        path = self.ledger(rows=[], summary=[("Unreviewed", 0)])
        problems = checker.check_ledger(3, path, expected_end=3)
        self.assert_problem(problems, "unknown summary status")
        self.assert_problem(problems, "no result rows matched")
        self.assert_problem(problems, "no row for 3.1, 3.2, 3.3")

    def test_unknown_chapter_needs_independent_inventory(self) -> None:
        # Keep this independent of which real chapters have been enrolled.
        chapter = max(checker.EXPECTED_ENDPOINTS, default=0) + 1
        path = self.write(
            f"CHAPTER{chapter}_COVERAGE.md",
            f"| Status | Count |\n| Total | 1 |\n\n| {chapter}.1 | Exact |\n",
        )
        self.assert_problem(
            checker.check_ledger(chapter, path),
            f"add Chapter {chapter}'s reviewed result endpoint",
        )


class EnrollmentAndLinkTests(FixtureTest):
    def test_new_ledger_cannot_escape_enrollment(self) -> None:
        self.write("CHAPTER7_COVERAGE.md")
        problems = checker.check_ledger_enrollment(self.root, ledgers={}, expected_endpoints={})
        self.assert_problem(problems, "unenrolled ledger; add Chapter 7 to LEDGERS and EXPECTED_ENDPOINTS")

    def test_enrollment_requires_expected_inventory(self) -> None:
        path = self.write("CHAPTER7_COVERAGE.md")
        problems = checker.check_ledger_enrollment(self.root, ledgers={7: path}, expected_endpoints={})
        self.assert_problem(problems, "add a reviewed result endpoint")

    def test_expected_inventory_requires_ledger_enrollment(self) -> None:
        problems = checker.check_ledger_enrollment(self.root, ledgers={}, expected_endpoints={7: 10})
        self.assert_problem(problems, "expected inventory has no LEDGERS entry")

    def test_valid_enrollment(self) -> None:
        path = self.write("CHAPTER3_COVERAGE.md")
        self.assertEqual(checker.check_ledger_enrollment(self.root, {3: path}, {3: 55}), [])

    def test_links_must_be_files(self) -> None:
        self.write("RockafellarWets/Good.lean")
        (self.root / "directory.lean").mkdir()
        ledger = self.write("CHAPTER3_COVERAGE.md", "[good](RockafellarWets/Good.lean#anchor) [bad](absent.lean) [directory](directory.lean)\n")
        problems = checker.check_ledger_links(ledger, self.root)
        self.assertEqual(len(problems), 2, problems)
        self.assert_problem(problems, "link target is not a file: absent.lean")
        self.assert_problem(problems, "link target is not a file: directory.lean")

    def test_external_and_local_anchor_links_are_ignored(self) -> None:
        ledger = self.write("CHAPTER3_COVERAGE.md", "[web](https://example.org) [mail](mailto:a@example.org) [anchor](#section)")
        self.assertEqual(checker.check_ledger_links(ledger, self.root), [])


class ImportTests(FixtureTest):
    def test_transitive_exports(self) -> None:
        self.write("RockafellarWets.lean", "import RockafellarWets.Chapter1\n")
        self.write("RockafellarWets/Chapter1.lean", "import RockafellarWets.Chapter1.Defs\n")
        self.write("RockafellarWets/Chapter1/Defs.lean", "def example := 1\n")
        self.assertEqual(checker.check_imports(self.root), [])

    def test_missing_import_reports_original_line(self) -> None:
        self.write("RockafellarWets.lean", "/- heading\n /- nested -/\n-/\nimport RockafellarWets.Absent -- explanation\n")
        self.assert_problem(checker.check_imports(self.root), "RockafellarWets.lean:4: import does not resolve: RockafellarWets.Absent")

    def test_directory_cannot_resolve_import(self) -> None:
        self.write("RockafellarWets.lean", "import RockafellarWets.Absent\n")
        (self.root / "RockafellarWets/Absent.lean").mkdir(parents=True)
        self.assert_problem(checker.check_imports(self.root), "import does not resolve: RockafellarWets.Absent")

    def test_unexported_module(self) -> None:
        self.write("RockafellarWets.lean")
        self.write("RockafellarWets/Unexported.lean", "def example := 1\n")
        self.assert_problem(checker.check_imports(self.root), "RockafellarWets/Unexported.lean: module is not reachable")

    def test_empty_basic_is_allowed(self) -> None:
        self.write("RockafellarWets.lean")
        self.write("RockafellarWets/Basic.lean", "/- empty /- nested -/ template -/\n-- deliberately minimal\n")
        self.assertEqual(checker.check_imports(self.root), [])

    def test_basic_with_content_must_be_exported(self) -> None:
        self.write("RockafellarWets.lean")
        self.write("RockafellarWets/Basic.lean", "def example := 1\n")
        self.assert_problem(checker.check_imports(self.root), "RockafellarWets/Basic.lean: module is not reachable")

    def test_missing_umbrella(self) -> None:
        self.write("RockafellarWets/Chapter1.lean")
        self.assert_problem(checker.check_imports(self.root), "top-level umbrella file not found")

    def test_nested_and_inline_comments_and_multiple_imports(self) -> None:
        source = (
            "/- import RockafellarWets.Fake\n"
            " /- nested -/ import RockafellarWets.AlsoFake\n"
            "-/\n"
            "-- import RockafellarWets.LineComment\n"
            "public import /- inline -/ Mathlib RockafellarWets.A RockafellarWets.B -- trailing\n"
        )
        self.write("RockafellarWets.lean", source)
        self.write("RockafellarWets/A.lean")
        self.write("RockafellarWets/B.lean")
        self.assertEqual(checker.project_imports(source), [(5, "RockafellarWets.A"), (5, "RockafellarWets.B")])
        self.assertEqual(checker.check_imports(self.root), [])

    def test_strings_protect_comment_delimiters(self) -> None:
        source = 'def marker := "escaped quote: \\" /- --"\nimport RockafellarWets.A\n'
        self.assertEqual(checker.project_imports(source), [(2, "RockafellarWets.A")])

    def test_multiline_strings_do_not_introduce_imports(self) -> None:
        source = 'def marker := "\nimport RockafellarWets.Fake\n"\nimport RockafellarWets.A\n'
        self.assertEqual(checker.project_imports(source), [(4, "RockafellarWets.A")])


if __name__ == "__main__":
    unittest.main()
