# Variational Analysis in Lean

A Lean 4 and Mathlib formalization of Rockafellar and Wets’s *Variational Analysis*.

**Complete coverage of all 830 numbered results across all 14 chapters.**
The chapter ledgers record **736 results formalized as stated** and **94
documented adaptations**. Each entry identifies the Lean declarations and
explains any changes in hypotheses, scope, or conventions.

[Lean API documentation](https://tonysf.github.io/rockafellar/docs/) ·
[Build and verification on GitHub](https://github.com/tonysf/rockafellar/actions/workflows/lean_action_ci.yml)

## Chapter coverage

Each chapter title links to its result-by-result ledger.

| Chapter | Numbered results |
| --- | ---: |
| 1. [Max and Min](CHAPTER1_COVERAGE.md) | 46 |
| 2. [Convexity](CHAPTER2_COVERAGE.md) | 57 |
| 3. [Cones and Cosmic Closure](CHAPTER3_COVERAGE.md) | 55 |
| 4. [Set Convergence](CHAPTER4_COVERAGE.md) | 48 |
| 5. [Set-Valued Mappings](CHAPTER5_COVERAGE.md) | 59 |
| 6. [Variational Geometry](CHAPTER6_COVERAGE.md) | 49 |
| 7. [Epigraphical Limits](CHAPTER7_COVERAGE.md) | 69 |
| 8. [Subderivatives and Subgradients](CHAPTER8_COVERAGE.md) | 54 |
| 9. [Lipschitzian Properties](CHAPTER9_COVERAGE.md) | 69 |
| 10. [Subdifferential Calculus](CHAPTER10_COVERAGE.md) | 59 |
| 11. [Dualization](CHAPTER11_COVERAGE.md) | 67 |
| 12. [Monotone Mappings](CHAPTER12_COVERAGE.md) | 68 |
| 13. [Second-Order Theory](CHAPTER13_COVERAGE.md) | 68 |
| 14. [Measurability](CHAPTER14_COVERAGE.md) | 62 |
| **Total** | **830** |

Ongoing work focuses on reviewing the adaptations, strengthening Lean statements
where possible, and documenting counterexamples where the printed statement
needs a correction.

## Build and verify

From the repository root, build with the pinned [Lean toolchain](lean-toolchain)
and check the coverage ledgers and module imports.

```bash
lake build
python3 -B scripts/check_ledgers.py
```

Use `import RockafellarWets` to load the full library. The chapter sources are
in [`RockafellarWets/`](RockafellarWets/).

The formalization is `sorry`-free. After building, run the separate kernel
dependency audit for all 14 chapters.

```bash
lake env lean scripts/audit_variational.lean
```

The audit includes private and generated declarations and allows only Lean’s
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## License

[Apache License 2.0](LICENSE)
