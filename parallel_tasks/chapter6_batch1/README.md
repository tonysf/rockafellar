# Chapter 6 parallel batch 1

This directory contains standalone prompts for the first parallel Chapter 6
formalization batch.  Copy the complete contents of one `pNN-*.md` file into a
fresh Codex task.  Every worker has exclusive ownership of a different new Lean
file, so all fourteen tasks can start at the same time.

## Required starting point

Every task must start from the **local** commit
`b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).  Do not start from
`origin/chapter3-exactification-chapter4`: at the time these prompts were
written, the local branch was 47 commits ahead of that remote ref.

Use a separate worktree or otherwise isolated checkout for every worker.  The
prompt assigns the exact branch name to use.  A worker should stop and report a
blocker if its `HEAD` is not `b2eb4ea` before implementation begins.

## Prompts

| ID | Branch | Prompt | Expected scope | Risk |
|---|---|---|---|---|
| P1 | `chapter6-p01-continuous-right-inverses` | [Continuous right inverses](p01-continuous-right-inverses.md) | Reusable continuous right-inverse family | Low; route checked |
| P2 | `chapter6-p02-local-submersion` | [Local submersion](p02-local-submersion.md) | Reusable local section theorem | Low; route checked |
| P3 | `chapter6-p03-regular-normal-change-coordinates` | [Regular-normal change of coordinates](p03-regular-normal-change-coordinates.md) | Regular-normal clause of 6.7 | Low/medium; proof checked |
| P4 | `chapter6-p04-interval-cones` | [Interval cones](p04-interval-cones.md) | One-dimensional interval/ray cone formulas | Medium |
| P5 | `chapter6-p05-product-cones` | [Product cones](p05-product-cones.md) | Binary `WithLp 2` convex-product cone formulas | Medium |
| P6 | `chapter6-p06-gradient-normals` | [Gradient normals](p06-gradient-normals.md) | Core differentiable-witness clause of 6.11 | Medium; core route checked |
| P7 | `chapter6-p07-smooth-majorant` | [Smooth majorant](p07-smooth-majorant.md) | Scalar smoothing infrastructure for full 6.11 | High |
| P8 | `chapter6-p08-optimality` | [Optimality](p08-optimality.md) | Every clause of 6.12 | Low/medium; core route checked |
| P9 | `chapter6-p09-proximal-normals` | [Proximal normals](p09-proximal-normals.md) | Results 6.16 and 6.17 | Medium |
| P10 | `chapter6-p10-supporting-halfspaces` | [Supporting halfspaces](p10-supporting-halfspaces.md) | Theorem 6.20 | Medium |
| P11 | `chapter6-p11-polarity` | [Polarity](p11-polarity.md) | Results 6.21 through 6.24 | Medium/high |
| P12 | `chapter6-p12-regular-tangents` | [Regular tangents](p12-regular-tangents.md) | Definition 6.25 and Theorem 6.26 | High |
| P13 | `chapter6-p13-generic-normal-continuity` | [Generic normal continuity](p13-generic-normal-continuity.md) | Audit and formalization of 6.49 | Medium; statement audit required |
| P14 | `chapter6-p14-elementary-cones` | [Elementary cones](p14-elementary-cones.md) | Locality and elementary cone formulas | Medium |

## Shared contract

Each worker prompt is self-contained, but they all enforce the same integration
contract:

- Add only the assigned new Lean file.  Do not edit existing source files.
- Place all new Lean declarations in `namespace RW`.
- Do not edit `README.md`, `CHAPTER6_COVERAGE.md`,
  `RockafellarWets/Chapter6.lean`, or `RockafellarWets.lean`.
- Do not import another P1--P14 worker's not-yet-integrated module.
- Do not leave `sorry`, `admit`, `axiom`, disabled linters, or placeholder
  declarations.
- Compile the assigned file directly with `lake env lean` and run any focused
  checks described by the prompt.
- Review `git diff --check` and commit only the assigned implementation.
- Report the final commit hash, theorem inventory, tests run, and any exact
  adaptation of a printed statement.

To prevent semantic conflicts at integration, P11 owns the canonical
polar-cone definition, P12 owns the canonical regular-tangent definition, and
P14 owns the canonical public locality, singleton, and `univ` cone theorem
names. P3 and P4 may use private or result-specific versions of P14 facts while
working independently, but must not publish competing generic names. P1 owns
the generic public right-inverse API; P2 must keep any independent linear
right-inverse construction private and publish only its nonlinear local-section
API. P9 owns generic public projection-to-regular-normal declarations; P10
must inline that calculation or keep any helper private or
supporting-halfspace-specific.

The workers deliberately do not update coverage bookkeeping.  A single
integration task performs those shared edits after the selected worker branches
are complete.

## Integration

After the desired branches have completed, copy
[the batch integration prompt](p15-integrate-batch1.md) into a fresh task.  The
integrator checks each branch before cherry-picking, harmonizes APIs without
weakening results, updates umbrella imports and coverage exactly once, and runs
the full repository verification.

## Natural second batch

The first integration unlocks another parallel fan-out:

- P1 + P2 + P3: the limiting-normal clause of 6.7.
- Completed 6.7 + P14: smooth manifolds in 6.8.
- P4 + P5: boxes in 6.10.
- P6 + P7: the globally smooth strengthening of 6.11.
- Completed 6.10 + P8: variational inequalities and complementarity in 6.13.
- P9: approximation of normals in 6.18.
- P12: recession definitions and properties in 6.33--6.34.
- P5 + P11 + P12: product sets in 6.41.
- P11 plus the existing Chapter 3 polyhedral layer: Farkas/polars in 6.45.
