# Chapter 6 parallel batch 2

This directory contains the worker prompts for the second Chapter 6
formalization batch.  Batch 2 starts from the fully verified Batch 1 integration
commit `9fa1c19eab36f7fc79845f679d35b87344366e0b` and is deliberately split into
two dependency waves.

The prompts are an orchestration record: they are not imported by Lean and do
not affect the build.  Each implementation worker owns one new Lean file and
must leave shared imports and coverage bookkeeping to the final integrator.

## Resource policy

Run at most **two implementation workers concurrently**.  Prefer to stagger
their focused Lean compilations so that the laptop remains responsive.  Every
Claude Code worker must use the authenticated Claude subscription with model
`claude-opus-5` and effort `max`; unset API-key environment variables for the
worker process and stop on subscription exhaustion instead of enabling API
credits.

## Wave 1

These seven workers are independent at the Batch 1 integration base.

| ID | Branch | Prompt | Result scope | Owned file |
|---|---|---|---|---|
| P16 | `chapter6-p16-limiting-normal-change-coordinates` | [Limiting normals under change of coordinates](p16-limiting-normal-change-coordinates.md) | Complete 6.7 | `LimitingNormalChangeOfCoordinates.lean` |
| P17 | `chapter6-p17-finite-boxes` | [Finite boxes](p17-finite-boxes.md) | Complete 6.10 | `FiniteBoxes.lean` |
| P18 | `chapter6-p18-smooth-gradient-witness` | [Smooth gradient witness](p18-smooth-gradient-witness.md) | Complete 6.11 | `SmoothGradientWitness.lean` |
| P19 | `chapter6-p19-normal-approximation` | [Approximation of normals](p19-normal-approximation.md) | Result 6.18 | `NormalApproximation.lean` |
| P20 | `chapter6-p20-recession-cones` | [Recession cones](p20-recession-cones.md) | Results 6.33--6.34 | `RecessionCones.lean` |
| P21 | `chapter6-p21-finite-product-cones` | [Finite product cones](p21-finite-product-cones.md) | Complete 6.41 | `FiniteProductCones.lean` |
| P22 | `chapter6-p22-farkas-polar-cones` | [Farkas and polyhedral cone polars](p22-farkas-polar-cones.md) | Result 6.45 | `FarkasPolarCones.lean` |

## Wave 2

Two workers become available as soon as their individual prerequisite branch
finishes; they do not need to wait for the rest of Wave 1.

| ID | Prerequisite | Branch | Result scope | Owned file |
|---|---|---|---|---|
| P23 | P16 | `chapter6-p23-smooth-manifolds` | Result 6.8 | `SmoothManifolds.lean` |
| P24 | P17 | `chapter6-p24-variational-complementarity` | Result 6.13 | `VariationalComplementarity.lean` |

The exact P23 and P24 base hashes are the accepted P16 and P17 commit hashes.
Their prompts are generated after those prerequisites pass audit, so each can
name and verify its exact immutable base.

## Integration

P25 audits every worker branch, cherry-picks accepted commits in dependency
order (`P16` before `P23`, `P17` before `P24`), reconciles APIs without
weakening statements, updates umbrella imports and coverage once, and runs the
full repository verification.  Its prompt is generated after all scheduled
workers finish so that it can record their exact tips.
