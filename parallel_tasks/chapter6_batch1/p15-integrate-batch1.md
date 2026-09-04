# Copy/paste prompt: integrate Chapter 6 parallel batch 1

You are the sole integration worker for the first parallel Chapter 6 batch in
the `lean_rockafellar` repository.  Integrate the completed worker branches
conservatively, verify the combined development, update shared bookkeeping once,
and commit the integration.  Do not invent proofs for failed or incomplete
worker branches during this task.

## Starting state

Create and work on the branch `chapter6-batch1-integration`, based exactly on
the local commit:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

The remote tracking branch is stale relative to this commit.  Verify the base
with `git rev-parse HEAD` before changing anything.  Preserve any user changes;
if the integration worktree is dirty at the outset, stop and report it.

## Candidate worker branches

The candidate branches are:

```text
chapter6-p01-continuous-right-inverses
chapter6-p02-local-submersion
chapter6-p03-regular-normal-change-coordinates
chapter6-p04-interval-cones
chapter6-p05-product-cones
chapter6-p06-gradient-normals
chapter6-p07-smooth-majorant
chapter6-p08-optimality
chapter6-p09-proximal-normals
chapter6-p10-supporting-halfspaces
chapter6-p11-polarity
chapter6-p12-regular-tangents
chapter6-p13-generic-normal-continuity
chapter6-p14-elementary-cones
```

Some high-risk branches may be absent or may have reported a genuine blocker.
Integrate only branches that exist, are based on `b2eb4ea`, have a clean focused
commit, compile their assigned file, and contain no `sorry`, `admit`, `axiom`, or
placeholder result.  List missing or rejected branches explicitly rather than
silently replacing their scope.

## Pre-integration audit

For every existing candidate branch:

1. Inspect its merge base and commits relative to `b2eb4ea`.
2. Inspect the complete diff and confirm it changes only its assigned new Lean
   file.
3. Confirm that no shared documentation, ledger, or umbrella import was edited.
4. Check for unproved declarations and unsafe shortcuts.
5. Compile the assigned file from that branch.
6. Record the branch tip and whether it is accepted or rejected.

Do not use destructive Git commands.  Do not rewrite worker history.

## Integration order

Cherry-pick accepted commits in this order so foundational APIs land before
their likely consumers:

1. P1, P2, P3, P14
2. P4, P5
3. P6, P7, P8
4. P9, P10, P11, P12, P13

Resolve only mechanical conflicts.  If two branches independently introduce
incompatible definitions or theorem names, stop, analyze both APIs, and make the
smallest principled reconciliation in a separate integration edit.  In
particular:

- P11 owns the canonical polar-cone definition and naming.
- P12 owns the canonical regular-tangent definition and naming.
- P1 owns the generic public continuous-linear right-inverse API; P2 owns the
  nonlinear local-section API and should expose no competing generic helper.
- P14 owns the canonical public locality, singleton, and `univ` cone theorem
  names; P3/P4 helpers for those facts must remain private or result-specific.
- P09 owns generic public projection-to-regular-normal declarations; P10 must
  inline the calculation or keep helpers private/supporting-halfspace-specific.
- P5 owns generic binary `WithLp 2` product-cone infrastructure.
- P4 owns scalar interval/ray specializations.
- P3 owns the regular-normal formula for 6.7, while P1 and P2 provide the
  infrastructure for the later limiting-normal formula.

Do not weaken theorem statements merely to make two branches coexist.

## Shared repository edits

After accepted branches compile together:

1. Add their imports to `RockafellarWets/Chapter6.lean` in dependency order.
2. Update `CHAPTER6_COVERAGE.md` conservatively, result by result.  Mark a result
   `Exact` only if every substantive printed clause is proved.  Use `Partial` or
   `Adapted` when appropriate and explain every outstanding or corrected clause.
3. Update the Chapter 6 paragraphs and counts in `README.md` to agree with the
   ledger.  Do not claim coverage from a rejected or incomplete branch.
4. Update `RockafellarWets.lean` only if its existing Chapter 6 umbrella import
   does not already make the new modules available.
5. Keep the result rows, status counts, links, and imports internally consistent.

## Verification

Run, at minimum:

```text
lake build
python3 scripts/check_ledgers.py
git diff --check
```

Also search all changed Lean files for `sorry`, `admit`, `axiom`, temporary
debugging declarations, and placeholder comments.  Run focused `lake env lean`
checks while resolving any combined-build failures.  Do not suppress warnings or
disable linters to obtain a green build.

## Completion criteria

The task is complete only when:

- every accepted worker module builds together;
- the full `lake build` passes;
- `scripts/check_ledgers.py` passes;
- all coverage claims match the actual accepted theorem inventory;
- the worktree contains no unrelated changes; and
- the integration is committed with a descriptive commit message.

In the final report, provide:

- the integration commit hash;
- accepted and rejected/missing worker branches;
- the exact results whose ledger status changed;
- all verification commands and outcomes; and
- any remaining blockers that should become second-batch tasks.
