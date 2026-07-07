# CLAUDE.md — Minimum-balanced-bipartitions-of-planar-graphs

## Project

Lean 4 formalization of A. Shantanam, "Minimum balanced bipartitions of planar
triangulations," Discrete Mathematics 343 (2020) 111572. Author: math PhD,
learning Lean hands-on via agent sessions. `main_theorem` and
`folklore_conjecture` (MinBal/MainTheorem.lean) are proved modulo the assumed
results in the README ledger.

## Architecture (do not restructure without explicit instruction)

- `Project/Foundations/` — concrete layer: CombMap (rotation systems),
  SurfaceGraph/PlaneGraph/IsPlanar, BlockCutTree. Shared conceptually with the
  sibling repo Pancyclicity-in-4-connected-planar-graphs; future Mathlib
  contribution (rotation systems don't exist in Mathlib).
- `Project/MinBal/` — abstract NearTriangulation interface + proof chain.

## Non-negotiable conventions

- **Never introduce `axiom`.** Assumed facts are `theorem foo : T := sorry`
  with a doc comment: citation if external, triage bucket, reason assumed.
- **Never leave the author with a proof he can't explain.** After completing
  any proof, provide a line-by-line explanation of why each tactic closes its
  goal.
- **`lake build` green after every task.** If a change breaks the build and
  can't be fixed within the session, revert and report.
- **Stop-and-report over improvising** whenever repo reality contradicts your
  instructions or expectations.
- **Session log:** at the end of every session, append a dated summary (done /
  found / blocked) to `docs/session_log.md`. Append only — never edit past
  entries. Commit and push it.
- **Prover log:** every time a proof attempt on a lemma gets stuck or fails,
  append one line to `docs/prover_log.md` (date, lemma, model/tool, outcome).
  This feeds a planned benchmark paper — failures are data, record them.
- Small commits, descriptive messages. Search Mathlib before defining anything.
- Scope work to a single session; if a task won't fit, break it down first.

## CI notes (hard-won, do not regress)

- `blueprint.yml` had `lint: true` with no registered lint driver — removed;
  do not re-add without also registering a lint driver in lakefile.toml.
- `Project.lean` must stay in `lake exe mk_all` canonical (alphabetical)
  order; `mk_all-check` enforces this. Never track local scratch .lean files
  (e.g. FormalizationPlan.lean) — mk_all would demand importing them;
  .gitignore them instead.
- Workflow concurrency groups must be scoped per-workflow
  (blueprint-${{ github.ref }} vs build-${{ github.ref }}), or pushes make
  them cancel each other.

## Current milestone

Convert the 9 remaining `axiom` declarations to sorried theorems (statements
byte-identical), tag each with its ledger bucket (A: provable from
Foundations; B: provable combinatorics, deferred; C: deep external, cite —
Jackson–Yu, J. Graph Theory 41 (2002) 138–150), keep README ledger in sync.
Then: weekly-lemma pipeline on bucket-A items, starting with `induce_euler`.
