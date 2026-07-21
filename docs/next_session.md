# minbal — begin Section 5 (sink_navigation) decomposition, zero proof work

Read CLAUDE.md first. `sink_navigation` (MinBal/MainTheorem.lean) is currently
one big honest stub for the paper's Section 5 — the degree-≥2, |V(S)|≥6 main
navigation line, the technical core of the paper. This session's job is to
DECOMPOSE it into a sequence of smaller sorried sub-lemmas, mirroring how
Section 3's navigation is already split into `lemma_3_1`/`lemma_3_3`/
`lemma_3_5` rather than left as one monolithic sorry. Do NOT attempt any
proofs. `lake build` must stay green throughout (green = "compiles with
honest sorries," not "proved").

## Task 1 — Re-derive Section 5's actual structure

You don't have the paper PDF in-repo. Work from what's available:
`sink_navigation`'s current statement, `SinkData`'s fields, the Section-3
navigation lemmas it's supposed to use (`lemma_3_1`, `lemma_3_3`,
`lemma_3_5` in Lemmas.lean — read their statements and proofs for the
pattern), and blueprint `prop:sinknav`'s prose ("using the navigation
Lemmas 3.1 and 3.3 to build the bipartition incrementally"). If you cannot
reconstruct a faithful decomposition from these sources alone — STOP and
report exactly what's missing (e.g. "need the paper's Section 5 text") rather
than inventing intermediate lemma statements you're not confident in.

## Task 2 — Propose the decomposition (in the session log first)

Before touching any `.lean` file, write the proposed sequence of sub-lemmas
(names, statements, how they compose to give `sink_navigation`) into the
session log as a plan. This is a review checkpoint — the author reads it
before the next session's Lean edits happen, same pattern as the bucket-review
step from 2026-07-13.

## Task 3 — Stub the sub-lemmas (if the decomposition is confident)

Only if Task 1 produced a decomposition you're actually confident is
faithful: add the sub-lemmas as `:= sorry` declarations (bucket C, doc
comments citing what part of Section 5 each covers), and rewrite
`sink_navigation`'s proof to chain them (still `:= sorry`-free chaining is
fine since it's just composition, but if any step needs new reasoning beyond
plugging sub-lemmas together, sorry that step honestly instead). If Task 1
was inconclusive, skip this task and just report the blocker.

## Task 4 — Ledger, blueprint, verification

Update the README ledger and blueprint `def:sinkdata`/`prop:sinknav` region
to reflect the new sub-lemma nodes (bucket C, `\uses{}` edges into
`prop:sinknav`). Regenerate `blueprint/lean_decls`. Verify locally, each
command named in the session log: `lake build`, `lake exe checkdecls
blueprint/lean_decls`, `leanblueprint pdf`, `leanblueprint web` — all exit 0.

## Task 5 — Close out

Update CLAUDE.md's Current milestone. Append dated session log entry
(include the proposed decomposition from Task 2, and NOTE whether Task 3
actually ran or was skipped as blocked). Overwrite `docs/next_session.md`
with a prompt for the first real proof attempt on the easiest sub-lemma
(same weekly-lemma constraints as the sibling repo: no new axioms/sorries
beyond the stub itself, statement unchanged, search Mathlib+Foundations
first, 3-strategies-then-stop, walkthrough on success, prover_log either
way). Commit granularly, push.

## Absolute constraints
- Zero proof work. Every declaration is `:= sorry` at session end (aside
  from pure composition/chaining, if any).
- No `axiom`. No removing existing sorries. No touching Foundations.
- Green `lake build` at every commit.
- Any contradiction with repo reality, or inability to reconstruct a
  faithful decomposition → STOP and report, do not improvise.
