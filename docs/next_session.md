# minbal — statement-faithfulness repair (restate & stub ONLY, zero proof work)

Read CLAUDE.md first. This session repairs statement-level unfaithfulness in the
main-theorem case analysis. EVERY declaration stays `:= sorry` — no proofs
attempted, no proofs removed. `lake build` must stay green throughout (a green
build here means "compiles with honest sorries", not "proved"). Work in small
commits, update the README ledger and blueprint to match, and STOP-and-report if
repo reality contradicts anything below rather than improvising a fix.

## Background (the bug being fixed)

The paper's Theorem 1.1 proof, once no *balanced* separating triangle exists
(balanced = each side ≥ ⌊n/2⌋−1 vertices; its negation, ≤ ⌊n/2⌋−2 on the
sink-side of every sep-triangle, fully orients the directed std-tree and forces
a SINK S to exist). The real case reduction is SEQUENTIAL:
- Prop 4.1 → balanced-sep-tri case (already present as `sep_tri_bipartition`/`prop_4_1`).
- No balanced sep-tri ⟹ sink S exists, S is a plane triangulation with no
  separating triangle of its own, |V(S)| ≥ 4.
- Prop 4.2 → handles std-tree-degree-1 sink; lets us assume degree ≥ 2.
- Prop 4.4 → handles |V(S)| = 4 (S ≅ K₄); lets us assume |V(S)| ≥ 6.
- Section 5 → the degree-≥2, |V(S)| ≥ 6 MAIN NAVIGATION line. This is the
  technical core of the paper and is CURRENTLY ABSENT from the Lean entirely.

Current Lean bugs:
1. `no_sep_tri_gives_sink` erases "the sink S" (a definite object) into
   existentially-quantified bare Finsets, and its right disjunct is the vacuous
   `∃ S_verts : Finset V, S_verts.card = 4` (true of any graph with ≥4 vertices).
2. `tiny_sink_bipartition`'s conclusion does not mention its hypothesis
   `S_verts` — as stated it asserts the main theorem with no real assumption.
3. Because of (1)+(2), `main_theorem_no_sep_tri` case-splits only two ways
   (→ prop_4_2 / prop_4_3) and the entire Section-5 |S|≥6 case is silently
   routed through the vacuous K₄ branch. Section 5 is MISSING, not deferred.
4. The Lean's `prop_4_3`/`tiny_sink_bipartition` actually realizes paper
   **Prop 4.4** (|S|=4), a mislabel.
5. Possible conclusion drift: blueprint's sep-tri prop concludes blocks ≤
   internal + **1** with G[V₁] **biconnected**, G[V₂] connected; Lean
   `sep_tri_bipartition` concludes **+2** with no biconnectivity. FLAG this for
   the author in the session log — do NOT silently change it; it may be an
   intentional weakening that still feeds the final +2 bound. Note it in the
   blueprint node comment as "Lean states the weaker +2 form; see author note."

## Task 1 — Introduce `SinkData` (interface, not construction)

Define a structure capturing exactly what the sink's downstream proofs consume.
Do NOT formalize the std-tree or the separating-triangle decomposition — this is
an opaque interface, mirroring how `NearTriangulation`/`toConcrete` are handled.
Fields (confirmed with author):
- `S : Finset V`  — the sink's vertex set
- a proof/field that `G.induce ↑S` is a plane triangulation with no separating
  triangle of its own (state via the existing predicates; if none exists,
  STOP and report rather than inventing one)
- `sepInG` : at least one triangle of S is separating in G (⟹ |S| ≥ 4)
- `stDegree : ℕ` — the sink's degree in the directed std-tree (opaque; used only
  to state the degree-1 vs degree-≥2 split)
- the interval / `I_verts`-style navigation data currently threaded through
  `deg1_sink_bipartition` (carry the same data as fields so the props can take
  `sd` instead of loose hypotheses)
Put it near the other MinBal interface defs. Doc-comment it as an interface to
the Jackson–Yu std-tree decomposition, bucket C provenance, awaiting Section 5 +
the decomposition construction.

## Task 2 — Restate `no_sep_tri_gives_sink` as sink-existence

Replace the vacuous disjunction with:
`(h : ¬ ∃ st : SepTri T, st.IsBalanced T) : ∃ sd : SinkData T, True`  — or, if
cleaner, return `SinkData T` directly under the hypothesis. The ⌊n/2⌋−2 bound
stays UPSTREAM in `h` (do not add it as a field). Keep it `:= sorry`, bucket C
(existence rests on full std-tree orientation → sink, i.e. Jackson–Yu). Update
doc comment to state exactly this.

## Task 3 — Repair the special-case props to consume `sd`

- `deg1_sink_bipartition` (paper Prop 4.2): take `(sd : SinkData T)` + a
  hypothesis `sd.stDegree = 1`; conclusion = the paper's 4.2 conclusion (both
  parts biconnected near-triangulations, per blueprint `prop:onedegsink`).
  Keep `:= sorry`, bucket B.
- `tiny_sink_bipartition` (paper **Prop 4.4**, FIX the mislabel in name-comment
  and doc): take `(sd : SinkData T)` + `sd.S.card = 4`; conclusion as paper 4.4.
  Keep `:= sorry`, bucket B.
- Ensure each hypothesis actually appears in the conclusion's witnesses or is
  genuinely used in the statement's meaning — no more orphaned hypotheses.

## Task 4 — Add the missing Section-5 case as an HONEST stub

Introduce a new declaration, e.g. `sink_navigation` (paper Section 5, the
degree-≥2 / |S| ≥ 6 main navigation line):
`(sd : SinkData T) (hdeg : sd.stDegree ≥ 2) (hsize : sd.S.card ≥ 6) :
   ∃ bp : Bipartition V, MainConclusion T bp := sorry`
Doc-comment: "Paper Section 5 — technical core, navigation lemmas
(lem:4con, lem:3con1). Bucket C. NOT YET FORMALIZED; this is the main
outstanding mathematical content of the repo."

## Task 5 — Make the case analysis three-way and faithful

Rewrite `main_theorem_no_sep_tri` so it: obtains `sd` from the repaired
`no_sep_tri_gives_sink`; splits on `sd.stDegree` (=1 → 4.2) and, for degree ≥ 2,
on `sd.S.card` (=4 → 4.4 ; ≥6 → `sink_navigation`). It must genuinely route the
|S|≥6 case through `sink_navigation`, not through the K₄ branch. `lake build`
green. If the degree/size trichotomy needs a small arithmetic bridge lemma
(e.g. |S| ≥ 4 ∧ ≠4 ∧ degree≥2 ⟹ ≥6 uses author's "≥1 edge" fact), state that
bridge as its own sorried lemma with a clear doc comment rather than hand-waving.

## Task 6 — Ledger, blueprint, honesty

- README ledger: add `sink_navigation` and any bridge lemma; re-bucket per above
  (expect: many former "A"s → B, `toConcrete`/`SinkData`-existence/`sink_navigation`
  → C). Add a prominent line: "Section 5 (|S|≥6 navigation) is NOT yet
  formalized — the main outstanding work." The ledger must now tell the true
  story: main_theorem compiles modulo these sorries INCLUDING one entire missing
  paper section.
- Blueprint: add nodes for `sink_navigation` and `SinkData`; add the +1/+2
  conclusion-drift note from bug #5. Regenerate lean_decls; `checkdecls` green.
- Verify locally, each command named in the session log: `lake build`,
  `lake exe checkdecls blueprint/lean_decls`, `leanblueprint pdf`,
  `leanblueprint web` — all exit 0.

## Task 7 — Close out

Update CLAUDE.md Current milestone to: "Statements faithful & Section-5 gap
explicit; next math work = formalize Section 5 (sink_navigation) as weekly
lemmas." Append dated session log (include the bug-5 flag for author decision
and the full before/after bucket table). Overwrite docs/next_session.md with a
prompt to begin Section 5 — but do NOT start Section 5 this session. Commit
granularly, push.

## Absolute constraints
- Zero proof work. Every declaration is `:= sorry` at session end.
- No `axiom`. No removing existing sorries. No touching Foundations.
- Green `lake build` at every commit.
- Any contradiction with repo reality → STOP and report, do not improvise.
