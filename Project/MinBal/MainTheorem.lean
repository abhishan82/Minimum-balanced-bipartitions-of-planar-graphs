-- Project/MinBal/MainTheorem.lean
-- The main theorem (Theorem 1.1) and the folklore conjecture corollary.
--
-- Theorem 1.1: Every plane triangulation has a balanced bipartition (V₁,V₂) such that
--   both G[V₁] and G[V₂] are connected near-triangulations and
--   b(G[V₁]) + b(G[V₂]) ≤ i(G[V₁]) + i(G[V₂]) + 2.
--
-- Corollary: e(V₁,V₂) ≤ n  (the folklore conjecture for planar graphs).

import Project.MinBal.Defs
import Project.MinBal.PlaneGraph
import Project.MinBal.Prop21
import Project.MinBal.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card

noncomputable section
open Classical

namespace MinBal

-- Only open Triangulation (not NearTriangulation) to avoid the `b` abbreviation clash.
open Triangulation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ## Main conclusion structure -/

/-- The conclusion of the main theorem for a bipartition `bp`. -/
structure MainConclusion (T : Triangulation G) (bp : Bipartition V) : Prop where
  balanced  : bp.IsBalanced
  nt₁       : HasNT G bp.V₁
  nt₂       : HasNT G bp.V₂
  -- Block count condition: b₁ + b₂ ≤ i₁ + i₂ + 2.
  -- Since NT.b = blockCount G, we state this directly in terms of graphs.
  -- We also need internal vertex counts; these depend on the outer face of each NT.
  -- For the blueprint, we store the bound as an existential over i₁, i₂.
  bcount    : ∃ (i₁ i₂ : ℕ),
    partBlockCount G bp.V₁ + partBlockCount G bp.V₂ ≤ i₁ + i₂ + 2 ∧
    -- Cor 2.2 witness: e(V₁,V₂) + (i₁+i₂) + 2 = n + (b₁+b₂)
    edgeCutSize G bp + (i₁ + i₂) + 2 =
      T.n + (partBlockCount G bp.V₁ + partBlockCount G bp.V₂)

/-! ## Separating triangles -/

/-- A separating triangle in G: a triangle {a,b,c} whose removal disconnects G. -/
structure SepTri (T : Triangulation G) where
  sa        : V
  sb        : V
  sc        : V
  hab       : sa ≠ sb
  hbc       : sb ≠ sc
  hac       : sa ≠ sc
  hadj_ab   : G.Adj sa sb
  hadj_bc   : G.Adj sb sc
  hadj_ac   : G.Adj sa sc
  sep       : ¬ (G.induce ({sa, sb, sc}ᶜ : Set V)).Connected

/-- A separating triangle is "balanced" if every connected component of G - {sa,sb,sc}
    has at least ⌊n/2⌋ - 1 vertices (where n = |V(G)|).
    Equivalently: no component has fewer than ⌊n/2⌋ - 1 vertices.
    We use ConnectedComponent.supp (a Set V) for component supports. -/
def SepTri.IsBalanced (T : Triangulation G) (st : SepTri T) : Prop :=
  let H := G.induce ({st.sa, st.sb, st.sc}ᶜ : Set V)
  ∀ (C : H.ConnectedComponent),
    Fintype.card V / 2 ≤ Set.ncard C.supp + 1

/-! ## Sink data (interface to the Jackson–Yu std-tree decomposition) -/

/-- **Bucket C** (deep external geometry; awaiting the std-tree decomposition
    construction — see README ledger).
    The data extracted from the (unformalized) directed std-tree decomposition
    of `T` once no balanced separating triangle exists: the sink component `S`
    — witnessed as a plane triangulation with no separating triangle of its
    own — together with a separating triangle of `G` whose vertices lie in
    `S` (this forces `S.card ≥ 4`), the sink's degree in the directed
    std-tree, and the interval navigation data threaded through the degree-1
    case (Prop 4.2).
    This is an opaque interface, mirroring how `NearTriangulation`/`toConcrete`
    are handled: it does NOT formalize the std-tree or the separating-triangle
    decomposition construction itself, only what the downstream case-analysis
    (Props 4.2, 4.4, and Section 5's `sink_navigation`) consumes. -/
structure SinkData (T : Triangulation G) where
  /-- The sink component's vertex set. -/
  S        : Finset V
  /-- `G[S]` is itself a plane triangulation. -/
  TS       : Triangulation (G.induce (↑S : Set V))
  /-- `S` has no separating triangle of its own (it is a genuine sink). -/
  noSepTri : ¬ Nonempty (SepTri TS)
  /-- `S` is cut off by some separating triangle of `G` (forces `S.card ≥ 4`). -/
  sepInG   : ∃ st : SepTri T, st.sa ∈ S ∧ st.sb ∈ S ∧ st.sc ∈ S
  /-- The sink's degree in the directed std-tree (opaque; used only to state
      the degree-1 vs degree-≥2 split). -/
  stDegree : ℕ
  /-- The interval navigation data threaded through the degree-1 case. -/
  I        : Finset V
  hI_small : I.card ≤ T.n / 2 + 1
  hS_I_tri : ∃ a b c : V, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ∈ I ∧ b ∈ I ∧ c ∈ I

/-! ## Special case propositions -/

/-- **Bucket A** (provable from Foundations; assumed for now — see README ledger).
    Separating triangle bipartition.
    Given a balanced separating triangle, there exists a bipartition where:
    - both parts are near-triangulations,
    - the bipartition is balanced,
    - the block counts satisfy b₁ + b₂ ≤ i₁ + i₂ + 2.
    The existence of such a bipartition and the NT structures come from the
    concrete plane graph geometry (combinatorial-map model).
    Reason assumed: geometric core of Prop. 4.1 — a separating triangle's
    two-region decomposition, read off the concrete embedding's face structure
    once `toConcrete`/`induceData` are available. -/
theorem sep_tri_bipartition
    (T  : Triangulation G)
    (st : SepTri T)
    (hb : st.IsBalanced T) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      blockCount (G.induce (↑bp.V₁ : Set V)) +
      blockCount (G.induce (↑bp.V₂ : Set V)) ≤
      internalVertCount NT₁.outer + internalVertCount NT₂.outer + 2 := sorry

/-- **Proposition 4.1 (warmup).**
    Handles the case where G has a "balanced" separating triangle.
    Uses `sep_tri_bipartition` for the geometric construction, then
    `cor_2_2_concrete` for the Corollary 2.2 identity. -/
theorem prop_4_1
    (T  : Triangulation G)
    (st : SepTri T)
    (hb : st.IsBalanced T) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  obtain ⟨bp, NT₁, NT₂, hbal, hbcount⟩ := sep_tri_bipartition T st hb
  refine ⟨bp, hbal, ⟨NT₁⟩, ⟨NT₂⟩, ?_⟩
  -- Apply cor_2_2_concrete to get the Cor 2.2 identity.
  have hcor := cor_2_2_concrete T bp NT₁ NT₂
  -- Witness i₁ = internalVertCount NT₁.outer, i₂ = internalVertCount NT₂.outer.
  exact ⟨internalVertCount NT₁.outer, internalVertCount NT₂.outer, hbcount, hcor⟩

/-- **Bucket B** (provable pure combinatorics; assumed for now — see README ledger).
    Degree-1 sink bipartition (paper Proposition 4.2).
    Given sink data `sd` whose std-tree degree is 1, there exists a balanced
    bipartition of `V(G)` such that both parts induce biconnected
    near-triangulations (blueprint `prop:onedegsink`). -/
theorem deg1_sink_bipartition
    (T  : Triangulation G)
    (sd : SinkData T)
    (hdeg1 : sd.stDegree = 1) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      IsBiconnected (G.induce (↑bp.V₁ : Set V)) ∧
      IsBiconnected (G.induce (↑bp.V₂ : Set V)) := sorry

/-- **Proposition 4.2 (degree-1 sink).**
    Handles the case where the sink of the standard tree has in-degree 1.
    Block-count bound is derived mechanically from biconnectivity via
    `biconnected_blockCount_eq_one` (each biconnected part has exactly 1
    block), rather than being asserted directly by `deg1_sink_bipartition`. -/
theorem prop_4_2
    (T  : Triangulation G)
    (sd : SinkData T)
    (hdeg1 : sd.stDegree = 1) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  obtain ⟨bp, NT₁, NT₂, hbal, hbc₁, hbc₂⟩ := deg1_sink_bipartition T sd hdeg1
  have hb₁ : partBlockCount G bp.V₁ = 1 := biconnected_blockCount_eq_one hbc₁
  have hb₂ : partBlockCount G bp.V₂ = 1 := biconnected_blockCount_eq_one hbc₂
  refine ⟨bp, hbal, ⟨NT₁⟩, ⟨NT₂⟩, ?_⟩
  refine ⟨internalVertCount NT₁.outer, internalVertCount NT₂.outer, ?_,
    cor_2_2_concrete T bp NT₁ NT₂⟩
  omega

/-- **Bucket B** (provable pure combinatorics; assumed for now — see README ledger).
    Tiny sink bipartition (paper **Proposition 4.4** — corrected from the
    former mislabel "4.3"; |V(S)| = 4, i.e. S ≅ K₄).
    Given sink data `sd` with `sd.S.card = 4`, there exists a balanced
    bipartition of `V(G)` such that both parts induce connected
    near-triangulations, with block count exceeding internal vertex count by
    at most 2 (blueprint `prop:sonly4`). -/
theorem tiny_sink_bipartition
    (T  : Triangulation G)
    (sd : SinkData T)
    (hS4 : sd.S.card = 4) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      blockCount (G.induce (↑bp.V₁ : Set V)) +
      blockCount (G.induce (↑bp.V₂ : Set V)) ≤
      internalVertCount NT₁.outer + internalVertCount NT₂.outer + 2 := sorry

/-- **Proposition 4.4 (tiny sink)** — corrected from the former mislabel "4.3"
    (this Lean declaration name is kept as `prop_4_3` for now; see session
    log — renaming it touches call sites and blueprint `\lean` tags, out of
    scope for a statement-faithfulness-only session).
    Handles the case where |V(S)| = 4 (S ≅ K₄). -/
theorem prop_4_3
    (T  : Triangulation G)
    (sd : SinkData T)
    (hS4 : sd.S.card = 4) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  obtain ⟨bp, NT₁, NT₂, hbal, hbcount⟩ := tiny_sink_bipartition T sd hS4
  exact ⟨bp, hbal, ⟨NT₁⟩, ⟨NT₂⟩,
    internalVertCount NT₁.outer, internalVertCount NT₂.outer,
    hbcount, cor_2_2_concrete T bp NT₁ NT₂⟩

/-- **Bucket C** (deep external geometry; assumed for now — see README ledger).
    No balanced sep-tri ⟹ sink `S` exists.
    When `G` has no balanced separating triangle, the directed std-tree
    decomposition — fully oriented by the negation of "balanced" (every
    sep-triangle's sink-side component has ≤ ⌊n/2⌋−2 vertices) — produces a
    genuine sink component, packaged as `SinkData`.
    Reason assumed: existence rests on the full std-tree orientation → sink
    argument, i.e. Jackson–Yu. The ⌊n/2⌋−2 bound stays upstream in `h`; it is
    deliberately not recorded as a `SinkData` field. -/
noncomputable def no_sep_tri_gives_sink
    (T : Triangulation G)
    (h : ¬ ∃ st : SepTri T, st.IsBalanced T) : SinkData T := sorry

/-! ## Section 5 — main navigation (NOT YET FORMALIZED) -/

/-- **Bucket C** (deep external geometry; NOT YET FORMALIZED — see README
    ledger). Paper Section 5 — the degree-≥2, |S|≥6 main navigation line, the
    technical core of the paper (navigation Lemmas `lemma_3_1`/`lemma_3_3`).
    This is the main outstanding mathematical content of the repository:
    Section 5 is currently an honest stub, not a deferred easy case. -/
theorem sink_navigation
    (T  : Triangulation G)
    (sd : SinkData T)
    (hdeg  : sd.stDegree ≥ 2)
    (hsize : sd.S.card ≥ 6) :
    ∃ bp : Bipartition V, MainConclusion T bp := sorry

/-! ## Case-split bridge facts -/

/-- **Bucket C** (rests on a paper-specific structural fact about the
    std-tree, not pure Finset arithmetic; assumed for now — see README
    ledger). Small bridge for the degree trichotomy in
    `main_theorem_no_sep_tri`: the sink's std-tree degree is never 0 (it has
    at least the incoming edge witnessed by `sd.sepInG`), so `≠ 1` gives
    `≥ 2`. Stated as its own sorried lemma rather than hand-waved. -/
theorem sinkData_stDegree_ge_two_of_ne_one
    (T : Triangulation G) (sd : SinkData T) (hne1 : sd.stDegree ≠ 1) :
    2 ≤ sd.stDegree := sorry

/-- **Bucket C** (rests on the paper's "≥1 edge" argument, not pure Finset
    arithmetic; assumed for now — see README ledger).
    Small bridge for the size trichotomy in `main_theorem_no_sep_tri`: a sink
    with `S.card ≠ 4` (and the generic `S.card ≥ 4` from `sd.sepInG`) has
    `S.card ≥ 6` — the author's "≥1 edge" argument rules out |S| = 5. Stated
    as its own sorried lemma rather than hand-waved. -/
theorem sinkData_card_ge_six_of_ne_four
    (T : Triangulation G) (sd : SinkData T) (hne4 : sd.S.card ≠ 4) :
    6 ≤ sd.S.card := sorry

/-- **Steps 2–5 of Theorem 1.1.**
    When `G` has no balanced separating triangle, obtains the sink `S` from
    `no_sep_tri_gives_sink` and splits three ways on its degree and size:
    degree 1 → Prop 4.2; degree ≥ 2 and |S| = 4 → Prop 4.4; degree ≥ 2 and
    |S| ≥ 6 → Section 5's `sink_navigation`. -/
theorem main_theorem_no_sep_tri
    (T : Triangulation G)
    (h : ¬ ∃ st : SepTri T, st.IsBalanced T) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  set sd := no_sep_tri_gives_sink T h
  by_cases hdeg1 : sd.stDegree = 1
  · exact prop_4_2 T sd hdeg1
  · by_cases hS4 : sd.S.card = 4
    · exact prop_4_3 T sd hS4
    · exact sink_navigation T sd
        (sinkData_stDegree_ge_two_of_ne_one T sd hdeg1)
        (sinkData_card_ge_six_of_ne_four T sd hS4)

/-! ## Main theorem -/

/-- **Theorem 1.1 (main theorem).**
    Every plane triangulation has a balanced bipartition with connected near-triangulation
    parts and block count ≤ internal vertex count + 2. -/
theorem main_theorem (T : Triangulation G) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  -- Step 1: reduce the "balanced separating triangle" case (Proposition 4.1).
  by_cases h_warmup : ∃ st : SepTri T, st.IsBalanced T
  · obtain ⟨st, hb⟩ := h_warmup
    exact prop_4_1 T st hb
  -- Steps 2–5: reduce to the 4-connected component case analysis.
  · exact main_theorem_no_sep_tri T h_warmup

/-! ## Folklore conjecture -/

/-- **Folklore conjecture (Corollary of Theorem 1.1).**
    Every plane triangulation G has a balanced bipartition with e(V₁,V₂) ≤ n. -/
theorem folklore_conjecture (T : Triangulation G) :
    ∃ bp : Bipartition V,
      bp.IsBalanced ∧ edgeCutSize G bp ≤ T.n := by
  obtain ⟨bp, hconc⟩ := main_theorem T
  refine ⟨bp, hconc.balanced, ?_⟩
  obtain ⟨i₁, i₂, hbcount, hcor22⟩ := hconc.bcount
  -- hcor22 : edgeCutSize + (i₁+i₂) + 2 = T.n + (b₁+b₂)
  -- hbcount : b₁+b₂ ≤ i₁+i₂+2
  -- Therefore: edgeCutSize = T.n + (b₁+b₂) - (i₁+i₂) - 2 ≤ T.n
  -- Bridge T.n abbreviation.
  have hTn : T.n = Fintype.card V := rfl
  rw [hTn] at hcor22
  omega

end MinBal

end -- noncomputable section
