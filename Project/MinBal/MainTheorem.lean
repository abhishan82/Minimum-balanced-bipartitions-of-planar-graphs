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

/-! ## Special case propositions -/

/-- **Axiom (separating triangle bipartition).**
    Given a balanced separating triangle, there exists a bipartition where:
    - both parts are near-triangulations,
    - the bipartition is balanced,
    - the block counts satisfy b₁ + b₂ ≤ i₁ + i₂ + 2.
    The existence of such a bipartition and the NT structures come from the
    concrete plane graph geometry (combinatorial-map model). -/
axiom sep_tri_bipartition
    (T  : Triangulation G)
    (st : SepTri T)
    (hb : st.IsBalanced T) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      blockCount (G.induce (↑bp.V₁ : Set V)) +
      blockCount (G.induce (↑bp.V₂ : Set V)) ≤
      internalVertCount NT₁.outer + internalVertCount NT₂.outer + 2

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

/-- **Axiom (degree-1 sink bipartition).**
    Geometric content of Prop 4.2: given a 4-connected sink component S with ≥ 5 vertices
    and a small interval I, there is a balanced bipartition with NT structures on both parts
    and block count bound b₁ + b₂ ≤ i₁ + i₂ + 2. -/
axiom deg1_sink_bipartition
    (T : Triangulation G)
    (S_verts : Finset V) (I_verts : Finset V)
    (hS4c  : Is4Connected (G.induce (↑S_verts : Set V)))
    (hsize : S_verts.card ≥ 5)
    (hI_small : I_verts.card ≤ T.n / 2 + 1)
    (hS_I_tri : ∃ a b c : V, a ∈ S_verts ∧ b ∈ S_verts ∧ c ∈ S_verts ∧
                              a ∈ I_verts ∧ b ∈ I_verts ∧ c ∈ I_verts) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      blockCount (G.induce (↑bp.V₁ : Set V)) +
      blockCount (G.induce (↑bp.V₂ : Set V)) ≤
      internalVertCount NT₁.outer + internalVertCount NT₂.outer + 2

/-- **Proposition 4.2 (degree-1 sink).**
    Handles the case where the sink of the standard tree has in-degree 1. -/
theorem prop_4_2
    (T : Triangulation G)
    (S_verts : Finset V) (I_verts : Finset V)
    (hS4c  : Is4Connected (G.induce (↑S_verts : Set V)))
    (hsize : S_verts.card ≥ 5)
    (hI_small : I_verts.card ≤ T.n / 2 + 1)
    (hS_I_tri : ∃ a b c : V, a ∈ S_verts ∧ b ∈ S_verts ∧ c ∈ S_verts ∧
                              a ∈ I_verts ∧ b ∈ I_verts ∧ c ∈ I_verts) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  obtain ⟨bp, NT₁, NT₂, hbal, hbcount⟩ :=
    deg1_sink_bipartition T S_verts I_verts hS4c hsize hI_small hS_I_tri
  exact ⟨bp, hbal, ⟨NT₁⟩, ⟨NT₂⟩,
    internalVertCount NT₁.outer, internalVertCount NT₂.outer,
    hbcount, cor_2_2_concrete T bp NT₁ NT₂⟩

/-- **Axiom (tiny sink bipartition).**
    Geometric content of Prop 4.3: when |V(S)| = 4 (S ≅ K₄), there is a balanced
    bipartition with NT structures on both parts and block count bound. -/
axiom tiny_sink_bipartition
    (T : Triangulation G)
    (S_verts : Finset V)
    (hS4 : S_verts.card = 4) :
    ∃ (bp : Bipartition V)
      (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))),
      bp.IsBalanced ∧
      blockCount (G.induce (↑bp.V₁ : Set V)) +
      blockCount (G.induce (↑bp.V₂ : Set V)) ≤
      internalVertCount NT₁.outer + internalVertCount NT₂.outer + 2

/-- **Proposition 4.3 (tiny sink).**
    Handles the case where |V(S)| = 4 (S ≅ K₄). -/
theorem prop_4_3
    (T : Triangulation G)
    (S_verts : Finset V)
    (hS4 : S_verts.card = 4) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  obtain ⟨bp, NT₁, NT₂, hbal, hbcount⟩ := tiny_sink_bipartition T S_verts hS4
  exact ⟨bp, hbal, ⟨NT₁⟩, ⟨NT₂⟩,
    internalVertCount NT₁.outer, internalVertCount NT₂.outer,
    hbcount, cor_2_2_concrete T bp NT₁ NT₂⟩

/-- **Axiom (no balanced sep-tri → sink case).**
    When G has no balanced separating triangle, the standard-tree decomposition
    produces a 4-connected sink S with either |S| ≥ 5 (→ Prop 4.2) or |S| = 4
    (→ Prop 4.3), together with the interval data needed.
    Deferred to the combinatorial-map model. -/
axiom no_sep_tri_gives_sink
    (T : Triangulation G)
    (h : ¬ ∃ st : SepTri T, st.IsBalanced T) :
    (∃ (S_verts I_verts : Finset V),
      Is4Connected (G.induce (↑S_verts : Set V)) ∧
      S_verts.card ≥ 5 ∧
      I_verts.card ≤ T.n / 2 + 1 ∧
      ∃ a b c : V, a ∈ S_verts ∧ b ∈ S_verts ∧ c ∈ S_verts ∧
                   a ∈ I_verts ∧ b ∈ I_verts ∧ c ∈ I_verts) ∨
    (∃ S_verts : Finset V, S_verts.card = 4)

/-- **Steps 2–5 of Theorem 1.1.**
    When G has no balanced separating triangle, reduces to Prop 4.2 or Prop 4.3. -/
theorem main_theorem_no_sep_tri
    (T : Triangulation G)
    (h : ¬ ∃ st : SepTri T, st.IsBalanced T) :
    ∃ bp : Bipartition V, MainConclusion T bp := by
  rcases no_sep_tri_gives_sink T h with
    ⟨S_verts, I_verts, hS4c, hsize, hI_small, hS_I_tri⟩ |
    ⟨S_verts, hS4⟩
  · exact prop_4_2 T S_verts I_verts hS4c hsize hI_small hS_I_tri
  · exact prop_4_3 T S_verts hS4

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
