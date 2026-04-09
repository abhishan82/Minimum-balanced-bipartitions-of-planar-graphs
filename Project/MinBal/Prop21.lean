-- Project/MinBal/Prop21.lean
-- Proposition 2.1: |E(G)| + b(G) + 2 = 2|V| + i(G)  for connected near-triangulations.
-- (Additive form avoids ℕ-subtraction issues; equivalent to e = 2n - 2 + i - b when b ≤ 2n-2+i.)
-- Corollary 2.2:   e(V₁,V₂) + (i₁+i₂) + 2 = |V| + (b₁+b₂).

import Project.MinBal.Defs
import Project.MinBal.PlaneGraph
import Project.MinBal.EdgePartition
import Project.MinBal.ConcreteNT
import Project.Foundations.BlockCutTree
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Classical

namespace MinBal

open NearTriangulation Triangulation

/-! ## Helper: blockCount lower bound -/

/-- Every connected near-triangulation has at least 1 block. -/
lemma one_le_blockCount {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : NearTriangulation G) : 1 ≤ NT.b :=
  NT.block_pos

/-! ## Axiom: cut vertex decomposition (pure geometry, no IH) -/

/-- Cut vertex decomposition: a near-triangulation with ≥ 2 blocks splits at a cut vertex
    into two sub-near-triangulations satisfying the counting equations.
    Proved by lifting to a concrete plane NT via `NearTriangulation.toConcrete`,
    obtaining the cut vertex from `multiblock_has_cut_vertex`, then applying
    `concretePlaneNT_cut_vertex_decomp`. -/
theorem nt_cut_vertex_decomp_basic {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : NearTriangulation G) (hb : 2 ≤ NT.b) :
    ∃ (S₁ S₂ : Finset V)
      (NT₁ : NearTriangulation (G.induce (↑S₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑S₂ : Set V))),
      2 ≤ S₁.card ∧ 2 ≤ S₂.card ∧
      S₁.card + S₂.card = Fintype.card V + 1 ∧
      NT.e = NT₁.e + NT₂.e ∧
      NT.b = NT₁.b + NT₂.b ∧
      NT₁.b < NT.b ∧ NT₂.b < NT.b ∧
      1 ≤ NT₁.b ∧ 1 ≤ NT₂.b ∧
      NT.i = NT₁.i + NT₂.i := by
  obtain ⟨c, hcv⟩ := multiblock_has_cut_vertex NT.connected hb
  exact concretePlaneNT_cut_vertex_decomp NT c hcv hb

/-! ## Proposition 2.1 (additive form) -/

/-- Strong-induction auxiliary: Prop 2.1 holds for any NT with block count ≤ m.
    The induction is universally quantified over all vertex types and graphs,
    so the IH applies to the sub-pieces NT₁, NT₂ (which live in different types). -/
private theorem prop_2_1_aux (m : ℕ) :
    ∀ {V' : Type*} [Fintype V'] {G' : SimpleGraph V'} (NT' : NearTriangulation G'),
    NT'.b ≤ m → NT'.e + NT'.b + 2 = 2 * NT'.n + NT'.i := by
  induction m with
  | zero =>
    intro V' _ G' NT' h
    exact absurd h (Nat.not_le.mpr (one_le_blockCount NT'))
  | succ k ih =>
    intro V' _ G' NT' hle
    by_cases hb1 : NT'.b ≤ 1
    · -- b' = 1: biconnected case, use Euler + incidence.
      have hb_eq : NT'.b = 1 := le_antisymm hb1 (one_le_blockCount NT')
      have hEuler  : Fintype.card V' + NT'.faces.card =
                     G'.edgeFinset.card + 2 := NT'.euler
      have hInc    : 2 * G'.edgeFinset.card =
                     3 * (NT'.faces.card - 1) + NT'.outer.card := NT'.incidence
      have hf_pos  : 0 < NT'.faces.card := NT'.f_pos
      have hout_le : NT'.outer.card ≤ Fintype.card V' := Finset.card_le_univ NT'.outer
      have hi_eq   : internalVertCount NT'.outer =
                     Fintype.card V' - NT'.outer.card := internalVertCount_eq NT'.outer
      -- blockCount G' = 1 (from hb_eq and the abbrev NT'.b = blockCount G').
      have hbc1 : blockCount G' = 1 := hb_eq
      -- Unfold abbreviations and let omega close the goal.
      show G'.edgeFinset.card + blockCount G' + 2 =
           2 * Fintype.card V' + internalVertCount NT'.outer
      rw [hi_eq, hbc1]
      omega
    · -- b' ≥ 2: decompose at a cut vertex.
      push_neg at hb1
      obtain ⟨S₁, S₂, NT₁, NT₂, hn₁, hn₂, hvcard, hecard, hbcount,
              hb₁_lt, hb₂_lt, hb₁, hb₂, hicount⟩ :=
        nt_cut_vertex_decomp_basic NT' hb1
      -- Apply IH to each sub-piece (both have block count ≤ k).
      have hih₁ : NT₁.e + NT₁.b + 2 = 2 * NT₁.n + NT₁.i :=
        ih NT₁ (by omega)
      have hih₂ : NT₂.e + NT₂.b + 2 = 2 * NT₂.n + NT₂.i :=
        ih NT₂ (by omega)
      -- Bridge NT₁.n = S₁.card and NT₂.n = S₂.card.
      have hNT₁n : NT₁.n = S₁.card := by
        show Fintype.card ↥(↑S₁ : Set V') = S₁.card
        rw [← Set.toFinset_card, Finset.toFinset_coe]
      have hNT₂n : NT₂.n = S₂.card := by
        show Fintype.card ↥(↑S₂ : Set V') = S₂.card
        rw [← Set.toFinset_card, Finset.toFinset_coe]
      -- Bridge: NT'.n, NT₁.n = S₁.card, NT₂.n = S₂.card (all abbrev-transparent).
      have hNT'n : NT'.n = Fintype.card V' := rfl
      -- Rewrite IH conclusions to use S₁.card / S₂.card.
      rw [hNT₁n] at hih₁
      rw [hNT₂n] at hih₂
      -- NT₁.i, NT₂.i, NT'.i are all `internalVertCount .outer` by definition.
      -- hicount : NT'.i = NT₁.i + NT₂.i connects the three.
      -- omega sees: hecard, hbcount, hicount, hvcard, hNT'n, hih₁, hih₂.
      omega

/-- **Proposition 2.1** (additive form).
    For any connected near-triangulation G:
      |E(G)| + b(G) + 2 = 2|V(G)| + i(G). -/
theorem prop_2_1 {V : Type*} [Fintype V] {G : SimpleGraph V} (NT : NearTriangulation G) :
    NT.e + NT.b + 2 = 2 * NT.n + NT.i :=
  prop_2_1_aux NT.b NT le_rfl

/-! ## Cut vertex decomposition (full form, with Prop 2.1 IH) -/

/-- **Cut vertex decomposition** (full form).
    Derives the Prop 2.1 IH conclusions for the sub-pieces from `prop_2_1`,
    avoiding circularity: `nt_cut_vertex_decomp_basic` provides the geometry;
    `prop_2_1` (already proved) supplies the IH. -/
theorem nt_cut_vertex_decomp {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : NearTriangulation G) (hb : 2 ≤ NT.b) :
    ∃ (S₁ S₂ : Finset V)
      (NT₁ : NearTriangulation (G.induce (↑S₁ : Set V)))
      (NT₂ : NearTriangulation (G.induce (↑S₂ : Set V))),
      2 ≤ S₁.card ∧ 2 ≤ S₂.card ∧
      S₁.card + S₂.card = Fintype.card V + 1 ∧
      NT.e = NT₁.e + NT₂.e ∧
      NT.b = NT₁.b + NT₂.b ∧
      NT₁.b < NT.b ∧ NT₂.b < NT.b ∧
      1 ≤ NT₁.b ∧ 1 ≤ NT₂.b ∧
      NT.i = NT₁.i + NT₂.i ∧
      NT₁.e + NT₁.b + 2 = 2 * S₁.card + NT₁.i ∧
      NT₂.e + NT₂.b + 2 = 2 * S₂.card + NT₂.i := by
  obtain ⟨S₁, S₂, NT₁, NT₂, hn₁, hn₂, hvcard, hecard, hbcount,
          hb₁_lt, hb₂_lt, hb₁, hb₂, hicount⟩ :=
    nt_cut_vertex_decomp_basic NT hb
  have hih₁ := prop_2_1 NT₁
  have hih₂ := prop_2_1 NT₂
  have hNT₁n : NT₁.n = S₁.card := by
    show Fintype.card ↥(↑S₁ : Set V) = S₁.card
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  have hNT₂n : NT₂.n = S₂.card := by
    show Fintype.card ↥(↑S₂ : Set V) = S₂.card
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  exact ⟨S₁, S₂, NT₁, NT₂, hn₁, hn₂, hvcard, hecard, hbcount, hb₁_lt, hb₂_lt, hb₁, hb₂,
         hicount, hNT₁n ▸ hih₁, hNT₂n ▸ hih₂⟩

/-! ## Edge partition identity -/

/-- The edge count of G equals the edge cut size plus the edge counts of the two induced parts. -/
theorem edgePartition_card
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (bp : Bipartition V) :
    edgeCutSize G bp +
    (G.induce (↑bp.V₁ : Set V)).edgeFinset.card +
    (G.induce (↑bp.V₂ : Set V)).edgeFinset.card =
    G.edgeFinset.card :=
  edgePartition_card_proof bp

/-! ## Corollary 2.2 (additive form) -/

/-- **Corollary 2.2** (additive form).
    For a triangulation G and bipartition bp where the two pieces are near-triangulations
    with combined edge/block/internal counts satisfying Prop 2.1:
      e(V₁,V₂) + (i₁+i₂) + 2 = n + (b₁+b₂).

    Hypotheses in additive form to avoid ℕ-subtraction in omega. -/
theorem cor_2_2
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T    : Triangulation G)
    (bp   : Bipartition V)
    -- Combined counts for the two pieces.
    (n₁ n₂ : ℕ)
    (e₁ e₂ : ℕ) (b₁ b₂ : ℕ) (i₁ i₂ : ℕ)
    -- Vertex counts match finset sizes.
    (hvn₁ : n₁ = bp.V₁.card) (hvn₂ : n₂ = bp.V₂.card)
    -- Prop 2.1 for each piece (additive form).
    (hP₁ : e₁ + b₁ + 2 = 2 * n₁ + i₁)
    (hP₂ : e₂ + b₂ + 2 = 2 * n₂ + i₂)
    -- Edge partition identity.
    (hpart : edgeCutSize G bp + e₁ + e₂ = T.e) :
    edgeCutSize G bp + (i₁ + i₂) + 2 = T.n + (b₁ + b₂) := by
  -- Bridge abbreviations.
  have hTe : T.e = G.edgeFinset.card := rfl
  have hTn : T.n = Fintype.card V    := rfl
  -- |E(T)| + 6 = 3n (additive form of e = 3n - 6).
  have hE : G.edgeFinset.card + 6 = 3 * Fintype.card V := by
    have h1 : G.edgeFinset.card = 3 * Fintype.card V - 6 := T.edge_count
    have h2 : 3 ≤ Fintype.card V := T.three_verts
    omega
  -- n₁ + n₂ = n.
  have hn : bp.V₁.card + bp.V₂.card = Fintype.card V := bp.card_add
  -- Rewrite hpart using concrete T.e.
  rw [hTe] at hpart
  -- Rewrite goal using concrete T.n.
  rw [hTn]
  omega

/-! ## Corollary 2.2 — concrete form -/

/-- **Corollary 2.2** (concrete form).
    When both induced parts are near-triangulations (so Prop 2.1 applies to each),
    we can derive the edge partition identity from `edgePartition_card` and obtain:
      e(V₁,V₂) + (i₁+i₂) + 2 = n + (b₁+b₂)
    directly, without requiring the user to supply `hpart`. -/
theorem cor_2_2_concrete
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (T   : Triangulation G)
    (bp  : Bipartition V)
    (NT₁ : NearTriangulation (G.induce (↑bp.V₁ : Set V)))
    (NT₂ : NearTriangulation (G.induce (↑bp.V₂ : Set V))) :
    edgeCutSize G bp +
      (internalVertCount NT₁.outer + internalVertCount NT₂.outer) + 2 =
    T.n + (blockCount (G.induce (↑bp.V₁ : Set V)) +
           blockCount (G.induce (↑bp.V₂ : Set V))) := by
  -- Abbreviate the two induced edge counts.
  set e₁ := (G.induce (↑bp.V₁ : Set V)).edgeFinset.card
  set e₂ := (G.induce (↑bp.V₂ : Set V)).edgeFinset.card
  -- The edge partition identity.
  have hpart : edgeCutSize G bp + e₁ + e₂ = T.e := by
    have h := edgePartition_card (G := G) bp
    simp only [e₁, e₂]
    linarith [h]
  -- Prop 2.1 for each part, rewriting using NT abbreviations.
  have hP₁ := prop_2_1 NT₁
  have hP₂ := prop_2_1 NT₂
  -- Bridge: NT₁.n = bp.V₁.card (both equal Fintype.card ↥bp.V₁).
  have hn₁ : NT₁.n = bp.V₁.card := by
    simp only [NearTriangulation.n]
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  have hn₂ : NT₂.n = bp.V₂.card := by
    simp only [NearTriangulation.n]
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  -- Apply cor_2_2 with e₁ = NT₁.e, etc.
  apply cor_2_2 T bp NT₁.n NT₂.n
      e₁ e₂
      (blockCount (G.induce (↑bp.V₁ : Set V)))
      (blockCount (G.induce (↑bp.V₂ : Set V)))
      (internalVertCount NT₁.outer)
      (internalVertCount NT₂.outer)
  · exact hn₁
  · exact hn₂
  · -- hP₁: NT₁.e + NT₁.b + 2 = 2*NT₁.n + NT₁.i
    -- rewrite in terms of e₁
    have he₁ : NT₁.e = e₁ := rfl
    have hb₁ : NT₁.b = blockCount (G.induce (↑bp.V₁ : Set V)) := rfl
    have hi₁ : NT₁.i = internalVertCount NT₁.outer := rfl
    linarith [hP₁]
  · have he₂ : NT₂.e = e₂ := rfl
    have hb₂ : NT₂.b = blockCount (G.induce (↑bp.V₂ : Set V)) := rfl
    have hi₂ : NT₂.i = internalVertCount NT₂.outer := rfl
    linarith [hP₂]
  · linarith [hpart]

end MinBal

end -- noncomputable section
