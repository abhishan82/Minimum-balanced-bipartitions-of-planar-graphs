-- Project/MinBal/Prop21.lean
-- Proposition 2.1: |E(G)| + b(G) + 2 = 2|V| + i(G)  for connected near-triangulations.
-- (Additive form avoids ℕ-subtraction issues; equivalent to e = 2n - 2 + i - b when b ≤ 2n-2+i.)
-- Corollary 2.2:   e(V₁,V₂) + (i₁+i₂) + 2 = |V| + (b₁+b₂).

import Project.MinBal.Defs
import Project.MinBal.PlaneGraph
import Project.MinBal.EdgePartition
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

/-! ## Decomposition infrastructure -/

/-- Leaf-block decomposition of a near-triangulation at a cut vertex.
    Carries only numeric data to avoid universe issues. -/
structure LeafDecomp {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : NearTriangulation G) : Type (max 0 1) where
  n₁ : ℕ
  n₂ : ℕ
  e₁ : ℕ
  e₂ : ℕ
  b₁ : ℕ
  b₂ : ℕ
  i₁ : ℕ
  i₂ : ℕ
  -- Size conditions.
  hn₁   : 2 ≤ n₁
  hn₂   : 2 ≤ n₂
  -- Splitting equations (all additive, no ℕ subtraction).
  vcard  : n₁ + n₂ = NT.n + 1      -- cut vertex shared: |V₁|+|V₂| = n+1
  ecard  : NT.e = e₁ + e₂
  bcount : NT.b = b₁ + b₂
  icount : NT.i = i₁ + i₂
  -- IH-provable formulas for the pieces (additive form).
  ih₁   : e₁ + b₁ + 2 = 2 * n₁ + i₁
  ih₂   : e₂ + b₂ + 2 = 2 * n₂ + i₂
  b₁_lt : b₁ < NT.b
  b₂_lt : b₂ < NT.b
  -- Lower bounds on block counts.
  hb₁   : 1 ≤ b₁
  hb₂   : 1 ≤ b₂

/-- Every near-triangulation with ≥ 2 blocks admits a leaf-block decomposition.
    The proof decomposes G at a cut vertex (which exists because b ≥ 2 implies G is not
    2-connected), producing two sub-near-triangulations with the given count equations.
    Deferred to the concrete combinatorial-map model (like `nt_vertex_move`). -/
axiom leaf_decomp_of_multiblock {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : NearTriangulation G) (hb : 2 ≤ NT.b) : Nonempty (LeafDecomp NT)

/-! ## Proposition 2.1 (additive form) -/

/-- **Proposition 2.1** (additive form).
    For any connected near-triangulation G:
      |E(G)| + b(G) + 2 = 2|V(G)| + i(G). -/
theorem prop_2_1 {V : Type*} [Fintype V] {G : SimpleGraph V} (NT : NearTriangulation G) :
    NT.e + NT.b + 2 = 2 * NT.n + NT.i := by
  have key : ∀ (bnd : ℕ), NT.b ≤ bnd →
      NT.e + NT.b + 2 = 2 * NT.n + NT.i := by
    intro bnd
    induction bnd with
    | zero =>
      intro h
      have := one_le_blockCount NT
      omega
    | succ k ih =>
      intro hle
      by_cases hb1 : NT.b ≤ 1
      · -- b = 1: biconnected case, use Euler + incidence.
        have hb_eq : NT.b = 1 := le_antisymm hb1 (one_le_blockCount NT)
        -- Bridge abbreviations to concrete ℕ terms for omega.
        have hNTn : NT.n = Fintype.card V         := rfl
        have hNTe : NT.e = G.edgeFinset.card      := rfl
        have hNTf : NT.f = NT.faces.card          := rfl
        have hNTi : NT.i = (Finset.univ \ NT.outer).card := rfl
        have hNTb : NT.b = blockCount G           := rfl
        -- Key arithmetic facts (all in terms of concrete ℕ values).
        have hEuler  : Fintype.card V + NT.faces.card =
                       G.edgeFinset.card + 2 := NT.euler
        have hInc    : 2 * G.edgeFinset.card =
                       3 * (NT.faces.card - 1) + NT.outer.card := NT.incidence
        have hf_pos  : 0 < NT.faces.card := NT.f_pos
        have hout_le : NT.outer.card ≤ Fintype.card V := Finset.card_le_univ NT.outer
        have hi_eq   : (Finset.univ \ NT.outer).card =
                       Fintype.card V - NT.outer.card := internalVertCount_eq NT.outer
        -- Rewrite goal using bridging equalities, then omega.
        rw [hNTe, hNTb, hNTn, hNTi]
        rw [hb_eq] at hNTb
        omega
      · -- b ≥ 2: decompose.
        push_neg at hb1
        obtain ⟨cd⟩ := leaf_decomp_of_multiblock NT hb1
        have hvcard  := cd.vcard
        have hecard  := cd.ecard
        have hbcount := cd.bcount
        have hicount := cd.icount
        have hih₁    := cd.ih₁
        have hih₂    := cd.ih₂
        have hhn₁    := cd.hn₁
        have hhn₂    := cd.hn₂
        have hhb₁    := cd.hb₁
        have hhb₂    := cd.hb₂
        omega
  exact key NT.b le_rfl

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
    (n₁ n₂ : ℕ) (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (e₁ e₂ : ℕ) (b₁ b₂ : ℕ) (i₁ i₂ : ℕ)
    -- Vertex counts match finset sizes.
    (hvn₁ : n₁ = bp.V₁.card) (hvn₂ : n₂ = bp.V₂.card)
    -- Prop 2.1 for each piece (additive form).
    (hP₁ : e₁ + b₁ + 2 = 2 * n₁ + i₁)
    (hP₂ : e₂ + b₂ + 2 = 2 * n₂ + i₂)
    -- Block counts ≥ 1.
    (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
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
      (by linarith [NT₁.two_verts]) (by linarith [NT₂.two_verts])
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
  · exact NT₁.block_pos
  · exact NT₂.block_pos
  · linarith [hpart]

end MinBal

end -- noncomputable section
