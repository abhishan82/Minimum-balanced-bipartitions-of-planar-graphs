-- Project/MinBal/EdgePartition.lean
-- Proof of the edge partition identity:
--   edgeCutSize G bp + e(G[V₁]) + e(G[V₂]) = e(G)

import Project.MinBal.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Sym.Sym2

noncomputable section
open Classical

namespace MinBal

variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V}

/-! ## Sym2 membership lemma for cross edges -/

/-- An edge s(u,v) is a cross-edge iff (u ∈ V₁ ∧ v ∈ V₂) or (u ∈ V₂ ∧ v ∈ V₁). -/
private lemma isCrossEdge_mk (bp : Bipartition V) (u v : V) :
    IsCrossEdge bp s(u, v) ↔
    (u ∈ bp.V₁ ∧ v ∈ bp.V₂) ∨ (u ∈ bp.V₂ ∧ v ∈ bp.V₁) := by
  constructor
  · rintro ⟨a, ha₁, b, hb₂, habs⟩
    rw [Sym2.eq_iff] at habs
    rcases habs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ha₁, hb₂⟩
    · exact Or.inr ⟨hb₂, ha₁⟩
  · rintro (⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩)
    · exact ⟨u, hu₁, v, hv₂, rfl⟩
    · exact ⟨v, hv₁, u, hu₂, Sym2.eq_swap⟩

/-! ## Three-way partition of G.edgeFinset -/

-- The union is: ((cross ∪ V₁-edges) ∪ V₂-edges)
-- = edgeCut G bp ∪ (G.edgeFinset ∩ V₁.sym2) ∪ (G.edgeFinset ∩ V₂.sym2)
-- In terms of Or: left(left) = cross, left(right) = V₁, right = V₂

private theorem edgeFinset_union (bp : Bipartition V) :
    G.edgeFinset =
    edgeCut G bp ∪ (G.edgeFinset ∩ bp.V₁.sym2) ∪ (G.edgeFinset ∩ bp.V₂.sym2) := by
  ext e
  simp only [Finset.mem_union, Finset.mem_inter, edgeCut, Finset.mem_filter]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ u v =>
      have hu := bp.mem_V₁_or_V₂ u
      have hv := bp.mem_V₁_or_V₂ v
      rcases hu with hu₁ | hu₂ <;> rcases hv with hv₁ | hv₂
      · -- both in V₁ → left(right)
        exact Or.inl (Or.inr ⟨he, Finset.mk_mem_sym2_iff.mpr ⟨hu₁, hv₁⟩⟩)
      · -- u∈V₁, v∈V₂ → cross → left(left)
        exact Or.inl (Or.inl ⟨he, (isCrossEdge_mk bp u v).mpr (Or.inl ⟨hu₁, hv₂⟩)⟩)
      · -- u∈V₂, v∈V₁ → cross → left(left)
        exact Or.inl (Or.inl ⟨he, (isCrossEdge_mk bp u v).mpr (Or.inr ⟨hu₂, hv₁⟩)⟩)
      · -- both in V₂ → right
        exact Or.inr ⟨he, Finset.mk_mem_sym2_iff.mpr ⟨hu₂, hv₂⟩⟩
  · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he

private theorem disjoint_cross_v1 (bp : Bipartition V) :
    Disjoint (edgeCut G bp) (G.edgeFinset ∩ bp.V₁.sym2) := by
  rw [Finset.disjoint_left]
  intro e hcross hv1
  simp only [edgeCut, Finset.mem_filter] at hcross
  simp only [Finset.mem_inter] at hv1
  induction e using Sym2.ind with
  | _ u v =>
    rw [isCrossEdge_mk] at hcross
    obtain ⟨_, hmem₁⟩ := hv1
    rw [Finset.mk_mem_sym2_iff] at hmem₁
    rcases hcross.2 with ⟨_, hv₂⟩ | ⟨hu₂, _⟩
    · exact Finset.disjoint_left.mp bp.disjoint hmem₁.2 hv₂
    · exact Finset.disjoint_left.mp bp.disjoint hmem₁.1 hu₂

private theorem disjoint_crossv1_v2 (bp : Bipartition V) :
    Disjoint (edgeCut G bp ∪ (G.edgeFinset ∩ bp.V₁.sym2))
             (G.edgeFinset ∩ bp.V₂.sym2) := by
  rw [Finset.disjoint_left]
  intro e hleft hv2
  simp only [Finset.mem_union, edgeCut, Finset.mem_filter, Finset.mem_inter] at hleft
  simp only [Finset.mem_inter] at hv2
  -- Induct first so mk_mem_sym2_iff applies to the concrete s(u,v).
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨_, hmem₂⟩ := hv2
    rw [Finset.mk_mem_sym2_iff] at hmem₂
    rcases hleft with ⟨_, hcross⟩ | ⟨_, hmem₁⟩
    · rw [isCrossEdge_mk] at hcross
      rcases hcross with ⟨hu₁, _⟩ | ⟨_, hv₁⟩
      · exact Finset.disjoint_left.mp bp.disjoint hu₁ hmem₂.1
      · exact Finset.disjoint_left.mp bp.disjoint hv₁ hmem₂.2
    · rw [Finset.mk_mem_sym2_iff] at hmem₁
      exact Finset.disjoint_left.mp bp.disjoint hmem₁.1 hmem₂.1

/-! ## Edge count of an induced subgraph -/

/-- The image of induced edgeFinset under Subtype.val equals G.edgeFinset ∩ S.sym2. -/
private lemma induce_edgeFinset_image (S : Finset V) :
    (G.induce (↑S : Set V)).edgeFinset.image (Sym2.map Subtype.val) =
    G.edgeFinset ∩ S.sym2 := by
  ext e
  simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, Finset.mem_inter]
  constructor
  · rintro ⟨e', he', rfl⟩
    induction e' using Sym2.ind with
    | _ u v =>
      simp only [Sym2.map_mk]
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he'
      refine ⟨?_, Finset.mk_mem_sym2_iff.mpr ⟨Finset.mem_coe.mp u.2, Finset.mem_coe.mp v.2⟩⟩
      rwa [SimpleGraph.mem_edgeSet]
  · intro ⟨hadj, hmem⟩
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨hu, hv⟩ := Finset.mk_mem_sym2_iff.mp hmem
      refine ⟨s(⟨u, Finset.mem_coe.mpr hu⟩, ⟨v, Finset.mem_coe.mpr hv⟩), ?_, ?_⟩
      · exact SimpleGraph.induce_adj.mpr hadj
      · simp [Sym2.map_mk]

/-- Sym2.map Subtype.val is injective on induced edges. -/
private lemma sym2Map_val_injOn (S : Finset V) :
    Set.InjOn (Sym2.map (Subtype.val : S → V))
      ↑(G.induce (↑S : Set V)).edgeFinset := by
  intro e₁ _ e₂ _ h
  induction e₁ using Sym2.ind with
  | _ u₁ v₁ =>
    induction e₂ using Sym2.ind with
    | _ u₂ v₂ =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
      rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨Subtype.val_injective h₁, Subtype.val_injective h₂⟩
      · exact Or.inr ⟨Subtype.val_injective h₁, Subtype.val_injective h₂⟩

/-- The edge count of G[S] equals |G.edgeFinset ∩ S.sym2|. -/
private theorem induce_edgeFinset_card (S : Finset V) :
    (G.induce (↑S : Set V)).edgeFinset.card = (G.edgeFinset ∩ S.sym2).card := by
  rw [← induce_edgeFinset_image S]
  exact (Finset.card_image_of_injOn (sym2Map_val_injOn S)).symm

/-! ## Main theorem -/

/-- **Edge partition identity.**
    For any bipartition (V₁, V₂) of V:
      e(V₁,V₂) + e(G[V₁]) + e(G[V₂]) = e(G). -/
theorem edgePartition_card_proof (bp : Bipartition V) :
    edgeCutSize G bp +
    (G.induce (↑bp.V₁ : Set V)).edgeFinset.card +
    (G.induce (↑bp.V₂ : Set V)).edgeFinset.card =
    G.edgeFinset.card := by
  rw [induce_edgeFinset_card bp.V₁, induce_edgeFinset_card bp.V₂]
  conv_rhs => rw [edgeFinset_union bp]
  rw [Finset.card_union_of_disjoint (disjoint_crossv1_v2 bp),
      Finset.card_union_of_disjoint (disjoint_cross_v1 bp)]
  simp [edgeCutSize]

end MinBal

end -- noncomputable section
