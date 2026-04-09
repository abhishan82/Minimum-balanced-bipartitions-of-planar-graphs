/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Project.MinBal.Defs
import Project.MinBal.PlaneGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic

/-!
# Block-Cut Tree (Basic)

This file develops the connection between blocks and cut vertices for finite simple graphs.

## Main results

* `IsBiconnected_iff_no_cut_vertex`: a connected graph on ≥ 3 vertices is biconnected
  iff it has no cut vertex.
* `blocks_share_at_most_one_vertex`: two distinct blocks share at most one vertex.
* `multiblock_has_cut_vertex`: if `blockCount G ≥ 2` then `G` has a cut vertex.

## References

* [R. Diestel, *Graph Theory*][diestel2017], Chapter 3
-/

noncomputable section
open Classical

namespace MinBal

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Biconnectivity and cut vertices -/

/-- A biconnected graph on ≥ 3 vertices has no cut vertex. -/
lemma IsBiconnected.no_cut_vertex (hbc : IsBiconnected G)
    (hn : 3 ≤ Fintype.card V) (v : V) : ¬IsCutVertex G v := by
  intro ⟨_, hdisconn⟩
  rcases hbc.2 with hcard | hconn
  · omega
  · exact hdisconn (hconn v)

/-- A connected graph with no cut vertex is biconnected. -/
lemma biconnected_of_no_cut_vertex (hconn : G.Connected)
    (h : ∀ v : V, ¬IsCutVertex G v) : IsBiconnected G :=
  ⟨hconn, Or.inr fun v => by
    by_contra hdisconn
    exact h v ⟨hconn, hdisconn⟩⟩

/-- Biconnectivity is equivalent to: connected + no cut vertex (for n ≥ 3). -/
theorem IsBiconnected_iff_no_cut_vertex (hconn : G.Connected) (hn : 3 ≤ Fintype.card V) :
    IsBiconnected G ↔ ∀ v : V, ¬IsCutVertex G v :=
  ⟨fun hbc v => hbc.no_cut_vertex hn v,
   biconnected_of_no_cut_vertex hconn⟩

/-! ## Blocks share at most one vertex -/

/-! ## Vertex deletion on induced subgraphs -/

/-- Removing a vertex from an induced subgraph is isomorphic to inducing on the sdiff
    in the ambient graph: `(G.induce S).induce {w | w ≠ v} ≃g G.induce (S \ {v})`.

    This is the key rewrite needed to translate biconnectivity (which removes a vertex
    of the induced subgraph type) into a statement about the ambient induced subgraph. -/
def induceSdiffIso (S : Finset V) (v : ↥(↑S : Set V)) :
    (G.induce (↑S : Set V)).induce {w : ↥(↑S : Set V) | w ≠ v} ≃g
    G.induce (↑(S \ {v.val}) : Set V) where
  toFun := fun ⟨⟨w, hwS⟩, hw⟩ => ⟨w, by
    rw [Finset.coe_sdiff, Finset.coe_singleton]
    exact ⟨hwS, fun h => hw (Subtype.ext h)⟩⟩
  invFun := fun ⟨w, hw⟩ =>
    ⟨⟨w, by rw [Finset.coe_sdiff, Finset.coe_singleton] at hw; exact hw.1⟩,
     fun h => by
       rw [Finset.coe_sdiff, Finset.coe_singleton] at hw
       exact hw.2 (congrArg Subtype.val h)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := Iff.rfl

omit [Fintype V] in
/-- Connectivity of the vertex-deleted induced subgraph equals connectivity of the sdiff. -/
lemma induce_sdiff_connected_iff (S : Finset V) (v : ↥(↑S : Set V)) :
    ((G.induce (↑S : Set V)).induce {w : ↥(↑S : Set V) | w ≠ v}).Connected ↔
    (G.induce (↑(S \ {v.val}) : Set V)).Connected :=
  (induceSdiffIso S v).connected_iff

/-! ## Biconnected union -/

omit [Fintype V] in
/-- Helper: G[S₁\{w}] is connected when G[S₁] is biconnected and w ∈ S₁. -/
private lemma IsBiconnected.remove_connected
    {S : Finset V} (hbc : IsBiconnected (G.induce (↑S : Set V))) {w : V} (hw : w ∈ S) :
    (G.induce (↑(S \ {w}) : Set V)).Connected := by
  rcases hbc.2 with hcard | hconn
  · -- |S| = 2: S \ {w} is a singleton, which is connected.
    have hScard : Fintype.card ↥(↑S : Set V) = S.card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    have h1 : (S \ {w}).card = 1 := by
      rw [← Finset.erase_eq, Finset.card_erase_of_mem hw]
      omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    rw [hu]
    haveI : Nonempty ↥(↑({u} : Finset V) : Set V) :=
      ⟨⟨u, by simp⟩⟩
    haveI : Subsingleton ↥(↑({u} : Finset V) : Set V) := by
      constructor; intro ⟨a, ha⟩ ⟨b, hb⟩
      simp at ha hb; exact Subtype.ext (ha.trans hb.symm)
    exact SimpleGraph.Connected.of_subsingleton
  · -- G[S] is biconnected with vertex-removal: use induceSdiffIso to transfer.
    rw [← induce_sdiff_connected_iff S ⟨w, hw⟩]
    exact hconn ⟨w, hw⟩

omit [Fintype V] in
/-- Helper: `induce_union_connected` restated with Finset coercions. -/
private lemma induce_union_conn {S₁ S₂ : Finset V}
    (h₁ : (G.induce (↑S₁ : Set V)).Preconnected)
    (h₂ : (G.induce (↑S₂ : Set V)).Preconnected)
    (hne : (S₁ ∩ S₂).Nonempty) :
    (G.induce (↑(S₁ ∪ S₂) : Set V)).Connected := by
  rw [Finset.coe_union]
  apply SimpleGraph.induce_union_connected h₁ h₂
  rw [← Finset.coe_inter]
  exact Finset.coe_nonempty.mpr hne

omit [Fintype V] in
/-- If G[S₁] and G[S₂] are both biconnected and |S₁ ∩ S₂| ≥ 2,
    then G[S₁ ∪ S₂] is biconnected. -/
theorem isBiconnected_induce_union {S₁ S₂ : Finset V}
    (h₁ : IsBiconnected (G.induce (↑S₁ : Set V)))
    (h₂ : IsBiconnected (G.induce (↑S₂ : Set V)))
    (hinter : 2 ≤ (S₁ ∩ S₂).card) :
    IsBiconnected (G.induce (↑(S₁ ∪ S₂) : Set V)) := by
  have hne : (S₁ ∩ S₂).Nonempty := Finset.card_pos.mp (by omega)
  -- Connectivity of the union.
  have hconn_union : (G.induce (↑(S₁ ∪ S₂) : Set V)).Connected :=
    induce_union_conn h₁.1.preconnected h₂.1.preconnected hne
  refine ⟨hconn_union, Or.inr ?_⟩
  -- For any w in S₁ ∪ S₂, show G[(S₁ ∪ S₂) \ {w}] is connected.
  intro ⟨w, hw⟩
  -- Use induceSdiffIso: goal becomes G[↑((S₁∪S₂)\{w})] is connected.
  rw [induce_sdiff_connected_iff (S₁ ∪ S₂) ⟨w, hw⟩]
  -- Helper: get a witness u ∈ (S₁ ∩ S₂) with u ≠ w.
  obtain ⟨u, hu, v, hv, huvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (S₁ ∩ S₂).card)
  -- At least one of u, v is ≠ w; pick it.
  have hex : ∃ z ∈ S₁ ∩ S₂, z ≠ w := by
    rcases ne_or_eq u w with h | rfl
    · exact ⟨u, hu, h⟩
    · exact ⟨v, hv, huvne.symm⟩
  obtain ⟨z, hzinter, hzw⟩ := hex
  -- Decompose: (S₁ ∪ S₂) \ {w} = (S₁ \ {w}) ∪ (S₂ \ {w})
  have heq : (S₁ ∪ S₂) \ {w} = S₁ \ {w} ∪ (S₂ \ {w}) := by
    ext a; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]; tauto
  rw [heq]
  -- Both parts are connected.
  have hconn₁ : (G.induce ↑(S₁ \ {w})).Connected := by
    by_cases hw₁ : w ∈ S₁
    · exact h₁.remove_connected hw₁
    · have : (S₁ \ {w} : Finset V) = S₁ := by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨And.left, fun ha => ⟨ha, fun h => hw₁ (h ▸ ha)⟩⟩
      rw [this]; exact h₁.1
  have hconn₂ : (G.induce ↑(S₂ \ {w})).Connected := by
    by_cases hw₂ : w ∈ S₂
    · exact h₂.remove_connected hw₂
    · have : (S₂ \ {w} : Finset V) = S₂ := by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨And.left, fun ha => ⟨ha, fun h => hw₂ (h ▸ ha)⟩⟩
      rw [this]; exact h₂.1
  -- The intersection (S₁ \ {w}) ∩ (S₂ \ {w}) contains z.
  apply induce_union_conn hconn₁.preconnected hconn₂.preconnected
  exact ⟨z, Finset.mem_inter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hzinter).1, by simpa using hzw⟩,
     Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hzinter).2, by simpa using hzw⟩⟩⟩

/-- Two distinct blocks cannot share two or more vertices. -/
theorem blocks_share_le_one
    {S₁ S₂ : Finset V}
    (hB₁ : IsBlock G S₁) (hB₂ : IsBlock G S₂) (hne : S₁ ≠ S₂) :
    (S₁ ∩ S₂).card ≤ 1 := by
  by_contra h
  push_neg at h
  -- G[S₁ ∪ S₂] is biconnected (from the axiom).
  have hbc_union : IsBiconnected (G.induce (↑(S₁ ∪ S₂) : Set V)) :=
    isBiconnected_induce_union hB₁.1 hB₂.1 h
  -- S₂ ⊄ S₁: if S₂ ⊆ S₁ and S₂ ≠ S₁ then S₂ ⊊ S₁, contradicting maximality of S₂.
  have hS₂_not_sub : ¬(S₂ ⊆ S₁) := by
    intro hS₂sub
    exact hB₂.2 S₁
      (Finset.ssubset_iff_subset_ne.mpr ⟨hS₂sub, hne.symm⟩) hB₁.1
  -- S₁ ≠ S₁ ∪ S₂: otherwise S₂ ⊆ S₁, contradicting hS₂_not_sub.
  have hne_union : S₁ ≠ S₁ ∪ S₂ := by
    intro heq
    apply hS₂_not_sub
    intro v hv
    have hmem : v ∈ S₁ ∪ S₂ := Finset.mem_union_right S₁ hv
    rwa [← heq] at hmem
  -- S₁ ⊊ S₁ ∪ S₂.
  have hsub : S₁ ⊂ S₁ ∪ S₂ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, hne_union⟩
  -- But IsBlock G S₁ says no proper biconnected superset of S₁ exists.
  exact hB₁.2 (S₁ ∪ S₂) hsub hbc_union

/-! ## Multiple blocks imply a cut vertex -/

/-- A connected graph with ≥ 2 blocks has a cut vertex.
    Proof: If no cut vertex existed, G would be biconnected, making `G.induce ↑Finset.univ`
    biconnected. But then the maximality field of any block B ⊊ Finset.univ would be violated,
    contradicting the existence of ≥ 2 distinct blocks. -/
theorem multiblock_has_cut_vertex
    (hconn : G.Connected) (hb : 2 ≤ blockCount G) :
    ∃ v : V, IsCutVertex G v := by
  by_contra hno_cv
  push_neg at hno_cv
  -- From G.Connected + no cut vertices: removing any vertex leaves G connected.
  have hvcconn : ∀ v : V, (G.induce {w : V | w ≠ v}).Connected := fun v => by
    by_contra hdisc
    exact hno_cv v ⟨hconn, hdisc⟩
  -- Extract two distinct blocks B₁ ≠ B₂ from blockCount G ≥ 2.
  have hcard : 1 < (Finset.univ.filter (IsBlock G)).card := by
    unfold blockCount at hb; omega
  obtain ⟨B₁, hB₁mem, B₂, hB₂mem, hne⟩ := Finset.one_lt_card.mp hcard
  have hB₁ : IsBlock G B₁ := (Finset.mem_filter.mp hB₁mem).2
  have hB₂ : IsBlock G B₂ := (Finset.mem_filter.mp hB₂mem).2
  -- Prove G.induce ↑Finset.univ is biconnected (since G has no cut vertex).
  have hbc_univ : IsBiconnected (G.induce (↑(Finset.univ : Finset V) : Set V)) := by
    refine ⟨?_, Or.inr ?_⟩
    · -- G.induce ↑Finset.univ ≃g G, and G is connected.
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hconn
    · -- Removing any vertex from G.induce ↑Finset.univ leaves it connected.
      intro ⟨w, hw⟩
      rw [induce_sdiff_connected_iff Finset.univ ⟨w, hw⟩]
      -- (↑(Finset.univ \ {w}) : Set V) = {x | x ≠ w}.
      have hset : (↑(Finset.univ \ {w} : Finset V) : Set V) = {x : V | x ≠ w} := by
        ext x; simp
      rw [hset]
      exact hvcconn w
  -- Derive contradiction: some block's maximality is violated by hbc_univ.
  rcases eq_or_ne B₁ Finset.univ with rfl | h
  · -- B₁ = Finset.univ, so B₂ ≠ Finset.univ, giving B₂ ⊊ Finset.univ.
    exact hB₂.2 Finset.univ
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne.symm⟩) hbc_univ
  · -- B₁ ≠ Finset.univ, giving B₁ ⊊ Finset.univ.
    exact hB₁.2 Finset.univ
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, h⟩) hbc_univ

/-! ## Cut-vertex splitting: vertex and edge count equations -/

/-- If `S₁ ∩ S₂ = {c}` and `S₁ ∪ S₂ = Finset.univ`, the vertex counts satisfy
    `|S₁| + |S₂| = n + 1`.  Pure Finset arithmetic. -/
theorem split_vertex_card {c : V} {S₁ S₂ : Finset V}
    (h_inter : S₁ ∩ S₂ = {c}) (h_union : S₁ ∪ S₂ = Finset.univ) :
    S₁.card + S₂.card = Fintype.card V + 1 := by
  have hcard := Finset.card_union_add_card_inter S₁ S₂
  rw [h_union, h_inter, Finset.card_univ, Finset.card_singleton] at hcard
  omega

/-- Edge count splits at a cut vertex: if `S₁ ∩ S₂ = {c}`, `S₁ ∪ S₂ = Finset.univ`, and no
    G-edge crosses from `S₁ \ {c}` to `S₂ \ {c}`, then
    `|E(G)| = |E(G[S₁])| + |E(G[S₂])|`.
    Proof: via `SimpleGraph.map_edgeFinset_induce` the induced edge sets biject with
    `G.edgeFinset ∩ Sᵢ.sym2`; these two are disjoint (both endpoints in `S₁ ∩ S₂ = {c}` would
    be a self-loop) and cover `G.edgeFinset` (no cross-edges allowed). -/
theorem induce_edge_split {c : V} {S₁ S₂ : Finset V} [DecidableEq V]
    (hc₁ : c ∈ S₁) (hc₂ : c ∈ S₂)
    (h_inter : S₁ ∩ S₂ = {c})
    (h_union : S₁ ∪ S₂ = Finset.univ)
    (hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v) :
    G.edgeFinset.card =
      (G.induce (↑S₁ : Set V)).edgeFinset.card +
      (G.induce (↑S₂ : Set V)).edgeFinset.card := by
  -- Work with images of induced edgeFinsets in G.edgeFinset via Sym2.map Subtype.val.
  let φ : ∀ {S : Finset V}, Sym2 ↥(↑S : Set V) → Sym2 V := fun e => e.map Subtype.val
  let A := (G.induce (↑S₁ : Set V)).edgeFinset.image (@φ S₁)
  let B := (G.induce (↑S₂ : Set V)).edgeFinset.image (@φ S₂)
  -- A.card = (G.induce ↑S₁).edgeFinset.card  (φ is injective on subtypes).
  have hinj : ∀ (S : Finset V), Function.Injective (@φ S) :=
    fun S => Sym2.map.injective Subtype.val_injective
  have hAcard : A.card = (G.induce (↑S₁ : Set V)).edgeFinset.card :=
    Finset.card_image_of_injective _ (hinj S₁)
  have hBcard : B.card = (G.induce (↑S₂ : Set V)).edgeFinset.card :=
    Finset.card_image_of_injective _ (hinj S₂)
  -- A ⊆ G.edgeFinset.
  have hAmem : A ⊆ G.edgeFinset := by
    intro e he
    simp only [A, Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.ind with
    | h u v =>
      simp only [φ, Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact SimpleGraph.induce_adj.mp (SimpleGraph.mem_edgeFinset.mp he')
  have hBmem : B ⊆ G.edgeFinset := by
    intro e he
    simp only [B, Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.ind with
    | h u v =>
      simp only [φ, Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact SimpleGraph.induce_adj.mp (SimpleGraph.mem_edgeFinset.mp he')
  -- A ∩ B = ∅: edge in both has both endpoints in S₁ ∩ S₂ = {c} → self-loop.
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [A, B, Finset.mem_image] at heA heB
    obtain ⟨e₁, he₁, rfl⟩ := heA
    obtain ⟨e₂, he₂, heq⟩ := heB
    induction e₁ using Sym2.ind with
    | h u₁ v₁ =>
      induction e₂ using Sym2.ind with
      | h u₂ v₂ =>
        simp only [φ, Sym2.map_mk] at heq
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
                   SimpleGraph.induce_adj] at he₁ he₂
        -- heq : s(u₁.val, v₁.val) = s(u₂.val, v₂.val) as Sym2 V
        rw [Sym2.eq_iff] at heq
        -- heq : (u₁.val = u₂.val ∧ v₁.val = v₂.val) ∨ (u₁.val = v₂.val ∧ v₁.val = u₂.val)
        rcases heq with ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩
        · -- u₁.val ∈ S₁ ∩ S₂ (u₁ ∈ S₁, u₂ ∈ S₂, u₁.val=u₂.val)
          have huc : u₁.val ∈ S₁ ∩ S₂ :=
            Finset.mem_inter.mpr ⟨Finset.mem_coe.mp u₁.2,
              hu_eq ▸ Finset.mem_coe.mp u₂.2⟩
          have hvc : v₁.val ∈ S₁ ∩ S₂ :=
            Finset.mem_inter.mpr ⟨Finset.mem_coe.mp v₁.2,
              hv_eq ▸ Finset.mem_coe.mp v₂.2⟩
          rw [h_inter, Finset.mem_singleton] at huc hvc
          exact absurd rfl (huc ▸ hvc ▸ he₁.ne)
        · -- hu_eq : ↑u₂ = ↑v₁, hv_eq : ↑v₂ = ↑u₁
          have huc : u₁.val ∈ S₁ ∩ S₂ :=
            Finset.mem_inter.mpr ⟨Finset.mem_coe.mp u₁.2,
              hv_eq.symm ▸ Finset.mem_coe.mp v₂.2⟩
          have hvc : v₁.val ∈ S₁ ∩ S₂ :=
            Finset.mem_inter.mpr ⟨Finset.mem_coe.mp v₁.2,
              hu_eq.symm ▸ Finset.mem_coe.mp u₂.2⟩
          rw [h_inter, Finset.mem_singleton] at huc hvc
          exact absurd rfl (huc ▸ hvc ▸ he₁.ne)
  -- G.edgeFinset ⊆ A ∪ B.
  have hcov : G.edgeFinset ⊆ A ∪ B := by
    intro e he
    rw [Finset.mem_union]
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hu : u ∈ S₁ ∨ u ∈ S₂ := Finset.mem_union.mp (h_union ▸ Finset.mem_univ u)
      have hv : v ∈ S₁ ∨ v ∈ S₂ := Finset.mem_union.mp (h_union ▸ Finset.mem_univ v)
      -- Helper: if u,v ∈ Sᵢ, then s(u,v) ∈ image of (G.induce ↑Sᵢ).edgeFinset.
      have in_image : ∀ S : Finset V, u ∈ S → v ∈ S →
          s(u, v) ∈ (G.induce (↑S : Set V)).edgeFinset.image (@φ S) := by
        intro S huS hvS
        apply Finset.mem_image.mpr
        exact ⟨s(⟨u, Finset.mem_coe.mpr huS⟩, ⟨v, Finset.mem_coe.mpr hvS⟩),
          SimpleGraph.mem_edgeFinset.mpr
            (SimpleGraph.induce_adj.mpr he),
          by simp [φ]⟩
      rcases hu with hu₁ | hu₂ <;> rcases hv with hv₁ | hv₂
      · exact Or.inl (in_image S₁ hu₁ hv₁)
      · by_cases hu_S₂ : u ∈ S₂
        · exact Or.inr (in_image S₂ hu_S₂ hv₂)
        · by_cases hv_S₁ : v ∈ S₁
          · exact Or.inl (in_image S₁ hu₁ hv_S₁)
          · exact absurd he (hno_cross u
              (Finset.mem_sdiff.mpr ⟨hu₁,
                fun h => hu_S₂ ((Finset.mem_singleton.mp h) ▸ hc₂)⟩) v
              (Finset.mem_sdiff.mpr ⟨hv₂,
                fun h => hv_S₁ ((Finset.mem_singleton.mp h) ▸ hc₁)⟩))
      · by_cases hv_S₂ : v ∈ S₂
        · exact Or.inr (in_image S₂ hu₂ hv_S₂)
        · by_cases hu_S₁ : u ∈ S₁
          · exact Or.inl (in_image S₁ hu_S₁ hv₁)
          · exact absurd he.symm (hno_cross v
              (Finset.mem_sdiff.mpr ⟨hv₁,
                fun h => hv_S₂ ((Finset.mem_singleton.mp h) ▸ hc₂)⟩) u
              (Finset.mem_sdiff.mpr ⟨hu₂,
                fun h => hu_S₁ ((Finset.mem_singleton.mp h) ▸ hc₁)⟩))
      · exact Or.inr (in_image S₂ hu₂ hv₂)
  -- Now count: |G.edgeFinset| = |A ∪ B| = |A| + |B|
  have hunion : A ∪ B = G.edgeFinset :=
    Finset.Subset.antisymm (Finset.union_subset hAmem hBmem) hcov
  rw [← hunion, Finset.card_union_of_disjoint hdisj, hAcard, hBcard]

/-- If `u ∈ S₁ \ {c}`, `v ∈ S₂ \ {c}`, and the two sides minus `c` are each connected in G,
    and G - {c} is disconnected, then G cannot have the edge `u-v`.
    Proof: if G.Adj u v, lift connectivity of G[S₁\{c}] and G[S₂\{c}] to G-{c} via explicit
    homomorphisms (inclusions of subtypes), showing G-{c} would be connected — contradiction. -/
theorem cut_vertex_no_cross_edge {c u v : V}
    (hsep : ¬ (G.induce ({w : V | w ≠ c})).Connected)
    (S₁ S₂ : Finset V)
    (h_inter : S₁ ∩ S₂ = {c})
    (h_union : S₁ ∪ S₂ = Finset.univ)
    (hu₁ : u ∈ S₁) (hu_ne : u ≠ c)
    (hv₂ : v ∈ S₂) (hv_ne : v ≠ c)
    (hconn₁ : (G.induce ↑(S₁ \ {c} : Finset V)).Connected)
    (hconn₂ : (G.induce ↑(S₂ \ {c} : Finset V)).Connected) :
    ¬ G.Adj u v := by
  intro hadj
  have hv_not_S₁ : v ∉ S₁ := by
    intro hv₁
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hv₁, hv₂⟩
    rw [h_inter] at this
    exact hv_ne (Finset.mem_singleton.mp this)
  have hu_mem : u ∈ ({w : V | w ≠ c} : Set V) := hu_ne
  have hv_mem : v ∈ ({w : V | w ≠ c} : Set V) := hv_ne
  have hreach : (G.induce ({w : V | w ≠ c})).Reachable ⟨u, hu_mem⟩ ⟨v, hv_mem⟩ :=
    (SimpleGraph.induce_adj.mpr hadj).reachable
  -- Inclusion homs: G[Sᵢ\{c}] →g G-{c} (valid since Sᵢ\{c} ⊆ {w|w≠c}).
  let φ₁ : G.induce ↑(S₁ \ {c} : Finset V) →g G.induce ({w : V | w ≠ c}) :=
    { toFun  := fun ⟨x, hx⟩ => ⟨x, fun hxc =>
          (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
            (Finset.mem_singleton.mpr hxc)⟩
      map_rel' := fun {a b} hab =>
          SimpleGraph.induce_adj.mpr (SimpleGraph.induce_adj.mp hab) }
  let φ₂ : G.induce ↑(S₂ \ {c} : Finset V) →g G.induce ({w : V | w ≠ c}) :=
    { toFun  := fun ⟨x, hx⟩ => ⟨x, fun hxc =>
          (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
            (Finset.mem_singleton.mpr hxc)⟩
      map_rel' := fun {a b} hab =>
          SimpleGraph.induce_adj.mpr (SimpleGraph.induce_adj.mp hab) }
  apply hsep
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu_mem⟩, fun ⟨w, hw⟩ => ?_⟩
  have hwU : w ∈ S₁ ∨ w ∈ S₂ := by
    have : w ∈ Finset.univ := Finset.mem_univ w
    rw [← h_union] at this
    exact Finset.mem_union.mp this
  have hu₁c : u ∈ S₁ \ {c} :=
    Finset.mem_sdiff.mpr ⟨hu₁, fun h => hu_ne (Finset.mem_singleton.mp h)⟩
  rcases hwU with hw₁ | hw₂
  · -- w ∈ S₁\{c}: path u→w in G[S₁\{c}], lifted via φ₁.
    have hw₁c : w ∈ S₁ \ {c} :=
      Finset.mem_sdiff.mpr ⟨hw₁, fun h => hw (Finset.mem_singleton.mp h)⟩
    exact (hconn₁.preconnected
        ⟨u, Finset.mem_coe.mpr hu₁c⟩ ⟨w, Finset.mem_coe.mpr hw₁c⟩).map φ₁
  · -- w ∈ S₂\{c}: path v→w in G[S₂\{c}], lifted via φ₂, then prepend u~v.
    have hw₂c : w ∈ S₂ \ {c} :=
      Finset.mem_sdiff.mpr ⟨hw₂, fun h => hw (Finset.mem_singleton.mp h)⟩
    have hv₂c : v ∈ S₂ \ {c} :=
      Finset.mem_sdiff.mpr ⟨hv₂, fun h => hv_ne (Finset.mem_singleton.mp h)⟩
    exact hreach.trans
      ((hconn₂.preconnected
          ⟨v, Finset.mem_coe.mpr hv₂c⟩ ⟨w, Finset.mem_coe.mpr hw₂c⟩).map φ₂)

/-! ## Disconnectedness from no cross-edges -/

omit [Fintype V] in
/-- If A and B are non-empty disjoint parts of S = A∪B with no G-edges between them,
    then G.induce ↑(A∪B) is disconnected (the two sides are unreachable from each other). -/
private lemma not_connected_of_no_cross {A B : Finset V}
    (hAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hno : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v) :
    ¬ (G.induce (↑(A ∪ B) : Set V)).Connected := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  -- Membership witnesses for the union type.
  have ha_sub : a ∈ (↑(A ∪ B) : Set V) :=
    Finset.mem_coe.mpr (Finset.mem_union_left B ha)
  have hb_sub : b ∈ (↑(A ∪ B) : Set V) :=
    Finset.mem_coe.mpr (Finset.mem_union_right A hb)
  -- a and b are in different parts, hence in different components.
  have ha_not_B : a ∉ B := Finset.disjoint_left.mp hAB ha
  have hb_not_A : b ∉ A := Finset.disjoint_right.mp hAB hb
  -- Key invariant: walks in G.induce ↑(A∪B) preserve membership in A.
  have key : ∀ (u v : ↥(↑(A ∪ B) : Set V)),
      (G.induce (↑(A ∪ B) : Set V)).Reachable u v →
      (u.val ∈ A → v.val ∈ A) := by
    intro u v ⟨walk⟩
    induction walk with
    | nil => exact id
    | @cons x y _ hadj _ ih =>
      -- hadj : G.induce ↑(A∪B)).Adj x y, so G.Adj x.val y.val
      have hGadj : G.Adj x.val y.val :=
        SimpleGraph.induce_adj.mp hadj
      intro hxA
      apply ih
      -- Show y.val ∈ A: y ∈ A∪B, and y ∉ B (else hno x y gives ¬G.Adj, contradiction).
      have hyAB := Finset.mem_coe.mp y.2
      rcases Finset.mem_union.mp hyAB with hyA | hyB
      · exact hyA
      · exact absurd hGadj (hno x.val hxA y.val hyB)
  -- Walk from a (∈ A) to b must keep us in A, but b ∉ A — contradiction.
  intro hconn
  have hreach_ab := hconn.preconnected ⟨a, ha_sub⟩ ⟨b, hb_sub⟩
  exact hb_not_A (key ⟨a, ha_sub⟩ ⟨b, hb_sub⟩ hreach_ab ha)

/-! ## Block containment under cut-vertex split -/

/-- Any biconnected induced subgraph lies entirely within S₁ or S₂. -/
private theorem biconnected_contained_in_side {c : V} {S₁ S₂ : Finset V}
    (h_inter : S₁ ∩ S₂ = {c})
    (h_union : S₁ ∪ S₂ = Finset.univ)
    (hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v)
    {B : Finset V} (hB : IsBiconnected (G.induce (↑B : Set V))) :
    B ⊆ S₁ ∨ B ⊆ S₂ := by
  -- Suppose B has a vertex in S₁\{c} and one in S₂\{c}; derive contradiction.
  by_contra h
  push_neg at h
  obtain ⟨hns₁, hns₂⟩ := h
  -- Pick u ∈ B with u ∉ S₁ (so u ∈ S₂\{c} by coverage).
  obtain ⟨u, huB, huS₁⟩ := Finset.not_subset.mp hns₁
  -- Pick v ∈ B with v ∉ S₂.
  obtain ⟨v, hvB, hvS₂⟩ := Finset.not_subset.mp hns₂
  -- u ∈ S₂ (since S₁∪S₂=univ, u ∉ S₁ → u ∈ S₂).
  have huS₂ : u ∈ S₂ := by
    have := Finset.mem_univ u; rw [← h_union] at this
    exact (Finset.mem_union.mp this).resolve_left huS₁
  -- v ∈ S₁.
  have hvS₁ : v ∈ S₁ := by
    have := Finset.mem_univ v; rw [← h_union] at this
    exact (Finset.mem_union.mp this).resolve_right hvS₂
  -- u ≠ c: if u = c then u ∈ S₁ (c ∈ S₁ from h_inter: S₁∩S₂={c}→c∈S₁).
  have huc : u ≠ c := by
    intro h
    apply huS₁; rw [h]
    have : c ∈ S₁ ∩ S₂ := by rw [h_inter]; exact Finset.mem_singleton_self c
    exact (Finset.mem_inter.mp this).1
  -- v ≠ c: similarly.
  have hvc : v ≠ c := by
    intro h
    apply hvS₂; rw [h]
    have : c ∈ S₁ ∩ S₂ := by rw [h_inter]; exact Finset.mem_singleton_self c
    exact (Finset.mem_inter.mp this).2
  -- u ∈ S₂\{c}, v ∈ S₁\{c}.
  have huS₂c : u ∈ S₂ \ {c} :=
    Finset.mem_sdiff.mpr ⟨huS₂, Finset.mem_singleton.not.mpr huc⟩
  have hvS₁c : v ∈ S₁ \ {c} :=
    Finset.mem_sdiff.mpr ⟨hvS₁, Finset.mem_singleton.not.mpr hvc⟩
  -- u ∉ S₁\{c} and v ∉ S₂\{c}, so they're on opposite sides of c.
  -- Define A = B ∩ (S₁\{c}) and D = B ∩ (S₂\{c}).
  -- v ∈ A and u ∈ D, so both are non-empty.
  set A := B ∩ (S₁ \ {c}) with hA_def
  set D := B ∩ (S₂ \ {c}) with hD_def
  have hvA : v ∈ A := Finset.mem_inter.mpr ⟨hvB, hvS₁c⟩
  have huD : u ∈ D := Finset.mem_inter.mpr ⟨huB, huS₂c⟩
  -- A and D are disjoint (S₁\{c} and S₂\{c} are disjoint by h_inter).
  have hAD_disj : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    have hxS₁c := (Finset.mem_inter.mp hxA).2
    have hxS₂c := (Finset.mem_inter.mp hxD).2
    have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hxS₁c).1, (Finset.mem_sdiff.mp hxS₂c).1⟩
    rw [h_inter] at this
    exact (Finset.mem_sdiff.mp hxS₁c).2 this
  -- No G-edges between A and D (since A ⊆ S₁\{c} and D ⊆ S₂\{c}).
  have hAD_no : ∀ a ∈ A, ∀ d ∈ D, ¬ G.Adj a d := by
    intro a haA d hdD
    exact hno_cross a ((Finset.mem_inter.mp haA).2) d ((Finset.mem_inter.mp hdD).2)
  -- B ⊆ S₁ ∪ S₂ = univ: B can be written as B ∩ (S₁\{c}) ∪ B ∩ (S₂\{c}) ∪ (B ∩ {c}).
  -- Case 1: c ∉ B. Then B = A ∪ D (no c), both non-empty, no edges between them.
  --   → G.induce ↑B is disconnected. Contradiction with hB.1 (biconnected → connected).
  -- Case 2: c ∈ B. Then B has ≥ 3 elements (v, u, c distinct).
  --   Removing c from G.induce ↑B gives G.induce ↑(B\{c}) ⊇ A ∪ D (both non-empty, no cross).
  --   → G.induce ↑(B\{c}) is disconnected.
  --   But biconnectivity (|B| ≥ 3 case) says removing any vertex leaves it connected.
  --   Contradiction.
  by_cases hcB : c ∈ B
  · -- Case 2: c ∈ B.
    -- |B| ≥ 3: B contains v (≠c), u (≠c), c, all distinct.
    have hvnc : v ≠ c := hvc
    have hunc : u ≠ c := huc
    have hvnu : v ≠ u := by
      intro h; exact huS₁ (h ▸ hvS₁)
    -- B has Fintype.card ↥(↑B : Set V) ≥ 3.
    have hcard3 : 3 ≤ Fintype.card ↥(↑B : Set V) := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
      have h1 : ({v, u, c} : Finset V) ⊆ B :=
        Finset.insert_subset_iff.mpr ⟨hvB, Finset.insert_subset_iff.mpr
          ⟨huB, Finset.singleton_subset_iff.mpr hcB⟩⟩
      have hvu_not : v ∉ ({u, c} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hvnu, hvc⟩
      have huc_not : u ∉ ({c} : Finset V) := Finset.mem_singleton.not.mpr huc
      have hcard_vuc : ({v, u, c} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem hvu_not, Finset.card_insert_of_notMem huc_not,
            Finset.card_singleton]
      linarith [Finset.card_le_card h1]
    -- IsBiconnected: the ∀ v case applies (since card ≥ 3, so ≠ 2).
    rcases hB.2 with hcard2 | hnocut
    · -- card = 2, but we have ≥ 3. Contradiction.
      omega
    · -- hnocut: removing any vertex of G.induce ↑B leaves it connected.
      -- Remove c: (G.induce ↑B).induce {w | w ≠ ⟨c, hcB⟩} is connected.
      have hrem := hnocut ⟨c, hcB⟩
      -- Translate to G.induce ↑(B\{c}) via induceSdiffIso.
      rw [induce_sdiff_connected_iff B ⟨c, hcB⟩] at hrem
      -- But G.induce ↑(B\{c}) contains A and D (both non-empty, no cross-edges).
      -- By not_connected_of_no_cross, G.induce ↑(A∪D) is not connected.
      -- We show G.induce ↑(A∪D) ≃g G.induce ↑(B\{c}) (since A∪D = B\{c}).
      have hAD_eq : A ∪ D = B \ {c} := by
        ext x; simp only [hA_def, hD_def, Finset.mem_union, Finset.mem_inter,
                           Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro (⟨hxB, hxS₁, hxnc⟩ | ⟨hxB, hxS₂, hxnc⟩) <;> exact ⟨hxB, hxnc⟩
        · intro ⟨hxB, hxnc⟩
          have hxuniv := Finset.mem_univ x; rw [← h_union] at hxuniv
          rcases Finset.mem_union.mp hxuniv with hxS₁ | hxS₂
          · left; exact ⟨hxB, hxS₁, hxnc⟩
          · right; exact ⟨hxB, hxS₂, hxnc⟩
      rw [← hAD_eq] at hrem
      exact not_connected_of_no_cross hAD_disj ⟨v, hvA⟩ ⟨u, huD⟩ hAD_no hrem
  · -- Case 1: c ∉ B. Then B = A ∪ D.
    have hB_eq : B = A ∪ D := by
      ext x; simp only [hA_def, hD_def, Finset.mem_union, Finset.mem_inter,
                         Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro hxB
        have hxuniv := Finset.mem_univ x; rw [← h_union] at hxuniv
        rcases Finset.mem_union.mp hxuniv with hxS₁ | hxS₂
        · have hxnc : x ≠ c := fun h => hcB (h ▸ hxB)
          left; exact ⟨hxB, hxS₁, hxnc⟩
        · have hxnc : x ≠ c := fun h => hcB (h ▸ hxB)
          right; exact ⟨hxB, hxS₂, hxnc⟩
      · rintro (⟨hxB, _⟩ | ⟨hxB, _⟩) <;> exact hxB
    -- G.induce ↑B = G.induce ↑(A∪D). Connected (from biconnected), but not_connected_of_no_cross says otherwise.
    rw [hB_eq] at hB
    exact not_connected_of_no_cross hAD_disj ⟨v, hvA⟩ ⟨u, huD⟩ hAD_no hB.1

/-- Every block of G lies entirely within S₁ or within S₂. -/
private theorem block_contained_in_side {c : V} {S₁ S₂ : Finset V}
    (h_inter : S₁ ∩ S₂ = {c})
    (h_union : S₁ ∪ S₂ = Finset.univ)
    (hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v)
    {B : Finset V} (hB : IsBlock G B) :
    B ⊆ S₁ ∨ B ⊆ S₂ :=
  biconnected_contained_in_side h_inter h_union hno_cross hB.1

/-! ## Block count additivity -/

/-- Graph iso between `G.induce B` and `(G.induce S).induce (B.subtype (· ∈ S))` when B ⊆ S. -/
private def induceSubtypeIso {B S : Finset V} (hBS : B ⊆ S) :
    G.induce (↑B : Set V) ≃g
    (G.induce (↑S : Set V)).induce (↑(B.subtype (· ∈ S)) : Set ↥(↑S : Set V)) where
  toFun := fun ⟨v, hv⟩ =>
    let hvB : v ∈ B := Finset.mem_coe.mp hv
    ⟨⟨v, Finset.mem_coe.mpr (hBS hvB)⟩, Finset.mem_coe.mpr (Finset.mem_subtype.mpr hvB)⟩
  invFun := fun ⟨⟨v, _⟩, hmem⟩ =>
    ⟨v, Finset.mem_coe.mpr (Finset.mem_subtype.mp (Finset.mem_coe.mp hmem))⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => by ext1; ext1; rfl
  map_rel_iff' := Iff.rfl

omit [Fintype V] in
/-- Iso between vertex-deleted graphs: G₁-{v} ≃g G₂-{e(v)} when G₁ ≃g G₂. -/
private def vertexDeleteIso {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} (e : G₁ ≃g G₂) (v : α) :
    G₁.induce {w : α | w ≠ v} ≃g G₂.induce {w : β | w ≠ e v} where
  toFun := fun ⟨w, hw⟩ => ⟨e w, fun heq => hw (e.toEquiv.injective heq)⟩
  invFun := fun ⟨w, hw⟩ =>
    ⟨e.symm w, fun heq =>
      hw ((RelIso.apply_symm_apply e w).symm.trans (congrArg e heq))⟩
  left_inv := fun ⟨w, _⟩ => Subtype.ext (e.toEquiv.symm_apply_apply w)
  right_inv := fun ⟨w, _⟩ => Subtype.ext (e.toEquiv.apply_symm_apply w)
  map_rel_iff' := by intro ⟨a, _⟩ ⟨b, _⟩; exact e.map_rel_iff'

omit [Fintype V] in
/-- One direction: IsBiconnected G₁ → IsBiconnected G₂ when G₁ ≃g G₂. -/
private lemma isBiconnected_of_iso_mp {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} (e : G₁ ≃g G₂)
    (h : IsBiconnected G₁) : IsBiconnected G₂ := by
  refine ⟨e.connected_iff.mp h.1, ?_⟩
  rcases h.2 with h2 | hnocut
  · left; exact (Fintype.card_congr e.toEquiv).symm.trans h2
  · right; intro v
    have hmv := (vertexDeleteIso e (e.symm v)).connected_iff.mp (hnocut (e.symm v))
    rw [RelIso.apply_symm_apply] at hmv; exact hmv

omit [Fintype V] in
/-- IsBiconnected is preserved by graph isomorphisms. -/
private lemma isBiconnected_of_iso {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} (e : G₁ ≃g G₂) :
    IsBiconnected G₁ ↔ IsBiconnected G₂ :=
  ⟨isBiconnected_of_iso_mp e, isBiconnected_of_iso_mp e.symm⟩

omit [Fintype V] in
/-- B.subtype (· ∈ S) |>.image Subtype.val = B when B ⊆ S. -/
private lemma subtype_image_val_eq {B S : Finset V} (hBS : B ⊆ S) :
    (B.subtype (· ∈ S)).image Subtype.val = B := by
  ext v
  simp only [Finset.mem_image, Finset.mem_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hv; exact ⟨⟨v, hBS hv⟩, hv, rfl⟩

omit [Fintype V] in
/-- (B.image Subtype.val).subtype (· ∈ S) = B for B : Finset ↥S. -/
private lemma image_val_subtype_eq {S : Finset V} (B : Finset ↥(↑S : Set V)) :
    (B.image Subtype.val).subtype (· ∈ S) = B := by
  ext ⟨v, hvS⟩
  simp only [Finset.mem_subtype, Finset.mem_image]
  constructor
  · intro ⟨u, hu, huv⟩
    have heq : u = ⟨v, Finset.mem_coe.mpr hvS⟩ :=
      Subtype.ext huv
    exact heq ▸ hu
  · intro hv; exact ⟨⟨v, Finset.mem_coe.mpr hvS⟩, hv, rfl⟩

omit [Fintype V] in
/-- Biconnected subgraph has ≥ 2 vertices. -/
private lemma isBiconnected_two_le_card {α : Type*} [Fintype α] {H : SimpleGraph α}
    (hH : IsBiconnected H) : 2 ≤ Fintype.card α := by
  rcases hH.2 with h2 | hnocut
  · omega
  · by_contra hlt
    push_neg at hlt
    haveI : Nonempty α := hH.1.nonempty
    have hcard1 : Fintype.card α = 1 := by linarith [Fintype.card_pos (α := α)]
    obtain ⟨v, hv_uniq⟩ := Fintype.card_eq_one_iff.mp hcard1
    have hemp : IsEmpty ↥({w : α | w ≠ v}) :=
      ⟨fun ⟨w, hw⟩ => hw (hv_uniq w)⟩
    exact hemp.false (hnocut v).nonempty.some

/-- A block B₁ of G[S₁] is also a block of G (under no-cross partition). -/
private theorem isBlock_image_of_isBlock_induce {c : V} {S₁ S₂ : Finset V}
    (h_inter : S₁ ∩ S₂ = {c}) (h_union : S₁ ∪ S₂ = Finset.univ)
    (hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v)
    {B₁ : Finset ↥(↑S₁ : Set V)} (hB₁ : IsBlock (G.induce (↑S₁ : Set V)) B₁) :
    IsBlock G (B₁.image Subtype.val) := by
  set B := B₁.image Subtype.val with hB_def
  have hBS₁ : B ⊆ S₁ := fun x hx => by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_coe.mp u.property
  -- Iso: G.induce ↑B ≃g (G.induce ↑S₁).induce ↑B₁
  have hiso : G.induce (↑B : Set V) ≃g (G.induce (↑S₁ : Set V)).induce (↑B₁ : Set ↥S₁) := by
    have heq : (↑B₁ : Set ↥S₁) = ↑(B.subtype (· ∈ S₁)) := by
      congr 1; exact (image_val_subtype_eq B₁).symm
    rw [heq]; exact induceSubtypeIso hBS₁
  have hbico : IsBiconnected (G.induce (↑B : Set V)) :=
    (isBiconnected_of_iso hiso).mpr hB₁.1
  refine ⟨hbico, fun B' hB'_sup hB'_bico => ?_⟩
  rcases biconnected_contained_in_side h_inter h_union hno_cross hB'_bico with hS₁ | hS₂
  · -- B' ⊆ S₁: lift B' to G[S₁] and derive contradiction with B₁ being a block
    set B₁' := B'.subtype (· ∈ S₁)
    -- induceSubtypeIso hS₁ : G.induce ↑B' ≃g (G.induce ↑S₁).induce ↑(B'.subtype (· ∈ S₁))
    -- and B₁' = B'.subtype (· ∈ S₁) by set, so this has the right type
    have hB₁'_iso : G.induce (↑B' : Set V) ≃g
        (G.induce (↑S₁ : Set V)).induce (↑B₁' : Set ↥S₁) :=
      induceSubtypeIso hS₁
    have hB₁'_bico : IsBiconnected ((G.induce ↑S₁).induce (↑B₁' : Set ↥S₁)) :=
      (isBiconnected_of_iso hB₁'_iso).mp hB'_bico
    have hB₁_sub : B₁ ⊆ B₁' := by
      intro u hu
      apply Finset.mem_subtype.mpr
      apply hB'_sup.subset
      rw [hB_def]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hB₁_ne : B₁ ≠ B₁' := by
      intro heq
      have hBB'_eq : B = B' := by
        rw [hB_def, heq]; exact subtype_image_val_eq hS₁
      exact absurd hBB'_eq hB'_sup.ne
    exact hB₁.2 B₁' (Finset.ssubset_iff_subset_ne.mpr ⟨hB₁_sub, hB₁_ne⟩) hB₁'_bico
  · -- B' ⊆ S₂ and B ⊆ S₁: B ⊆ {c}, but |B₁| ≥ 2
    have hB_sub_c : B ⊆ ({c} : Finset V) := by
      rw [← h_inter]; exact Finset.subset_inter hBS₁ (hB'_sup.subset.trans hS₂)
    have hB_card_le1 : B.card ≤ 1 :=
      (Finset.card_le_card hB_sub_c).trans (by simp)
    have hB₁_card_ge2 : 2 ≤ B₁.card := by
      have h := isBiconnected_two_le_card hB₁.1
      rwa [← Set.toFinset_card, Finset.toFinset_coe] at h
    have hcard_eq : B.card = B₁.card := by
      rw [hB_def, Finset.card_image_of_injective _ Subtype.val_injective]
    omega

/-- A block B of G contained in S₁ is a block of G[S₁]. -/
private theorem isBlock_subtype_of_isBlock {S₁ : Finset V}
    {B : Finset V} (hB : IsBlock G B) (hBS₁ : B ⊆ S₁) :
    IsBlock (G.induce (↑S₁ : Set V)) (B.subtype (· ∈ S₁)) := by
  set B₁ := B.subtype (· ∈ S₁) with hB₁_def
  have hiso : G.induce (↑B : Set V) ≃g (G.induce (↑S₁ : Set V)).induce (↑B₁ : Set ↥S₁) :=
    induceSubtypeIso hBS₁
  have hbico : IsBiconnected ((G.induce ↑S₁).induce (↑B₁ : Set ↥S₁)) :=
    (isBiconnected_of_iso hiso).mp hB.1
  refine ⟨hbico, fun B₁' hB₁'_sup hB₁'_bico => ?_⟩
  -- Lift B₁' to G and contradict hB's maximality
  set B' := B₁'.image Subtype.val with hB'_def
  have hB'S₁ : B' ⊆ S₁ := fun x hx => by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_coe.mp u.property
  -- B' = B₁'.image Subtype.val, so B'.subtype(·∈S₁) = B₁' by image_val_subtype_eq
  have hB'_iso : G.induce (↑B' : Set V) ≃g
      (G.induce (↑S₁ : Set V)).induce (↑B₁' : Set ↥S₁) := by
    have heq : (↑B₁' : Set ↥S₁) = ↑(B'.subtype (· ∈ S₁)) := by
      congr 1; exact (image_val_subtype_eq B₁').symm
    rw [heq]; exact induceSubtypeIso hB'S₁
  have hB'_bico : IsBiconnected (G.induce (↑B' : Set V)) :=
    (isBiconnected_of_iso hB'_iso).mpr hB₁'_bico
  have hB_sub_B' : B ⊆ B' := fun x hx =>
    Finset.mem_image.mpr ⟨⟨x, Finset.mem_coe.mpr (hBS₁ hx)⟩,
      hB₁'_sup.subset (Finset.mem_subtype.mpr hx), rfl⟩
  have hB_ne_B' : B ≠ B' := by
    intro heq
    obtain ⟨x, hxB₁', hxB₁⟩ := Finset.not_subset.mp hB₁'_sup.not_subset
    exact hxB₁ (Finset.mem_subtype.mpr (heq ▸ Finset.mem_image.mpr ⟨x, hxB₁', rfl⟩))
  exact hB.2 B' (Finset.ssubset_iff_subset_ne.mpr ⟨hB_sub_B', hB_ne_B'⟩) hB'_bico

/-- Block count is additive under a no-cross partition with cut vertex c. -/
theorem blockCount_add_of_no_cross {c : V} {S₁ S₂ : Finset V}
    (h_inter : S₁ ∩ S₂ = {c}) (h_union : S₁ ∪ S₂ = Finset.univ)
    (hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v) :
    blockCount G = blockCount (G.induce (↑S₁ : Set V)) +
                   blockCount (G.induce (↑S₂ : Set V)) := by
  simp only [blockCount]
  -- Symmetric partition hypotheses for S₂
  have h_inter₂ : S₂ ∩ S₁ = {c} := by rw [Finset.inter_comm]; exact h_inter
  have h_union₂ : S₂ ∪ S₁ = Finset.univ := by rw [Finset.union_comm]; exact h_union
  have hno_cross₂ : ∀ u ∈ S₂ \ {c}, ∀ v ∈ S₁ \ {c}, ¬ G.Adj u v :=
    fun u hu v hv hadj => hno_cross v hv u hu hadj.symm
  -- Block finsets
  let f₁ : Finset ↥(↑S₁ : Set V) → Finset V := (·.image Subtype.val)
  let f₂ : Finset ↥(↑S₂ : Set V) → Finset V := (·.image Subtype.val)
  set bG := (Finset.univ (α := Finset V)).filter (IsBlock G)
  set bS₁ := (Finset.univ (α := Finset ↥(↑S₁ : Set V))).filter (IsBlock (G.induce ↑S₁))
  set bS₂ := (Finset.univ (α := Finset ↥(↑S₂ : Set V))).filter (IsBlock (G.induce ↑S₂))
  -- Images land in bG
  have him₁ : ∀ B₁ ∈ bS₁, f₁ B₁ ∈ bG := fun B₁ hB₁ => by
    simp only [bG, Finset.mem_filter, Finset.mem_univ, true_and]
    exact isBlock_image_of_isBlock_induce h_inter h_union hno_cross
      ((Finset.mem_filter.mp hB₁).2)
  have him₂ : ∀ B₂ ∈ bS₂, f₂ B₂ ∈ bG := fun B₂ hB₂ => by
    simp only [bG, Finset.mem_filter, Finset.mem_univ, true_and]
    exact isBlock_image_of_isBlock_induce h_inter₂ h_union₂ hno_cross₂
      ((Finset.mem_filter.mp hB₂).2)
  -- f₁ and f₂ are injective
  have hf₁_inj : Set.InjOn f₁ ↑bS₁ := fun B₁ _ B₁' _ heq => by
    simp only [f₁] at heq
    ext u
    constructor
    · intro hu
      obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp (heq ▸ Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      exact Subtype.val_injective hwu ▸ hw
    · intro hu
      obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp (heq.symm ▸ Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      exact Subtype.val_injective hwu ▸ hw
  have hf₂_inj : Set.InjOn f₂ ↑bS₂ := fun B₂ _ B₂' _ heq => by
    simp only [f₂] at heq
    ext u
    constructor
    · intro hu
      obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp (heq ▸ Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      exact Subtype.val_injective hwu ▸ hw
    · intro hu
      obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp (heq.symm ▸ Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      exact Subtype.val_injective hwu ▸ hw
  -- bG = image f₁ bS₁ ∪ image f₂ bS₂ (set equality)
  have hbG_eq : bG = bS₁.image f₁ ∪ bS₂.image f₂ := by
    ext B
    simp only [bG, bS₁, bS₂, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_union, Finset.mem_image]
    constructor
    · intro hB
      rcases block_contained_in_side h_inter h_union hno_cross hB with hS₁ | hS₂
      · exact Or.inl ⟨B.subtype (· ∈ S₁),
          isBlock_subtype_of_isBlock hB hS₁,
          subtype_image_val_eq hS₁⟩
      · exact Or.inr ⟨B.subtype (· ∈ S₂),
          isBlock_subtype_of_isBlock hB hS₂,
          subtype_image_val_eq hS₂⟩
    · rintro (⟨B₁, hB₁, rfl⟩ | ⟨B₂, hB₂, rfl⟩)
      · exact isBlock_image_of_isBlock_induce h_inter h_union hno_cross hB₁
      · exact isBlock_image_of_isBlock_induce h_inter₂ h_union₂ hno_cross₂ hB₂
  -- The two images are disjoint
  have hdisj : Disjoint (bS₁.image f₁) (bS₂.image f₂) := by
    rw [Finset.disjoint_left]
    intro B hB₁ hB₂
    obtain ⟨B₁, hB₁', rfl⟩ := Finset.mem_image.mp hB₁
    obtain ⟨B₂, hB₂', hBeq⟩ := Finset.mem_image.mp hB₂
    -- B₁.image Subtype.val ⊆ S₁ and ⊆ S₂ → ⊆ {c} → card ≤ 1
    -- But B₁ is biconnected → card ≥ 2 → contradiction
    have hBS₁ : B₁.image Subtype.val ⊆ S₁ := fun x hx => by
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_coe.mp u.property
    have hBS₂ : B₁.image Subtype.val ⊆ S₂ := by
      have hB₂val : B₂.image Subtype.val ⊆ S₂ := by
        intro x hx
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_coe.mp u.property
      simp only [f₁, f₂] at hBeq
      rwa [← hBeq]
    have hBc : B₁.image Subtype.val ⊆ ({c} : Finset V) := by
      rw [← h_inter]; exact Finset.subset_inter hBS₁ hBS₂
    have hBcard_le1 : (B₁.image Subtype.val).card ≤ 1 :=
      (Finset.card_le_card hBc).trans (by simp)
    have hcard_img : (B₁.image Subtype.val).card = B₁.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hge2 : 2 ≤ B₁.card := by
      have hbico : IsBiconnected ((G.induce ↑S₁).induce (↑B₁ : Set ↥S₁)) :=
        (Finset.mem_filter.mp hB₁').2.1
      have h := isBiconnected_two_le_card hbico
      rwa [← Set.toFinset_card, Finset.toFinset_coe] at h
    omega
  -- Count
  rw [hbG_eq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn hf₁_inj, Finset.card_image_of_injOn hf₂_inj]

/-! ## Consequences for near-triangulations -/

/-- A near-triangulation with ≥ 2 blocks has a cut vertex. -/
theorem NearTriangulation.has_cut_vertex {G : SimpleGraph V}
    (NT : NearTriangulation G) (hb : 2 ≤ NT.b) :
    ∃ v : V, IsCutVertex G v :=
  multiblock_has_cut_vertex NT.connected hb

end MinBal

end -- noncomputable section
