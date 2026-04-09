-- Project/MinBal/Defs.lean
-- Core definitions for minimum balanced bipartitions.

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

-- We work noncomputably throughout; all decidability is provided by Classical.
noncomputable section
open Classical SimpleGraph

namespace MinBal

/-! ## Bipartitions -/

/-- A bipartition of `V`: two disjoint finsets whose union is all of `V`. -/
structure Bipartition (V : Type*) [Fintype V] where
  V₁ : Finset V
  V₂ : Finset V
  union    : V₁ ∪ V₂ = Finset.univ
  disjoint : Disjoint V₁ V₂

namespace Bipartition

variable {V : Type*} [Fintype V]

/-- Sizes of the two parts sum to |V|. -/
theorem card_add (bp : Bipartition V) : bp.V₁.card + bp.V₂.card = Fintype.card V := by
  have h := bp.union
  rw [← Finset.card_univ, ← h]
  exact (Finset.card_union_of_disjoint bp.disjoint).symm

/-- A bipartition is balanced when the parts differ in size by at most 1. -/
def IsBalanced (bp : Bipartition V) : Prop :=
  bp.V₁.card = bp.V₂.card ∨
  bp.V₁.card = bp.V₂.card + 1 ∨
  bp.V₂.card = bp.V₁.card + 1

/-- Every vertex belongs to exactly one part. -/
theorem mem_V₁_or_V₂ (bp : Bipartition V) (v : V) : v ∈ bp.V₁ ∨ v ∈ bp.V₂ := by
  have : v ∈ Finset.univ := Finset.mem_univ v
  rw [← bp.union] at this
  exact Finset.mem_union.mp this

end Bipartition

/-! ## Edge cut -/

/-- An edge `e = s(u, v)` crosses the bipartition `bp` if one endpoint is in each part. -/
def IsCrossEdge {V : Type*} [Fintype V] (bp : Bipartition V) (e : Sym2 V) : Prop :=
  ∃ u ∈ bp.V₁, ∃ v ∈ bp.V₂, e = s(u, v)

/-- The edge cut: edges of `G` crossing `bp`. -/
def edgeCut {V : Type*} [Fintype V] (G : SimpleGraph V) (bp : Bipartition V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (IsCrossEdge bp)

/-- Size of the edge cut. -/
def edgeCutSize {V : Type*} [Fintype V] (G : SimpleGraph V) (bp : Bipartition V) : ℕ :=
  (edgeCut G bp).card

/-! ## Biconnectivity -/

/-- `G` is biconnected if it is connected and either has exactly 2 vertices,
    or removing any single vertex leaves it connected.
    (Paper's definition: biconnected ↔ 2-connected or K₂.) -/
def IsBiconnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  (Fintype.card V = 2 ∨ ∀ v : V, (G.induce ({w : V | w ≠ v})).Connected)

/-! ## Cut vertices -/

/-- `v` is a cut vertex of `G` if `G` is connected and removing `v` disconnects it. -/
def IsCutVertex {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : Prop :=
  G.Connected ∧ ¬(G.induce ({w : V | w ≠ v})).Connected

/-! ## Blocks -/

/-- `S` induces a block of `G` if `G.induce S` is biconnected and maximal with this property. -/
def IsBlock {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsBiconnected (G.induce (S : Set V)) ∧
  ∀ S' : Finset V, S ⊂ S' → ¬IsBiconnected (G.induce (S' : Set V))

/-- Number of blocks of `G`.
    Defined as the number of finsets that are block vertex-sets.
    Properties (decomposition additivity, etc.) are stated as separate lemmas. -/
def blockCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ (α := Finset V)).filter (IsBlock G) |>.card

/-! ## Internal vertices -/

/-- Vertices not on the outer face boundary `outer`. -/
def internalVerts {V : Type*} [Fintype V] (outer : Finset V) : Finset V :=
  Finset.univ \ outer

/-- Count of internal vertices. -/
def internalVertCount {V : Type*} [Fintype V] (outer : Finset V) : ℕ :=
  (internalVerts outer).card

theorem internalVertCount_eq {V : Type*} [Fintype V] (outer : Finset V) :
    internalVertCount outer = Fintype.card V - outer.card := by
  unfold internalVertCount internalVerts
  -- Finset.card_sdiff : (a \ b).card = a.card - (b ∩ a).card  (no subset hypothesis)
  simp [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]

end MinBal

end -- noncomputable section
