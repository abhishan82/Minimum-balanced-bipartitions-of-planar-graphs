-- Project/MinBal/PlaneGraph.lean
-- Abstract axiomatization of plane graphs (Option A).
-- NearTriangulation G is indexed by G : SimpleGraph V (not V alone),
-- so that G.edgeFinset is available without decidability issues.

import Project.MinBal.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

noncomputable section
open Classical SimpleGraph

-- Make DecidableRel for any SimpleGraph adjacency available classically.
instance (priority := 100) {V : Type*} (G : SimpleGraph V) :
    DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

-- Make edgeSet finite for finite vertex types.
instance (priority := 100) {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype G.edgeSet.toFinset := inferInstance

namespace MinBal

/-! ## Near-triangulations (indexed by graph G) -/

/-- A near-triangulation structure for `G : SimpleGraph V`:
    - outer face boundary `outer : Finset V`
    - face set `faces : Finset (Finset V)`
    satisfying Euler's formula and the edge–face incidence identity.
    These are the key axioms we rely on; they will be proved from a concrete
    combinatorial map in a future development. -/
structure NearTriangulation {V : Type*} [Fintype V] (G : SimpleGraph V) where
  outer     : Finset V
  faces     : Finset (Finset V)
  -- Structural requirements
  connected  : G.Connected
  outer_mem  : outer ∈ faces
  two_verts  : 2 ≤ Fintype.card V
  -- Every inner face is a triangle (3-vertex boundary).
  inner_tri  : ∀ f ∈ faces, f ≠ outer → f.card = 3
  -- Euler's formula: |V| - |E| + |F| = 2, equivalently n + f = e + 2.
  euler      : Fintype.card V + faces.card = G.edgeFinset.card + 2
  -- Edge–face incidence: 2|E| = 3(|F|−1) + |outer|.
  incidence  : 2 * G.edgeFinset.card = 3 * (faces.card - 1) + outer.card
  -- Every connected graph with ≥ 2 vertices has at least one block.
  block_pos  : 1 ≤ blockCount G

namespace NearTriangulation

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Convenient abbreviations. -/
abbrev n (_ : NearTriangulation G) : ℕ := Fintype.card V
abbrev e (_ : NearTriangulation G) : ℕ := G.edgeFinset.card
abbrev f (NT : NearTriangulation G) : ℕ := NT.faces.card
abbrev i (NT : NearTriangulation G) : ℕ := internalVertCount NT.outer
abbrev b (_ : NearTriangulation G) : ℕ := blockCount G

/-- The face count is positive (the outer face is present). -/
lemma f_pos (NT : NearTriangulation G) : 0 < NT.f :=
  Finset.card_pos.mpr ⟨NT.outer, NT.outer_mem⟩

end NearTriangulation

/-! ## Triangulations -/

/-- A triangulation: a near-triangulation where the outer face is also a triangle. -/
structure Triangulation {V : Type*} [Fintype V] (G : SimpleGraph V)
    extends NearTriangulation G where
  outer_tri : outer.card = 3
  -- The three outer vertices are pairwise adjacent (outer face is a triangle).
  outer_adj : ∀ u v : V, u ∈ outer → v ∈ outer → u ≠ v → G.Adj u v
  -- Triangulations are 3-connected: removing any ≤ 2 vertices leaves G connected.
  three_connected : ∀ S : Finset V, S.card ≤ 2 → (G.induce (↑Sᶜ : Set V)).Connected
  -- Removing any two outer vertices leaves a near-triangulation on the complement.
  -- (Key for Lemma 3.3 base case: V₁ = {a,b} ⊆ outer → G[univ \ {a,b}] is a NT.)
  complement_hasNT : ∀ (S : Finset V), 2 ≤ S.card → S ⊆ outer →
      Nonempty (NearTriangulation (G.induce (↑(Finset.univ \ S) : Set V)))
  -- Any connected induced subgraph with ≥ 2 vertices, in a triangulation, that is
  -- a near-triangulation, has its complement also being a near-triangulation.
  -- (Key for Lemma 3.1 base case: V₁ = {u₁,v₁} → G[univ \ {u₁,v₁}] is a NT.)
  complement_pair_hasNT : ∀ (u v : V), G.Adj u v →
      Nonempty (NearTriangulation (G.induce (↑(Finset.univ \ ({u, v} : Finset V)) : Set V)))

namespace Triangulation

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A triangulation has ≥ 3 vertices. -/
lemma three_verts (T : Triangulation G) : 3 ≤ Fintype.card V := by
  calc 3 = T.outer.card := T.outer_tri.symm
    _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- For a triangulation: 2|E| = 3|F| (every face is a triangle). -/
lemma edge_face_incidence_tri (T : Triangulation G) : 2 * T.e = 3 * T.f := by
  -- T.incidence : 2 * G.edgeFinset.card = 3 * (T.faces.card - 1) + T.outer.card
  -- T.outer_tri : T.outer.card = 3
  -- T.f_pos     : 0 < T.faces.card
  -- Unfold abbreviations so omega sees everything as nat arithmetic.
  show 2 * G.edgeFinset.card = 3 * T.faces.card
  have h  := T.incidence
  have ho := T.outer_tri   -- T.outer.card = 3
  have hf := T.f_pos       -- 0 < T.faces.card
  rw [ho] at h
  omega

/-- |E| = 3|V| − 6. -/
theorem edge_count (T : Triangulation G) : T.e = 3 * T.n - 6 := by
  -- Spell out types explicitly so omega sees through abbreviations.
  have hE : Fintype.card V + T.faces.card = G.edgeFinset.card + 2 := T.euler
  have hI : 2 * G.edgeFinset.card = 3 * T.faces.card := T.edge_face_incidence_tri
  have hn : 3 ≤ Fintype.card V := T.three_verts
  show G.edgeFinset.card = 3 * Fintype.card V - 6
  omega

end Triangulation

end MinBal

end -- noncomputable section
