/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Combinatorial Maps on Simple Graphs

A **combinatorial map** (rotation system) on a simple graph `G` assigns to each
vertex a cyclic ordering of the darts (oriented edges) leaving it. Formally, it
is a permutation `σ` on `G.Dart` that preserves the source vertex.

The **face permutation** `φ(d) = σ(d.symm)` — reverse the dart to its pair, then
apply the rotation at the new source — generates the faces of the embedding as its
cyclic orbits.

## Main definitions

* `SimpleGraph.CombMap`: A rotation system — a dart permutation preserving source.
* `SimpleGraph.CombMap.facePerm`: The face permutation `φ = σ ∘ α`.
* `SimpleGraph.CombMap.faceCount`: The number of face orbits (cycles of `facePerm`).

## References

* [B. Mohar and C. Thomassen, *Graphs on Surfaces*][mohar2001]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The dart reversal involution `α(d) = d.symm` as an `Equiv.Perm` on `G.Dart`. -/
def dartRevEquiv (G : SimpleGraph V) [DecidableRel G.Adj] : Equiv.Perm G.Dart where
  toFun    := Dart.symm
  invFun   := Dart.symm
  left_inv := Dart.symm_involutive
  right_inv := Dart.symm_involutive

@[simp]
theorem dartRevEquiv_apply (d : G.Dart) : G.dartRevEquiv d = d.symm :=
  rfl

/-- A **combinatorial map** (rotation system) on `G`: a dart permutation `σ`
that preserves the source vertex of each dart — i.e., `σ` permutes the darts
leaving each vertex independently, implementing a cyclic local ordering. -/
structure CombMap (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The rotation permutation `σ`. -/
  perm   : Equiv.Perm G.Dart
  /-- `σ` preserves the source vertex: darts at `v` stay at `v`. -/
  source : ∀ d : G.Dart, (perm d).fst = d.fst

namespace CombMap

variable (cm : G.CombMap)

/-- The **face permutation** `φ(d) = σ(d.symm)`: reverse the dart to obtain its
partner (oriented the other way along the same edge), then apply the rotation at
the new source vertex. The cyclic orbits of `φ` are precisely the faces of the
combinatorial embedding. -/
def facePerm : Equiv.Perm G.Dart where
  toFun    := fun d => cm.perm d.symm
  invFun   := fun d => (cm.perm.symm d).symm
  left_inv := fun d => by simp [Dart.symm_symm, Equiv.symm_apply_apply]
  right_inv := fun d => by simp [Dart.symm_symm, Equiv.apply_symm_apply]

@[simp]
theorem facePerm_apply (d : G.Dart) : cm.facePerm d = cm.perm d.symm :=
  rfl

/-- The source vertex of `φ(d)` is the target vertex of `d`.
(Reversing `d` swaps source and target; `σ` then preserves the new source.) -/
theorem facePerm_fst (d : G.Dart) : (cm.facePerm d).fst = d.snd := by
  rw [facePerm_apply, cm.source d.symm]
  -- Goal: d.symm.fst = d.snd, which holds definitionally.
  rfl

/-- The **face count**: the number of face orbits, i.e., the number of cyclic
orbits of the face permutation `φ`. -/
noncomputable def faceCount : ℕ :=
  cm.facePerm.cycleFactorsFinset.card

/-- The face permutation has no fixed points: every dart lies in a face orbit.
Proof: `(φ d).fst = d.snd ≠ d.fst` since `G` has no self-loops. -/
theorem facePerm_ne_self (d : G.Dart) : cm.facePerm d ≠ d := fun h => by
  have hfst := cm.facePerm_fst d
  rw [h] at hfst
  -- hfst : d.fst = d.snd; d.adj.ne : d.fst ≠ d.snd
  exact d.adj.ne hfst

/-- The support of the face permutation is all darts:
`cm.facePerm.support = Finset.univ`. -/
theorem facePerm_support_eq_univ : cm.facePerm.support = Finset.univ := by
  ext d
  simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
  exact cm.facePerm_ne_self d

/-- The sum of face-boundary sizes equals the total number of darts:
`∑ f, f.support.card = Fintype.card G.Dart = 2 |E|`.

This is the dart-face incidence equation: each dart belongs to exactly one face. -/
theorem sum_support_card_cycleFactorsFinset :
    cm.facePerm.cycleFactorsFinset.sum (fun c => c.support.card) =
    Fintype.card G.Dart := by
  -- cycleFactorsFinset.sum (fun c => c.support.card) = cycleType.sum = support.card
  have h_eq : cm.facePerm.cycleFactorsFinset.sum (fun c => c.support.card) =
      cm.facePerm.cycleType.sum := by
    -- Both sides equal (cycleFactorsFinset.1.map (Finset.card ∘ support)).sum
    show (cm.facePerm.cycleFactorsFinset.1.map (fun c => c.support.card)).sum =
         (cm.facePerm.cycleFactorsFinset.1.map (Finset.card ∘ Equiv.Perm.support)).sum
    rfl
  rw [h_eq, Equiv.Perm.sum_cycleType, facePerm_support_eq_univ, Finset.card_univ]

end CombMap

/-! ## Dart embedding for induced subgraphs -/

/-- Embed a dart of `G.induce ↑S` as a dart of `G` by forgetting the subtype wrappers. -/
def dartInduceEmbed (S : Finset V) (d : (G.induce (↑S : Set V)).Dart) : G.Dart :=
  { fst := d.fst.val
    snd := d.snd.val
    adj := by have := d.adj; rwa [SimpleGraph.induce_adj] at this }

@[simp]
theorem dartInduceEmbed_fst (S : Finset V) (d : (G.induce (↑S : Set V)).Dart) :
    (dartInduceEmbed S d).fst = d.fst.val := rfl

@[simp]
theorem dartInduceEmbed_snd (S : Finset V) (d : (G.induce (↑S : Set V)).Dart) :
    (dartInduceEmbed S d).snd = d.snd.val := rfl

namespace CombMap

/-- `cm.perm` preserves the source vertex under any number of iterations. -/
theorem perm_pow_fst (cm : G.CombMap) (n : ℕ) (d : G.Dart) :
    ((cm.perm ^ n) d).fst = d.fst := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [cm.source, ih]

/-- For any dart `d` with `d.snd ∈ S`, there exists `k ≥ 1` such that
    `(cm.perm ^ k d).snd ∈ S` — take `k = orderOf cm.perm`, which returns `d`. -/
theorem exists_next_in_finset (cm : G.CombMap) (S : Finset V)
    (d : G.Dart) (hd : d.snd ∈ S) :
    ∃ k : ℕ, 1 ≤ k ∧ ((cm.perm ^ k) d).snd ∈ S :=
  ⟨orderOf cm.perm, orderOf_pos cm.perm, by
    have : (cm.perm ^ orderOf cm.perm) d = d := by
      have h := pow_orderOf_eq_one cm.perm
      exact congr_fun (congr_arg DFunLike.coe h) d
    rw [this]; exact hd⟩

end CombMap

end SimpleGraph
