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

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem facePerm_apply (d : G.Dart) : cm.facePerm d = cm.perm d.symm :=
  rfl

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem dartInduceEmbed_fst (S : Finset V) (d : (G.induce (↑S : Set V)).Dart) :
    (dartInduceEmbed S d).fst = d.fst.val := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem dartInduceEmbed_snd (S : Finset V) (d : (G.induce (↑S : Set V)).Dart) :
    (dartInduceEmbed S d).snd = d.snd.val := rfl

namespace CombMap

omit [Fintype V] [DecidableEq V] in
/-- `cm.perm` preserves the source vertex under any number of iterations. -/
theorem perm_pow_fst (cm : G.CombMap) (n : ℕ) (d : G.Dart) :
    ((cm.perm ^ n) d).fst = d.fst := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [cm.source, ih]

omit [DecidableEq V] in
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

/-! ## Restriction of a CombMap to an induced subgraph -/

/-- The "next rotation step that stays in S": given dart `d` with source in `S`
    and target in `S`, find the smallest `k ≥ 1` such that `(cm.perm^k d).snd ∈ S`.
    This always exists (take `k = orderOf cm.perm`). -/
noncomputable def nextInSet (cm : G.CombMap) (S : Finset V)
    (d : G.Dart) (hd : d.snd ∈ S) : ℕ :=
  Nat.find (cm.exists_next_in_finset S d hd)

theorem nextInSet_pos (cm : G.CombMap) (S : Finset V)
    (d : G.Dart) (hd : d.snd ∈ S) : 1 ≤ cm.nextInSet S d hd :=
  (Nat.find_spec (cm.exists_next_in_finset S d hd)).1

theorem nextInSet_mem (cm : G.CombMap) (S : Finset V)
    (d : G.Dart) (hd : d.snd ∈ S) :
    ((cm.perm ^ cm.nextInSet S d hd) d).snd ∈ S :=
  (Nat.find_spec (cm.exists_next_in_finset S d hd)).2

/-- The rotation step that stays in S also has source in S (preserved by `perm_pow_fst`). -/
theorem nextInSet_fst (cm : G.CombMap) (S : Finset V)
    (d : G.Dart) (hd_fst : d.fst ∈ S) (hd : d.snd ∈ S) :
    ((cm.perm ^ cm.nextInSet S d hd) d).fst ∈ S := by
  rw [perm_pow_fst]; exact hd_fst

/-- The restricted rotation function on darts of G[S]:
    maps a dart d = (u → v) of G[S] to the next rotation step staying in S.
    The result is a dart of G[S] since both endpoints land in S. -/
noncomputable def inducePermFun (cm : G.CombMap) (S : Finset V)
    (d : (G.induce (↑S : Set V)).Dart) :
    (G.induce (↑S : Set V)).Dart :=
  let d' := dartInduceEmbed S d
  let k := cm.nextInSet S d' (Finset.mem_coe.mp d.snd.property)
  let gd' := (cm.perm ^ k) d'
  { fst := ⟨gd'.fst, Finset.mem_coe.mpr (cm.nextInSet_fst S d'
      (Finset.mem_coe.mp d.fst.property) (Finset.mem_coe.mp d.snd.property))⟩
    snd := ⟨gd'.snd, Finset.mem_coe.mpr (cm.nextInSet_mem S d'
      (Finset.mem_coe.mp d.snd.property))⟩
    adj := SimpleGraph.induce_adj.mpr gd'.adj }

/-- `inducePermFun` preserves the source vertex of a dart. -/
theorem inducePermFun_fst (cm : G.CombMap) (S : Finset V)
    (d : (G.induce (↑S : Set V)).Dart) :
    (cm.inducePermFun S d).fst = d.fst := by
  simp only [inducePermFun]
  ext
  exact cm.perm_pow_fst _ _

/-- `inducePermFun` is a bijection on darts of G[S].
    Proof: it is injective (by minimality of `nextInSet`) and the dart type is finite,
    so injectivity implies bijectivity. -/
theorem inducePermFun_bijective (cm : G.CombMap) (S : Finset V) :
    Function.Bijective (cm.inducePermFun S) := by
  apply Function.Injective.bijective_of_finite
  intro d₁ d₂ h
  have hd₁s : (dartInduceEmbed S d₁).snd ∈ S := Finset.mem_coe.mp d₁.snd.property
  have hd₂s : (dartInduceEmbed S d₂).snd ∈ S := Finset.mem_coe.mp d₂.snd.property
  set k₁ := cm.nextInSet S (dartInduceEmbed S d₁) hd₁s
  set k₂ := cm.nextInSet S (dartInduceEmbed S d₂) hd₂s
  have hk₁pos : 1 ≤ k₁ := cm.nextInSet_pos S (dartInduceEmbed S d₁) hd₁s
  have hk₂pos : 1 ≤ k₂ := cm.nextInSet_pos S (dartInduceEmbed S d₂) hd₂s
  -- fst equality: immediate from inducePermFun_fst
  have hfst : d₁.fst = d₂.fst :=
    calc d₁.fst = (cm.inducePermFun S d₁).fst := (cm.inducePermFun_fst S d₁).symm
      _ = (cm.inducePermFun S d₂).fst := by rw [h]
      _ = d₂.fst := cm.inducePermFun_fst S d₂
  -- The underlying G.Darts `(perm^k_i) dᵢ'` are equal
  -- (same fst via perm_pow_fst; same snd comes definitionally from h.snd)
  have hdart : (cm.perm ^ k₁) (dartInduceEmbed S d₁) =
               (cm.perm ^ k₂) (dartInduceEmbed S d₂) := by
    apply Dart.ext; apply Prod.ext
    · simp only [perm_pow_fst, dartInduceEmbed_fst]
      exact congrArg Subtype.val hfst
    · show ((cm.perm ^ k₁) (dartInduceEmbed S d₁)).snd =
           ((cm.perm ^ k₂) (dartInduceEmbed S d₂)).snd
      exact congrArg (fun d : (G.induce (↑S : Set V)).Dart => d.snd.val) h
  -- k₁ = k₂ by minimality of nextInSet: if they differed, one dart's snd would be in S
  -- at a step before the minimum, contradicting minimality.
  have hk_eq : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with h12 | h12 | h12
    · -- k₁ < k₂: derive d₁' = perm^(k₂-k₁) d₂' with d₁'.snd ∈ S, contradicting nextInSet min
      exfalso
      have hpos : 1 ≤ k₂ - k₁ := by omega
      have hlt : k₂ - k₁ < k₂ := by omega
      have heq : dartInduceEmbed S d₁ =
          (cm.perm ^ (k₂ - k₁)) (dartInduceEmbed S d₂) := by
        apply (cm.perm ^ k₁).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (by omega)]
        exact hdart
      have hmem : ((cm.perm ^ (k₂ - k₁)) (dartInduceEmbed S d₂)).snd ∈ S :=
        heq ▸ hd₁s
      exact @Nat.find_min _ _ (cm.exists_next_in_finset S (dartInduceEmbed S d₂) hd₂s)
        (k₂ - k₁) hlt ⟨hpos, hmem⟩
    · exact h12
    · -- k₁ > k₂: symmetric argument
      exfalso
      have hpos : 1 ≤ k₁ - k₂ := by omega
      have hlt : k₁ - k₂ < k₁ := by omega
      have heq : dartInduceEmbed S d₂ =
          (cm.perm ^ (k₁ - k₂)) (dartInduceEmbed S d₁) := by
        apply (cm.perm ^ k₂).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' (by omega)]
        exact hdart.symm
      have hmem : ((cm.perm ^ (k₁ - k₂)) (dartInduceEmbed S d₁)).snd ∈ S :=
        heq ▸ hd₂s
      exact @Nat.find_min _ _ (cm.exists_next_in_finset S (dartInduceEmbed S d₁) hd₁s)
        (k₁ - k₂) hlt ⟨hpos, hmem⟩
  -- k₁ = k₂ + equal G.Darts → d₁' = d₂' → d₁ = d₂
  have hd'eq : dartInduceEmbed S d₁ = dartInduceEmbed S d₂ :=
    (cm.perm ^ k₁).injective (hk_eq ▸ hdart)
  apply Dart.ext; apply Prod.ext
  · exact hfst
  · exact Subtype.ext (congrArg (·.snd) hd'eq)

/-- The restricted rotation as an `Equiv.Perm` on darts of G[S]. -/
noncomputable def inducePerm (cm : G.CombMap) (S : Finset V) :
    Equiv.Perm (G.induce (↑S : Set V)).Dart :=
  Equiv.ofBijective _ (cm.inducePermFun_bijective S)

/-- `inducePerm` preserves source vertices. -/
theorem inducePerm_source (cm : G.CombMap) (S : Finset V)
    (d : (G.induce (↑S : Set V)).Dart) :
    (cm.inducePerm S d).fst = d.fst :=
  cm.inducePermFun_fst S d

/-- **CombMap induced on G[S]**: the rotation system restricted to the induced subgraph. -/
noncomputable def induce (cm : G.CombMap) (S : Finset V) :
    (G.induce (↑S : Set V)).CombMap where
  perm   := cm.inducePerm S
  source := cm.inducePerm_source S

/-- **Axiom**: The Euler characteristic of the induced CombMap on a connected G[S].
    The face count of the induced CombMap satisfies the Euler formula for the
    plane graph restricted to S. -/
axiom induce_euler (cm : G.CombMap) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected) :
    (Fintype.card ↥(↑S : Set V) : ℤ) -
    (G.induce (↑S : Set V)).edgeFinset.card +
    (cm.induce S).faceCount = 2

end CombMap

end SimpleGraph
