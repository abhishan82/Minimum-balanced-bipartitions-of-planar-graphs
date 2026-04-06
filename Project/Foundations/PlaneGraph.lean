/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Project.Foundations.CombMap

/-!
# Surface Graphs, Plane Graphs, and Planarity

This file defines graph embeddings on orientable surfaces via combinatorial maps,
parameterized by genus `g`. The key cases are:

* `g = 0`: plane graphs (sphere / plane)
* `g = 1`: torus graphs
* etc.

## Main definitions

* `SimpleGraph.SurfaceGraph G g`: A combinatorial map on `G` realizing an embedding
  on an orientable surface of genus `g`. The Euler characteristic condition
  `V - E + F = 2 - 2g` is a field.
* `SimpleGraph.PlaneGraph G`: Abbreviation for `G.SurfaceGraph 0`.
* `SimpleGraph.IsPlanar G`: `G` admits a plane graph structure.
* `SimpleGraph.SurfaceGraph.Face`: A face of the embedding — a cyclic orbit of `φ`.
* `SimpleGraph.SurfaceGraph.faceFinset`: The finite set of all faces.

## Main results

* `SimpleGraph.SurfaceGraph.euler_formula`: The Euler formula `V - E + F = 2 - 2g`
  (immediate from the `euler` field).
* `SimpleGraph.PlaneGraph.euler_formula`: For plane graphs, `V - E + F = 2`.

## References

* [B. Mohar and C. Thomassen, *Graphs on Surfaces*][mohar2001]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A **surface graph** of genus `g`: a simple graph `G` together with a
combinatorial map (rotation system) whose Euler characteristic satisfies
`V - E + F = 2 - 2g`, realizing a cellular embedding of `G` on an orientable
surface of genus `g`. -/
structure SurfaceGraph (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ) where
  /-- The underlying combinatorial map (rotation system). -/
  cmap  : G.CombMap
  /-- The Euler characteristic condition for genus `g`:
  `V - E + F = 2 - 2g`. -/
  euler : (Fintype.card V : ℤ) - G.edgeFinset.card + cmap.faceCount = 2 - 2 * g

/-- A **plane graph**: a graph embedded on the sphere/plane (genus 0).
This is the genus-0 case of `SurfaceGraph`. -/
abbrev PlaneGraph (G : SimpleGraph V) [DecidableRel G.Adj] :=
  G.SurfaceGraph 0

/-- A graph is **planar** if it admits some plane graph structure. -/
def IsPlanar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty (G.PlaneGraph)

namespace SurfaceGraph

variable {g : ℕ} (pg : G.SurfaceGraph g)

/-- The **Euler formula** for a genus-`g` surface embedding:
`V - E + F = 2 - 2g`. -/
theorem euler_formula :
    (Fintype.card V : ℤ) - G.edgeFinset.card + pg.cmap.faceCount = 2 - 2 * g :=
  pg.euler

/-- A **face** of the embedding is a cyclic orbit of the face permutation `φ`,
represented as a cycle factor of `φ`. The number of faces equals `pg.cmap.faceCount`. -/
def Face (pg : G.SurfaceGraph g) :=
  {σ : Equiv.Perm G.Dart // σ ∈ pg.cmap.facePerm.cycleFactorsFinset}

/-- The **darts** of a face: the support of its cycle permutation. -/
noncomputable def Face.darts (f : pg.Face) : Finset G.Dart :=
  f.val.support

/-- The **size** of a face: the number of darts on its boundary. -/
noncomputable def Face.size (f : pg.Face) : ℕ :=
  f.darts.card

/-- A face is a finite type: it is a subtype of a `Finset`, so inherits a `Fintype` instance.
    We use `Fintype.subtype` to construct the instance explicitly, avoiding inference issues
    with the `def`-wrapped `Face` type. -/
noncomputable instance instFintypeFace : Fintype (pg.Face) :=
  show Fintype {σ : Equiv.Perm G.Dart // σ ∈ pg.cmap.facePerm.cycleFactorsFinset} from
    Fintype.subtype pg.cmap.facePerm.cycleFactorsFinset (fun _ => Iff.rfl)

/-- The set of all faces, as a `Finset` of cycle permutations. -/
noncomputable def faceFinset : Finset (Equiv.Perm G.Dart) :=
  pg.cmap.facePerm.cycleFactorsFinset

/-- The face count agrees with `cmap.faceCount`. -/
theorem card_faceFinset_eq :
    pg.faceFinset.card = pg.cmap.faceCount :=
  rfl

/-- `Fintype.card pg.Face` equals `pg.cmap.faceCount`.
    This bridges the subtype cardinality to the combinatorial map face count. -/
theorem card_face_eq_faceCount :
    Fintype.card pg.Face = pg.cmap.faceCount := by
  simp only [Face, CombMap.faceCount, Fintype.card_coe]

end SurfaceGraph

namespace PlaneGraph

variable (pg : G.PlaneGraph)

/-- The **Euler formula** for plane graphs: `V - E + F = 2`. -/
theorem euler_formula :
    (Fintype.card V : ℤ) - G.edgeFinset.card + pg.cmap.faceCount = 2 := by
  simpa using pg.euler

/-- The **dual graph** `G*`: faces of `pg` as vertices, with two faces adjacent
iff they share a boundary dart (i.e., are separated by a common edge of `G`).
Dart `d` and `d.symm` lie on opposite sides of each edge, giving the duality. -/
noncomputable def dual : SimpleGraph pg.Face :=
  { Adj    := fun f1 f2 => f1 ≠ f2 ∧
                ∃ d : G.Dart, d ∈ f1.val.support ∧ d.symm ∈ f2.val.support
    symm   := fun {f1 f2} ⟨hne, d, hd1, hd2⟩ =>
                ⟨hne.symm, d.symm, hd2, by simpa using hd1⟩
    loopless := ⟨fun f h => h.1 rfl⟩ }

/-- Classical `DecidableRel` instance for the dual graph's adjacency relation.
The adjacency `f₁ ~ f₂` is decidable since `G.Dart` is finite (existential over
a finite type with decidable membership). We use `Classical.propDecidable` to
avoid computing the witness explicitly. -/
noncomputable instance instDecidableRelDualAdj (pg : G.PlaneGraph) :
    DecidableRel pg.dual.Adj :=
  fun _ _ => Classical.propDecidable _

/-- An **outer face** of a plane graph: any face may be designated the
infinite (outer) face of the planar embedding. This is a type alias for
`pg.Face`; the choice of which face is "outer" is left to the user. -/
abbrev outerFace := pg.Face

/-- The **internal dual** of `pg` relative to outer face `f`:
the dual graph `G*` with the vertex corresponding to `f` deleted. -/
noncomputable def internalDual (f : pg.Face) :
    SimpleGraph {f' : pg.Face // f' ≠ f} :=
  pg.dual.induce {f' | f' ≠ f}

end PlaneGraph

end SimpleGraph
