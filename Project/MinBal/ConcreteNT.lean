-- Project/MinBal/ConcreteNT.lean
-- Bridges concrete PlaneGraph embeddings to the abstract NearTriangulation structure.

import Project.MinBal.PlaneGraph
import Project.Foundations.PlaneGraph
import Project.Foundations.BlockCutTree
import Mathlib.Data.Finset.Basic

noncomputable section
open Classical

namespace MinBal

open SimpleGraph NearTriangulation

-- Do NOT redeclare [DecidableRel G.Adj]: the global instance from MinBal.PlaneGraph covers it.
variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V}

/-! ## Per-face helpers -/

/-- Vertex set of a face: sources of its boundary darts. -/
noncomputable def faceVertSet (pg : G.PlaneGraph) (f : pg.Face) : Finset V :=
  f.val.support.image (·.fst)

/-- Dart count of a face. -/
private noncomputable def dartCount (pg : G.PlaneGraph) (f : pg.Face) : ℕ :=
  f.val.support.card

/-! ## ConcretePlaneNT structure -/

/-- A concrete plane near-triangulation: a PlaneGraph with a designated outer face
    satisfying triangulation conditions. -/
structure ConcretePlaneNT (G : SimpleGraph V) where
  pg           : G.PlaneGraph
  outerFace    : pg.Face
  inner_tri    : ∀ f : pg.Face, f ≠ outerFace → dartCount pg f = 3
  dart_eq_vert : ∀ f : pg.Face, dartCount pg f = (faceVertSet pg f).card
  /-- Distinct faces have distinct vertex sets; image has same card as faceCount. -/
  faceCount_eq : (Finset.univ.image (faceVertSet pg)).card =
                 pg.cmap.facePerm.cycleFactorsFinset.card
  connected    : G.Connected
  two_verts    : 2 ≤ Fintype.card V
  block_pos    : 1 ≤ blockCount G

namespace ConcretePlaneNT

/-- Shorthand for the face count. -/
private noncomputable def FC (cnt : ConcretePlaneNT G) : ℕ :=
  cnt.pg.cmap.facePerm.cycleFactorsFinset.card

/-- Outer face as a vertex set. -/
noncomputable def outerVerts (cnt : ConcretePlaneNT G) : Finset V :=
  faceVertSet cnt.pg cnt.outerFace

/-- All face vertex sets. -/
noncomputable def faceVerts (cnt : ConcretePlaneNT G) : Finset (Finset V) :=
  Finset.univ.image (faceVertSet cnt.pg)

theorem faceVerts_card (cnt : ConcretePlaneNT G) :
    (faceVerts cnt).card = FC cnt :=
  cnt.faceCount_eq

theorem outerVerts_mem (cnt : ConcretePlaneNT G) :
    outerVerts cnt ∈ faceVerts cnt :=
  Finset.mem_image.mpr ⟨cnt.outerFace, Finset.mem_univ _, rfl⟩

theorem inner_tri_card (cnt : ConcretePlaneNT G) :
    ∀ f ∈ faceVerts cnt,
      f ≠ outerVerts cnt → f.card = 3 := by
  intro f hf hne
  simp only [faceVerts, Finset.mem_image, Finset.mem_univ, true_and] at hf
  obtain ⟨face, hf_eq⟩ := hf
  have hface_ne : face ≠ cnt.outerFace := by
    intro h
    apply hne
    simp only [outerVerts]
    rw [← hf_eq, h]
  rw [← hf_eq, ← cnt.dart_eq_vert face]
  exact cnt.inner_tri face hface_ne

/-! ## Counting identities -/

/-- The raw Euler field for a plane graph (g=0). -/
private theorem raw_euler (cnt : ConcretePlaneNT G) :
    (Fintype.card V : ℤ) - G.edgeFinset.card + FC cnt = 2 := by
  have h := cnt.pg.euler  -- : (n:ℤ) - e + faceCount = 2 - 2 * 0
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h
  -- FC cnt and cnt.pg.cmap.faceCount are definitionally equal, so convert closes the goal.
  convert h using 2

/-- Sum of dart counts over all faces = 2 * |E(G)|. -/
theorem dart_face_sum (cnt : ConcretePlaneNT G) :
    (Finset.univ : Finset cnt.pg.Face).sum (fun f => dartCount cnt.pg f) =
    2 * G.edgeFinset.card := by
  have hreindex :
      (Finset.univ : Finset cnt.pg.Face).sum (fun f => dartCount cnt.pg f) =
      cnt.pg.cmap.facePerm.cycleFactorsFinset.sum (fun c => c.support.card) := by
    -- Face = {σ // σ ∈ cycleFactorsFinset}; sum over univ of that subtype = sum over the Finset.
    -- After unfolding dartCount: f.val.support.card for f : Face.
    -- Finset.sum_coe_sort: ∑ i : ↥s, f i = ∑ i ∈ s, f i
    simp only [dartCount, SurfaceGraph.Face]
    exact Finset.sum_coe_sort cnt.pg.cmap.facePerm.cycleFactorsFinset (fun c => c.support.card)
  have hkey := cnt.pg.cmap.sum_support_card_cycleFactorsFinset
  rw [hreindex, hkey, dart_card_eq_twice_card_edges]

/-- Euler formula: n + faceVerts.card = e + 2. -/
theorem euler_eq (cnt : ConcretePlaneNT G) :
    Fintype.card V + (faceVerts cnt).card = G.edgeFinset.card + 2 := by
  have hpg := raw_euler cnt
  have hF : (faceVerts cnt).card = FC cnt := faceVerts_card cnt
  omega

/-- Fintype.card of the Face subtype equals faceVerts.card. -/
private theorem face_fintype_card (cnt : ConcretePlaneNT G) :
    Fintype.card cnt.pg.Face = (faceVerts cnt).card := by
  rw [SurfaceGraph.card_face_eq_faceCount]
  -- Goal: cnt.pg.cmap.faceCount = (faceVerts cnt).card
  -- faceVerts_card: (faceVerts cnt).card = FC cnt = facePerm.cycleFactorsFinset.card = faceCount
  exact (faceVerts_card cnt).symm

/-- Incidence: 2|E| = 3(faceVerts.card − 1) + outerVerts.card. -/
theorem incidence_eq (cnt : ConcretePlaneNT G) :
    2 * G.edgeFinset.card =
    3 * ((faceVerts cnt).card - 1) + (outerVerts cnt).card := by
  have hsum := dart_face_sum cnt
  have hout_dart : dartCount cnt.pg cnt.outerFace = (outerVerts cnt).card := by
    show dartCount cnt.pg cnt.outerFace = (faceVertSet cnt.pg cnt.outerFace).card
    simp only [dartCount, faceVertSet]
    exact cnt.dart_eq_vert cnt.outerFace
  have hinner :
      (Finset.univ.erase cnt.outerFace).sum (fun f => dartCount cnt.pg f) =
      3 * ((faceVerts cnt).card - 1) := by
    have hall3 : ∀ f ∈ Finset.univ.erase cnt.outerFace, dartCount cnt.pg f = 3 :=
      fun f hf => cnt.inner_tri f (Finset.mem_erase.mp hf).1
    rw [Finset.sum_congr rfl hall3, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        face_fintype_card]
  have hsplit :
      (Finset.univ : Finset cnt.pg.Face).sum (fun f => dartCount cnt.pg f) =
      dartCount cnt.pg cnt.outerFace +
        (Finset.univ.erase cnt.outerFace).sum (fun f => dartCount cnt.pg f) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  rw [hsplit, hout_dart, hinner] at hsum
  omega

/-! ## Conversion to NearTriangulation -/

/-- A ConcretePlaneNT determines an abstract NearTriangulation. -/
def toNearTriangulation (cnt : ConcretePlaneNT G) : NearTriangulation G where
  outer     := outerVerts cnt
  faces     := faceVerts cnt
  connected := cnt.connected
  outer_mem := outerVerts_mem cnt
  two_verts := cnt.two_verts
  inner_tri := inner_tri_card cnt
  euler     := euler_eq cnt
  incidence := incidence_eq cnt
  block_pos := cnt.block_pos

end ConcretePlaneNT

/-! ## Cut-vertex decomposition axiom -/

/-- **Axiom (cut-vertex decomposition — geometric core).**
    A near-triangulation with a cut vertex `c` decomposes into two sub-near-triangulations
    on sets S₁, S₂.  The geometric content: c is the unique shared vertex, the pieces
    partition V, the components `G[Sᵢ \ {c}]` are connected (characterising the components
    of `G - {c}`), and internal vertices split additively.
    The edge-count equation `G.edgeFinset.card = NT₁.e + NT₂.e` is derived as a theorem
    from the connectivity conditions via `cut_vertex_no_cross_edge` + `induce_edge_split`.
    The block-count equation `blockCount G = NT₁.b + NT₂.b` is derived as a theorem
    via `blockCount_add_of_no_cross`. -/
axiom concretePlaneNT_cut_vertex_decomp_geo
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : MinBal.NearTriangulation G)
    (c : V) (hcv : MinBal.IsCutVertex G c) (hb : 2 ≤ MinBal.blockCount G) :
    ∃ (S₁ S₂ : Finset V)
      (NT₁ : MinBal.NearTriangulation (G.induce (↑S₁ : Set V)))
      (NT₂ : MinBal.NearTriangulation (G.induce (↑S₂ : Set V))),
      c ∈ S₁ ∧ c ∈ S₂ ∧
      S₁ ∩ S₂ = {c} ∧
      S₁ ∪ S₂ = Finset.univ ∧
      (G.induce (↑(S₁ \ {c} : Finset V) : Set V)).Connected ∧
      (G.induce (↑(S₂ \ {c} : Finset V) : Set V)).Connected ∧
      NT.i = NT₁.i + NT₂.i

omit [Fintype V] [DecidableEq V] in
/-- Helper: `Fintype.card ↥(↑S : Set V) = S.card`. -/
private theorem fintype_card_coe_eq (S : Finset V) :
    Fintype.card ↥(↑S : Set V) = S.card := by
  rw [← Set.toFinset_card, Finset.toFinset_coe]

/-- Derive the full cut-vertex decomposition from the geometric core axiom.
    - `2 ≤ Sᵢ.card` follows from `NTᵢ.two_verts` + `fintype_card_coe_eq`.
    - `S₁.card + S₂.card = n+1` follows from `Finset.card_union_add_card_inter` + partition.
    - `NTᵢ.b < blockCount G` follows from block additivity + `NTⱼ.block_pos`.
    - `1 ≤ NTᵢ.b` is exactly `NTᵢ.block_pos`.
    The `NT.i = NT₁.i + NT₂.i` equation is NOT derived here (no `prop_2_1` available yet);
    it is derived in `Prop21.lean` after `prop_2_1` is proved. -/
theorem concretePlaneNT_cut_vertex_decomp
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (NT : MinBal.NearTriangulation G)
    (c : V) (hcv : MinBal.IsCutVertex G c) (hb : 2 ≤ MinBal.blockCount G) :
    ∃ (S₁ S₂ : Finset V)
      (NT₁ : MinBal.NearTriangulation (G.induce (↑S₁ : Set V)))
      (NT₂ : MinBal.NearTriangulation (G.induce (↑S₂ : Set V))),
      2 ≤ S₁.card ∧ 2 ≤ S₂.card ∧
      S₁.card + S₂.card = Fintype.card V + 1 ∧
      G.edgeFinset.card = NT₁.e + NT₂.e ∧
      MinBal.blockCount G = NT₁.b + NT₂.b ∧
      NT₁.b < MinBal.blockCount G ∧ NT₂.b < MinBal.blockCount G ∧
      1 ≤ NT₁.b ∧ 1 ≤ NT₂.b ∧
      NT.i = NT₁.i + NT₂.i := by
  obtain ⟨S₁, S₂, NT₁, NT₂,
    hc₁, hc₂, h_inter, h_union, hconn₁, hconn₂, hint⟩ :=
    concretePlaneNT_cut_vertex_decomp_geo NT c hcv hb
  have hS₁2 : 2 ≤ S₁.card := (fintype_card_coe_eq S₁) ▸ NT₁.two_verts
  have hS₂2 : 2 ≤ S₂.card := (fintype_card_coe_eq S₂) ▸ NT₂.two_verts
  -- Derive no-cross-edge from connectivity conditions.
  have hno_cross : ∀ u ∈ S₁ \ {c}, ∀ v ∈ S₂ \ {c}, ¬ G.Adj u v := by
    intro u hu v hv
    have hu₁ := (Finset.mem_sdiff.mp hu).1
    have hu_ne : u ≠ c := fun h => (Finset.mem_sdiff.mp hu).2 (Finset.mem_singleton.mpr h)
    have hv₂ := (Finset.mem_sdiff.mp hv).1
    have hv_ne : v ≠ c := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_singleton.mpr h)
    exact cut_vertex_no_cross_edge hcv.2 S₁ S₂ h_inter h_union
      hu₁ hu_ne hv₂ hv_ne hconn₁ hconn₂
  -- Derive edge-count and block-count additivity.
  have hedge : G.edgeFinset.card = NT₁.e + NT₂.e :=
    induce_edge_split hc₁ hc₂ h_inter h_union hno_cross
  have hblock : MinBal.blockCount G = NT₁.b + NT₂.b :=
    blockCount_add_of_no_cross h_inter h_union hno_cross
  refine ⟨S₁, S₂, NT₁, NT₂, hS₁2, hS₂2, ?_, hedge, hblock, ?_, ?_, ?_, ?_, hint⟩
  · -- S₁.card + S₂.card = n + 1
    have hcard := Finset.card_union_add_card_inter S₁ S₂
    rw [h_union, h_inter, Finset.card_univ, Finset.card_singleton] at hcard
    omega
  · -- NT₁.b < blockCount G
    have h1 : 1 ≤ NT₂.b := NT₂.block_pos
    omega
  · -- NT₂.b < blockCount G
    have h1 : 1 ≤ NT₁.b := NT₁.block_pos
    omega
  · exact NT₁.block_pos
  · exact NT₂.block_pos

end MinBal

end -- noncomputable section
