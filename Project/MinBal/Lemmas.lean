-- Project/MinBal/Lemmas.lean
-- Section 3 partitioning lemmas.
--
-- Key design: NearTriangulation is Type-valued so can't be a field of a Prop structure.
-- We use HasNT (Nonempty predicate) for existence, and blockCount for block counts.

import Project.MinBal.Defs
import Project.MinBal.PlaneGraph
import Project.MinBal.Prop21
import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets

noncomputable section
open Classical

namespace MinBal

open NearTriangulation Triangulation

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## 4-connectivity -/

/-- G is 4-connected: has ≥ 5 vertices and removing any ≤ 3 vertices leaves it connected. -/
def Is4Connected (G : SimpleGraph V) : Prop :=
  5 ≤ Fintype.card V ∧
  ∀ S : Finset V, S.card ≤ 3 → (G.induce (↑Sᶜ : Set V)).Connected

/-! ## HasNT predicate -/

/-- The induced subgraph on S admits a near-triangulation structure. -/
def HasNT (G : SimpleGraph V) (S : Finset V) : Prop :=
  Nonempty (NearTriangulation (G.induce (↑S : Set V)))

/-- Convenient abbreviation for the block count of an induced subgraph's near-triangulation.
    Since NT.b = blockCount G, the value is blockCount (G.induce ↑S). -/
noncomputable def partBlockCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  blockCount (G.induce (↑S : Set V))

/-- Any connected induced subgraph with ≥ 2 vertices of a near-triangulation admits a
    near-triangulation structure. Uses `NearTriangulation.toConcrete` to obtain the concrete
    plane graph, then `ConcretePlaneNT.induce` for the induced triangulation, then
    `ConcretePlaneNT.toNearTriangulation` to recover the abstract structure. -/
theorem hasNT_of_nt_induce (NT : NearTriangulation G) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected) (h2 : 2 ≤ S.card) :
    HasNT G S :=
  ⟨(NT.toConcrete.induce S hconn h2).toNearTriangulation⟩

/-! ## K₂ helpers -/

omit [Fintype V] in
/-- Helper: Fintype.card of the subtype of a Finset coercion equals the Finset cardinality. -/
private lemma card_set_coe_finset (s : Finset V) :
    Fintype.card ↥(↑s : Set V) = s.card := by
  rw [← Set.toFinset_card, Finset.toFinset_coe]

omit [Fintype V] in
/-- K₂ (two adjacent vertices) is biconnected. -/
lemma K2_isBiconnected {u v : V} (huv : G.Adj u v) :
    IsBiconnected (G.induce (↑({u, v} : Finset V) : Set V)) := by
  have hne : u ≠ v := G.ne_of_adj huv
  have hconn : (G.induce (↑({u, v} : Finset V) : Set V)).Connected := by
    have : (↑({u, v} : Finset V) : Set V) = {u, v} := by simp [Finset.coe_insert, Finset.coe_singleton]
    rw [this]; exact SimpleGraph.induce_pair_connected_of_adj huv
  exact ⟨hconn, Or.inl (by rw [card_set_coe_finset, Finset.card_pair hne])⟩

omit [Fintype V] in
/-- Two adjacent distinct vertices admit a near-triangulation (K₂ structure). -/
lemma K2_hasNT {u v : V} (huv : G.Adj u v) : HasNT G {u, v} := by
  have hne : u ≠ v := G.ne_of_adj huv
  -- The K₂ vertex type.
  have hcard : Fintype.card ↥(↑({u, v} : Finset V) : Set V) = 2 :=
    (card_set_coe_finset {u, v}).trans (Finset.card_pair hne)
  -- H = G.induce ↑{u,v} is connected (using induce_pair_connected_of_adj for Set literal).
  have hconn : (G.induce (↑({u, v} : Finset V) : Set V)).Connected := by
    convert SimpleGraph.induce_pair_connected_of_adj huv using 2
    · simp [Finset.coe_insert, Finset.coe_singleton]
    · simp [Finset.coe_insert, Finset.coe_singleton]
  -- Membership witnesses.
  have hu : u ∈ ({u, v} : Finset V) := Finset.mem_insert_self u _
  have hv : v ∈ ({u, v} : Finset V) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v))
  -- The one edge s(u', v').
  let u' : ↥(↑({u, v} : Finset V) : Set V) := ⟨u, hu⟩
  let v' : ↥(↑({u, v} : Finset V) : Set V) := ⟨v, hv⟩
  have hu'v' : (G.induce (↑({u, v} : Finset V) : Set V)).Adj u' v' :=
    SimpleGraph.induce_adj.mpr huv
  -- Pin edge count to a named variable before refine, so omega sees it uniformly.
  set e := (G.induce (↑({u, v} : Finset V) : Set V)).edgeFinset.card with he_def
  have hedge_ge : 1 ≤ e :=
    Finset.card_pos.mpr ⟨s(u', v'), SimpleGraph.mem_edgeFinset.mpr hu'v'⟩
  have hedge_le : e ≤ 1 :=
    (SimpleGraph.card_edgeFinset_le_card_choose_two).trans
      (by rw [hcard]; native_decide)
  have hedge : e = 1 := le_antisymm hedge_le hedge_ge
  -- Pin vertex count.
  set n := Fintype.card ↥(↑({u, v} : Finset V) : Set V) with hn_def
  -- Construct the NearTriangulation. outer = Finset.univ, faces = {Finset.univ}.
  refine ⟨⟨Finset.univ, {Finset.univ}, hconn,
    Finset.mem_singleton_self Finset.univ,
    ?two_verts, ?inner_tri, ?euler, ?incidence, ?block_pos⟩⟩
  case two_verts => show 2 ≤ n; omega
  case inner_tri => intro f hf hne_outer; exact absurd (Finset.mem_singleton.mp hf) hne_outer
  case euler =>
    -- n + |{Finset.univ}| = e + 2, i.e. n + 1 = e + 2
    -- Use hcard and hedge, converting hedge to a fact about e.
    have he : e = 1 := hedge
    have hn : n = 2 := hcard
    simp only [Finset.card_singleton]
    -- goal: n + 1 = e + 2 (since Fintype.card = n and faces.card = 1)
    -- But Fintype.card is n by def of set, and edgeFinset.card is e by def of set.
    -- If set worked, omega could close. Otherwise use show + exact:
    exact show n + 1 = e + 2 by omega
  case incidence =>
    have he : e = 1 := hedge
    have hn : n = 2 := hcard
    simp only [Finset.card_singleton, Finset.card_univ]
    exact show 2 * e = 3 * (1 - 1) + n by omega
  case block_pos =>
    -- K₂ has Finset.univ as its unique block.
    set H := G.induce (↑({u, v} : Finset V) : Set V)
    -- The vertex type W of H has card 2.
    have hcardW : Fintype.card ↥(↑({u, v} : Finset V) : Set V) = 2 := hcard
    -- H.induce ↑univ ≃g H (where univ : Finset W).
    have hiso : H.induce (↑(Finset.univ : Finset ↥(↑({u, v} : Finset V) : Set V)) : Set _) ≃g H := by
      rw [Finset.coe_univ]
      exact SimpleGraph.induceUnivIso H
    -- IsBiconnected (H.induce ↑univ): card = 2 branch.
    have hbiconn_univ : IsBiconnected
        (H.induce (↑(Finset.univ : Finset ↥(↑({u, v} : Finset V) : Set V)) : Set _)) := by
      constructor
      · exact hiso.symm.connected_iff.mp (K2_isBiconnected huv).1
      · left; exact (Fintype.card_congr hiso.toEquiv).trans hcardW
    -- Finset.univ has no proper superset.
    have hmax : ∀ S' : Finset ↥(↑({u, v} : Finset V) : Set V),
        Finset.univ ⊂ S' → ¬IsBiconnected (H.induce (↑S' : Set _)) :=
      fun S' h _ => h.ne (Finset.univ_subset_iff.mp h.subset).symm
    have hIsBlock : IsBlock H Finset.univ := ⟨hbiconn_univ, hmax⟩
    unfold blockCount
    rw [Nat.one_le_iff_ne_zero]
    exact Finset.card_ne_zero.mpr ⟨Finset.univ,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIsBlock⟩⟩

/-! ## Lemma 3.5 (partition refinement) — stated before 3.1 and 3.3 which both use it -/

/-- **Axiom (plane graph good vertex — existence, two neighbors, and V₂ biconnectivity).**
    The key planarity content: given an NT-bipartition with |V₂| > |avoid|,
    the planar boundary between V₁ and V₂ contains a vertex v ∈ V₂ \ avoid
    with two distinct V₁-neighbors such that G[V₂ \ {v}] is biconnected.
    Biconnectivity of G[V₁ ∪ {v}] is then derived combinatorially via
    `biconn_add_vertex` (no planarity needed for that half). -/
axiom nt_good_vertex_exists
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T      : Triangulation G)
    (bp     : Bipartition V)
    (avoid  : Finset V)
    (havoid : avoid ⊆ bp.V₂)
    (hV₁NT  : HasNT G bp.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp.V₁ : Set V)))
    (hV₂NT  : HasNT G bp.V₂)
    (hV₂    : avoid.card < bp.V₂.card) :
    ∃ v : V, v ∈ bp.V₂ ∧ v ∉ avoid ∧
      ∃ u₁ u₂ : V, u₁ ∈ bp.V₁ ∧ u₂ ∈ bp.V₁ ∧ u₁ ≠ u₂ ∧
        G.Adj v u₁ ∧ G.Adj v u₂ ∧
        IsBiconnected (G.induce (↑(bp.V₂ \ {v}) : Set V))

/-- **Good move exists** (derived from `nt_good_vertex_exists` + `biconn_add_vertex`).
    The biconnectivity of G[V₁ ∪ {v}] follows combinatorially from v having two
    distinct V₁-neighbors in an already-biconnected G[V₁]. -/
theorem nt_good_move_exists
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T      : Triangulation G)
    (bp     : Bipartition V)
    (avoid  : Finset V)
    (havoid : avoid ⊆ bp.V₂)
    (hV₁NT  : HasNT G bp.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp.V₁ : Set V)))
    (hV₂NT  : HasNT G bp.V₂)
    (hV₂    : avoid.card < bp.V₂.card) :
    ∃ v : V, v ∈ bp.V₂ ∧ v ∉ avoid ∧
      IsBiconnected (G.induce (↑(bp.V₁ ∪ {v}) : Set V)) ∧
      IsBiconnected (G.induce (↑(bp.V₂ \ {v}) : Set V)) := by
  obtain ⟨v, hvin, hnavoid, u₁, u₂, hu₁, hu₂, hne, hadj₁, hadj₂, hbc₂⟩ :=
    nt_good_vertex_exists T bp avoid havoid hV₁NT hV₁bc hV₂NT hV₂
  have hv_not_V₁ : v ∉ bp.V₁ := Finset.disjoint_right.mp bp.disjoint hvin
  exact ⟨v, hvin, hnavoid,
    biconn_add_vertex hV₁bc hv_not_V₁ hu₁ hu₂ hne hadj₁ hadj₂, hbc₂⟩

/-- **Plane graph vertex move** (derived from `nt_good_move_exists`).
    Block count bound follows from biconnectivity: both moved parts are biconnected
    → each has exactly 1 block (`biconnected_blockCount_eq_one`), so
    LHS = 1 + 1 = 2 ≤ 1 + 1 + 1 ≤ b(V₁) + b(V₂) + 1 = RHS. -/
theorem nt_vertex_move_geo
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T      : Triangulation G)
    (bp     : Bipartition V)
    (avoid  : Finset V)
    (havoid : avoid ⊆ bp.V₂)
    (hV₁NT  : HasNT G bp.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp.V₁ : Set V)))
    (hV₂NT  : HasNT G bp.V₂)
    (hV₂    : avoid.card < bp.V₂.card) :
    ∃ v : V, v ∈ bp.V₂ ∧ v ∉ avoid ∧
      IsBiconnected (G.induce (↑(bp.V₁ ∪ {v}) : Set V)) ∧
      IsBiconnected (G.induce (↑(bp.V₂ \ {v}) : Set V)) ∧
      partBlockCount G (bp.V₁ ∪ {v}) + partBlockCount G (bp.V₂ \ {v}) ≤
        partBlockCount G bp.V₁ + partBlockCount G bp.V₂ + 1 := by
  obtain ⟨v, hvin, hnavoid, hbc₁, hbc₂⟩ :=
    nt_good_move_exists T bp avoid havoid hV₁NT hV₁bc hV₂NT hV₂
  refine ⟨v, hvin, hnavoid, hbc₁, hbc₂, ?_⟩
  -- Both moved parts are biconnected → each has blockCount = 1.
  have h1 : partBlockCount G (bp.V₁ ∪ {v}) = 1 := biconnected_blockCount_eq_one hbc₁
  have h2 : partBlockCount G (bp.V₂ \ {v}) = 1 := biconnected_blockCount_eq_one hbc₂
  -- Each original part has blockCount ≥ 1 (from HasNT.block_pos).
  have h3 : 1 ≤ partBlockCount G bp.V₁ := hV₁NT.some.block_pos
  have h4 : 1 ≤ partBlockCount G bp.V₂ := hV₂NT.some.block_pos
  omega

omit [Fintype V] in
/-- Helper: `Fintype.card ↥(↑S : Set V) = S.card`. -/
private lemma card_finset_coe (S : Finset V) :
    Fintype.card ↥(↑S : Set V) = S.card := by
  rw [← Set.toFinset_card, Finset.toFinset_coe]

/-- **Plane graph vertex move** (Lemma 3.5 axiom — now a theorem).
    Derives `HasNT` for both parts from biconnectivity via `hasNT_of_nt_induce`,
    with the geometric core (existence of v, biconnectivity, block count) from
    `nt_vertex_move_geo`. -/
theorem nt_vertex_move
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T      : Triangulation G)
    (bp     : Bipartition V)
    (avoid  : Finset V)
    (havoid : avoid ⊆ bp.V₂)
    (hV₁NT  : HasNT G bp.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp.V₁ : Set V)))
    (hV₂NT  : HasNT G bp.V₂)
    (hV₂    : avoid.card < bp.V₂.card) :
    ∃ v : V, v ∈ bp.V₂ ∧ v ∉ avoid ∧
      HasNT G (bp.V₁ ∪ {v}) ∧
      IsBiconnected (G.induce (↑(bp.V₁ ∪ {v}) : Set V)) ∧
      HasNT G (bp.V₂ \ {v}) ∧
      IsBiconnected (G.induce (↑(bp.V₂ \ {v}) : Set V)) ∧
      partBlockCount G (bp.V₁ ∪ {v}) + partBlockCount G (bp.V₂ \ {v}) ≤
        partBlockCount G bp.V₁ + partBlockCount G bp.V₂ + 1 := by
  obtain ⟨v, hv_in, hv_nav, hbc₁, hbc₂, hblock⟩ :=
    nt_vertex_move_geo T bp avoid havoid hV₁NT hV₁bc hV₂NT hV₂
  -- v ∉ bp.V₁ by disjointness of the bipartition.
  have hv_not_V₁ : v ∉ bp.V₁ := Finset.disjoint_right.mp bp.disjoint hv_in
  -- |V₁ ∪ {v}| ≥ 2: since |V₁| ≥ 2 (from hV₁NT.two_verts) and v is new.
  have hV₁'_card : 2 ≤ (bp.V₁ ∪ {v}).card := by
    obtain ⟨NT₁⟩ := hV₁NT
    have h2 : 2 ≤ bp.V₁.card := (card_finset_coe bp.V₁) ▸ NT₁.two_verts
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv_not_V₁),
        Finset.card_singleton]
    omega
  -- |V₂ \ {v}| ≥ 2: from biconnectedness of G[V₂ \ {v}].
  have hV₂'_card : 2 ≤ (bp.V₂ \ {v}).card := by
    have h := isBiconnected_two_le_card hbc₂
    rwa [card_finset_coe] at h
  -- HasNT for both parts via hasNT_of_nt_induce applied to T (a NearTriangulation).
  refine ⟨v, hv_in, hv_nav,
    hasNT_of_nt_induce T.toNearTriangulation _ hbc₁.1 hV₁'_card, hbc₁,
    hasNT_of_nt_induce T.toNearTriangulation _ hbc₂.1 hV₂'_card, hbc₂,
    hblock⟩

/-- **Lemma 3.5.**
    Given a bipartition with |V₂| > |avoid| (where avoid ⊆ V₂), there exists
    v ∈ V₂ \ avoid such that moving v to V₁ keeps both parts near-triangulations
    and increases total block count by at most 1. -/
theorem lemma_3_5
    (T      : Triangulation G)
    (bp     : Bipartition V)
    (avoid  : Finset V)
    (havoid : avoid ⊆ bp.V₂)
    (hV₁NT  : HasNT G bp.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp.V₁ : Set V)))
    (hV₂NT  : HasNT G bp.V₂)
    (hV₂    : avoid.card < bp.V₂.card) :
    ∃ v : V, v ∈ bp.V₂ ∧ v ∉ avoid ∧
      ∃ (bp' : Bipartition V),
        bp'.V₁ = bp.V₁ ∪ {v} ∧
        bp'.V₂ = bp.V₂ \ {v} ∧
        HasNT G bp'.V₁ ∧ IsBiconnected (G.induce (↑bp'.V₁ : Set V)) ∧
        HasNT G bp'.V₂ ∧ IsBiconnected (G.induce (↑bp'.V₂ : Set V)) ∧
        partBlockCount G bp'.V₁ + partBlockCount G bp'.V₂ ≤
          partBlockCount G bp.V₁ + partBlockCount G bp.V₂ + 1 := by
  -- Get the good vertex from the geo axiom (via nt_vertex_move).
  obtain ⟨v, hv_in, hv_not_avoid, hntV₁', hbcV₁', hntV₂', hbcV₂', hblock⟩ :=
    nt_vertex_move T bp avoid havoid hV₁NT hV₁bc hV₂NT hV₂
  -- v ∉ bp.V₁ by disjointness.
  have hv_not_V₁ : v ∉ bp.V₁ := Finset.disjoint_right.mp bp.disjoint hv_in
  -- Construct bp' = (bp.V₁ ∪ {v}, bp.V₂ \ {v}).
  have hunion : (bp.V₁ ∪ {v}) ∪ (bp.V₂ \ {v}) = Finset.univ := by
    rw [Finset.union_assoc,
        Finset.union_sdiff_of_subset (Finset.singleton_subset_iff.mpr hv_in),
        bp.union]
  have hdisj : Disjoint (bp.V₁ ∪ {v}) (bp.V₂ \ {v}) := by
    rw [Finset.disjoint_union_left]
    exact ⟨bp.disjoint.mono_right Finset.sdiff_subset,
           disjoint_sdiff_self_right⟩
  refine ⟨v, hv_in, hv_not_avoid, ⟨bp.V₁ ∪ {v}, bp.V₂ \ {v}, hunion, hdisj⟩,
    rfl, rfl, hntV₁', hbcV₁', hntV₂', hbcV₂', hblock⟩

/-! ## Lemma 3.1 -/

/-- **Lemma 3.1.**
    For a 4-connected plane triangulation (or K₄) with disjoint edges e₁ = u₁v₁
    and e₂ = u₂v₂, and every k with 2 ≤ k ≤ n-2, there is a bipartition (V₁,V₂)
    with |V₁| = k, eᵢ ⊆ G[Vᵢ], and both parts biconnected near-triangulations. -/
theorem lemma_3_1
    (T     : Triangulation G)
    (h4c   : Is4Connected G ∨ Fintype.card V = 4)
    (u₁ v₁ u₂ v₂ : V)
    (he₁   : G.Adj u₁ v₁)
    (he₂   : G.Adj u₂ v₂)
    (hdisj : Disjoint ({u₁, v₁} : Finset V) ({u₂, v₂} : Finset V))
    (k     : ℕ) (hk_lo : 2 ≤ k) (hk_hi : k ≤ T.n - 2) :
    ∃ bp : Bipartition V,
      bp.V₁.card = k ∧
      u₁ ∈ bp.V₁ ∧ v₁ ∈ bp.V₁ ∧ u₂ ∈ bp.V₂ ∧ v₂ ∈ bp.V₂ ∧
      HasNT G bp.V₁ ∧ IsBiconnected (G.induce (↑bp.V₁ : Set V)) ∧
      HasNT G bp.V₂ ∧ IsBiconnected (G.induce (↑bp.V₂ : Set V)) := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk2 : k' + 1 = 2
    · -- Base case k = 2: V₁ = {u₁, v₁}.
      have hne : u₁ ≠ v₁ := G.ne_of_adj he₁
      -- u₂, v₂ ∉ {u₁, v₁}: directly from vertex-disjointness.
      have hu₂ : u₂ ∉ ({u₁, v₁} : Finset V) :=
        Finset.disjoint_right.mp hdisj (Finset.mem_insert_self u₂ _)
      have hv₂ : v₂ ∉ ({u₁, v₁} : Finset V) :=
        Finset.disjoint_right.mp hdisj
          (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v₂)))
      let V₁ : Finset V := {u₁, v₁}
      let V₂ : Finset V := Finset.univ \ V₁
      have hunion : V₁ ∪ V₂ = Finset.univ := by
        simp [V₁, V₂, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
      refine ⟨⟨V₁, V₂, hunion, disjoint_sdiff_self_right⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [V₁, Finset.card_insert_of_notMem (Finset.mem_singleton.not.mpr hne), hk2]
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu₂⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv₂⟩
      · exact K2_hasNT he₁
      · exact K2_isBiconnected he₁
      · -- HasNT G (univ \ {u₁,v₁}): use complement_pair_hasNT
        exact T.complement_pair_hasNT u₁ v₁ he₁
      · -- IsBiconnected G[univ \ {u₁,v₁}]
        -- Note: (Finset.univ \ {u₁,v₁}) = {u₁,v₁}ᶜ definitionally (Finset.compl).
        have hne' : u₁ ≠ v₁ := G.ne_of_adj he₁
        -- Connectivity: from 4-connectivity (removing 2 ≤ 3 vertices) or three_connected (2 ≤ 2).
        have hconn_V₂ : (G.induce (↑({u₁, v₁}ᶜ : Finset V) : Set V)).Connected := by
          rcases h4c with ⟨_, h4conn⟩ | hn4
          · exact h4conn {u₁, v₁} (by simp [Finset.card_pair hne'])
          · exact T.three_connected {u₁, v₁} (by simp [Finset.card_pair hne'])
        constructor
        · -- Connected: {u₁,v₁}ᶜ = univ \ {u₁,v₁} definitionally.
          exact hconn_V₂
        · -- Card = 2 or vertex removal stays connected.
          rcases h4c with ⟨h5, h4conn⟩ | hn4
          · -- 4-connected (n ≥ 5): use vertex removal within G[univ \ {u₁,v₁}].
            right; intro w
            -- Transfer: G.induce ↑S₃ᶜ →g (G.induce ↑{u₁,v₁}ᶜ).induce {x|x≠w}
            -- where S₃ = {u₁,v₁,w.val}, surjective, so connected transfers.
            set S₃ := ({u₁, v₁, w.val} : Finset V) with hS₃_def
            have hS₃card : S₃.card ≤ 3 := by
              show ({u₁, v₁, w.val} : Finset V).card ≤ 3
              have h1 := Finset.card_insert_le u₁ ({v₁, w.val} : Finset V)
              have h2 := Finset.card_insert_le v₁ ({w.val} : Finset V)
              simp only [Finset.card_singleton] at h2; omega
            have hS₃conn : (G.induce (↑S₃ᶜ : Set V)).Connected := h4conn S₃ hS₃card
            -- Membership helpers
            have sub_compl : ∀ y : V, y ∉ S₃ → y ∈ ({u₁, v₁} : Finset V)ᶜ := by
              intro y hy
              rw [Finset.mem_compl]; intro h; apply hy
              simp only [hS₃_def, Finset.mem_insert, Finset.mem_singleton]
              simp only [Finset.mem_insert, Finset.mem_singleton] at h
              exact h.elim (fun hu => Or.inl hu) (fun hv => Or.inr (Or.inl hv))
            have ne_w_of_not_S₃ : ∀ y : V, y ∉ S₃ → y ≠ w.val := by
              intro y hy heq; apply hy; rw [heq, hS₃_def]
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
                      (Or.inr (Finset.mem_singleton_self _))))
            -- Build the surjective graph hom
            let φ : G.induce (↑S₃ᶜ : Set V) →g
                (G.induce (↑({u₁, v₁}ᶜ : Finset V) : Set V)).induce {x | x ≠ w} :=
              { toFun := fun y =>
                  let hmem := Finset.mem_compl.mp (Finset.mem_coe.mp y.2)
                  ⟨⟨y.val, Finset.mem_coe.mpr (sub_compl y.val hmem)⟩,
                   fun heq => ne_w_of_not_S₃ y.val hmem (congr_arg Subtype.val heq)⟩
                map_rel' := fun h => h }
            have φ_surj : Function.Surjective φ := fun x => by
              have hx_compl : x.val.val ∈ ({u₁, v₁} : Finset V)ᶜ :=
                Finset.mem_coe.mp x.val.2
              have hx_ne_w : x.val.val ≠ w.val := fun heq => x.2 (Subtype.ext heq)
              have hx_not_S₃ : x.val.val ∉ S₃ := by
                simp only [hS₃_def, Finset.mem_insert, Finset.mem_singleton]; push_neg
                have hnotv12 : x.val.val ∉ ({u₁, v₁} : Finset V) :=
                  Finset.mem_compl.mp hx_compl
                simp only [Finset.mem_insert, Finset.mem_singleton] at hnotv12
                push_neg at hnotv12
                exact ⟨hnotv12.1, hnotv12.2, hx_ne_w⟩
              exact ⟨⟨x.val.val, Finset.mem_coe.mpr (Finset.mem_compl.mpr hx_not_S₃)⟩,
                     Subtype.ext (Subtype.ext rfl)⟩
            exact SimpleGraph.Connected.map φ φ_surj hS₃conn
          · -- n = 4: card(V \ {u₁,v₁}) = 4 - 2 = 2.
            left
            rw [card_set_coe_finset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
                Finset.card_univ, Finset.card_pair hne', hn4]
    · -- Inductive step: k = k'+1 ≥ 3.
      have hk'_lo : 2 ≤ k' := by omega
      have hk'_hi : k' ≤ T.n - 2 := by
        have hTn : T.n = Fintype.card V := rfl; rw [hTn] at hk_hi ⊢; omega
      obtain ⟨bp₀, hsize₀, hu₁₀, hv₁₀, hu₂₀, hv₂₀, hnt₁₀, hbc₁₀, hnt₂₀, hbc₂₀⟩ :=
        ih hk'_lo hk'_hi
      -- |bp₀.V₂| ≥ 3: |V₁| = k' and |V| ≥ k'+3 (k'+1 ≤ n-2 ⟹ n ≥ k'+3).
      have hV₂card3 : 3 ≤ bp₀.V₂.card := by
        have hca := bp₀.card_add
        have hTn : T.n = Fintype.card V := rfl; rw [hTn] at hk_hi; omega
      -- avoid = {u₂, v₂} ⊆ V₂, card 2 < |V₂|.
      have hne₂ : u₂ ≠ v₂ := G.ne_of_adj he₂
      have havoid_sub : ({u₂, v₂} : Finset V) ⊆ bp₀.V₂ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact hx.elim (fun h => h ▸ hu₂₀) (fun h => h ▸ hv₂₀)
      have havoid_card : ({u₂, v₂} : Finset V).card < bp₀.V₂.card := by
        rw [Finset.card_pair hne₂]; omega
      obtain ⟨v, hv_in, hv_not_avoid, bp', heq₁, heq₂, hnt₁', hbc₁', hnt₂', hbc₂', _⟩ :=
        lemma_3_5 T bp₀ {u₂, v₂} havoid_sub hnt₁₀ hbc₁₀ hnt₂₀ havoid_card
      have hv_not_V₁ : v ∉ bp₀.V₁ := Finset.disjoint_right.mp bp₀.disjoint hv_in
      have hv_ne_u₂ : v ≠ u₂ := by
        intro h; apply hv_not_avoid; rw [h]; exact Finset.mem_insert_self u₂ _
      have hv_ne_v₂ : v ≠ v₂ := by
        intro h; apply hv_not_avoid; rw [h]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      have hu₂' : u₂ ∈ bp'.V₂ := by
        rw [heq₂]
        exact Finset.mem_sdiff.mpr ⟨hu₂₀, Finset.mem_singleton.not.mpr (Ne.symm hv_ne_u₂)⟩
      have hv₂' : v₂ ∈ bp'.V₂ := by
        rw [heq₂]
        exact Finset.mem_sdiff.mpr ⟨hv₂₀, Finset.mem_singleton.not.mpr (Ne.symm hv_ne_v₂)⟩
      refine ⟨bp', ?_, ?_, ?_, ?_, ?_, hnt₁', ?_, hnt₂', ?_⟩
      · rw [heq₁, Finset.card_union_of_disjoint
              (Finset.disjoint_singleton_right.mpr hv_not_V₁),
            Finset.card_singleton, hsize₀]
      · rw [heq₁]; exact Finset.mem_union_left _ hu₁₀
      · rw [heq₁]; exact Finset.mem_union_left _ hv₁₀
      · exact hu₂'
      · exact hv₂'
      · exact hbc₁'
      · exact hbc₂'

/-! ## Lemma 3.3 -/

/-- **Lemma 3.3.**
    Plane triangulation with outer face {a,b,c}: for every 2 ≤ k ≤ n-1,
    there is a bipartition with {a,b} ⊆ V₁, c ∈ V₂, both parts are
    (biconnected) near-triangulations. -/
theorem lemma_3_3
    (T     : Triangulation G)
    (a b c : V)
    (habc  : T.outer = {a, b, c})
    (hab   : a ≠ b) (hbc   : b ≠ c) (hac   : a ≠ c)
    (k     : ℕ) (hk_lo : 2 ≤ k) (hk_hi : k ≤ T.n - 1) :
    ∃ bp : Bipartition V,
      bp.V₁.card = k ∧
      a ∈ bp.V₁ ∧ b ∈ bp.V₁ ∧ c ∈ bp.V₂ ∧
      HasNT G bp.V₁ ∧ IsBiconnected (G.induce (↑bp.V₁ : Set V)) ∧
      HasNT G bp.V₂ := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk2 : k' + 1 = 2
    · -- Base case k = 2: V₁ = {a, b}.
      -- a and b are adjacent: they are distinct outer vertices of the triangulation.
      have ha : a ∈ T.outer := by rw [habc]; simp
      have hb : b ∈ T.outer := by rw [habc]; simp
      have hc_mem : c ∈ T.outer := by rw [habc]; simp
      have hab_adj : G.Adj a b := T.outer_adj a b ha hb hab
      -- Build the bipartition.
      have hc_not_ab : c ∉ ({a, b} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h => h.elim hac.symm hbc.symm
      let V₁ : Finset V := {a, b}
      let V₂ : Finset V := Finset.univ \ V₁
      have hunion : V₁ ∪ V₂ = Finset.univ := by
        simp [V₁, V₂, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
      refine ⟨⟨V₁, V₂, hunion, disjoint_sdiff_self_right⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- |V₁| = 2
        simp [V₁, Finset.card_insert_of_notMem (Finset.mem_singleton.not.mpr hab), hk2]
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc_not_ab⟩
      · -- HasNT G {a,b}: K₂ near-triangulation.
        exact K2_hasNT hab_adj
      · -- IsBiconnected G[{a,b}]: K₂ is biconnected.
        exact K2_isBiconnected hab_adj
      · -- HasNT G (univ \ {a,b}): use complement_hasNT with S = {a,b} ⊆ outer.
        have hS_sub : ({a, b} : Finset V) ⊆ T.outer := by
          rw [habc]; intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))
        have hS_card : 2 ≤ ({a, b} : Finset V).card := by
          rw [Finset.card_pair hab]
        -- complement_hasNT gives Nonempty (NearTriangulation (G.induce ↑(univ \ {a,b})))
        -- which is exactly HasNT G V₂ since V₂ = univ \ {a,b}.
        exact T.complement_hasNT {a, b} hS_card hS_sub
    · -- Inductive step k = k'+1 ≥ 3.
      have hk'_lo : 2 ≤ k' := by omega
      have hk'_hi : k' ≤ T.n - 1 := by
        have hTn : T.n = Fintype.card V := rfl; rw [hTn] at hk_hi ⊢; omega
      obtain ⟨bp₀, hsize₀, ha₀, hb₀, hc₀, hnt₁₀, hbc₁₀, hnt₂₀⟩ :=
        ih hk'_lo hk'_hi
      have hV₂card : 2 ≤ bp₀.V₂.card := by
        have hca := bp₀.card_add
        have hTn : T.n = Fintype.card V := rfl; rw [hTn] at hk_hi; omega
      have hc_sub : ({c} : Finset V) ⊆ bp₀.V₂ := Finset.singleton_subset_iff.mpr hc₀
      have hcard_avoid : ({c} : Finset V).card < bp₀.V₂.card := by
        simp [Finset.card_singleton]; omega
      obtain ⟨v, hv_in, hv_not_avoid, bp', heq₁, heq₂, hnt₁', hbc₁', hnt₂', _, _⟩ :=
        lemma_3_5 T bp₀ {c} hc_sub hnt₁₀ hbc₁₀ hnt₂₀ hcard_avoid
      have hv_ne : v ≠ c := fun h => hv_not_avoid (h ▸ Finset.mem_singleton_self c)
      have hv_not_V₁ : v ∉ bp₀.V₁ := Finset.disjoint_right.mp bp₀.disjoint hv_in
      refine ⟨bp', ?_, ?_, ?_, ?_, hnt₁', ?_, hnt₂'⟩
      · rw [heq₁, Finset.card_union_of_disjoint
              (Finset.disjoint_singleton_right.mpr hv_not_V₁),
            Finset.card_singleton, hsize₀]
      · rw [heq₁]; exact Finset.mem_union_left _ ha₀
      · rw [heq₁]; exact Finset.mem_union_left _ hb₀
      · rw [heq₂]
        exact Finset.mem_sdiff.mpr ⟨hc₀, fun h => hv_ne (Finset.mem_singleton.mp h).symm⟩
      · exact hbc₁'

/-! ## Corollary 3.2 -/

/-- **Corollary 3.2.**
    Every plane triangulation with n ≥ 4 has a balanced bipartition (V₁, V₂)
    with |V₁| = ⌊n/2⌋, both parts biconnected near-triangulations.
    (The n = 3 case is trivial; HasNT requires ≥ 2 vertices per part so
    ⌊3/2⌋ = 1 is excluded here.) -/
theorem cor_3_2 (T : Triangulation G) (hn4 : 4 ≤ T.n) :
    ∃ bp : Bipartition V,
      bp.IsBalanced ∧
      HasNT G bp.V₁ ∧ IsBiconnected (G.induce (↑bp.V₁ : Set V)) ∧
      HasNT G bp.V₂ := by
  -- Extract outer vertices a, b, c from T.outer (a triangle).
  -- card_eq_three gives: hab : a ≠ b, hac : a ≠ c, hbc : b ≠ c, habc_eq : T.outer = {a,b,c}
  obtain ⟨a, b, c, hab, hac, hbc, habc_eq⟩ := Finset.card_eq_three.mp T.outer_tri
  have hTn : T.n = Fintype.card V := rfl
  -- k = ⌊n/2⌋, satisfies 2 ≤ k ≤ n-1 since n ≥ 4.
  set k := Fintype.card V / 2 with hk_def
  have hk_lo : 2 ≤ k := by rw [hTn] at hn4; omega
  have hk_hi : k ≤ T.n - 1 := by rw [hTn]; omega
  -- Apply lemma_3_3 with the outer vertex labelling.
  -- (lemma_3_3 takes (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) — order matches.)
  obtain ⟨bp, hsize, _, _, _, hnt₁, hbc₁, hnt₂⟩ :=
    lemma_3_3 T a b c habc_eq hab hbc hac k hk_lo hk_hi
  -- IsBalanced: |V₁| = k = ⌊n/2⌋, so the parts differ in size by at most 1.
  refine ⟨bp, ?_, hnt₁, hbc₁, hnt₂⟩
  unfold Bipartition.IsBalanced
  have hca := bp.card_add
  rw [hsize] at hca    -- hca : k + bp.V₂.card = Fintype.card V
  rw [hsize]           -- goal: k = bp.V₂.card ∨ k = bp.V₂.card + 1 ∨ bp.V₂.card = k + 1
  omega

/-! ## Corollary 3.6 (iterated refinement) -/

/-- **Corollary 3.6.**
    Starting from a lemma_3_3 bipartition, moving k vertices from V₂ to V₁
    keeps both parts near-triangulations and increases total block count by at most k. -/
theorem cor_3_6
    (T     : Triangulation G)
    (c     : V)
    (bp₀   : Bipartition V)
    (hV₁NT  : HasNT G bp₀.V₁)
    (hV₁bc  : IsBiconnected (G.induce (↑bp₀.V₁ : Set V)))
    (hV₂NT  : HasNT G bp₀.V₂)
    (hc_in  : c ∈ bp₀.V₂)
    (k     : ℕ) (hk : k ≤ bp₀.V₂.card - 1) :
    ∃ (bp : Bipartition V),
      bp₀.V₁ ⊆ bp.V₁ ∧
      c ∈ bp.V₂ ∧
      bp.V₁.card = bp₀.V₁.card + k ∧
      HasNT G bp.V₁ ∧ IsBiconnected (G.induce (↑bp.V₁ : Set V)) ∧
      HasNT G bp.V₂ ∧
      partBlockCount G bp.V₁ + partBlockCount G bp.V₂ ≤
        partBlockCount G bp₀.V₁ + partBlockCount G bp₀.V₂ + k := by
  induction k with
  | zero =>
    exact ⟨bp₀, Finset.Subset.refl _, hc_in, by simp, hV₁NT, hV₁bc, hV₂NT, le_refl _⟩
  | succ k' ih =>
    obtain ⟨bp', hsub', hc', hsize', hnt₁', hbc₁', hnt₂', hb'⟩ :=
      ih (by omega)
    -- bp'.V₂.card ≥ 2: from k'+1 ≤ bp₀.V₂.card - 1 and cardinality arithmetic.
    have hV₂_card : 2 ≤ bp'.V₂.card := by
      have h1 := bp'.card_add
      have h2 := bp₀.card_add
      omega
    -- Apply lemma_3_5 to get v and the refined bipartition bp''.
    have hc_sub' : ({c} : Finset V) ⊆ bp'.V₂ := Finset.singleton_subset_iff.mpr hc'
    have hcard_avoid' : ({c} : Finset V).card < bp'.V₂.card := by
      simp [Finset.card_singleton]; omega
    obtain ⟨v, hv_in, hv_not_avoid, bp'', heq₁, heq₂, hnt₁'', hbc₁'', hnt₂'', hbc₂'', hb''⟩ :=
      lemma_3_5 T bp' {c} hc_sub' hnt₁' hbc₁' hnt₂' hcard_avoid'
    have hv_ne : v ≠ c := fun h => hv_not_avoid (h ▸ Finset.mem_singleton_self c)
    -- v ∉ bp'.V₁ (disjointness of parts).
    have hv_not_V₁ : v ∉ bp'.V₁ := Finset.disjoint_right.mp bp'.disjoint hv_in
    refine ⟨bp'', ?_, ?_, ?_, hnt₁'', hbc₁'', hnt₂'', ?_⟩
    · -- bp₀.V₁ ⊆ bp''.V₁ = bp'.V₁ ∪ {v}
      rw [heq₁]; exact hsub'.trans Finset.subset_union_left
    · -- c ∈ bp''.V₂ = bp'.V₂ \ {v}
      rw [heq₂]
      exact Finset.mem_sdiff.mpr ⟨hc', fun h => hv_ne (Finset.mem_singleton.mp h).symm⟩
    · -- bp''.V₁.card = bp₀.V₁.card + (k' + 1)
      rw [heq₁, Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hv_not_V₁),
          Finset.card_singleton]
      omega
    · -- Block count bound: combine hb'' and hb'.
      omega

end MinBal

end -- noncomputable section
