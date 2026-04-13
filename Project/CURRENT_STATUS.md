# Formalization Status — Minimum Balanced Bipartitions of Planar Graphs

**Last updated:** 2026-04-12  
**Build:** Clean — 1312 jobs, 0 errors

---

## Architecture

```
Project/
  Foundations/
    CombMap.lean        — Combinatorial maps (rotation systems), face permutations
    PlaneGraph.lean     — SurfaceGraph (genus g), PlaneGraph abbreviation
    BlockCutTree.lean   — Biconnectivity, blocks, cut vertices, block-cut tree
  MinBal/
    Defs.lean           — Bipartition, IsBiconnected, IsCutVertex, blockCount
    PlaneGraph.lean     — NearTriangulation, Triangulation (abstract axioms)
    EdgePartition.lean  — Edge partition identity: cut + V₁-edges + V₂-edges = E
    ConcreteNT.lean     — ConcretePlaneNT, conversion to/from abstract NT
    Prop21.lean         — Prop 2.1 (e + b + 2 = 2n + i) and Cor 2.2
    Lemmas.lean         — Lemma 3.1 (nt pairs), 3.3, 3.5 (vertex move)
    MainTheorem.lean    — Main theorem 1.1 and folklore conjecture
```

---

## Axiom Inventory (9 remaining, as of 2026-04-12)

### CombMap.lean (1)
| Axiom | Status | Notes |
|-------|--------|-------|
| `CombMap.induce_euler` | axiom | Euler formula V-E+F=2 for induced CombMap on connected subgraph. Requires planarity of ambient embedding — cannot be stated for arbitrary CombMap |

### ConcreteNT.lean (3)
| Axiom | Status | Notes |
|-------|--------|-------|
| `concretePlaneNT_cut_vertex_decomp_geo` | axiom | Cut-vertex decomposition: c splits NT into two sub-NTs with NT.i = NT₁.i + NT₂.i (outer face additivity) |
| `ConcretePlaneNT.induceData` | axiom | Connected G[S] with ≥2 verts inherits NT structure: outer face, triangular inner faces, face count, ≥1 block |
| `NearTriangulation.toConcrete` | axiom | Representation theorem: every abstract NT is realizable as a ConcretePlaneNT |

### Lemmas.lean (1)
| Axiom | Status | Notes |
|-------|--------|-------|
| `nt_good_vertex_exists` | axiom | Existence of v ∈ V₂\avoid with two distinct V₁-neighbors s.t. G[V₂\{v}] is biconnected (planarity essential) |

### MainTheorem.lean (4)
| Axiom | Status | Notes |
|-------|--------|-------|
| `sep_tri_bipartition` | axiom | Balanced sep-triangle → balanced bipartition with NT structures |
| `deg1_sink_bipartition` | axiom | 4-connected sink (≥5 verts) → balanced bipartition with NT structures |
| `tiny_sink_bipartition` | axiom | K₄ sink (4 verts) → balanced bipartition with NT structures |
| `no_sep_tri_gives_sink` | axiom | No balanced sep-tri → standard tree gives 4-connected sink |

---

## Proved Theorems (key results)

### Section 2
- **Prop 2.1** `prop_2_1`: e + b + 2 = 2n + i (inductive proof via cut-vertex decomp)
- **Cor 2.2** `cor_2_2_concrete`: e(V₁,V₂) + (i₁+i₂) + 2 = n + (b₁+b₂)
- **Edge partition** `edge_partition_identity`: cut + G[V₁]-edges + G[V₂]-edges = G-edges

### Section 3
- **Lemma 3.1** `lemma_3_1`: For 4-connected triangulation, bipartition with k verts in V₁ and both parts biconn NTs (inductive on k, uses Lemma 3.5)
- **Lemma 3.3** `lemma_3_3`: For triangulation with outer face {a,b,c}, bipartition with {a,b} ⊆ V₁ and c ∈ V₂, both biconn NTs
- **Lemma 3.5** `lemma_3_5` / **vertex move** `nt_vertex_move`: Given NT-bipartition, can move v from V₂ to V₁ preserving NT and biconn on both parts, with block count bound

### Main
- **Theorem 1.1** `main_theorem`: Every plane triangulation has a balanced bipartition with both parts biconn NTs and b₁+b₂ ≤ i₁+i₂+2
- **Folklore conjecture** `folklore_conjecture`: e(V₁,V₂) ≤ n

### Block-cut tree infrastructure
- `biconn_add_vertex`: Adding vertex with ≥2 distinct neighbors to biconn subgraph gives biconn subgraph
- `biconnected_blockCount_eq_one`: IsBiconnected → blockCount = 1
- `isBiconnected_two_le_card`: IsBiconnected → ≥2 vertices
- `blockCount_add_of_no_cross`: Split at cut vertex gives additive block counts
- `multiblock_has_cut_vertex`: blockCount ≥ 2 → has cut vertex
- `inducePermFun_bijective`: Restricted rotation system is bijective

### Axioms recently reduced to theorems
- `nt_good_move_exists` → theorem via `nt_good_vertex_exists` + `biconn_add_vertex`
- `biconn_add_vertex` → proved (pure combinatorics)
- `biconnected_blockCount_eq_one` → proved
- `CombMap.inducePermFun_bijective` → proved (minimality of nextInSet)
- `nt_vertex_move` → theorem (from geo move exists + hasNT_of_nt_induce)
- `hasNT_of_nt_induce` → theorem (toConcrete + induce + toNearTriangulation)

---

## Next Steps for Future Development

The remaining 9 axioms all require the combinatorial-map (CombMap) model for planarity:

1. **`induce_euler`** — Needs to show restricted CombMap is genus-0 when ambient is genus-0. Likely requires showing face orbits correspond to planar faces.
2. **`concretePlaneNT_cut_vertex_decomp_geo`** — Outer face cycle splits at c giving additive inner vertex count.
3. **`induceData`** — Inherited NT structure from ambient planar embedding.
4. **`NearTriangulation.toConcrete`** — Representation theorem (deepest).
5. **Main theorem cases** (4 axioms) — Specific planarity constructions.

Priority: Items 1-4 must be proved before the main theorem cases (which call `toConcrete` indirectly through `hasNT_of_nt_induce`).
