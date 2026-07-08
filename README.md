# Minimum Balanced Bipartitions of Planar Triangulations — Lean 4

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Project](https://github.com/abhishan82/Minimum-balanced-bipartitions-of-planar-graphs/actions/workflows/build-project.yml/badge.svg)](https://github.com/abhishan82/Minimum-balanced-bipartitions-of-planar-graphs/actions/workflows/build-project.yml)

Formalization of [A. Shantanam, *Minimum balanced bipartitions of planar
triangulations*, Discrete Mathematics 343 (2020) 111572], which confirms the
folklore conjecture that every planar graph $G$ admits a minimum balanced
bipartition $(V_1, V_2)$ with $e(V_1, V_2) \leq |V(G)|$.

## Main results (formalized)

- `MinBal.main_theorem` (Theorem 1.1) — If $G$ is a plane triangulation, then
  there exists a balanced bipartition $(V_1, V_2)$ of $V(G)$ such that both
  $G[V_1]$ and $G[V_2]$ are connected near-triangulations, and the total
  number of blocks in $G[V_1]$ and $G[V_2]$ exceeds the total number of
  internal vertices by at most 2.
- `MinBal.folklore_conjecture` — Every plane triangulation $G$ has a balanced
  bipartition $(V_1, V_2)$ with $e(V_1, V_2) \leq |V(G)|$.

Both are fully proved relative to the assumed results in the ledger below.

## Architecture

- `Project/Foundations/` — reusable graph-embedding infrastructure:
  combinatorial maps (rotation systems), surface graphs with Euler
  characteristic, planarity, block-cut trees. Rotation systems do not yet
  exist in Mathlib; this layer is developed with eventual upstreaming in mind.
- `Project/MinBal/` — an abstract `NearTriangulation` interface (Euler formula
  and edge–face incidence as fields) and the combinatorial proof of the main
  theorem on top of it.

## Assumed results (sorry ledger)

Deep geometric facts are stated precisely as `theorem ... := sorry` (not
`axiom` — see [CLAUDE.md](CLAUDE.md)); everything else is proved. Buckets:
(A) provable from Foundations — planned; (B) provable pure combinatorics —
planned; (C) deep external geometry — assumed with citation.

| Declaration | File | Bucket | Notes |
|---|---|---|---|
| `induce_euler` | Foundations/CombMap.lean | A | Euler char of a CombMap restricted to a connected induced subgraph; provable by vertex/edge-deletion induction on `cycleFactorsFinset`, blocked only by a missing "cycle-merge" counting lemma, not by any external theorem. |
| `concretePlaneNT_cut_vertex_decomp_geo` | MinBal/ConcreteNT.lean | A | Cut-vertex splits a `ConcretePlaneNT` into two sub-embeddings; derivable once `toConcrete`/`induceData` give the concrete rotation system, purely from its face structure. |
| `induceData` | MinBal/ConcreteNT.lean | A | Induced-subgraph near-triangulation data (outer face, triangular inner faces, face count); a direct consequence of `induce_euler` in the same CombMap model. |
| `NearTriangulation.toConcrete` | MinBal/ConcreteNT.lean | C | Representation theorem: every abstract near-triangulation (Euler formula + incidence identity) is realizable as a concrete rotation-system embedding. The converse-Euler / planar-realizability direction; Jackson–Yu-adjacent (B. Jackson, X. Yu, "Hamilton cycles in plane triangulations", J. Graph Theory 41 (2002) 138–150). |
| `nt_good_vertex_exists` | MinBal/Lemmas.lean | A | Existence of a boundary vertex with two distinct neighbors in the other part (Lemma 3.5's planarity content); a face-walk argument on the concrete embedding once `toConcrete`/`induceData` are available. |
| `sep_tri_bipartition` | MinBal/MainTheorem.lean | A | Geometric core of Prop. 4.1: a separating triangle's two-region decomposition, read off the concrete embedding's face structure. |
| `deg1_sink_bipartition` | MinBal/MainTheorem.lean | A | Geometric core of Prop. 4.2 (degree-1 sink, ≥5 vertices); built from the concrete embedding plus 4-connectivity. |
| `tiny_sink_bipartition` | MinBal/MainTheorem.lean | A | Geometric core of Prop. 4.3 (sink $\cong K_4$); same embedding-dependent construction, small case. |
| `no_sep_tri_gives_sink` | MinBal/MainTheorem.lean | A | Standard-tree decomposition producing a 4-connected sink when no balanced separating triangle exists. "Separating triangle" and the standard tree are themselves embedding notions, so this is deferred to the combinatorial-map model like the other Section 4 cases, once `toConcrete`/`induceData` are available. |

## Blueprint

Dependency graph and paper-to-Lean correspondence:
[abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs](https://abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs/)
([PDF](https://abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs/blueprint.pdf),
[dependency graph](https://abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs/blueprint/dep_graph_document.html),
[API docs](https://abhishan82.github.io/Minimum-balanced-bipartitions-of-planar-graphs/docs/)).

## Author

Abhinav Shantanam (paper and formalization). Formalization assisted by LLM
coding agents; every proof reviewed by the author.
