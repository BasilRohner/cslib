/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

module
public import Cslib.Algorithms.Lean.Graph.Graph
public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# Basic graph theory definitions

This file introduces fundamental graph-theoretic concepts for the graph structures
defined in `Graph.lean`: adjacency, neighborhoods, degree, cliques, independent sets,
connectivity, trees, and more.

## Main definitions

### SimpleGraph
* `SimpleGraph.Adj`: adjacency relation.
* `SimpleGraph.neighborhood`: open neighborhood N(v).
* `SimpleGraph.closedNeighborhood`: closed neighborhood N[v].
* `SimpleGraph.degree`: degree of a vertex.
* `SimpleGraph.minDegree`: minimum degree δ(G).
* `SimpleGraph.maxDegree`: maximum degree Δ(G).
* `SimpleGraph.IsRegular`: every vertex has the same degree.
* `SimpleGraph.IsClique`: a set of pairwise adjacent vertices.
* `SimpleGraph.cliqueNumber`: the size of a largest clique ω(G).
* `SimpleGraph.IsIndependentSet`: a set of pairwise non-adjacent vertices.
* `SimpleGraph.independenceNumber`: the size of a largest independent set α(G).
* `SimpleGraph.complement`: the complement graph.
* `SimpleGraph.IsSubgraph`: subgraph relation.
* `SimpleGraph.IsSpanningSubgraph`: subgraph with the same vertex set.
* `SimpleGraph.Reachable`: reflexive transitive closure of adjacency.
* `SimpleGraph.IsConnected`: every pair of vertices is reachable.
* `SimpleGraph.IsAcyclic`: no cycle exists.
* `SimpleGraph.IsTree`: connected and acyclic.
* `SimpleGraph.IsForest`: acyclic.
* `SimpleGraph.IsBipartite`: vertex set can be 2-colored.
* `SimpleGraph.IsComplete`: all distinct vertices are adjacent.
* `SimpleGraph.chromaticNumber`: minimum number of colors for a proper coloring χ(G).

### Graph
* `Graph.Adj`, `Graph.neighborhood`: analogous definitions for general graphs, using
  `Set` instead of `Finset`.

### SimpleDiGraph
* `SimpleDiGraph.AdjTo`, `SimpleDiGraph.AdjFrom`: directed adjacency.
* `SimpleDiGraph.outNeighborhood`, `SimpleDiGraph.inNeighborhood`: directed neighborhoods.
* `SimpleDiGraph.outDegree`, `SimpleDiGraph.inDegree`: directed degrees.

## Notation

* `N(G, v)` — open neighborhood of `v` in `G`.
* `N[G, v]` — closed neighborhood of `v` in `G`.
* `deg(G, v)` — degree of `v` in `G`.
* `δ(G)` — minimum degree of `G`.
* `Δ(G)` — maximum degree of `G`.
* `ω(G)` — clique number of `G`.
* `α'(G)` — independence number of `G`.
* `χ(G)` — chromatic number of `G`.
-/

namespace Cslib.Algorithms.Lean

variable {α ε : Type*}

-- Instances for Finset.fold with min
private instance : Std.Commutative (min : ℕ → ℕ → ℕ) := ⟨Nat.min_comm⟩
private instance : Std.Associative (min : ℕ → ℕ → ℕ) := ⟨Nat.min_assoc⟩

-- ============================================================================
-- SimpleGraph: basic definitions
-- ============================================================================

section SimpleGraph

variable [DecidableEq α]

/-- Two vertices are adjacent in a simple graph if their unordered pair is an edge. -/
def SimpleGraph.Adj (G : SimpleGraph α) (u v : α) : Prop :=
  Sym2.mk u v ∈ G.edgeSet

/-- Decidability of adjacency in a simple graph. -/
instance SimpleGraph.adjDecidable (G : SimpleGraph α) (u v : α) :
    Decidable (G.Adj u v) :=
  Finset.decidableMem _ _

/-- The open neighborhood of a vertex: the set of vertices adjacent to it. -/
def SimpleGraph.neighborhood (G : SimpleGraph α) (v : α) : Finset α :=
  G.vertexSet.filter (G.Adj v)

/-- The closed neighborhood of a vertex: the vertex itself together with its
open neighborhood, restricted to vertices of the graph. -/
def SimpleGraph.closedNeighborhood (G : SimpleGraph α) (v : α) : Finset α :=
  G.vertexSet.filter (fun u => G.Adj v u ∨ u = v)

/-- The degree of a vertex: the cardinality of its open neighborhood. -/
def SimpleGraph.degree (G : SimpleGraph α) (v : α) : ℕ :=
  (G.neighborhood v).card

/-- The minimum degree of a simple graph. Returns 0 for the empty graph. -/
def SimpleGraph.minDegree (G : SimpleGraph α) : ℕ :=
  G.vertexSet.fold min G.vertexSet.card G.degree

/-- The maximum degree of a simple graph. Returns 0 for the empty graph. -/
def SimpleGraph.maxDegree (G : SimpleGraph α) : ℕ :=
  G.vertexSet.sup G.degree

/-- A simple graph is `k`-regular if every vertex has degree `k`. -/
def SimpleGraph.IsRegular (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∀ v ∈ G.vertexSet, G.degree v = k

-- --------------------------------------------------------------------------
-- Cliques and independent sets
-- --------------------------------------------------------------------------

/-- A set of vertices forms a clique if it consists of vertices and every two distinct
vertices in it are adjacent. -/
def SimpleGraph.IsClique (G : SimpleGraph α) (S : Finset α) : Prop :=
  S ⊆ G.vertexSet ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

instance SimpleGraph.isCliqueDecidable (G : SimpleGraph α) : DecidablePred G.IsClique :=
  fun S => show Decidable (S ⊆ G.vertexSet ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) from
    inferInstance

/-- The clique number ω(G): the maximum size of a clique. Returns 0 for the empty graph. -/
def SimpleGraph.cliqueNumber (G : SimpleGraph α) : ℕ :=
  (G.vertexSet.powerset.filter (G.IsClique)).sup Finset.card

/-- A set of vertices is independent if no two distinct vertices in it are adjacent. -/
def SimpleGraph.IsIndependentSet (G : SimpleGraph α) (S : Finset α) : Prop :=
  S ⊆ G.vertexSet ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

instance SimpleGraph.isIndependentSetDecidable (G : SimpleGraph α) :
    DecidablePred G.IsIndependentSet :=
  fun S => show Decidable (S ⊆ G.vertexSet ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v) from
    inferInstance

/-- The independence number α(G): the maximum size of an independent set. -/
def SimpleGraph.independenceNumber (G : SimpleGraph α) : ℕ :=
  (G.vertexSet.powerset.filter (G.IsIndependentSet)).sup Finset.card

-- --------------------------------------------------------------------------
-- Complement, subgraph, complete
-- --------------------------------------------------------------------------

/-- The complement of a simple graph: same vertex set, an edge exists between distinct
vertices iff it does not in the original graph. -/
def SimpleGraph.complement (G : SimpleGraph α) : SimpleGraph α where
  vertexSet := G.vertexSet
  edgeSet :=
    ((G.vertexSet ×ˢ G.vertexSet).image (fun p => Sym2.mk p.1 p.2)).filter
      (fun e => ¬ e.IsDiag) \ G.edgeSet
  incidence := by
    intro e he v hv
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_image,
               Finset.mem_product] at he
    obtain ⟨⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, _⟩, _⟩ := he
    exact (Sym2.mem_iff.mp hv).elim (· ▸ ha) (· ▸ hb)
  loopless := by
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_filter] at he
    exact he.1.2

/-- `H` is a subgraph of `G` if the vertices and edges of `H` are subsets of those of `G`. -/
def SimpleGraph.IsSubgraph (H G : SimpleGraph α) : Prop :=
  H.vertexSet ⊆ G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-- `H` is a spanning subgraph of `G` if it has the same vertex set and its edges are a
subset of those of `G`. -/
def SimpleGraph.IsSpanningSubgraph (H G : SimpleGraph α) : Prop :=
  H.vertexSet = G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-- A simple graph is complete if every pair of distinct vertices is adjacent. -/
def SimpleGraph.IsComplete (G : SimpleGraph α) : Prop :=
  ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, u ≠ v → G.Adj u v

-- --------------------------------------------------------------------------
-- Connectivity and trees
-- --------------------------------------------------------------------------

/-- Two vertices are reachable if they are related by the reflexive transitive closure
of the adjacency relation. -/
def SimpleGraph.Reachable (G : SimpleGraph α) (u v : α) : Prop :=
  Relation.ReflTransGen G.Adj u v

/-- A simple graph is connected if it is nonempty and every pair of vertices is reachable
from each other. -/
def SimpleGraph.IsConnected (G : SimpleGraph α) : Prop :=
  G.vertexSet.Nonempty ∧ ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Reachable u v

/-- A cycle in a simple graph: an injective sequence of at least 3 vertices such that
consecutive vertices (cyclically) are adjacent. -/
def SimpleGraph.HasCycle (G : SimpleGraph α) : Prop :=
  ∃ (n : ℕ) (_ : n ≥ 3) (f : Fin n → α),
    Function.Injective f ∧
    (∀ i : Fin n, f i ∈ G.vertexSet) ∧
    (∀ i : Fin n, G.Adj (f i) (f ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩))

/-- A simple graph is acyclic if it contains no cycle. -/
def SimpleGraph.IsAcyclic (G : SimpleGraph α) : Prop :=
  ¬ G.HasCycle

/-- A simple graph is a forest if it is acyclic. -/
abbrev SimpleGraph.IsForest (G : SimpleGraph α) : Prop :=
  G.IsAcyclic

/-- A simple graph is a tree if it is connected and acyclic. -/
def SimpleGraph.IsTree (G : SimpleGraph α) : Prop :=
  G.IsConnected ∧ G.IsAcyclic

-- --------------------------------------------------------------------------
-- Bipartiteness and coloring
-- --------------------------------------------------------------------------

/-- A simple graph is bipartite if its vertex set can be partitioned into two independent
sets. -/
def SimpleGraph.IsBipartite (G : SimpleGraph α) : Prop :=
  ∃ A B : Finset α, A ∪ B = G.vertexSet ∧ Disjoint A B ∧
    G.IsIndependentSet A ∧ G.IsIndependentSet B

/-- A proper coloring of a simple graph with `k` colors: an assignment of colors to
vertices such that adjacent vertices receive different colors. -/
def SimpleGraph.IsProperColoring (G : SimpleGraph α) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Adj u v → c u ≠ c v

/-- The chromatic number χ(G): the minimum number of colors needed for a proper coloring.
Returns 0 for the empty graph (the empty function is a valid 0-coloring). -/
noncomputable def SimpleGraph.chromaticNumber (G : SimpleGraph α) : ℕ :=
  @Nat.find (fun k => ∃ c : α → Fin k, G.IsProperColoring k c)
    (fun k => Classical.dec _)
    ⟨G.vertexSet.card + 1, by
      sorry⟩

end SimpleGraph

-- ============================================================================
-- Graph (general, possibly infinite): basic definitions
-- ============================================================================

section Graph

/-- Two vertices are adjacent in a general graph if some edge has them as distinct
endpoints. -/
def Graph.Adj (G : Graph α ε) (u v : α) : Prop :=
  ∃ e ∈ G.edgeSet, u ∈ G.endpoints e ∧ v ∈ G.endpoints e ∧ u ≠ v

/-- The open neighborhood of a vertex in a general graph: the set of adjacent vertices. -/
def Graph.neighborhood (G : Graph α ε) (v : α) : Set α :=
  {u ∈ G.vertexSet | G.Adj v u}

/-- The closed neighborhood of a vertex in a general graph. -/
def Graph.closedNeighborhood (G : Graph α ε) (v : α) : Set α :=
  G.neighborhood v ∪ {v}

/-- Two vertices are reachable in a general graph if they are related by the reflexive
transitive closure of adjacency. -/
def Graph.Reachable (G : Graph α ε) (u v : α) : Prop :=
  Relation.ReflTransGen G.Adj u v

/-- A general graph is connected if it is nonempty and every pair of vertices is
reachable. -/
def Graph.IsConnected (G : Graph α ε) : Prop :=
  G.vertexSet.Nonempty ∧ ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Reachable u v

end Graph

-- ============================================================================
-- SimpleDiGraph: basic definitions
-- ============================================================================

section SimpleDiGraph

variable [DecidableEq α]

/-- Vertex `u` has a directed edge to `v` in a simple directed graph. -/
def SimpleDiGraph.AdjTo (G : SimpleDiGraph α) (u v : α) : Prop :=
  (u, v) ∈ G.edgeSet

/-- Vertex `u` has a directed edge from `v` in a simple directed graph. -/
def SimpleDiGraph.AdjFrom (G : SimpleDiGraph α) (u v : α) : Prop :=
  G.AdjTo v u

instance SimpleDiGraph.adjToDecidable (G : SimpleDiGraph α) (u v : α) :
    Decidable (G.AdjTo u v) :=
  Finset.decidableMem _ _

instance SimpleDiGraph.adjFromDecidable (G : SimpleDiGraph α) (u v : α) :
    Decidable (G.AdjFrom u v) :=
  SimpleDiGraph.adjToDecidable G v u

/-- The out-neighborhood of a vertex: vertices reachable by a single directed edge. -/
def SimpleDiGraph.outNeighborhood (G : SimpleDiGraph α) (v : α) : Finset α :=
  G.vertexSet.filter (G.AdjTo v)

/-- The in-neighborhood of a vertex: vertices with a directed edge to it. -/
def SimpleDiGraph.inNeighborhood (G : SimpleDiGraph α) (v : α) : Finset α :=
  G.vertexSet.filter (G.AdjFrom v)

/-- The out-degree of a vertex: the number of outgoing edges. -/
def SimpleDiGraph.outDegree (G : SimpleDiGraph α) (v : α) : ℕ :=
  (G.outNeighborhood v).card

/-- The in-degree of a vertex: the number of incoming edges. -/
def SimpleDiGraph.inDegree (G : SimpleDiGraph α) (v : α) : ℕ :=
  (G.inNeighborhood v).card

/-- Two vertices are reachable in a simple directed graph if they are related by the
reflexive transitive closure of the directed adjacency relation. -/
def SimpleDiGraph.Reachable (G : SimpleDiGraph α) (u v : α) : Prop :=
  Relation.ReflTransGen G.AdjTo u v

/-- A simple directed graph is strongly connected if every vertex is reachable from
every other vertex. -/
def SimpleDiGraph.IsStronglyConnected (G : SimpleDiGraph α) : Prop :=
  G.vertexSet.Nonempty ∧ ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Reachable u v

end SimpleDiGraph

-- ============================================================================
-- DiGraph (general, possibly infinite): basic definitions
-- ============================================================================

section DiGraph

/-- Vertex `u` has a directed edge to `v` in a general directed graph. -/
def DiGraph.AdjTo (G : DiGraph α ε) (u v : α) : Prop :=
  ∃ e ∈ G.edgeSet, G.endpoints e = (u, v)

/-- The out-neighborhood of a vertex in a general directed graph. -/
def DiGraph.outNeighborhood (G : DiGraph α ε) (v : α) : Set α :=
  {u ∈ G.vertexSet | G.AdjTo v u}

/-- The in-neighborhood of a vertex in a general directed graph. -/
def DiGraph.inNeighborhood (G : DiGraph α ε) (v : α) : Set α :=
  {u ∈ G.vertexSet | G.AdjTo u v}

end DiGraph

-- ============================================================================
-- Notation
-- ============================================================================

section Notation

/-- Notation for the open neighborhood of a vertex. -/
scoped notation "N(" G ", " v ")" => SimpleGraph.neighborhood G v
/-- Notation for the closed neighborhood of a vertex. -/
scoped notation "N[" G ", " v "]" => SimpleGraph.closedNeighborhood G v
/-- Notation for the degree of a vertex. -/
scoped notation "deg(" G ", " v ")" => SimpleGraph.degree G v
/-- Notation for the minimum degree of a graph. -/
scoped notation "δ(" G ")" => SimpleGraph.minDegree G
/-- Notation for the maximum degree of a graph. -/
scoped notation "Δ(" G ")" => SimpleGraph.maxDegree G
/-- Notation for the clique number of a graph. -/
scoped notation "ω(" G ")" => SimpleGraph.cliqueNumber G
/-- Notation for the independence number of a graph. -/
scoped notation "α'(" G ")" => SimpleGraph.independenceNumber G
/-- Notation for the chromatic number of a graph. -/
scoped notation "χ(" G ")" => SimpleGraph.chromaticNumber G

/-- Notation for the out-degree of a vertex in a directed graph. -/
scoped notation "deg⁺(" G ", " v ")" => SimpleDiGraph.outDegree G v
/-- Notation for the in-degree of a vertex in a directed graph. -/
scoped notation "deg⁻(" G ", " v ")" => SimpleDiGraph.inDegree G v
/-- Notation for the out-neighborhood of a vertex in a directed graph. -/
scoped notation "N⁺(" G ", " v ")" => SimpleDiGraph.outNeighborhood G v
/-- Notation for the in-neighborhood of a vertex in a directed graph. -/
scoped notation "N⁻(" G ", " v ")" => SimpleDiGraph.inNeighborhood G v

end Notation

end Cslib.Algorithms.Lean
