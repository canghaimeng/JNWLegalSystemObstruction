import JNWLegalSystem.Stages
import JNWLegalSystem.Collapse

namespace JNW

variable {V : Type*}

def GirthAtLeastFour (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle → 4 ≤ w.length

theorem girthAtLeastFour_of_triangleFree [DecidableEq V] (G : SimpleGraph V)
    (htri : ∀ a b c : V, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) :
    GirthAtLeastFour G := by
  intro v w hw
  have h3 := hw.three_le_length
  by_contra h4
  have heq : w.length = 3 := by omega
  have hclique : ∃ s : Finset V, G.IsNClique 3 s :=
    G.is3Clique_iff_exists_cycle_length_three.mpr ⟨v, w, hw, heq⟩
  obtain ⟨s, hs⟩ := hclique
  obtain ⟨a, b, c, hab, hac, hbc, hsc⟩ := G.is3Clique_iff.mp hs
  exact htri a b c ⟨hab, hbc, hac.symm⟩

def kappa2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] : ℚ :=
  1 - (Fintype.card V : ℚ) / 2 + (G.edgeFinset.card : ℚ) / 4

namespace Vertex

theorem graph_girthAtLeastFour : GirthAtLeastFour graph :=
  girthAtLeastFour_of_triangleFree graph triangleFree

theorem graph_kappa2 : kappa2 graph = 1 := by
  norm_num [kappa2, card_vertex, card_edges]

theorem graph_fourVertexConnectedGraph : FourVertexConnectedGraph graph :=
  fourVertexConnected

theorem graph_connected : graph.Connected := by
  have h := connected_after_deleting (∅ : Finset Vertex) (by simp)
  have hset : {v : Vertex | v ∉ (∅ : Finset Vertex)} = (Set.univ : Set Vertex) := by
    ext v
    simp
  rw [hset] at h
  have hu : (graph.induce Set.univ).Connected := h
  exact (SimpleGraph.induceUnivIso graph).connected_iff.mp hu

theorem graph_ordinaryFourConnectedSubgraph_collapse :
    ∀ H : graph.Subgraph, OrdinaryFourConnected H → H = ⊤ := by
  intro H hH
  exact ordinaryFourConnected_collapse graph graph_connected fourRegular H hH

/-- Zero-parameter formal witness for the non-parenthetical, four-connected form of
Jankiewicz--Norin--Wise Problem 5.2.  No assertion about all three-connected
ordinary subgraphs is made here. -/
theorem jnw_problem5_2_four_connected :
    Fintype.card Vertex = 33 ∧
    graph.edgeFinset.card = 66 ∧
    FourRegular ∧
    FourVertexConnectedGraph graph ∧
    TriangleFree ∧
    GirthAtLeastFour graph ∧
    HasDisplayedFourCycle ∧
    kappa2 graph = 1 ∧
    ¬ LegalSystem graph ∧
    ∀ H : graph.Subgraph, OrdinaryFourConnected H → H = ⊤ := by
  exact ⟨card_vertex, card_edges, fourRegular, graph_fourVertexConnectedGraph,
    triangleFree, graph_girthAtLeastFour, hasDisplayedFourCycle, graph_kappa2,
    graph_noLegalSystem, graph_ordinaryFourConnectedSubgraph_collapse⟩

end Vertex
end JNW
