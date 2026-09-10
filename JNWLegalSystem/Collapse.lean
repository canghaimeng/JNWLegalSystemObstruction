import JNWLegalSystem.Connectivity
import JNWLegalSystem.OrbitLemmas

namespace JNW

variable {V : Type*} [Fintype V] [DecidableEq V]

def FourVertexConnectedGraph (G : SimpleGraph V) : Prop :=
  Fintype.card V ≥ 5 ∧
  ∀ deleted : Finset V, deleted.card ≤ 3 →
    (G.induce {v | v ∉ deleted}).Connected

def OrdinaryFourConnected {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  Nat.card H.verts ≥ 5 ∧
  ∀ deleted : Finset H.verts, deleted.card ≤ 3 →
    (H.coe.induce {v | v ∉ deleted}).Connected

theorem fourConnected_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h4 : FourVertexConnectedGraph G) :
    ∀ v : V, 4 ≤ (G.neighborFinset v).card := by
  intro v
  by_contra hdeg
  have hdeg3 : (G.neighborFinset v).card ≤ 3 := by omega
  let deleted := G.neighborFinset v
  have hdegDeleted : deleted.card ≤ 3 := by simpa [deleted] using hdeg3
  have hconn := h4.2 deleted hdeg3
  have hvdel : v ∉ deleted := by
    simp [deleted]
  have hsmall : (deleted ∪ {v}).card ≤ 4 := by
    have hu := Finset.card_union_le deleted {v}
    have hs : ({v} : Finset V).card = 1 := by simp
    omega
  have hproper : deleted ∪ {v} ≠ (Finset.univ : Finset V) := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_univ] at hc
    have hV := h4.1
    omega
  have hnotall : ¬ ∀ w : V, w ∈ deleted ∪ {v} := by
    intro hall
    exact hproper (Finset.eq_univ_of_forall hall)
  push_neg at hnotall
  obtain ⟨w, hw⟩ := hnotall
  have hwdel : w ∉ deleted := fun h ↦ hw (Finset.mem_union_left _ h)
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hw (by simp)
  have hreach := hconn.preconnected ⟨v, hvdel⟩ ⟨w, hwdel⟩
  have hsubne : (⟨v, hvdel⟩ : {x : V // x ∉ deleted}) ≠ ⟨w, hwdel⟩ := by
    intro h
    exact hwv (congrArg Subtype.val h).symm
  obtain ⟨q, hq⟩ := hreach.nonempty_neighborSet_left hsubne
  have hqmem : q.1 ∈ G.neighborFinset v := by
    simpa using hq
  exact q.2 hqmem

theorem connected_regular_subgraph_collapse (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGconn : G.Connected) (hreg : ∀ v, (G.neighborFinset v).card = 4)
    (H : G.Subgraph) [Fintype ↑H.verts]
    [∀ v : V, Fintype ↑(H.neighborSet v)]
    [DecidableRel H.coe.Adj] (hH4 : FourVertexConnectedGraph H.coe) : H = ⊤ := by
  have hmin := fourConnected_minDegree H.coe hH4
  have hdegree (v : H.verts) : H.degree v.1 = 4 := by
    have hlow : 4 ≤ H.degree v.1 := by
      rw [← H.coe_degree v]
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hmin v
    have hupp : H.degree v.1 ≤ 4 := (H.degree_le v.1).trans_eq (by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact hreg v.1)
    omega
  have hneighbors (v : H.verts) : H.neighborSet v.1 = G.neighborSet v.1 := by
    apply Set.eq_of_subset_of_card_le (H.neighborSet_subset v.1)
    rw [G.card_neighborSet_eq_degree]
    change G.degree v.1 ≤ H.degree v.1
    have hgdeg : G.degree v.1 = 4 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact hreg v.1
    rw [hdegree v, hgdeg]
  obtain ⟨v0, hv0⟩ : H.verts.Nonempty := by
    have hcardH := hH4.1
    have hc : 0 < Fintype.card H.verts := by omega
    simpa [Set.nonempty_def] using Fintype.card_pos_iff.mp hc
  have hclosed : ∀ {u w : V}, u ∈ H.verts → G.Adj u w → w ∈ H.verts := by
    intro u w hu huw
    let u' : H.verts := ⟨u, hu⟩
    have hwN : w ∈ H.neighborSet u := by
      rw [hneighbors u']
      exact huw
    exact H.neighborSet_subset_verts u hwN
  have hvert : H.verts = Set.univ := by
    ext w
    constructor
    · intro _
      trivial
    · intro _
      have hr := hGconn.preconnected v0 w
      exact reachable_preserves G (· ∈ H.verts) hclosed hr hv0
  apply SimpleGraph.Subgraph.ext hvert
  funext u w
  apply propext
  constructor
  · exact H.adj_sub
  · intro huw
    have hu : u ∈ H.verts := by rw [hvert]; trivial
    let u' : H.verts := ⟨u, hu⟩
    have hwN : w ∈ H.neighborSet u := by
      rw [hneighbors u']
      exact huw
    exact hwN

theorem ordinaryFourConnected_collapse (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGconn : G.Connected) (hreg : ∀ v, (G.neighborFinset v).card = 4)
    (H : G.Subgraph) (hH4 : OrdinaryFourConnected H) : H = ⊤ := by
  classical
  letI : Fintype H.verts := Fintype.ofFinite H.verts
  letI : ∀ v : V, Fintype (H.neighborSet v) := fun _ ↦ Fintype.ofFinite _
  letI : DecidableRel H.coe.Adj := Classical.decRel _
  apply connected_regular_subgraph_collapse G hGconn hreg H
  constructor
  · simpa [Nat.card_eq_fintype_card] using hH4.1
  · exact hH4.2

end JNW
