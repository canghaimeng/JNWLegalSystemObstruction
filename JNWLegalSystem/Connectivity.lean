import JNWLegalSystem.Construction

namespace JNW.Vertex

theorem mem_allVertices (v : Vertex) : v ∈ allVertices := by
  cases v with
  | a i => fin_cases i <;> simp [allVertices]
  | b i => fin_cases i <;> simp [allVertices]
  | x t r => fin_cases t <;> fin_cases r <;> simp [allVertices]
  | y t j => fin_cases t <;> fin_cases j <;> simp [allVertices]

theorem nodup_allVertices : allVertices.Nodup := by native_decide

def canonicalDeletionList (deleted : Finset Vertex) : List Vertex :=
  allVertices.filter fun v ↦ v ∈ deleted

theorem canonicalDeletionList_toFinset (deleted : Finset Vertex) :
    (canonicalDeletionList deleted).toFinset = deleted := by
  ext v
  simp [canonicalDeletionList, mem_allVertices]

theorem canonicalDeletionList_length (deleted : Finset Vertex) :
    (canonicalDeletionList deleted).length = deleted.card := by
  unfold canonicalDeletionList
  rw [← List.toFinset_card_of_nodup (nodup_allVertices.filter _)]
  exact congrArg Finset.card (canonicalDeletionList_toFinset deleted)

theorem canonicalDeletionList_sublist (deleted : Finset Vertex) :
    List.Sublist (canonicalDeletionList deleted) allVertices :=
  List.filter_sublist

theorem mem_smallDeletionLists (deleted : Finset Vertex) (hcard : deleted.card ≤ 3) :
    deleted ∈ smallDeletionLists := by
  unfold smallDeletionLists
  rw [List.mem_flatMap]
  refine ⟨deleted.card, by simpa using Nat.lt_succ_iff.mpr hcard, ?_⟩
  rw [List.mem_map]
  refine ⟨canonicalDeletionList deleted, ?_, canonicalDeletionList_toFinset deleted⟩
  rw [List.mem_sublistsLen]
  exact ⟨canonicalDeletionList_sublist deleted, canonicalDeletionList_length deleted⟩

theorem reachSet_survives (deleted : Finset Vertex) (start v : Vertex)
    (hs : start ∉ deleted) : ∀ n, v ∈ reachSet deleted start n → v ∉ deleted := by
  intro n
  induction n generalizing v with
  | zero =>
      intro hv
      simp only [reachSet, Finset.mem_singleton] at hv
      subst v
      exact hs
  | succ n ih =>
      intro hv
      simp only [reachSet, expand, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      rcases hv with hv | ⟨hv, _⟩
      · exact ih v hv
      · exact hv

theorem reachSet_reachable (deleted : Finset Vertex) (start v : Vertex)
    (hs : start ∉ deleted) : ∀ n, ∀ hv : v ∈ reachSet deleted start n,
      (graph.induce {z | z ∉ deleted}).Reachable
        ⟨start, hs⟩ ⟨v, reachSet_survives deleted start v hs n hv⟩ := by
  intro n
  induction n generalizing v with
  | zero =>
      intro hv
      simp only [reachSet, Finset.mem_singleton] at hv
      subst v
      simpa using
        (SimpleGraph.Reachable.refl :
          (graph.induce {z | z ∉ deleted}).Reachable ⟨start, hs⟩ ⟨start, hs⟩)
  | succ n ih =>
      intro hv
      simp only [reachSet, expand, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      rcases hv with hv | ⟨hvdel, w, hw, hwv⟩
      · exact ih v hv
      · have hwdel := reachSet_survives deleted start w hs n hw
        have hadj : (graph.induce {z | z ∉ deleted}).Adj ⟨w, hwdel⟩ ⟨v, hvdel⟩ := by
          exact hwv
        exact (ih w hw).trans hadj.reachable

theorem connected_after_deleting (deleted : Finset Vertex) (hcard : deleted.card ≤ 3) :
    (graph.induce {v | v ∉ deleted}).Connected := by
  have hmem := mem_smallDeletionLists deleted hcard
  have hcert := connectivityCertificate
  rw [ConnectivityCertificate, List.all_eq_true] at hcert
  have hdeleted := hcert deleted hmem
  cases hroot : firstSurvivor deleted with
  | none =>
      simp [hroot] at hdeleted
  | some root =>
      have hrootSurvives : root ∉ deleted := by
        have := List.find?_some hroot
        simpa [firstSurvivor] using this
      have hall :
          allVertices.all (fun v ↦
            (v ∈ deleted) || (v ∈ reachSet deleted root 32)) = true := by
        simpa [hroot] using hdeleted
      have hreached (v : Vertex) (hv : v ∉ deleted) :
          v ∈ reachSet deleted root 32 := by
        have hvall := (List.all_eq_true.mp hall) v (mem_allVertices v)
        simpa [hv] using hvall
      rw [SimpleGraph.connected_iff]
      constructor
      · intro u v
        have hu := reachSet_reachable deleted root u.1 hrootSurvives 32 (hreached u.1 u.2)
        have hv := reachSet_reachable deleted root v.1 hrootSurvives 32 (hreached v.1 v.2)
        exact hu.symm.trans hv
      · exact ⟨⟨root, hrootSurvives⟩⟩

theorem fourVertexConnected : FourVertexConnected := by
  constructor
  · simpa [card_vertex]
  · exact connected_after_deleting

end JNW.Vertex
