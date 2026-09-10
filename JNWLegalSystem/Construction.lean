import JNWLegalSystem.Basic

namespace JNW

inductive Vertex where
  | a : Fin 6 → Vertex
  | b : Fin 6 → Vertex
  | x : Fin 3 → Fin 3 → Vertex
  | y : Fin 3 → Fin 4 → Vertex
deriving DecidableEq, Repr, Fintype

namespace Vertex

def boundary (t : Fin 3) : Fin 4 → Vertex :=
  match t.1 with
  | 0 => ![a 0, a 1, b 1, b 0]
  | 1 => ![a 2, a 3, b 3, b 2]
  | _ => ![a 4, a 5, b 5, b 4]

def baseAdj : Vertex → Vertex → Prop
  | a i, a j => j = i + 1
  | b i, b j => j = i + 1
  | a i, b j => i = j
  | x t r, y u j => t = u
  | q, y t j => q = boundary t j
  | _, _ => False

instance : DecidableRel baseAdj := by
  intro u v
  cases u <;> cases v <;> simp [baseAdj] <;> infer_instance

def graph : SimpleGraph Vertex := SimpleGraph.fromRel baseAdj

instance : DecidableRel graph.Adj := by
  intro u v
  change Decidable ((SimpleGraph.fromRel baseAdj).Adj u v)
  rw [SimpleGraph.fromRel_adj]
  infer_instance

theorem card_vertex : Fintype.card Vertex = 33 := by native_decide

theorem card_edges : graph.edgeFinset.card = 66 := by native_decide

def FourRegular : Prop :=
  ∀ v : Vertex, (graph.neighborFinset v).card = 4

theorem fourRegular : FourRegular := by
  unfold FourRegular
  native_decide

def TriangleFree : Prop :=
  ∀ u v w : Vertex, ¬ (graph.Adj u v ∧ graph.Adj v w ∧ graph.Adj w u)

theorem triangleFree : TriangleFree := by
  unfold TriangleFree
  native_decide

def HasDisplayedFourCycle : Prop :=
  graph.Adj (a 0) (a 1) ∧ graph.Adj (a 1) (b 1) ∧
  graph.Adj (b 1) (b 0) ∧ graph.Adj (b 0) (a 0)

theorem hasDisplayedFourCycle : HasDisplayedFourCycle := by
  unfold HasDisplayedFourCycle
  native_decide

def expand (deleted reached : Finset Vertex) : Finset Vertex :=
  reached ∪ Finset.univ.filter fun v ↦
    v ∉ deleted ∧ ∃ w ∈ reached, graph.Adj w v

def reachSet (deleted : Finset Vertex) (start : Vertex) : Nat → Finset Vertex
  | 0 => {start}
  | n + 1 => expand deleted (reachSet deleted start n)

def allVertices : List Vertex :=
  (List.ofFn fun i : Fin 6 ↦ a i) ++
  (List.ofFn fun i : Fin 6 ↦ b i) ++
  ((List.ofFn fun t : Fin 3 ↦
    (List.ofFn fun r : Fin 3 ↦ x t r)).flatten) ++
  ((List.ofFn fun t : Fin 3 ↦
    (List.ofFn fun j : Fin 4 ↦ y t j)).flatten)

def smallDeletionLists : List (Finset Vertex) :=
  (List.range 4).flatMap fun n ↦
    (List.sublistsLen n allVertices).map List.toFinset

def firstSurvivor (deleted : Finset Vertex) : Option Vertex :=
  allVertices.find? fun v ↦ v ∉ deleted

def ConnectivityCertificate : Prop :=
  smallDeletionLists.all (fun deleted ↦
    match firstSurvivor deleted with
    | none => false
    | some start =>
        let reached := reachSet deleted start 32
        allVertices.all fun v ↦ (v ∈ deleted) || (v ∈ reached)
  ) = true

theorem connectivityCertificate : ConnectivityCertificate := by
  unfold ConnectivityCertificate smallDeletionLists firstSurvivor allVertices reachSet expand
  native_decide

def FourVertexConnected : Prop :=
  Fintype.card Vertex ≥ 5 ∧
  ∀ deleted : Finset Vertex, deleted.card ≤ 3 →
    (graph.induce {v | v ∉ deleted}).Connected

end Vertex
end JNW
