import JNWLegalSystem.Averaging
import JNWLegalSystem.Construction

namespace JNW.Vertex

def IsPrism : Vertex → Prop
  | .a _ | .b _ => True
  | _ => False

instance : DecidablePred IsPrism := by
  intro v
  cases v <;> unfold IsPrism <;> infer_instance

abbrev PrismVertex := {v : Vertex // IsPrism v}

def prism : SimpleGraph PrismVertex := graph.induce IsPrism

instance : DecidableRel prism.Adj := by
  intro u v
  change Decidable (graph.Adj u.1 v.1)
  infer_instance

theorem card_prismVertex : Fintype.card PrismVertex = 12 := by native_decide

theorem card_prismEdges : prism.edgeFinset.card = 18 := by native_decide

theorem prism_noLegalSystem : ¬ LegalSystem prism := by
  intro h
  have hc := legalSystem_curvature_obstruction prism h
  rw [card_prismVertex, card_prismEdges] at hc
  omega

end JNW.Vertex
