import JNWLegalSystem.Amalgam
import JNWLegalSystem.Construction

namespace JNW.Vertex

abbrev beforeStageP (k : Nat) : Vertex → Prop := fun v ↦
  match v with
  | .a _ | .b _ => True
  | .x t _ | .y t _ => t.1 < k

abbrev beforeStage (k : Nat) : Set Vertex := {v | beforeStageP k v}

abbrev capSideP (t : Fin 3) (v : Vertex) : Prop :=
  (OnC4 (boundary t 0) (boundary t 1) (boundary t 2) (boundary t 3) v) ∨
  match v with
  | .x u _ | .y u _ => u = t
  | _ => False

abbrev capSide (t : Fin 3) : Set Vertex := {v | capSideP t v}

instance (k : Nat) : DecidablePred (beforeStageP k) := by
  intro v
  cases v <;> unfold beforeStageP <;> infer_instance

instance (k : Nat) : DecidablePred (beforeStage k) := by
  intro v
  change Decidable (beforeStageP k v)
  infer_instance

instance (t : Fin 3) : DecidablePred (capSideP t) := by
  intro v
  unfold capSideP OnC4
  cases v <;> infer_instance

instance (t : Fin 3) : DecidablePred (capSide t) := by
  intro v
  change Decidable (capSideP t v)
  infer_instance

abbrev V2 := ↑(beforeStage 2)
abbrev G2 : SimpleGraph V2 := graph.induce (beforeStage 2)

instance : DecidableRel G2.Adj := by
  intro u v
  change Decidable (graph.Adj u.1 v.1)
  infer_instance

abbrev left1 : Set V2 := {v | v.1 ∈ beforeStage 1}
abbrev right1 : Set V2 := {v | v.1 ∈ capSide 1}

instance : DecidablePred left1 := by
  intro v
  change Decidable (beforeStageP 1 v.1)
  infer_instance

instance : DecidablePred right1 := by
  intro v
  change Decidable (capSideP 1 v.1)
  infer_instance

abbrev V1 := ↑left1
abbrev G1 : SimpleGraph V1 := G2.induce left1

instance : DecidableRel G1.Adj := by
  intro u v
  change Decidable (graph.Adj u.1.1 v.1.1)
  infer_instance

abbrev left0 : Set V1 := {v | v.1.1 ∈ beforeStage 0}
abbrev right0 : Set V1 := {v | v.1.1 ∈ capSide 0}

instance : DecidablePred left0 := by
  intro v
  change Decidable (beforeStageP 0 v.1.1)
  infer_instance

instance : DecidablePred right0 := by
  intro v
  change Decidable (capSideP 0 v.1.1)
  infer_instance

abbrev V0 := ↑left0
abbrev G0 : SimpleGraph V0 := G1.induce left0

instance : DecidableRel G0.Adj := by
  intro u v
  change Decidable (graph.Adj u.1.1.1 v.1.1.1)
  infer_instance

set_option maxHeartbeats 3000000 in
theorem raw_no_cross (t : Fin 3) {u v : Vertex}
    (hlu : beforeStageP t.1 u) (hnru : ¬ capSideP t u)
    (hrv : capSideP t v) (hnlv : ¬ beforeStageP t.1 v) : ¬ graph.Adj u v := by
  intro huv
  cases u with
  | a i =>
    cases v with
    | a j => fin_cases t <;> fin_cases i <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | b j => fin_cases t <;> fin_cases i <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | x tv r => fin_cases t <;> fin_cases i <;> fin_cases tv <;> fin_cases r <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | y tv j => fin_cases t <;> fin_cases i <;> fin_cases tv <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
  | b i =>
    cases v with
    | a j => fin_cases t <;> fin_cases i <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | b j => fin_cases t <;> fin_cases i <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | x tv r => fin_cases t <;> fin_cases i <;> fin_cases tv <;> fin_cases r <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | y tv j => fin_cases t <;> fin_cases i <;> fin_cases tv <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
  | x tu ru =>
    cases v with
    | a j => fin_cases t <;> fin_cases tu <;> fin_cases ru <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | b j => fin_cases t <;> fin_cases tu <;> fin_cases ru <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | x tv rv => fin_cases t <;> fin_cases tu <;> fin_cases ru <;> fin_cases tv <;> fin_cases rv <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | y tv j => fin_cases t <;> fin_cases tu <;> fin_cases ru <;> fin_cases tv <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
  | y tu ju =>
    cases v with
    | a j => fin_cases t <;> fin_cases tu <;> fin_cases ju <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | b j => fin_cases t <;> fin_cases tu <;> fin_cases ju <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | x tv rv => fin_cases t <;> fin_cases tu <;> fin_cases ju <;> fin_cases tv <;> fin_cases rv <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]
    | y tv j => fin_cases t <;> fin_cases tu <;> fin_cases ju <;> fin_cases tv <;> fin_cases j <;> simp_all [capSideP, OnC4, graph, baseAdj, boundary]

set_option maxHeartbeats 2000000 in
abbrev split2 : ExactC4Split graph where
  left := beforeStage 2
  right := capSide 2
  v0 := boundary 2 0
  v1 := boundary 2 1
  v2 := boundary 2 2
  v3 := boundary 2 3
  h01 := by native_decide
  h12 := by native_decide
  h23 := by native_decide
  h30 := by native_decide
  h02 := by native_decide
  h13 := by native_decide
  h01_ne := by native_decide
  h02_ne := by native_decide
  h03_ne := by native_decide
  h12_ne := by native_decide
  h13_ne := by native_decide
  h23_ne := by native_decide
  cover := by
    intro v
    change beforeStageP 2 v ∨ capSideP 2 v
    cases v with
    | a i => simp [beforeStage, beforeStageP]
    | b i => simp [beforeStage, beforeStageP]
    | x t r => fin_cases t <;> simp [beforeStage, beforeStageP, capSide, capSideP]
    | y t j => fin_cases t <;> simp [beforeStage, beforeStageP, capSide, capSideP]
  intersection := by
    intro v hl hr
    change beforeStageP 2 v at hl
    change capSideP 2 v at hr
    cases v with
    | a i => fin_cases i <;> simp_all [beforeStage, beforeStageP, capSide, capSideP,
        OnC4, boundary]
    | b i => fin_cases i <;> simp_all [beforeStage, beforeStageP, capSide, capSideP,
        OnC4, boundary]
    | x t r => fin_cases t <;> simp_all [beforeStage, beforeStageP, capSide, capSideP]
    | y t j => fin_cases t <;> simp_all [beforeStage, beforeStageP, capSide, capSideP]
  interface_left := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  interface_right := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  no_cross := by
    intro u v hlu hnru hrv hnlv huv
    exact raw_no_cross 2 hlu hnru hrv hnlv huv
  left₀ := .a 0
  left₁ := .a 1
  right₀ := .x 2 0
  right₁ := .x 2 1
  left₀_only := by native_decide
  left₁_only := by native_decide
  right₀_only := by native_decide
  right₁_only := by native_decide
  left_ne := by native_decide
  right_ne := by native_decide

abbrev split1 : ExactC4Split G2 where
  left := left1
  right := right1
  v0 := ⟨boundary 1 0, by native_decide⟩
  v1 := ⟨boundary 1 1, by native_decide⟩
  v2 := ⟨boundary 1 2, by native_decide⟩
  v3 := ⟨boundary 1 3, by native_decide⟩
  h01 := by native_decide
  h12 := by native_decide
  h23 := by native_decide
  h30 := by native_decide
  h02 := by native_decide
  h13 := by native_decide
  h01_ne := by native_decide
  h02_ne := by native_decide
  h03_ne := by native_decide
  h12_ne := by native_decide
  h13_ne := by native_decide
  h23_ne := by native_decide
  cover := by
    intro v
    rcases v with ⟨v, hv⟩
    change beforeStageP 2 v at hv
    change beforeStageP 1 v ∨ capSideP 1 v
    cases v with
    | a i => simp [beforeStageP]
    | b i => simp [beforeStageP]
    | x t r => fin_cases t <;> simp_all [beforeStageP, capSideP]
    | y t j => fin_cases t <;> simp_all [beforeStageP, capSideP]
  intersection := by
    intro v hl hr
    rcases v with ⟨v, hv⟩
    change beforeStageP 1 v at hl
    change capSideP 1 v at hr
    have hbase : OnC4 (boundary 1 0) (boundary 1 1) (boundary 1 2) (boundary 1 3) v := by
      cases v with
      | a i => fin_cases i <;> simp_all [beforeStageP, capSideP, OnC4, boundary]
      | b i => fin_cases i <;> simp_all [beforeStageP, capSideP, OnC4, boundary]
      | x t r => fin_cases t <;> simp_all [beforeStageP, capSideP]
      | y t j => fin_cases t <;> simp_all [beforeStageP, capSideP]
    rcases hbase with rfl | rfl | rfl | rfl <;> simp [OnC4]
  interface_left := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  interface_right := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  no_cross := by
    intro u v hlu hnru hrv hnlv huv
    exact raw_no_cross 1 hlu hnru hrv hnlv huv
  left₀ := ⟨.a 0, by native_decide⟩
  left₁ := ⟨.a 1, by native_decide⟩
  right₀ := ⟨.x 1 0, by native_decide⟩
  right₁ := ⟨.x 1 1, by native_decide⟩
  left₀_only := by native_decide
  left₁_only := by native_decide
  right₀_only := by native_decide
  right₁_only := by native_decide
  left_ne := by native_decide
  right_ne := by native_decide

abbrev split0 : ExactC4Split G1 where
  left := left0
  right := right0
  v0 := ⟨⟨boundary 0 0, by native_decide⟩, by native_decide⟩
  v1 := ⟨⟨boundary 0 1, by native_decide⟩, by native_decide⟩
  v2 := ⟨⟨boundary 0 2, by native_decide⟩, by native_decide⟩
  v3 := ⟨⟨boundary 0 3, by native_decide⟩, by native_decide⟩
  h01 := by native_decide
  h12 := by native_decide
  h23 := by native_decide
  h30 := by native_decide
  h02 := by native_decide
  h13 := by native_decide
  h01_ne := by native_decide
  h02_ne := by native_decide
  h03_ne := by native_decide
  h12_ne := by native_decide
  h13_ne := by native_decide
  h23_ne := by native_decide
  cover := by
    intro v
    rcases v with ⟨⟨v, hv2⟩, hv1⟩
    change beforeStageP 1 v at hv1
    change beforeStageP 0 v ∨ capSideP 0 v
    cases v with
    | a i => simp [beforeStageP]
    | b i => simp [beforeStageP]
    | x t r => fin_cases t <;> simp_all [beforeStageP, capSideP]
    | y t j => fin_cases t <;> simp_all [beforeStageP, capSideP]
  intersection := by
    intro v hl hr
    rcases v with ⟨⟨v, hv2⟩, hv1⟩
    change beforeStageP 0 v at hl
    change capSideP 0 v at hr
    have hbase : OnC4 (boundary 0 0) (boundary 0 1) (boundary 0 2) (boundary 0 3) v := by
      cases v with
      | a i => fin_cases i <;> simp_all [beforeStageP, capSideP, OnC4, boundary]
      | b i => fin_cases i <;> simp_all [beforeStageP, capSideP, OnC4, boundary]
      | x t r => fin_cases t <;> simp_all [beforeStageP, capSideP]
      | y t j => fin_cases t <;> simp_all [beforeStageP, capSideP]
    rcases hbase with rfl | rfl | rfl | rfl <;> simp [OnC4]
  interface_left := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  interface_right := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl <;> native_decide
  no_cross := by
    intro u v hlu hnru hrv hnlv huv
    exact raw_no_cross 0 hlu hnru hrv hnlv huv
  left₀ := ⟨⟨.a 4, by native_decide⟩, by native_decide⟩
  left₁ := ⟨⟨.a 5, by native_decide⟩, by native_decide⟩
  right₀ := ⟨⟨.x 0 0, by native_decide⟩, by native_decide⟩
  right₁ := ⟨⟨.x 0 1, by native_decide⟩, by native_decide⟩
  left₀_only := by native_decide
  left₁_only := by native_decide
  right₀_only := by native_decide
  right₁_only := by native_decide
  left_ne := by native_decide
  right_ne := by native_decide

theorem graph_legal_implies_G2_legal (h : LegalSystem graph) : LegalSystem G2 :=
  split2.legalSystem_restrict_left h

theorem G2_legal_implies_G1_legal (h : LegalSystem G2) : LegalSystem G1 :=
  split1.legalSystem_restrict_left h

theorem G1_legal_implies_G0_legal (h : LegalSystem G1) : LegalSystem G0 :=
  split0.legalSystem_restrict_left h

theorem card_G0_vertices : Fintype.card V0 = 12 := by native_decide

theorem card_G0_edges : G0.edgeFinset.card = 18 := by native_decide

theorem G0_noLegalSystem : ¬ LegalSystem G0 := by
  intro h
  have hc := legalSystem_curvature_obstruction G0 h
  rw [card_G0_vertices, card_G0_edges] at hc
  omega

theorem graph_noLegalSystem : ¬ LegalSystem graph := by
  intro h
  exact G0_noLegalSystem (G1_legal_implies_G0_legal
    (G2_legal_implies_G1_legal (graph_legal_implies_G2_legal h)))

end JNW.Vertex
