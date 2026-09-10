import JNWLegalSystem.Basic

namespace JNW

variable {V : Type*} [Fintype V] [DecidableEq V]

def basisState (v : V) : State V := fun w ↦ if w = v then 1 else 0

lemma one_add_one : (1 + 1 : ZMod 2) = 0 := by native_decide

lemma zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hlt := z.val_lt
  have h : z.val = 0 ∨ z.val = 1 := by omega
  rcases h with h | h
  · left
    apply ZMod.val_injective
    simpa [ZMod.val_one] using h
  · right
    apply ZMod.val_injective
    simpa [ZMod.val_one] using h

def flipCoeff (v : V) : State V ≃ State V where
  toFun c := c + basisState v
  invFun c := c + basisState v
  left_inv c := by
    funext w
    by_cases h : w = v <;> simp [basisState, h, one_add_one, add_assoc]
  right_inv c := by
    funext w
    by_cases h : w = v <;> simp [basisState, h, one_add_one, add_assoc]

theorem orbit_flip_self (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) (v : V) (hm : MoveAt G v (moves v)) :
    orbitState moves start (flipCoeff v coeff) v =
      orbitState moves start coeff v + 1 := by
  simp [orbitState, flipCoeff, basisState, add_mul, Finset.sum_add_distrib, hm.1,
    add_assoc]

theorem orbit_flip_neighbor (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) (v w : V) (hm : MoveAt G v (moves v)) (hvw : G.Adj v w) :
    orbitState moves start (flipCoeff v coeff) w = orbitState moves start coeff w := by
  simp [orbitState, flipCoeff, basisState, add_mul, Finset.sum_add_distrib, hm.2 w hvw]

def Occupied (moves : V → State V) (start : State V) (v : V) (coeff : State V) : Prop :=
  orbitState moves start coeff v ≠ 0

instance (moves : V → State V) (start : State V) (v : V) (coeff : State V) :
    Decidable (Occupied moves start v coeff) := by
  unfold Occupied
  infer_instance

theorem occupied_flip_self_iff (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) (v : V) (hm : MoveAt G v (moves v)) :
    Occupied moves start v (flipCoeff v coeff) ↔ ¬ Occupied moves start v coeff := by
  rw [Occupied, Occupied, orbit_flip_self G moves start coeff v hm]
  generalize orbitState moves start coeff v = z
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · norm_num
  · simp [one_add_one]

theorem occupied_flip_neighbor_iff (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) (v w : V) (hm : MoveAt G v (moves v)) (hvw : G.Adj v w) :
    Occupied moves start w (flipCoeff v coeff) ↔ Occupied moves start w coeff := by
  simp [Occupied, orbit_flip_neighbor G moves start coeff v w hm hvw]

def occupiedFlipEquiv (G : SimpleGraph V) (moves : V → State V)
    (start : State V) (v : V) (hm : MoveAt G v (moves v)) :
    {c : State V // Occupied moves start v c} ≃
      {c : State V // ¬ Occupied moves start v c} where
  toFun c := ⟨flipCoeff v c.1, by
    intro h
    exact (occupied_flip_self_iff G moves start c.1 v hm).mp h c.2⟩
  invFun c := ⟨flipCoeff v c.1,
    (occupied_flip_self_iff G moves start c.1 v hm).mpr c.2⟩
  left_inv c := by
    apply Subtype.ext
    exact (flipCoeff v).left_inv c.1
  right_inv c := by
    apply Subtype.ext
    exact (flipCoeff v).left_inv c.1

theorem two_mul_occupied_card (G : SimpleGraph V) (moves : V → State V)
    (start : State V) (v : V) (hm : MoveAt G v (moves v)) :
    2 * Fintype.card {c : State V // Occupied moves start v c} =
      Fintype.card (State V) := by
  have heq := Fintype.card_congr (occupiedFlipEquiv G moves start v hm)
  have hsum := Fintype.card_congr (Equiv.sumCompl (Occupied moves start v))
  simp only [Fintype.card_sum] at hsum
  omega

def edgeFlipEquiv (G : SimpleGraph V) (moves : V → State V)
    (start : State V) (u v : V) (huv : G.Adj u v)
    (hm : ∀ w, MoveAt G w (moves w)) :
    {c : State V // Occupied moves start u c ∧ Occupied moves start v c} ≃
      {c : State V // Occupied moves start u c ∧ ¬ Occupied moves start v c} where
  toFun c := ⟨flipCoeff v c.1, by
    constructor
    · exact (occupied_flip_neighbor_iff G moves start c.1 v u (hm v) huv.symm).mpr c.2.1
    · intro h
      exact (occupied_flip_self_iff G moves start c.1 v (hm v)).mp h c.2.2⟩
  invFun c := ⟨flipCoeff v c.1, by
    constructor
    · exact (occupied_flip_neighbor_iff G moves start c.1 v u (hm v) huv.symm).mpr c.2.1
    · exact (occupied_flip_self_iff G moves start c.1 v (hm v)).mpr c.2.2⟩
  left_inv c := by
    apply Subtype.ext
    exact (flipCoeff v).left_inv c.1
  right_inv c := by
    apply Subtype.ext
    exact (flipCoeff v).left_inv c.1

def splitSecondEquiv (P Q : State V → Prop) [DecidablePred Q] :
    {c : State V // P c ∧ Q c} ⊕ {c : State V // P c ∧ ¬ Q c} ≃
      {c : State V // P c} where
  toFun
    | Sum.inl c => ⟨c.1, c.2.1⟩
    | Sum.inr c => ⟨c.1, c.2.1⟩
  invFun c := if h : Q c.1 then Sum.inl ⟨c.1, c.2, h⟩ else Sum.inr ⟨c.1, c.2, h⟩
  left_inv c := by
    cases c with
    | inl c => simp [c.2.2]
    | inr c => simp [c.2.2]
  right_inv c := by
    apply Subtype.ext
    by_cases h : Q c.1 <;> simp [h]

theorem four_mul_edge_occupied_card (G : SimpleGraph V) (moves : V → State V)
    (start : State V) (u v : V) (huv : G.Adj u v)
    (hm : ∀ w, MoveAt G w (moves w)) :
    4 * Fintype.card
        {c : State V // Occupied moves start u c ∧ Occupied moves start v c} =
      Fintype.card (State V) := by
  have houter := two_mul_occupied_card G moves start u (hm u)
  have hsplit := Fintype.card_congr
    (splitSecondEquiv (Occupied moves start u) (Occupied moves start v))
  have hedge := Fintype.card_congr (edgeFlipEquiv G moves start u v huv hm)
  simp only [Fintype.card_sum] at hsplit
  omega

def arcCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start coeff : State V) : Nat :=
  Fintype.card {p : V × V //
    G.Adj p.1 p.2 ∧ Occupied moves start p.1 coeff ∧ Occupied moves start p.2 coeff}

def occupiedArcEquiv (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) :
    {p : ({v : V // Occupied moves start v coeff} ×
        {v : V // Occupied moves start v coeff}) //
      (G.induce {v | Occupied moves start v coeff}).Adj p.1 p.2} ≃
    {p : V × V //
      G.Adj p.1 p.2 ∧ Occupied moves start p.1 coeff ∧ Occupied moves start p.2 coeff} where
  toFun p := ⟨(p.1.1.1, p.1.2.1), p.2, p.1.1.2, p.1.2.2⟩
  invFun p := ⟨(⟨p.1.1, p.2.2.1⟩, ⟨p.1.2, p.2.2.2⟩), p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem arcCount_eq_twice_induced_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start coeff : State V) :
    arcCount G moves start coeff =
      2 * (G.induce {v | Occupied moves start v coeff}).edgeFinset.card := by
  calc
    arcCount G moves start coeff =
        Fintype.card {p : ({v : V // Occupied moves start v coeff} ×
            {v : V // Occupied moves start v coeff}) //
          (G.induce {v | Occupied moves start v coeff}).Adj p.1 p.2} :=
      Fintype.card_congr (occupiedArcEquiv G moves start coeff).symm
    _ = ((Finset.univ.filter fun p :
          ({v : V // Occupied moves start v coeff} ×
            {v : V // Occupied moves start v coeff}) ↦
          (G.induce {v | Occupied moves start v coeff}).Adj p.1 p.2).card) :=
      Fintype.card_subtype _
    _ = 2 * (G.induce {v | Occupied moves start v coeff}).edgeFinset.card :=
      (G.induce {v | Occupied moves start v coeff}).two_mul_card_edgeFinset.symm

theorem sum_indicator_eq_card_subtype {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] :
    (∑ x : A, if P x then 1 else 0) = Fintype.card {x : A // P x} := by
  rw [Fintype.card_subtype]
  simp

theorem support_orbit_card_eq_sum_indicator (moves : V → State V)
    (start coeff : State V) :
    (support (orbitState moves start coeff)).card =
      ∑ v : V, if Occupied moves start v coeff then 1 else 0 := by
  change (Finset.univ.filter fun v ↦ orbitState moves start coeff v ≠ 0).card = _
  rw [sum_indicator_eq_card_subtype]
  rw [Fintype.card_subtype]
  rfl

def totalVertexOccupancy (moves : V → State V) (start : State V) : Nat :=
  ∑ coeff : State V, (support (orbitState moves start coeff)).card

theorem two_mul_totalVertexOccupancy (G : SimpleGraph V) (moves : V → State V)
    (start : State V) (hm : ∀ v, MoveAt G v (moves v)) :
    2 * totalVertexOccupancy moves start =
      Fintype.card V * Fintype.card (State V) := by
  unfold totalVertexOccupancy
  simp_rw [support_orbit_card_eq_sum_indicator]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  calc
    (∑ v : V, 2 * ∑ coeff : State V,
        if Occupied moves start v coeff then 1 else 0) =
        ∑ v : V, Fintype.card (State V) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [sum_indicator_eq_card_subtype]
      exact two_mul_occupied_card G moves start v (hm v)
    _ = Fintype.card V * Fintype.card (State V) := by simp

theorem arcCount_eq_sum_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start coeff : State V) :
    arcCount G moves start coeff =
      ∑ p : V × V,
        if G.Adj p.1 p.2 ∧ Occupied moves start p.1 coeff ∧
          Occupied moves start p.2 coeff then 1 else 0 := by
  unfold arcCount
  rw [Fintype.card_subtype]
  simp

def totalArcOccupancy (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start : State V) : Nat :=
  ∑ coeff : State V, arcCount G moves start coeff

theorem four_mul_totalArcOccupancy (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start : State V)
    (hm : ∀ v, MoveAt G v (moves v)) :
    4 * totalArcOccupancy G moves start =
      (2 * G.edgeFinset.card) * Fintype.card (State V) := by
  unfold totalArcOccupancy
  simp_rw [arcCount_eq_sum_indicator]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  calc
    (∑ p : V × V, 4 *
          ∑ coeff : State V,
            if G.Adj p.1 p.2 ∧ Occupied moves start p.1 coeff ∧
              Occupied moves start p.2 coeff then (1 : Nat) else 0) =
        ∑ p : V × V, if G.Adj p.1 p.2 then Fintype.card (State V) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : G.Adj p.1 p.2
      · simp only [hp, true_and, if_true]
        rw [sum_indicator_eq_card_subtype]
        exact four_mul_edge_occupied_card G moves start p.1 p.2 hp hm
      · simp [hp]
    _ = (2 * G.edgeFinset.card) * Fintype.card (State V) := by
      rw [G.two_mul_card_edgeFinset]
      rw [← Finset.sum_filter]
      simp

theorem legalState_arc_inequality (G : SimpleGraph V) [DecidableRel G.Adj]
    (moves : V → State V) (start coeff : State V)
    (hlegal : LegalState G (orbitState moves start coeff)) :
    2 * (support (orbitState moves start coeff)).card ≤
      arcCount G moves start coeff + 2 := by
  have hconn := hlegal.1.card_vert_le_card_edgeSet_add_one
  have hedges : Nat.card (G.induce {v | orbitState moves start coeff v ≠ 0}).edgeSet =
      (G.induce {v | orbitState moves start coeff v ≠ 0}).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rw [hedges] at hconn
  have hsupp : Nat.card {v : V | orbitState moves start coeff v ≠ 0} =
      (support (orbitState moves start coeff)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [support]
  have harc := arcCount_eq_twice_induced_edges G moves start coeff
  unfold Occupied at harc
  omega

theorem legalSystem_curvature_obstruction (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : LegalSystem G) :
    2 * Fintype.card V ≤ G.edgeFinset.card + 4 := by
  rcases h with ⟨moves, start, hm, hlegal⟩
  have hsum : 2 * totalVertexOccupancy moves start ≤
      totalArcOccupancy G moves start + 2 * Fintype.card (State V) := by
    calc
      2 * totalVertexOccupancy moves start =
          ∑ coeff : State V, 2 * (support (orbitState moves start coeff)).card := by
        simp [totalVertexOccupancy, Finset.mul_sum]
      _ ≤ ∑ coeff : State V, (arcCount G moves start coeff + 2) :=
        Finset.sum_le_sum fun coeff _ ↦
          legalState_arc_inequality G moves start coeff (hlegal coeff)
      _ = totalArcOccupancy G moves start + 2 * Fintype.card (State V) := by
        simp [totalArcOccupancy, Finset.sum_add_distrib, mul_comm]
  have hv := two_mul_totalVertexOccupancy G moves start hm
  have he := four_mul_totalArcOccupancy G moves start hm
  have hN : 0 < Fintype.card (State V) := Fintype.card_pos
  nlinarith

end JNW
