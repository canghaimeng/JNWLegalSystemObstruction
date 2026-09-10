import JNWLegalSystem.Averaging

namespace JNW

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zmod2_ne_zero_iff_eq_one (z : ZMod 2) : z ≠ 0 ↔ z = 1 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> simp

theorem zmod2_add_one_ne_zero_iff (z : ZMod 2) : z + 1 ≠ 0 ↔ z = 0 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · simp
  · simp [one_add_one]

theorem zmod2_add_one_eq_zero_iff (z : ZMod 2) : z + 1 = 0 ↔ z ≠ 0 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · simp
  · simp [one_add_one]

theorem zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · simp
  · exact one_add_one

theorem zmod2_solve_add_eq (a b c : ZMod 2) (h : a + b = c) : b = a + c := by
  calc
    b = 0 + b := by simp
    _ = (a + a) + b := by rw [zmod2_add_self]
    _ = a + (a + b) := by simp [add_assoc]
    _ = a + c := by rw [h]

theorem legalState_compl (G : SimpleGraph V) (s : State V) (h : LegalState G s) :
    LegalState G (complState s) := by
  unfold LegalState at h ⊢
  unfold complState
  have hset₁ : {v : V | s v + 1 ≠ 0} = {v : V | s v = 0} := by
    ext v
    exact zmod2_add_one_ne_zero_iff (s v)
  have hset₂ : {v : V | s v + 1 = 0} = {v : V | s v ≠ 0} := by
    ext v
    exact zmod2_add_one_eq_zero_iff (s v)
  constructor
  · rw [hset₁]
    exact h.2
  · rw [hset₂]
    exact h.1

theorem orbit_compl_start (moves : V → State V) (start coeff : State V) :
    orbitState moves (complState start) coeff =
      complState (orbitState moves start coeff) := by
  funext x
  simp [orbitState, complState, add_assoc, add_comm, add_left_comm]

def restrictState (P : Set V) (s : State V) : State P :=
  fun v ↦ s v.1

def restrictMoves (P : Set V) (moves : V → State V) : P → State P :=
  fun v w ↦ moves v.1 w.1

def extendCoeff (P : Set V) [DecidablePred (· ∈ P)]
    (coeff : State P) : State V :=
  fun v ↦ if h : v ∈ P then coeff ⟨v, h⟩ else 0

theorem orbit_restrict_eq (P : Set V) [DecidablePred (· ∈ P)]
    (moves : V → State V) (start : State V) (coeff : State P) :
    orbitState (restrictMoves P moves) (restrictState P start) coeff =
      restrictState P (orbitState moves start (extendCoeff P coeff)) := by
  funext x
  unfold orbitState restrictMoves restrictState
  congr 1
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun v ↦ v ∈ P)
    (fun v ↦ extendCoeff P coeff v * moves v x.1)
  calc
    ∑ v, coeff v * moves v.1 x.1 =
        ∑ v : {v : V // v ∈ P}, extendCoeff P coeff v.1 * moves v.1 x.1 := by
      apply Finset.sum_congr rfl
      intro v _
      change coeff v * moves v.1 x.1 =
        (if h : v.1 ∈ P then coeff ⟨v.1, h⟩ else 0) * moves v.1 x.1
      rw [dif_pos v.2]
    _ = (∑ v : {v : V // v ∈ P}, extendCoeff P coeff v.1 * moves v.1 x.1) +
        ∑ v : {v : V // v ∉ P}, extendCoeff P coeff v.1 * moves v.1 x.1 := by
      have hz : (∑ v : {v : V // v ∉ P},
          extendCoeff P coeff v.1 * moves v.1 x.1) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [extendCoeff, v.2]
      rw [hz, add_zero]
    _ = ∑ v : V, extendCoeff P coeff v * moves v x.1 := hsum

def induceRestrictIso (G : SimpleGraph V) (P : Set V) (Q : V → Prop) :
    (G.induce P).induce {v | Q v.1} ≃g G.induce {v | P v ∧ Q v} where
  toFun v := ⟨v.1.1, v.1.2, v.2⟩
  invFun v := ⟨⟨v.1, v.2.1⟩, v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem orbit_flip_state (moves : V → State V) (start coeff : State V) (v : V) :
    orbitState moves start (flipCoeff v coeff) =
      xorState (orbitState moves start coeff) (moves v) := by
  funext x
  simp [orbitState, flipCoeff, basisState, xorState, add_mul, Finset.sum_add_distrib,
    add_assoc]

theorem legal_orbit_after_move (G : SimpleGraph V) (moves : V → State V)
    (start coeff : State V) (hlegal : ∀ c, LegalState G (orbitState moves start c)) (v : V) :
    LegalState G (xorState (orbitState moves start coeff) (moves v)) := by
  rw [← orbit_flip_state]
  exact hlegal _

theorem isolated_occupied_eq (G : SimpleGraph V) (s : State V) (hlegal : LegalState G s)
    (w : V) (hw : s w ≠ 0) (hiso : ∀ z, G.Adj w z → s z = 0) :
    ∀ z, s z ≠ 0 → z = w := by
  intro z hz
  by_contra hzw
  have hsubne : (⟨w, hw⟩ : {x : V // s x ≠ 0}) ≠ ⟨z, hz⟩ := by
    intro h
    exact hzw (congrArg Subtype.val h).symm
  have hreach := hlegal.1.preconnected ⟨w, hw⟩ ⟨z, hz⟩
  obtain ⟨q, hq⟩ := hreach.nonempty_neighborSet_left hsubne
  exact q.2 (hiso q.1 hq)

theorem state_eq_basis_of_isolated (G : SimpleGraph V) (s : State V)
    (hlegal : LegalState G s) (w : V) (hw : s w ≠ 0)
    (hiso : ∀ z, G.Adj w z → s z = 0) : s = basisState w := by
  funext z
  by_cases hz : s z = 0
  · by_cases hzw : z = w
    · subst z
      exact (hw hz).elim
    · simp [basisState, hzw, hz]
  · have hzw := isolated_occupied_eq G s hlegal w hw hiso z hz
    subst z
    simp [basisState, (zmod2_ne_zero_iff_eq_one _).mp hw]

theorem no_singleton_orbit_with_two_nonneighbors (G : SimpleGraph V)
    (moves : V → State V) (start coeff : State V)
    (hm : ∀ v, MoveAt G v (moves v))
    (hlegal : ∀ c, LegalState G (orbitState moves start c))
    (x w z : V) (hxw : x ≠ w) (hxz : x ≠ z) (hwz : w ≠ z)
    (hnxw : ¬ G.Adj x w) (hnxz : ¬ G.Adj x z)
    (hs : orbitState moves start coeff = basisState x) : False := by
  let s := orbitState moves start coeff
  let cw := flipCoeff w coeff
  let cz := flipCoeff z coeff
  have hcwLegal : LegalState G (orbitState moves start cw) := hlegal cw
  have hczLegal : LegalState G (orbitState moves start cz) := hlegal cz
  have hcw_w : orbitState moves start cw w ≠ 0 := by
    rw [show cw = flipCoeff w coeff by rfl, orbit_flip_self G moves start coeff w (hm w), hs]
    simp [basisState, hxw.symm]
  have hcw_iso : ∀ q, G.Adj w q → orbitState moves start cw q = 0 := by
    intro q hwq
    rw [show cw = flipCoeff w coeff by rfl,
      orbit_flip_neighbor G moves start coeff w q (hm w) hwq, hs]
    have hqx : q ≠ x := by
      intro h
      subst q
      exact hnxw hwq.symm
    simp [basisState, hqx]
  have hcwBasis : orbitState moves start cw = basisState w :=
    state_eq_basis_of_isolated G _ hcwLegal w hcw_w hcw_iso
  have hcz_z : orbitState moves start cz z ≠ 0 := by
    rw [show cz = flipCoeff z coeff by rfl, orbit_flip_self G moves start coeff z (hm z), hs]
    simp [basisState, hxz.symm]
  have hcz_iso : ∀ q, G.Adj z q → orbitState moves start cz q = 0 := by
    intro q hzq
    rw [show cz = flipCoeff z coeff by rfl,
      orbit_flip_neighbor G moves start coeff z q (hm z) hzq, hs]
    have hqx : q ≠ x := by
      intro h
      subst q
      exact hnxz hzq.symm
    simp [basisState, hqx]
  have hczBasis : orbitState moves start cz = basisState z :=
    state_eq_basis_of_isolated G _ hczLegal z hcz_z hcz_iso
  have hmoveW : moves w = xorState (basisState x) (basisState w) := by
    funext q
    have hflip := congrFun (orbit_flip_state moves start coeff w) q
    rw [hcwBasis, hs] at hflip
    exact zmod2_solve_add_eq _ _ _ hflip.symm
  have hmoveZ : moves z = xorState (basisState x) (basisState z) := by
    funext q
    have hflip := congrFun (orbit_flip_state moves start coeff z) q
    rw [hczBasis, hs] at hflip
    exact zmod2_solve_add_eq _ _ _ hflip.symm
  let cwz := flipCoeff z cw
  have hcwzLegal : LegalState G (orbitState moves start cwz) := hlegal cwz
  have hcwzEq : orbitState moves start cwz =
      xorState (xorState (basisState x) (basisState w)) (basisState z) := by
    rw [show cwz = flipCoeff z cw by rfl, orbit_flip_state, hcwBasis, hmoveZ]
    funext q
    simp [xorState, zmod2_add_self, add_assoc, add_left_comm, add_comm]
  have hcwz_x : orbitState moves start cwz x ≠ 0 := by
    rw [hcwzEq]
    simp [xorState, basisState, hxw, hxz]
  have hcwz_iso : ∀ q, G.Adj x q → orbitState moves start cwz q = 0 := by
    intro q hxq
    rw [hcwzEq]
    have hqx : q ≠ x := by
      intro h
      subst q
      exact G.loopless.irrefl x hxq
    have hqw : q ≠ w := by
      intro h
      subst q
      exact hnxw hxq
    have hqz : q ≠ z := by
      intro h
      subst q
      exact hnxz hxq
    simp [xorState, basisState, hqx, hqw, hqz]
  have hOnlyX := isolated_occupied_eq G _ hcwzLegal x hcwz_x hcwz_iso
  have hcwz_w : orbitState moves start cwz w ≠ 0 := by
    rw [hcwzEq]
    simp [xorState, basisState, hxw.symm, hwz]
  exact hxw (hOnlyX w hcwz_w).symm

theorem reachable_preserves (G : SimpleGraph V) (P : V → Prop)
    (hclosed : ∀ {u v}, P u → G.Adj u v → P v)
    {u v : V} (huv : G.Reachable u v) (hu : P u) : P v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact hu
  | tail hxy hyz ih => exact hclosed ih hyz

end JNW
