import JNWLegalSystem.OrbitLemmas

namespace JNW

variable {V : Type*} [Fintype V] [DecidableEq V]

def OnC4 (a b c d v : V) : Prop := v = a ∨ v = b ∨ v = c ∨ v = d

structure ExactC4Split (G : SimpleGraph V) where
  left : Set V
  right : Set V
  v0 : V
  v1 : V
  v2 : V
  v3 : V
  h01 : G.Adj v0 v1
  h12 : G.Adj v1 v2
  h23 : G.Adj v2 v3
  h30 : G.Adj v3 v0
  h02 : ¬ G.Adj v0 v2
  h13 : ¬ G.Adj v1 v3
  h01_ne : v0 ≠ v1
  h02_ne : v0 ≠ v2
  h03_ne : v0 ≠ v3
  h12_ne : v1 ≠ v2
  h13_ne : v1 ≠ v3
  h23_ne : v2 ≠ v3
  cover : ∀ v, left v ∨ right v
  intersection : ∀ v, left v → right v → OnC4 v0 v1 v2 v3 v
  interface_left : ∀ v, OnC4 v0 v1 v2 v3 v → left v
  interface_right : ∀ v, OnC4 v0 v1 v2 v3 v → right v
  no_cross : ∀ {u v}, left u → ¬ right u → right v → ¬ left v → ¬ G.Adj u v
  left₀ : V
  left₁ : V
  right₀ : V
  right₁ : V
  left₀_only : left left₀ ∧ ¬ right left₀
  left₁_only : left left₁ ∧ ¬ right left₁
  right₀_only : right right₀ ∧ ¬ left right₀
  right₁_only : right right₁ ∧ ¬ left right₁
  left_ne : left₀ ≠ left₁
  right_ne : right₀ ≠ right₁

namespace ExactC4Split

variable {G : SimpleGraph V} (S : ExactC4Split G)

theorem exists_clear_opposite_pair (moves : V → State V) (start coeff : State V)
    (hm : ∀ v, MoveAt G v (moves v))
    (p q r t : V)
    (hpr : G.Adj p r) (hpt : G.Adj p t)
    (hqr : G.Adj q r) (hqt : G.Adj q t)
    (hp : orbitState moves start coeff p ≠ 0)
    (hq : orbitState moves start coeff q ≠ 0)
    (hr : orbitState moves start coeff r = 0)
    (ht : orbitState moves start coeff t = 0) :
    ∃ coeff', orbitState moves start coeff' p = 0 ∧
      orbitState moves start coeff' q = 0 ∧
      orbitState moves start coeff' r = 0 ∧
      orbitState moves start coeff' t = 0 := by
  have hp1 := (zmod2_ne_zero_iff_eq_one _).mp hp
  have hq1 := (zmod2_ne_zero_iff_eq_one _).mp hq
  by_cases hpq0 : moves p q = 0
  · by_cases hqp0 : moves q p = 0
    · refine ⟨flipCoeff q (flipCoeff p coeff), ?_, ?_, ?_, ?_⟩
      · rw [orbit_flip_state]
        change orbitState moves start (flipCoeff p coeff) p + moves q p = 0
        rw [orbit_flip_self G moves start coeff p (hm p), hp1, hqp0, one_add_one]
        simp
      · rw [orbit_flip_self G moves start (flipCoeff p coeff) q (hm q)]
        rw [orbit_flip_state]
        change orbitState moves start coeff q + moves p q + 1 = 0
        rw [hq1, hpq0]
        simp [one_add_one]
      · rw [orbit_flip_neighbor G moves start (flipCoeff p coeff) q r (hm q) hqr]
        rw [orbit_flip_neighbor G moves start coeff p r (hm p) hpr, hr]
      · rw [orbit_flip_neighbor G moves start (flipCoeff p coeff) q t (hm q) hqt]
        rw [orbit_flip_neighbor G moves start coeff p t (hm p) hpt, ht]
    · have hqp1 := (zmod2_ne_zero_iff_eq_one _).mp hqp0
      refine ⟨flipCoeff q coeff, ?_, ?_, ?_, ?_⟩
      · rw [orbit_flip_state]
        change orbitState moves start coeff p + moves q p = 0
        rw [hp1, hqp1, one_add_one]
      · rw [orbit_flip_self G moves start coeff q (hm q), hq1, one_add_one]
      · rw [orbit_flip_neighbor G moves start coeff q r (hm q) hqr, hr]
      · rw [orbit_flip_neighbor G moves start coeff q t (hm q) hqt, ht]
  · have hpq1 := (zmod2_ne_zero_iff_eq_one _).mp hpq0
    refine ⟨flipCoeff p coeff, ?_, ?_, ?_, ?_⟩
    · rw [orbit_flip_self G moves start coeff p (hm p), hp1, one_add_one]
    · rw [orbit_flip_state]
      change orbitState moves start coeff q + moves p q = 0
      rw [hq1, hpq1, one_add_one]
    · rw [orbit_flip_neighbor G moves start coeff p r (hm p) hpr, hr]
    · rw [orbit_flip_neighbor G moves start coeff p t (hm p) hpt, ht]

theorem left_not_right_of_not_interface {v : V} (hl : S.left v)
    (hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 v) : ¬ S.right v := by
  intro hr
  exact hnc (S.intersection v hl hr)

theorem right_not_left_of_not_interface {v : V} (hr : S.right v)
    (hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 v) : ¬ S.left v := by
  intro hl
  exact hnc (S.intersection v hl hr)

theorem adjacent_forces_left {u v : V} (hlu : S.left u)
    (hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 u) (huv : G.Adj u v) : S.left v := by
  rcases S.cover v with hlv | hrv
  · exact hlv
  · by_contra hnlv
    exact S.no_cross hlu (S.left_not_right_of_not_interface hlu hnc) hrv hnlv huv

theorem adjacent_forces_right {u v : V} (hru : S.right u)
    (hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 u) (huv : G.Adj u v) : S.right v := by
  rcases S.cover v with hlv | hrv
  · by_contra hnrv
    exact S.no_cross hlv hnrv hru
      (S.right_not_left_of_not_interface hru hnc) huv.symm
  · exact hrv

theorem component_meets_interface (s : State V) (hlegal : LegalState G s)
    {x y : V} (hlx : S.left x) (hly : S.left y)
    (hx : s x ≠ 0) (hy : s y ≠ 0)
    (hxy : ¬ (G.induce {v | S.left v ∧ s v ≠ 0}).Reachable
      ⟨x, hlx, hx⟩ ⟨y, hly, hy⟩) :
    ∃ (q : V) (hc : OnC4 S.v0 S.v1 S.v2 S.v3 q) (hq : s q ≠ 0),
      (G.induce {v | S.left v ∧ s v ≠ 0}).Reachable
        ⟨x, hlx, hx⟩ ⟨q, S.interface_left q hc, hq⟩ := by
  by_contra hnone
  push_neg at hnone
  let H := G.induce {v | s v ≠ 0}
  let P : {v : V // s v ≠ 0} → Prop := fun q ↦
    ∃ hlq : S.left q.1,
      (G.induce {v | S.left v ∧ s v ≠ 0}).Reachable
        ⟨x, hlx, hx⟩ ⟨q.1, hlq, q.2⟩
  have hclosed : ∀ {u v}, P u → H.Adj u v → P v := by
    intro u v hu huv
    rcases hu with ⟨hlu, hreach⟩
    have hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 u.1 := by
      intro hcu
      exact hnone u.1 hcu u.2
        (by simpa using hreach)
    have hlv : S.left v.1 := S.adjacent_forces_left hlu hnc huv
    refine ⟨hlv, hreach.trans ?_⟩
    have hadj : (G.induce {v | S.left v ∧ s v ≠ 0}).Adj
        ⟨u.1, hlu, u.2⟩ ⟨v.1, hlv, v.2⟩ := by
      exact huv
    exact hadj.reachable
  have hglobal : H.Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
    hlegal.1.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  have hPy : P ⟨y, hy⟩ := reachable_preserves H P hclosed hglobal ⟨hlx, .rfl⟩
  exact hxy hPy.2

theorem c4_pattern_of_not_reachable (s : State V) {q r : V}
    (hqC : OnC4 S.v0 S.v1 S.v2 S.v3 q)
    (hrC : OnC4 S.v0 S.v1 S.v2 S.v3 r)
    (hq : s q ≠ 0) (hr : s r ≠ 0)
    (hnr : ¬ (G.induce {v | S.left v ∧ s v ≠ 0}).Reachable
      ⟨q, S.interface_left q hqC, hq⟩ ⟨r, S.interface_left r hrC, hr⟩) :
    (s S.v0 ≠ 0 ∧ s S.v2 ≠ 0 ∧ s S.v1 = 0 ∧ s S.v3 = 0) ∨
    (s S.v1 ≠ 0 ∧ s S.v3 ≠ 0 ∧ s S.v0 = 0 ∧ s S.v2 = 0) := by
  let H := G.induce {v | S.left v ∧ s v ≠ 0}
  have r01 (h0 : s S.v0 ≠ 0) (h1 : s S.v1 ≠ 0) :
      H.Reachable ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩
        ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩ := by
    have h : H.Adj ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩
        ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩ := by
      change G.Adj S.v0 S.v1
      exact S.h01
    exact h.reachable
  have r12 (h1 : s S.v1 ≠ 0) (h2 : s S.v2 ≠ 0) :
      H.Reachable ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩
        ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩ := by
    have h : H.Adj ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩
        ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩ := by
      change G.Adj S.v1 S.v2
      exact S.h12
    exact h.reachable
  have r23 (h2 : s S.v2 ≠ 0) (h3 : s S.v3 ≠ 0) :
      H.Reachable ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩
        ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩ := by
    have h : H.Adj ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩
        ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩ := by
      change G.Adj S.v2 S.v3
      exact S.h23
    exact h.reachable
  have r30 (h3 : s S.v3 ≠ 0) (h0 : s S.v0 ≠ 0) :
      H.Reachable ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩
        ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩ := by
    have h : H.Adj ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩
        ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩ := by
      change G.Adj S.v3 S.v0
      exact S.h30
    exact h.reachable
  have r02a (h0 : s S.v0 ≠ 0) (h1 : s S.v1 ≠ 0) (h2 : s S.v2 ≠ 0) :
      H.Reachable ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩
        ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩ :=
    (r01 h0 h1).trans (r12 h1 h2)
  have r02b (h0 : s S.v0 ≠ 0) (h3 : s S.v3 ≠ 0) (h2 : s S.v2 ≠ 0) :
      H.Reachable ⟨S.v0, S.interface_left _ (by simp [OnC4]), h0⟩
        ⟨S.v2, S.interface_left _ (by simp [OnC4]), h2⟩ :=
    (r30 h3 h0).symm.trans (r23 h2 h3).symm
  have r13a (h1 : s S.v1 ≠ 0) (h0 : s S.v0 ≠ 0) (h3 : s S.v3 ≠ 0) :
      H.Reachable ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩
        ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩ :=
    (r01 h0 h1).symm.trans (r30 h3 h0).symm
  have r13b (h1 : s S.v1 ≠ 0) (h2 : s S.v2 ≠ 0) (h3 : s S.v3 ≠ 0) :
      H.Reachable ⟨S.v1, S.interface_left _ (by simp [OnC4]), h1⟩
        ⟨S.v3, S.interface_left _ (by simp [OnC4]), h3⟩ :=
    (r12 h1 h2).trans (r23 h2 h3)
  rcases hqC with rfl | rfl | rfl | rfl
  · rcases hrC with rfl | rfl | rfl | rfl
    · exact (hnr .rfl).elim
    · exact (hnr (r01 hq hr)).elim
    · left
      refine ⟨hq, hr, ?_, ?_⟩
      · by_contra h1
        exact hnr (r02a hq h1 hr)
      · by_contra h3
        exact hnr (r02b hq h3 hr)
    · exact (hnr (r30 hr hq).symm).elim
  · rcases hrC with rfl | rfl | rfl | rfl
    · exact (hnr (r01 hr hq).symm).elim
    · exact (hnr .rfl).elim
    · exact (hnr (r12 hq hr)).elim
    · right
      refine ⟨hq, hr, ?_, ?_⟩
      · by_contra h0
        exact hnr (r13a hq h0 hr)
      · by_contra h2
        exact hnr (r13b hq h2 hr)
  · rcases hrC with rfl | rfl | rfl | rfl
    · left
      refine ⟨hr, hq, ?_, ?_⟩
      · by_contra h1
        exact hnr (r02a hr h1 hq).symm
      · by_contra h3
        exact hnr (r02b hr h3 hq).symm
    · exact (hnr (r12 hr hq).symm).elim
    · exact (hnr .rfl).elim
    · exact (hnr (r23 hq hr)).elim
  · rcases hrC with rfl | rfl | rfl | rfl
    · exact (hnr (r30 hq hr)).elim
    · right
      refine ⟨hr, hq, ?_, ?_⟩
      · by_contra h0
        exact hnr (r13a hr h0 hq).symm
      · by_contra h2
        exact hnr (r13b hr h2 hq).symm
    · exact (hnr (r23 hr hq).symm).elim
    · exact (hnr .rfl).elim

theorem zero_interface_impossible (moves : V → State V) (start coeff : State V)
    (hm : ∀ v, MoveAt G v (moves v))
    (hlegal : ∀ c, LegalState G (orbitState moves start c))
    (hzero : ∀ q, OnC4 S.v0 S.v1 S.v2 S.v3 q →
      orbitState moves start coeff q = 0) : False := by
  let s := orbitState moves start coeff
  have hsLegal : LegalState G s := hlegal coeff
  obtain ⟨u, hu⟩ := hsLegal.1.nonempty
  rcases S.cover u with hlu | hru
  · have hallLeft : ∀ v, s v ≠ 0 → S.left v := by
      intro v hv
      let H := G.induce {z | s z ≠ 0}
      let P : {z : V // s z ≠ 0} → Prop := fun z ↦ S.left z.1
      have hclosed : ∀ {p q}, P p → H.Adj p q → P q := by
        intro p q hp hpq
        have hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 p.1 := by
          intro hcp
          exact p.2 (hzero p.1 hcp)
        exact S.adjacent_forces_left hp hnc hpq
      have huv : H.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
        hsLegal.1.preconnected ⟨u, hu⟩ ⟨v, hv⟩
      exact reachable_preserves H P hclosed huv hlu
    let y := S.right₀
    have hy0 : s y = 0 := by
      by_contra hy
      exact S.right₀_only.2 (hallLeft y hy)
    let cy := flipCoeff y coeff
    have hcyLegal : LegalState G (orbitState moves start cy) := hlegal cy
    have hcyy : orbitState moves start cy y ≠ 0 := by
      change orbitState moves start coeff y = 0 at hy0
      rw [show cy = flipCoeff y coeff by rfl,
        orbit_flip_self G moves start coeff y (hm y), hy0]
      norm_num
    have hcyIso : ∀ q, G.Adj y q → orbitState moves start cy q = 0 := by
      intro q hyq
      rw [show cy = flipCoeff y coeff by rfl,
        orbit_flip_neighbor G moves start coeff y q (hm y) hyq]
      by_contra hq
      have hlq := hallLeft q hq
      have hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 q := by
        intro hcq
        exact hq (hzero q hcq)
      have hnrq := S.left_not_right_of_not_interface hlq hnc
      exact S.no_cross hlq hnrq S.right₀_only.1 S.right₀_only.2 hyq.symm
    have hsingle : orbitState moves start cy = basisState y :=
      state_eq_basis_of_isolated G _ hcyLegal y hcyy hcyIso
    have hyL0 : y ≠ S.left₀ := by
      intro h
      exact S.left₀_only.2 (h ▸ S.right₀_only.1)
    have hyL1 : y ≠ S.left₁ := by
      intro h
      exact S.left₁_only.2 (h ▸ S.right₀_only.1)
    have hnyL0 : ¬ G.Adj y S.left₀ := by
      intro h
      exact S.no_cross S.left₀_only.1 S.left₀_only.2
        S.right₀_only.1 S.right₀_only.2 h.symm
    have hnyL1 : ¬ G.Adj y S.left₁ := by
      intro h
      exact S.no_cross S.left₁_only.1 S.left₁_only.2
        S.right₀_only.1 S.right₀_only.2 h.symm
    exact no_singleton_orbit_with_two_nonneighbors G moves start cy hm hlegal
      y S.left₀ S.left₁ hyL0 hyL1 S.left_ne hnyL0 hnyL1 hsingle
  · have hallRight : ∀ v, s v ≠ 0 → S.right v := by
      intro v hv
      let H := G.induce {z | s z ≠ 0}
      let P : {z : V // s z ≠ 0} → Prop := fun z ↦ S.right z.1
      have hclosed : ∀ {p q}, P p → H.Adj p q → P q := by
        intro p q hp hpq
        have hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 p.1 := by
          intro hcp
          exact p.2 (hzero p.1 hcp)
        exact S.adjacent_forces_right hp hnc hpq
      have huv : H.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
        hsLegal.1.preconnected ⟨u, hu⟩ ⟨v, hv⟩
      exact reachable_preserves H P hclosed huv hru
    let x := S.left₀
    have hx0 : s x = 0 := by
      by_contra hx
      exact S.left₀_only.2 (hallRight x hx)
    let cx := flipCoeff x coeff
    have hcxLegal : LegalState G (orbitState moves start cx) := hlegal cx
    have hcxx : orbitState moves start cx x ≠ 0 := by
      change orbitState moves start coeff x = 0 at hx0
      rw [show cx = flipCoeff x coeff by rfl,
        orbit_flip_self G moves start coeff x (hm x), hx0]
      norm_num
    have hcxIso : ∀ q, G.Adj x q → orbitState moves start cx q = 0 := by
      intro q hxq
      rw [show cx = flipCoeff x coeff by rfl,
        orbit_flip_neighbor G moves start coeff x q (hm x) hxq]
      by_contra hq
      have hrq := hallRight q hq
      have hnc : ¬ OnC4 S.v0 S.v1 S.v2 S.v3 q := by
        intro hcq
        exact hq (hzero q hcq)
      have hnlq := S.right_not_left_of_not_interface hrq hnc
      exact S.no_cross S.left₀_only.1 S.left₀_only.2 hrq hnlq hxq
    have hsingle : orbitState moves start cx = basisState x :=
      state_eq_basis_of_isolated G _ hcxLegal x hcxx hcxIso
    have hxR0 : x ≠ S.right₀ := by
      intro h
      exact S.right₀_only.2 (h ▸ S.left₀_only.1)
    have hxR1 : x ≠ S.right₁ := by
      intro h
      exact S.right₁_only.2 (h ▸ S.left₀_only.1)
    have hnxR0 : ¬ G.Adj x S.right₀ :=
      S.no_cross S.left₀_only.1 S.left₀_only.2
        S.right₀_only.1 S.right₀_only.2
    have hnxR1 : ¬ G.Adj x S.right₁ :=
      S.no_cross S.left₀_only.1 S.left₀_only.2
        S.right₁_only.1 S.right₁_only.2
    exact no_singleton_orbit_with_two_nonneighbors G moves start cx hm hlegal
      x S.right₀ S.right₁ hxR0 hxR1 S.right_ne hnxR0 hnxR1 hsingle

theorem left_occupied_connected (moves : V → State V) (start coeff : State V)
    (hm : ∀ v, MoveAt G v (moves v))
    (hlegal : ∀ c, LegalState G (orbitState moves start c)) :
    (G.induce {v | S.left v ∧ orbitState moves start coeff v ≠ 0}).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · intro x y
    by_contra hxy
    obtain ⟨q, hqC, hq, hxq⟩ := S.component_meets_interface
      (orbitState moves start coeff) (hlegal coeff) x.2.1 y.2.1 x.2.2 y.2.2 hxy
    obtain ⟨r, hrC, hr, hyr⟩ := S.component_meets_interface
      (orbitState moves start coeff) (hlegal coeff) y.2.1 x.2.1 y.2.2 x.2.2
        (fun h ↦ hxy h.symm)
    have hqr : ¬ (G.induce {v | S.left v ∧ orbitState moves start coeff v ≠ 0}).Reachable
        ⟨q, S.interface_left q hqC, hq⟩ ⟨r, S.interface_left r hrC, hr⟩ := by
      intro h
      exact hxy (hxq.trans (h.trans hyr.symm))
    rcases S.c4_pattern_of_not_reachable (orbitState moves start coeff)
      hqC hrC hq hr hqr with hac | hbd
    · obtain ⟨coeff', h0, h2, h1, h3⟩ := exists_clear_opposite_pair
        moves start coeff hm S.v0 S.v2 S.v1 S.v3
        S.h01 S.h30.symm S.h12.symm S.h23 hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
      apply S.zero_interface_impossible moves start coeff' hm hlegal
      intro z hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · obtain ⟨coeff', h1, h3, h0, h2⟩ := exists_clear_opposite_pair
        moves start coeff hm S.v1 S.v3 S.v0 S.v2
        S.h01.symm S.h12 S.h30 S.h23.symm hbd.1 hbd.2.1 hbd.2.2.1 hbd.2.2.2
      apply S.zero_interface_impossible moves start coeff' hm hlegal
      intro z hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  · by_contra hempty
    have hzero : ∀ q, OnC4 S.v0 S.v1 S.v2 S.v3 q →
        orbitState moves start coeff q = 0 := by
      intro q hqC
      by_contra hq
      exact hempty ⟨⟨q, S.interface_left q hqC, hq⟩⟩
    exact S.zero_interface_impossible moves start coeff hm hlegal hzero

theorem restrictMoves_left_moveAt (moves : V → State V)
    (hm : ∀ v, MoveAt G v (moves v)) :
    ∀ v, MoveAt (G.induce S.left) v (restrictMoves S.left moves v) := by
  intro v
  constructor
  · exact (hm v.1).1
  · intro w hvw
    exact (hm v.1).2 w.1 hvw

theorem legalSystem_restrict_left [DecidablePred (· ∈ S.left)]
    (h : LegalSystem G) : LegalSystem (G.induce S.left) := by
  classical
  rcases h with ⟨moves, start, hm, hlegal⟩
  refine ⟨restrictMoves S.left moves, restrictState S.left start,
    S.restrictMoves_left_moveAt moves hm, ?_⟩
  intro coeff
  let ext := extendCoeff S.left coeff
  let global := orbitState moves start ext
  have horbit : orbitState (restrictMoves S.left moves) (restrictState S.left start) coeff =
      restrictState S.left global := by
    exact orbit_restrict_eq S.left moves start coeff
  rw [horbit]
  unfold LegalState
  constructor
  · have hc := S.left_occupied_connected moves start ext hm hlegal
    have hi := (induceRestrictIso G S.left (fun v ↦ global v ≠ 0)).connected_iff.mpr hc
    simpa [restrictState] using hi
  · have hlegalCompl : ∀ c, LegalState G (orbitState moves (complState start) c) := by
      intro c
      rw [orbit_compl_start]
      exact legalState_compl G _ (hlegal c)
    have hc := S.left_occupied_connected moves (complState start) ext hm hlegalCompl
    have hset : {v : V | S.left v ∧ orbitState moves (complState start) ext v ≠ 0} =
        {v : V | S.left v ∧ global v = 0} := by
      ext v
      rw [orbit_compl_start]
      change (S.left v ∧ orbitState moves start ext v + 1 ≠ 0) ↔
        (S.left v ∧ orbitState moves start ext v = 0)
      exact and_congr_right fun _ ↦ zmod2_add_one_ne_zero_iff _
    rw [hset] at hc
    have hi := (induceRestrictIso G S.left (fun v ↦ global v = 0)).connected_iff.mpr hc
    simpa [restrictState] using hi

abbrev swap : ExactC4Split G where
  left := S.right
  right := S.left
  v0 := S.v0
  v1 := S.v1
  v2 := S.v2
  v3 := S.v3
  h01 := S.h01
  h12 := S.h12
  h23 := S.h23
  h30 := S.h30
  h02 := S.h02
  h13 := S.h13
  h01_ne := S.h01_ne
  h02_ne := S.h02_ne
  h03_ne := S.h03_ne
  h12_ne := S.h12_ne
  h13_ne := S.h13_ne
  h23_ne := S.h23_ne
  cover v := (S.cover v).symm
  intersection v hr hl := S.intersection v hl hr
  interface_left := S.interface_right
  interface_right := S.interface_left
  no_cross := by
    intro u v hru hnlu hlv hnrv huv
    exact S.no_cross hlv hnrv hru hnlu huv.symm
  left₀ := S.right₀
  left₁ := S.right₁
  right₀ := S.left₀
  right₁ := S.left₁
  left₀_only := S.right₀_only
  left₁_only := S.right₁_only
  right₀_only := S.left₀_only
  right₁_only := S.left₁_only
  left_ne := S.right_ne
  right_ne := S.left_ne

theorem legalSystem_restrict_right [DecidablePred (· ∈ S.right)]
    (h : LegalSystem G) : LegalSystem (G.induce S.right) := by
  exact S.swap.legalSystem_restrict_left h

end ExactC4Split
end JNW
