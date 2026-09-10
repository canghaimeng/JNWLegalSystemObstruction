import Mathlib

namespace JNW

abbrev State (V : Type*) := V → ZMod 2

def support {V : Type*} [Fintype V] (s : State V) : Finset V :=
  Finset.univ.filter fun v ↦ s v ≠ 0

def complState {V : Type*} (s : State V) : State V := fun v ↦ s v + 1

def xorState {V : Type*} (s t : State V) : State V := fun v ↦ s v + t v

def MoveAt {V : Type*} (G : SimpleGraph V) (v : V) (m : State V) : Prop :=
  m v = 1 ∧ ∀ w, G.Adj v w → m w = 0

def orbitState {V : Type*} [Fintype V]
    (moves : V → State V) (start coeff : State V) : State V :=
  fun x ↦ start x + ∑ v, coeff v * moves v x

def LegalState {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : State V) : Prop :=
  (G.induce {v | s v ≠ 0}).Connected ∧
  (G.induce {v | s v = 0}).Connected

def LegalSystem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ moves : V → State V, ∃ start : State V,
    (∀ v, MoveAt G v (moves v)) ∧
    ∀ coeff : State V, LegalState G (orbitState moves start coeff)

end JNW
