import PNP.DeltaSigma   -- liefert Ihre pair, fst, snd
import PNP.TM.Core
import PNP.EvalSemantics

namespace PNP

/-- s-m-n-Theorem (Parametrisierung) -/
axiom smn : Nat → Nat → Nat
axiom smn_spec {f a x s : Nat} :
  eval (smn f a) x s = eval f (pair a x) s

/-- Fixpunkt-Eigenschaft für smn mit universeller TM -/
axiom smn_univ_fixed_point :
  pair (smn univ (pair univ 0)) 0 = pair univ 0

/-- Universelle TM: simuliert jede andere TM. -/
axiom univ : Nat
axiom univ_spec : ∀ {e x s : Nat}, eval univ (pair e x) s = eval e x s

/-- Spezifikation für Fixpunkt-Lemma – Akzeptanzäquivalenz ohne Zeitbindung -/
axiom Fix.evalPair_spec (e x : Nat) :
  (∃ s, eval e x s = true) ↔ ∃ s, eval e (pair (fst x) (snd x)) s = true

/-- Kleene’s Rekursionssatz -/
theorem kleene_recursion :
  ∃ e, ∀ x s, eval e x s = eval (pair e 0) x s := by
  let param := pair univ 0
  let e := smn univ param
  use e
  intro x s
  calc
    eval e x s
      = eval univ (pair param x) s   := smn_spec (f := univ) (a := param) (x := x) (s := s)
    _ = eval param x s               := univ_spec (e := param) (x := x) (s := s)
    _ = eval (pair univ 0) x s       := rfl
    _ = eval (pair e 0) x s          := by rw [← smn_univ_fixed_point]

/-- Allgemeines Fixpunkt-Lemma für Prädikate F -/
theorem fixpoint (F : Nat → Nat → Prop)
  (Hspec : ∀ e x, (∃ s, eval e x s = true) ↔ F e x) :
  ∃ e', ∀ x, F e' x ↔ F (pair e' 0) x := by
  obtain ⟨e', he⟩ := kleene_recursion
  use e'
  intro x
  constructor
  · intro hF
    obtain ⟨s, hs⟩ := (Hspec e' x).mpr hF
    have hs' := by rw [he x s] at hs; exact hs
    exact (Hspec (pair e' 0) x).mp ⟨s, hs'⟩
  · intro hF'
    obtain ⟨s, hs'⟩ := (Hspec (pair e' 0) x).mpr hF'
    have hs := by rw [← he x s] at hs'; exact hs'
    exact (Hspec e' x).mp ⟨s, hs⟩

end PNP
