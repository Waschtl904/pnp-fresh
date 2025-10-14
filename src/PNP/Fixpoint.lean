import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma
import PNP.TM.Core
import PNP.EvalSemantics
import Arith.Complexity.Verif

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

/-- Spezifikation für Fixpunkt-Lemma mit evalPair -/
theorem Fix.evalPair_spec (e x : Nat) :
  (∃ s, eval e x s = true) ↔ (∃ y s, Verif e (fst x) y s ∧ p (Nat.size (fst x)) s 1 1) := by
  constructor
  · intro ⟨s, hs⟩
    -- x wird als pair (fst x) (snd x) interpretiert
    have h_pair : eval e x s = evalPair e (fst x) (snd x) s := by
      conv_lhs => rw [← pair_fst_snd x]
      exact eval_pair_equiv
    rw [h_pair] at hs
    have ⟨h_verif, h_time⟩ := (Verif.evalPair_spec).mp hs
    exact ⟨snd x, s, h_verif, h_time⟩
  · intro ⟨y, s, ⟨h_verif, h_time⟩⟩
    have hs : evalPair e (fst x) y s = true := h_verif
    have h_pair : evalPair e (fst x) y s = eval e (pair (fst x) y) s := eval_pair_inv
    rw [h_pair] at hs
    exact ⟨s, hs⟩

/-- Kleene's Rekursionssatz -/
theorem kleene_recursion :
  ∃ e, ∀ x s, eval e x s = eval (pair e 0) x s := by
  let param := pair univ 0
  let e := smn univ param
  use e
  intro x s
  calc
    eval e x s
        = eval univ (pair param x) s   := by
      dsimp [e]
      exact smn_spec (f := univ) (a := param) (x := x) (s := s)
    _   = eval param x s             := by
      exact univ_spec (e := param) (x := x) (s := s)
    _   = eval (pair univ 0) x s      := by
      rfl
    _   = eval (pair e 0) x s        := by
      rw [← smn_univ_fixed_point]

/-- Fixpunkt-Lemma für beliebige Prädikate F. -/
theorem fixpoint (F : Nat → Nat → Prop)
  (Hspec : ∀ e x, (∃ s, eval e x s = true) ↔ F e x) :
  ∃ e', ∀ x, F e' x ↔ F (pair e' 0) x := by
  obtain ⟨e', he⟩ := kleene_recursion
  use e'
  intro x
  constructor
  · intro hF
    obtain ⟨s, hs⟩ := (Hspec e' x).mpr hF
    have hs' : eval (pair e' 0) x s = true := by
      rw [he x s] at hs
      exact hs
    exact (Hspec (pair e' 0) x).mp ⟨s, hs'⟩
  · intro hF'
    obtain ⟨s, hs'⟩ := (Hspec (pair e' 0) x).mpr hF'
    have hs : eval e' x s = true := by
      rw [← he x s] at hs'
      exact hs'
    exact (Hspec e' x).mp ⟨s, hs⟩

end PNP
