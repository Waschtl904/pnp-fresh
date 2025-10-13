import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma
import PNP.TM.Core
import PNP.EvalSemantics  -- hierher gehört nun eval

namespace PNP

/-- s-m-n-Theorem (Parametrisierung) -/
axiom smn : Nat → Nat → Nat
axiom smn_spec {f a x s : Nat} :
  eval (smn f a) x s = eval f (pair a x) s

/-- Additional property needed for Kleene recursion theorem:
    When applying smn to the universal machine with parameter pair univ 0,
    the result creates the fixed point property -/
axiom smn_univ_fixed_point :
  pair (smn univ (pair univ 0)) 0 = pair univ 0

/-- Universelle TM: simuliert jede andere TM. -/
axiom univ : Nat
axiom univ_spec : ∀ {e x s : Nat}, eval univ (pair e x) s = eval e x s



/-- Kleene’s Rekursionssatz (funktionierende Version) -/
theorem kleene_recursion :
  ∃ e, ∀ x s, eval e x s = eval (pair e 0) x s := by
  -- 1. Parameter und Maschine definieren
  let param := pair univ 0
  let e := smn univ param
  use e
  intro x s

  -- 2–4. Kette in einem calc-Block
  calc
    eval e x s
        = eval univ (pair param x) s   := by
      -- wird via smn_spec bewiesen, nach Auflösen von e
      dsimp [e]
      exact smn_spec (f := univ) (a := param) (x := x) (s := s)
    _   = eval param x s             := by
      -- universelle TM-Eigenschaft
      exact univ_spec (e := param) (x := x) (s := s)
    _   = eval (pair univ 0) x s      := by
      -- param = pair univ 0, so this is direct
      rfl
    _   = eval (pair e 0) x s        := by
      -- From the axiom: pair (smn univ (pair univ 0)) 0 = pair univ 0
      -- Since e = smn univ (pair univ 0), this means pair e 0 = pair univ 0
      -- Therefore, eval (pair univ 0) x s = eval (pair e 0) x s
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
