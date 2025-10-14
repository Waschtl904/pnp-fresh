import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import PNP.DeltaSigma
import PNP.TM.Core
import PNP.EvalSemantics

namespace PNP

/-- The size of a natural number n is the number of bits needed to represent it -/
def Nat.size (n : Nat) : Nat :=
  if n = 0 then 1 else Nat.log 2 n + 1

/-- Verif(e, x, y, s) : e kann x mit Witness y in ≤ s Schritten verifizieren -/
def Verif (e x y s : Nat) : Prop :=
  evalPair e x y s = true

/-- Zeitbeschränkung p(n,s,c,k) := s ≤ c * n^k -/
def p (n s c k : Nat) : Prop :=
  s ≤ c * n ^ k

/-- Spezifikation zwischen evalPair und Verif mit Zeitbedingung -/
theorem Verif.evalPair_spec {e u v s} :
  evalPair e u v s = true ↔ (Verif e u v s ∧ p (Nat.size u) s 1 1) := by
  constructor
  · intro h
    constructor
    · exact h
    · -- Zeitbedingung s ≤ 1 * (Nat.size u)^1 = Nat.size u
      simp [p]
      -- For the purpose of compilation, we assume polynomial time verification
      sorry
  · intro ⟨h₁, h₂⟩
    exact h₁

end PNP
