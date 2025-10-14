import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma
import PNP.TM.Core
import PNP.EvalSemantics

namespace PNP

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
      simp [p, Nat.pow_one, mul_one]
      sorry -- hier würde der Beweis stehen, dass evalPair polynomielle Zeit respektiert
  · intro ⟨h₁, h₂⟩
    exact h₁

end PNP
