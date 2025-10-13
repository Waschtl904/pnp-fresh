import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma
import PNP.TM.Core

namespace PNP

/-- Verif(e, x, y, s) : e akzeptiert die kodierte Eingabe ⟨x,y⟩ in ≤ s Schritten -/
def Verif (e x y s : Nat) : Prop :=
  PNP.TM.AcceptRun e (pair x y) [] s

/-- Zeitbeschränkung p(n,s,c,k) := s ≤ c * n^k -/
def p (n s c k : Nat) : Prop :=
  s ≤ c * n ^ k

end PNP
