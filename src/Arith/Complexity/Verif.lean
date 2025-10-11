import Mathlib.Data.Nat.Basic
import PNP.TM.AcceptRun
import PNP.DeltaSigma

namespace PNP

/-- Verif(e, x, y, s) : Σ₁-Verifikationsprädikat -/
def Verif (e x y s : Nat) : Prop :=
  TM.AcceptRun e (pair x y) [] s

/-- p(n, s, c, k) := s ≤ c * n^k -/
def p (n s c k : Nat) : Prop :=
  s ≤ c * n ^ k

end PNP
