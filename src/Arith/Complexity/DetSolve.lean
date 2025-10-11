import Mathlib.Data.Nat.Basic
import PNP.TM.AcceptRun

namespace PNP

/-- DetSolve(f, x, t) : deterministische Entscheidung ≤ t Schritte -/
def DetSolve (f x t : Nat) : Prop :=
  PNP.TM.AcceptRun f x [] t

end PNP
