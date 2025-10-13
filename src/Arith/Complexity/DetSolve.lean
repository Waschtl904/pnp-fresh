import Mathlib.Data.Nat.Basic
import PNP.TM.Core

namespace PNP

/-- DetSolve(f, x, t): f entscheidet x in ≤ t Schritten deterministisch -/
def DetSolve (f x t : Nat) : Prop :=
  PNP.TM.AcceptRun f x [] t

end PNP
