import PNP.TM.AcceptRun

namespace PNP

/-- DetSolve(f, x, t): deterministische Entscheidung in ≤ t Schritten -/
def DetSolve (f x t : Nat) : Prop :=
  PNP.TM.AcceptRun f x [] t

end PNP
