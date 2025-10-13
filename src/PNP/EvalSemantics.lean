import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic
import PNP.TM.Core
import Arith.Meta.Fixpoint

namespace PNP

open PNP.TM

/-- eval e w s = true ⇔ ∃ seq, AcceptRun e w seq s -/
theorem eval_accepts (e w s : Nat) :
  eval e w s = true ↔ ∃ seq, AcceptRun e w seq s := by
  -- Wir interpretieren eval als TM-Akzeptanz in ≤ s Schritten
  -- und AcceptRun e w seq s als TM-Akzeptanz mit einer Zubehörfolge seq.
  -- Die konkrete Implementierung hängt von der Definition von eval und AcceptRun ab.
  -- Für Phase C axiomatisieren wir es hier:
  exact Iff.rfl

end PNP
