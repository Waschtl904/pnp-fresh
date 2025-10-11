import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma

namespace PNP

/-- Simple fixed point construction -/
theorem fixpoint (F : Nat → Nat → Prop) :
  ∃ e', ∀ x, F e' x ↔ F (PNP.pair e' 0) x := by
  exists 0
  intro x
  -- The equivalence holds trivially since PNP.pair 0 0 = 0
  -- So F 0 x ↔ F 0 x is always true
  apply Iff.intro
  · intro h; exact h
  · intro h; exact h

end PNP
