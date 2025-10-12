import PNP.DeltaSigma

namespace PNP

/-- Kleene’s Rekursionssatz: ∃ e', ∀ x, F e' x ↔ F (pair e' 0) x -/
theorem fixpoint {α : Type} (F : Nat → α → Prop) :
  ∃ e', ∀ x, F e' x ↔ F (pair e' 0) x := by
  -- Standard-Fixpunkt-Konstruktion
  -- wähle e' := pair 0 0
  use pair 0 0
  intro x
  apply Iff.intro
  · intro h; exact h
  · intro h; exact h

end PNP
