import Init.Data.Nat.Basic      -- für ℕ, +, -, etc.
import Mathlib.Data.Nat.Basic  -- mathlib⁴-Grundlagen
import Mathlib.Data.Nat.Sqrt   -- mathlib⁴-Quadratwurzel

namespace Delta0

def pair (x y : ℕ) : ℕ :=
  ((x + y) * (x + y + 1)) / 2 + y

def π₁ (z : ℕ) : ℕ :=
  let w := (Nat.sqrt (8 * z + 1) - 1) / 2
  w - (w * (w + 1)) / 2

def π₂ (z : ℕ) : ℕ :=
  z - (π₁ z * (π₁ z + 1)) / 2

@[simp] theorem pair_proj (x y : ℕ) :
  π₁ (pair x y) = x ∧ π₂ (pair x y) = y := by
  -- hier schreibe Ihren Beweis
  sorry

end Delta0
