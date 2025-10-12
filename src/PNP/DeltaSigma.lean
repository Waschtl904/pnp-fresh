import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log

namespace PNP

/-- Paarungsfunktion: ⟨u,v⟩ = 2^u * (2*v + 1) -/
def pair (u v : Nat) : Nat :=
  (2 ^ u) * (2 * v + 1)

/-- Hilfsfunktion: rekursive Zählung der Zweierpotenzen -/
def aux (m : Nat) : Nat :=
  if m = 0 then 0
  else if m % 2 = 1 then 0
  else 1 + aux (m / 2)
termination_by m

/-- Größte Zweierpotenz, die n teilt -/
def maxTwoPowerDiv (n : Nat) : Nat :=
  if n = 0 then 0 else aux n

/-- Projektion π₁: erster Parameter der Paarung -/
def fst (z : Nat) : Nat :=
  if z = 0 then 0 else maxTwoPowerDiv z

/-- Projektion π₂: zweiter Parameter der Paarung -/
def snd (z : Nat) : Nat :=
  if z = 0 then 0 else
    let u := fst z
    (z / (2 ^ u) - 1) / 2

/-- Struktur der Paarungsfunktion -/
lemma pair_structure (u v : Nat) :
  (2 * v + 1) % 2 = 1 ∧ pair u v = (2 ^ u) * (2 * v + 1) := by
  constructor
  · simp
  · rfl

/-- pair ist niemals null -/
lemma pair_ne_zero (u v : Nat) : pair u v ≠ 0 := by
  unfold pair
  apply Nat.mul_ne_zero
  · exact Nat.ne_of_gt (Nat.pow_pos (by norm_num))
  · apply Nat.succ_ne_zero

/-- maxTwoPowerDiv findet genau u, wenn n = pair u v -/
theorem maxTwoPowerDiv_correct (u v : Nat) :
  maxTwoPowerDiv (pair u v) = u := by
  unfold maxTwoPowerDiv
  rw [if_neg (pair_ne_zero u v)]
  induction u with
  | zero =>
    unfold pair aux
    simp
  | succ n ih =>
    unfold pair aux
    have h1 : 2^(n+1) * (2*v + 1) ≠ 0 := by
      apply Nat.mul_ne_zero
      · exact Nat.ne_of_gt (Nat.pow_pos (Nat.succ_pos 1))
      · apply Nat.succ_ne_zero
    have h2 : (2^(n+1) * (2*v + 1)) % 2 ≠ 1 := by
      simp [Nat.mul_mod]
    rw [if_neg h1, if_neg h2]
    have h3 : (2^(n+1) * (2*v + 1)) / 2 = 2^n * (2*v + 1) := by
      rw [Nat.pow_succ]
      rw [Nat.mul_assoc]
      rw [Nat.mul_comm (2^n)]
      rw [Nat.mul_assoc]
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      rw [Nat.mul_comm]
    rw [h3]
    -- Now we have: 1 + aux (2^n * (2*v + 1))
    -- Since 2^n * (2*v + 1) = pair n v, and aux (pair n v) = n by induction hypothesis
    have h_pair : 2^n * (2*v + 1) = pair n v := rfl
    rw [h_pair, ih]
    -- Now we have: 1 + n = n + 1, which is true by commutativity
    exact Nat.add_comm 1 n

/-- fst(pair u v) = u -/
theorem pair_fst_snd (u v : Nat) : fst (pair u v) = u := by
  unfold fst
  rw [if_neg (pair_ne_zero u v)]
  exact maxTwoPowerDiv_correct u v

/-- snd(pair u v) = v -/
theorem pair_snd_fst (u v : Nat) : snd (pair u v) = v := by
  -- Use the fact that we know pair u v ≠ 0 and the structure
  have h_ne : pair u v ≠ 0 := pair_ne_zero u v
  unfold snd
  split_ifs with h
  · -- This case would mean pair u v = 0, but we know it's not
    contradiction
  · -- The main case: (pair u v / 2^fst(pair u v) - 1) / 2 = v
    have h_fst : fst (pair u v) = u := pair_fst_snd u v
    have h_pair : pair u v = 2^u * (2*v + 1) := rfl
    rw [h_fst, h_pair]
    -- Now we have: (2^u * (2*v + 1) / 2^u - 1) / 2 = v
    have h_pos : 0 < 2^u := by
      cases u with
      | zero => exact Nat.zero_lt_one
      | succ u' => exact Nat.pow_pos (Nat.succ_pos 1)
    have h1 : 2^u * (2*v + 1) / 2^u = 2*v + 1 := Nat.mul_div_cancel_left _ h_pos
    simp [h1]

end PNP
