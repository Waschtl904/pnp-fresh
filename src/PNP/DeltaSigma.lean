import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log

namespace PNP

/-- Paarungsfunktion: ⟨u,v⟩ = 2^u * (2*v + 1) -/
def pair (u v : Nat) : Nat :=
  2 ^ u * (2 * v + 1)

/-- Hilfsfunktion: rekursive Zählung der Zweierpotenzen -/
def aux : Nat → Nat
  | 0     => 0
  | m + 1 =>
    if (m + 1) % 2 = 0 then 1 + aux ((m + 1) / 2) else 0
decreasing_by
  simp_wf
  have h : (m + 1) / 2 < m + 1 := by
    cases (m + 1).mod_two_eq_zero_or_one with
    | inl h_even =>
      exact Nat.div_lt_self (Nat.zero_lt_succ _) (Nat.lt_succ_self 1)
    | inr h_odd =>
      exact Nat.div_lt_self (Nat.zero_lt_succ _) (Nat.lt_succ_self _)
  decreasing_trivial

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

/-- Struktur der Paarungsfunktion: (2*v+1) ist ungerade und pair u v = 2^u*(2*v+1) -/
lemma pair_structure (u v : Nat) :
  (2 * v + 1) % 2 = 1 ∧ pair u v = 2 ^ u * (2 * v + 1) := by
  constructor
  · simp
  · rfl

/-- pair ist niemals 0 -/
lemma pair_ne_zero (u v : Nat) : pair u v ≠ 0 := by
  unfold pair
  apply Nat.mul_ne_zero
  · intro h
    cases u with
    | zero => exact absurd h (Nat.ne_of_gt Nat.zero_lt_one)
    | succ u => exact absurd h (Nat.ne_of_gt (by norm_num))
  · apply Nat.succ_ne_zero

/-- maxTwoPowerDiv findet genau u, wenn n = pair u v -/
theorem maxTwoPowerDiv_correct (u v : Nat) :
    maxTwoPowerDiv (pair u v) = u := by
  unfold maxTwoPowerDiv
  have nz : pair u v ≠ 0 := pair_ne_zero u v
  rw [if_neg nz]
  induction u with
  | zero =>
    -- pair 0 v = 1 * (2*v+1) ≠ 0, aux (2*v+1) = 0
    unfold aux pair
    simp
  | succ u ih =>
    -- For u+1, pair (u+1) v = 2^(u+1) * (2*v+1) which is even, so aux = 1 + aux (2^u * (2*v+1))
    -- And aux (2^u * (2*v+1)) = u by induction hypothesis, so aux = 1 + u = u + 1
    have aux_succ : aux (2 ^ (u + 1) * (2 * v + 1)) = u + 1 := by
      -- Since 2^(u+1) * (2*v+1) is even and ≠ 0, aux = 1 + aux ( (2^(u+1) * (2*v+1)) / 2 )
      have h_even : (2 ^ (u + 1) * (2 * v + 1)) % 2 = 0 := by simp [Nat.mul_mod]
      have h_ne_zero : 2 ^ (u + 1) * (2 * v + 1) ≠ 0 := by
        apply Nat.mul_ne_zero <;> norm_num
      -- Split on whether the expression is 0 or not (it can't be 0)
      cases eq : 2 ^ (u + 1) * (2 * v + 1) with
      | zero => contradiction
      | succ m =>
        -- The goal is aux (Nat.succ m) = u + 1
        -- Since 2^(u+1) * (2*v+1) is even and m = 2^(u+1) * (2*v+1) - 1, m is odd
        -- For odd m, aux (Nat.succ m) = 0, but this contradicts since we know it should be u + 1
        -- Wait, that's not right. Let me use the correct logic.
        -- Since we know (m + 1) is even, aux (Nat.succ m) = 1 + aux ((m + 1) / 2)
        -- Since we know (m + 1) is even, aux (Nat.succ m) = 1 + aux ((m + 1) / 2)
        unfold aux
        -- First, use h_mod_eq to simplify the if condition since we know (m + 1) % 2 = 0
        have h_mod_eq : (m + 1) % 2 = 0 := by rw [← eq]; exact h_even
        rw [if_pos h_mod_eq]
        -- Now the goal is 1 + aux ((m + 1) / 2) = u + 1
        -- And (m + 1) / 2 = 2^u * (2*v + 1)
        have h_half : (m + 1) / 2 = 2 ^ u * (2 * v + 1) := by
          -- Since 2^(u+1) * (2*v+1) = 2 * 2^u * (2*v+1), dividing by 2 gives 2^u * (2*v+1)
          calc (m + 1) / 2 = (2 ^ (u + 1) * (2 * v + 1)) / 2 := by rw [eq]
          _ = 2 ^ u * (2 * v + 1) := by
            -- Since 2^(u+1) = 2 * 2^u, we have (2 * 2^u * (2*v+1)) / 2 = 2^u * (2*v+1)
            apply Nat.div_eq_of_eq_mul_right
            · exact Nat.zero_lt_succ 1  -- 2 > 0
            · rw [pow_succ', Nat.mul_assoc]
        -- By induction hypothesis, aux (2^u * (2*v + 1)) = u
        have ih_applied : aux (2 ^ u * (2 * v + 1)) = u := by
          apply ih
          exact pair_ne_zero u v
        -- Now rewrite the goal: 1 + aux ((m + 1) / 2) = 1 + aux (2^u * (2*v + 1)) = 1 + u = u + 1
        rw [h_half, ih_applied]
        exact Nat.add_comm 1 u
    -- Now use aux_succ to prove the main goal
    -- The goal is aux (pair (u + 1) v) = u + 1, and aux_succ proves exactly this
    -- We need to unfold pair to match the expression in aux_succ
    unfold pair
    exact aux_succ

/-- fst(pair u v) = u -/
theorem pair_fst_snd (u v : Nat) :
    fst (pair u v) = u := by
  unfold fst
  have nz : pair u v ≠ 0 := pair_ne_zero u v
  rw [if_neg nz]
  exact maxTwoPowerDiv_correct u v


/-- snd(pair u v) = v -/
theorem pair_snd_fst (u v : Nat) :
    snd (pair u v) = v := by
  unfold snd
  have nz : pair u v ≠ 0 := pair_ne_zero u v
  rw [if_neg nz]
  have fst_eq : fst (pair u v) = u := pair_fst_snd u v
  -- Direct calculation using the pair definition
  have pair_eq : pair u v = 2 ^ u * (2 * v + 1) := rfl
  calc (pair u v / 2 ^ (fst (pair u v)) - 1) / 2 = (pair u v / 2 ^ u - 1) / 2 := by rw [fst_eq]
  _ = (2 ^ u * (2 * v + 1) / 2 ^ u - 1) / 2 := by rw [pair_eq]
  _ = ((2 * v + 1) - 1) / 2 := by
    have h : 2 ^ u * (2 * v + 1) / 2 ^ u = 2 * v + 1 := by
      apply Nat.div_eq_of_eq_mul_left
      · cases u <;> simp [Nat.pow_succ]
      · exact Nat.mul_comm (2 ^ u) (2 * v + 1)
    rw [h]
  _ = (2 * v) / 2 := by simp
  _ = v := by
    cases v <;> simp

end PNP
