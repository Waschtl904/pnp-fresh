import Lean
import Lean.Elab.Tactic

open Lean Meta Elab Tactic

namespace PNP

/-- Paarungsfunktion: ⟨u,v⟩ = 2^u * (2*v + 1) -/
def pair (u v : Nat) : Nat :=
  2 ^ u * (2 * v + 1)

/-- Hilfsfunktion: rekursive Zählung der Zweierpotenzen -/
def aux : Nat → Nat
  | 0 => 0
  | m + 1 =>
    if (m + 1) % 2 = 0 then 1 + aux ((m + 1) / 2) else 0
  decreasing_by omega

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

/-- Struktur der Paarungsfunktion: (2*v+1) ist ungerade -/
lemma pair_structure (u v : Nat) :
  (2 * v + 1) % 2 = 1 ∧ pair u v = 2 ^ u * (2 * v + 1) := by
  constructor
  · simp
  · rfl

/-- pair ist niemals 0 -/
lemma pair_ne_zero (u v : Nat) : pair u v ≠ 0 := by
  unfold pair
  apply Nat.mul_ne_zero
  · omega
  · omega

/-- maxTwoPowerDiv findet genau u, wenn n = pair u v -/
theorem maxTwoPowerDiv_correct (u v : Nat) :
  maxTwoPowerDiv (pair u v) = u := by
  unfold maxTwoPowerDiv
  have nz : pair u v ≠ 0 := pair_ne_zero u v
  rw [if_neg nz]
  induction u with
  | zero =>
    unfold aux pair
    simp
  | succ u ih =>
    -- For u+1, pair (u+1) v = 2^(u+1) * (2*v+1) which is even
    have aux_succ : aux (2 ^ (u + 1) * (2 * v + 1)) = u + 1 := by
      have h_even : (2 ^ (u + 1) * (2 * v + 1)) % 2 = 0 := by
        simp [Nat.mul_mod]
      have h_ne_zero : 2 ^ (u + 1) * (2 * v + 1) ≠ 0 := by omega
      cases eq : 2 ^ (u + 1) * (2 * v + 1) with
      | zero => contradiction
      | succ m =>
        unfold aux
        have h_mod_eq : (m + 1) % 2 = 0 := by rw [← eq]; exact h_even
        rw [if_pos h_mod_eq]
        have h_half : (m + 1) / 2 = 2 ^ u * (2 * v + 1) := by
          calc (m + 1) / 2
            = (2 ^ (u + 1) * (2 * v + 1)) / 2 := by rw [eq]
            _ = 2 ^ u * (2 * v + 1) := by
              rw [show (2 : Nat) ^ (u + 1) = 2 * 2 ^ u by omega]
              rw [Nat.mul_assoc]
              exact Nat.mul_div_cancel_left _ (by omega)
        have ih_applied : aux (2 ^ u * (2 * v + 1)) = u := by
          apply ih
          exact pair_ne_zero u v
        rw [h_half, ih_applied]
        omega
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
  have pair_eq : pair u v = 2 ^ u * (2 * v + 1) := rfl
  calc (pair u v / 2 ^ (fst (pair u v)) - 1) / 2
    = (pair u v / 2 ^ u - 1) / 2 := by rw [fst_eq]
    _ = (2 ^ u * (2 * v + 1) / 2 ^ u - 1) / 2 := by rw [pair_eq]
    _ = ((2 * v + 1) - 1) / 2 := by
      have h : 2 ^ u * (2 * v + 1) / 2 ^ u = 2 * v + 1 := by
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h]
    _ = (2 * v) / 2 := by simp
    _ = v := by omega

end PNP