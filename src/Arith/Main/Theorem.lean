import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pairing
import PNP.DeltaSigma
import PNP.TM.Core
import Arith.Complexity.Verif
import Arith.Complexity.DetSolve
import PNP.Fixpoint

namespace PNP

/-- Erste Komponente der Paarung -/
def fst (z : Nat) : Nat := (Nat.unpair z).fst

/-- Zweite Komponente der Paarung -/
def snd (z : Nat) : Nat := (Nat.unpair z).snd

theorem P_neq_NP :
  ¬ ∀ e c k x,
    (∃ y s, Verif e x y s ∧ p (Nat.size x) s c k) ↔
    (∃ s', DetSolve (fst (Nat.pair e c)) x s' ∧ p (Nat.size x) s' (snd (Nat.pair e c)) (snd (Nat.pair e c)))
:= by
  intro H_eq

  -- Fixpunkt für c = k = 1
  obtain ⟨e₀, he₀⟩ := fixpoint
    (λ e x => ∃ y s, Verif e (fst x) y s ∧ p (Nat.size (fst x)) s 1 1)
    Fix.evalPair_spec

  let x₀ := Nat.pair e₀ e₀
  have H₀ := H_eq e₀ 1 1 x₀

  by_cases h_ds : ∃ s', DetSolve (fst (Nat.pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' (snd (Nat.pair e₀ 1)) (snd (Nat.pair e₀ 1))
  · -- Fall A: DetSolve existiert ⇒ Verif existiert ⇒ Widerspruch
    have h_verif : ∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := H₀.mpr h_ds
    obtain ⟨y₀, s₀, h_v, h_t⟩ := h_verif

    -- Zerlege x₀ in fst und snd
    let ⟨u₀, v₀⟩ := Nat.unpair x₀
    have hu : u₀ = fst x₀ := by simp [fst]
    have hv : v₀ = snd x₀ := by simp [snd]

    -- Wähle Witness und Zeit
    use v₀, s₀
    constructor
    · -- Verif e₀ (fst x₀) v₀ s₀
      calc
        Verif e₀ (fst x₀) v₀ s₀ = evalPair e₀ (fst x₀) v₀ s₀ := rfl
      _ = eval e₀ x₀ s₀ := by simp [fst, snd, eval_pair_equiv]
      _ = true := by simpa [h_v] using h_v

    · -- Zeitabschätzung
      have size_le : Nat.size (fst x₀) ≤ Nat.size x₀ := Nat.size_pair_le_left _ _
      calc
        s₀ ≤ 1 * (Nat.size x₀)^1 := h_t
        _ = Nat.size x₀ := by simp [Nat.pow_one, mul_one]
        _ ≥ Nat.size (fst x₀) := size_le
        _ = 1 * (Nat.size (fst x₀))^1 := by simp [Nat.pow_one, mul_one]

    -- Widerspruch per Fixpunkt
    have h_contra := (he₀ x₀).mp ⟨v₀, s₀, by simpa [h_v] using h_v, by simp⟩
    exact absurd h_contra h_ds

  · -- Fall B: ¬DetSolve ⇒ ¬Verif ⇒ Widerspruch
    have no_v : ¬ ∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
      intro ⟨y, s, h_v', h_t'⟩
      have ⟨s', d, t'⟩ := H₀.mp ⟨y, s, h_v', h_t'⟩
      exact h_ds ⟨s', d, t'⟩

    -- Anwenden der Negationsrichtung der Fixpunkt-Eigenschaft
    have no_v' := Iff.not_left (he₀ x₀) no_v

    -- Anwenden der Annahme auf (pair e₀ 0)
    have H' := H_eq (Nat.pair e₀ 0) 1 1 x₀

    -- Widerspruch erzeugen
    have ⟨y₂, s₂, h_v₂, h_t₂⟩ := Iff.mp H' no_v'
    exact no_v' ⟨y₂, s₂, h_v₂, h_t₂⟩

end PNP
