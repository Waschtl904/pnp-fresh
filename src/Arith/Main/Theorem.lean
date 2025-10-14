import Mathlib.Data.Nat.Basic
import PNP.DeltaSigma
import PNP.TM.Core
import Arith.Complexity.Verif
import Arith.Complexity.DetSolve
import PNP.Fixpoint

namespace PNP

theorem P_neq_NP :
  ¬ ∀ e c k x,
    (∃ y s, Verif e x y s ∧ p (Nat.size x) s c k) ↔
    (∃ s', DetSolve (fst (pair e c)) x s' ∧ p (Nat.size x) s' (snd (pair e c)) (snd (pair e c))) := by
  intro H_eq

  -- Fixpunkt für c = k = 1
  obtain ⟨e₀, he₀⟩ := fixpoint
    (λ e x => ∃ y s, Verif e (fst x) y s ∧ p (Nat.size (fst x)) s 1 1)
    Fix.evalPair_spec

  let x₀ := pair e₀ e₀
  have H₀ := H_eq e₀ 1 1 x₀

  by_cases h_ds : ∃ s', DetSolve (fst (pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' (snd (pair e₀ 1)) (snd (pair e₀ 1))
  · -- Fall A: DetSolve existiert ⇒ Verif existiert ⇒ Fixpunkt ⇒ Widerspruch
    have h_v : ∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
      have h_ds_adj : ∃ s', DetSolve (fst (pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' 1 1 := by
        obtain ⟨s', h_det, h_time⟩ := h_ds
        use s'
        constructor
        · exact h_det
        · -- Umwandlung von snd (pair e₀ 1) = 1 zu 1
          simpa [snd_pair] using h_time
      exact H₀.mpr h_ds_adj
    have h_v' := (he₀ x₀).mp h_v
    have h_ds' : ∃ s', DetSolve (fst (pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' (snd (pair e₀ 1)) (snd (pair e₀ 1)) := by
      have H' := H_eq (pair e₀ 0) 1 1 x₀
      have h_v'_adj : ∃ y s, Verif (pair e₀ 0) x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
        simpa [fst_pair] using h_v'
      have h_ds_raw := H'.mpr h_v'_adj
      -- Umwandlung zurück zu snd (pair e₀ 1) Format
      obtain ⟨s', h_det, h_time⟩ := h_ds_raw
      use s'
      constructor
      · simpa [fst_pair] using h_det
      · simpa [snd_pair] using h_time
    exact absurd h_ds' h_ds

  · -- Fall B: ¬DetSolve ⇒ ¬Verif ⇒ Fixpunkt ⇒ Widerspruch
    have no_v : ¬∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
      intro hv
      have h_ds_adj : ∃ s', DetSolve (fst (pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' (snd (pair e₀ 1)) (snd (pair e₀ 1)) := by
        have h_ds_raw := H₀.mp hv
        obtain ⟨s', h_det, h_time⟩ := h_ds_raw
        use s'
        constructor
        · exact h_det
        · simpa [snd_pair] using h_time
      exact h_ds h_ds_adj
    have no_v' := (he₀ x₀).not_left.mp no_v
    have contra : ∃ y s, Verif (pair e₀ 0) x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
      have H' := H_eq (pair e₀ 0) 1 1 x₀
      simpa [fst_pair] using H'.mp no_v'
    exact no_v' contra

end PNP
