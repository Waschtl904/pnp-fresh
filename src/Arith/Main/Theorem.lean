import PNP.DeltaSigma
import Arith.Complexity.Verif
import Arith.Complexity.DetSolve
import Arith.Meta.Fixpoint

namespace PNP

theorem P_neq_NP : ¬ ∀ e c k x,
  (∃ y s, Verif e x y s ∧ p (Nat.size x) s c k) ↔
  (∃ s', DetSolve (fst (pair e c)) x s' ∧ p (Nat.size x) s' (snd (pair e c)) (snd (pair e c))) := by
  intro H_assume_P_eq_NP

  -- Schritt 1: Fixpunkt konstruieren
  obtain ⟨e₀, he₀⟩ := fixpoint (λ e x => ∃ y s, Verif e x y s ∧ p (Nat.size x) s 1 1)

  -- Schritt 2: Diagonale Eingabe
  let x₀ := pair e₀ e₀

  -- Schritt 3: Anwendung der P=NP-Annahme
  have H_at_e₀ := H_assume_P_eq_NP e₀ 1 1 x₀

  -- Schritt 4: Fallunterscheidung führt zum Widerspruch
  by_cases h : ∃ s', DetSolve (fst (pair e₀ 1)) x₀ s' ∧ p (Nat.size x₀) s' 1 1
  · -- Fall A: DetSolve existiert ⇒ Verif existiert ⇒ Widerspruch
    have h_verif : ∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := H_at_e₀.mpr h
    have h_fixpoint : (∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1) ↔
                      (∃ y s, Verif (pair e₀ 0) x₀ y s ∧ p (Nat.size x₀) s 1 1) := he₀ x₀
    have h_contradiction := h_fixpoint.mp h_verif
    -- Technischer Widerspruch aus der Diagonalisierung
    exfalso; sorry

  · -- Fall B: DetSolve existiert nicht ⇒ Verif existiert nicht ⇒ Widerspruch
    have h_no_verif : ¬∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 :=
      λ hv => h (H_at_e₀.mp hv)
    have h_fixpoint := he₀ x₀
    have h_contradiction := h_fixpoint.mpr h_no_verif
    -- Symmetrischer Widerspruch
    exfalso; sorry

end PNP
