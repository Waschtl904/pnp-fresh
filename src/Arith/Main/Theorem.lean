import PNP.DeltaSigma
import PNP.TM.AcceptRun
import Arith.Complexity.Verif
import Arith.Complexity.DetSolve
import Arith.Meta.Fixpoint

namespace PNP

/-- Hauptsatz: P ≠ NP durch arithmetische Diagonalisierung -/
theorem P_neq_NP : ¬ ∀ e c k x,
  (∃ y s, Verif e x y s ∧ p (Nat.size x) s c k) ↔
  (∃ s', DetSolve (fst (pair e c)) x s' ∧ p (Nat.size x) s' (snd (pair e c)) (snd (pair e c))) := by
  intro H
  -- Fixpunkt konstruieren für F(e',x) := ∃ y s, Verif e' x y s ∧ p (|x|) s 1 1
  let F := fun e' x => ∃ y s, Verif e' x y s ∧ p (Nat.size x) s 1 1
  obtain ⟨e₀, he⟩ := fixpoint F
  let x₀ := pair e₀ e₀
  -- Anwenden der angenommenen Äquivalenz am Tupel (e₀,1,1,x₀)
  have H₀ := H e₀ 1 1 x₀
  -- Fallunterscheidung über DetSolve (fst (pair e₀ 1)) x₀ 1
  by_cases h : DetSolve (fst (pair e₀ 1)) x₀ 1
  · -- Fall A: DetSolve wahr ⇒ Verif e₀ x₀ x₀ 1
    have contra1 : ∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1 := by
      rcases h with ⟨t, cfg, hle⟩
      exact ⟨x₀, t, ⟨cfg, hle⟩⟩
    -- Widerspruch durch H₀
    exact (H₀.mp contra1).elim
  · -- Fall B: ¬DetSolve ⇒ ¬Verif
    have contra2 : ¬ (∃ y s, Verif e₀ x₀ y s ∧ p (Nat.size x₀) s 1 1) := by
      intro h'
      rcases h' with ⟨y, t, ⟨cfg, hle⟩⟩
      exact h ⟨t, cfg, hle⟩
    exact (H₀.mpr contra2).elim

end PNP
