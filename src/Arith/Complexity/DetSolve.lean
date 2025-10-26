import PNP.DeltaSigma
import PNP.EvalSemantics
import PNP.TM.Core

namespace PNP

/-- DetSolve(e, x, c, k) : Es existiert ein Witness y und Laufzeit s ≤ c * |x|^k,
   so dass TM `e` Eingabe `pair x y` in ≤ s Schritten akzeptiert. -/
def DetSolve (e : TM.TMDesc) (x c k : Nat) : Prop :=
  ∃ y s, eval_TM e (pair x y) s = true ∧ s ≤ c * (x.size) ^ k

/-- Aus DetSolve folgt Existenz eines akzeptierenden Laufs -/
theorem DetSolve.exists_run {e : TM.TMDesc} {x c k}
    (h : DetSolve e x c k) :
  ∃ y s seq, AcceptRun e (pair x y) seq s ∧ s ≤ c * (x.size) ^ k := by
  rcases h with ⟨y, s, h_eval, h_bound⟩
  -- eval_TM e (pair x y) s = true ↔ ∃ seq, AcceptRun e (pair x y) seq s
  have h_eval_spec := Iff.mp (PNP.eval_spec_TM (e := e) (w := pair x y) (s := s)) h_eval
  choose seq h_acc using h_eval_spec
  exact ⟨y, s, seq, h_acc, h_bound⟩

/-- Umgekehrt: Ein akzeptierender Lauf liefert DetSolve -/
theorem DetSolve.of_run {e : TM.TMDesc} {x c k y s seq}
    (h_acc : AcceptRun e (pair x y) seq s)
    (h_bound : s ≤ c * (x.size) ^ k) :
  DetSolve e x c k := by
  use y, s
  constructor
  · -- eval_TM e (pair x y) s = true
    exact Iff.mpr (PNP.eval_spec_TM (e := e) (w := pair x y) (s := s)) (Exists.intro seq h_acc)
  · exact h_bound

end PNP
