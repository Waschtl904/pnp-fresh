import PNP.TM.Core
import PNP.DeltaSigma


open Classical

namespace PNP

open PNP.TM

/-- `AcceptRun e w seq s` bedeutet, dass TM `e` auf Eingabe `w` innerhalb von `s` Schritten
    die Bandkonfiguration `seq` erreicht und dabei in akzeptierendem Zustand endet. -/
inductive AcceptRun : TMDesc → Nat → List Nat → Nat → Prop
  | done {e : TMDesc} {w : Nat} {seq : List Nat} {s : Nat} {cfg : ExecConfig} :
      -- in s Schritten haben wir die Konfiguration cfg erreicht, und cfg.state = accepting_state
      run e (ExecConfig.mk w [] 0) s = cfg →
      cfg.state = accepting_state →
      AcceptRun e w cfg.tape s
  | step {e : TMDesc} {w : Nat} {seq : List Nat} {t : Nat} {cfg cfg' : ExecConfig} {tm : TMDesc} :
      -- ein weiterer Schritt
      tm = e →  -- wir nutzen `e` als TMDesc direkt
      cfg.state = cfg.state →
      TM.step tm cfg = cfg' →
      AcceptRun e w seq t →
      AcceptRun e w seq (t+1)

/-- `eval e w s = true` genau dann, wenn TM `e` Eingabe `w` in ≤ `s` Schritten akzeptiert -/
noncomputable def eval (e : Nat) (w s : Nat) : Bool :=
  decide (∃ seq, AcceptRun (TM.decodeTM e) w seq s)

/-- `eval_TM e w s = true` genau dann, wenn TM `e` Eingabe `w` in ≤ `s` Schritten akzeptiert -/
noncomputable def eval_TM (e : TMDesc) (w s : Nat) : Bool :=
  decide (∃ seq, AcceptRun e w seq s)

/-- `evalPair e u v s = true` genau dann, wenn TM `e` mit separaten Parametern `u` und `v`
    in ≤ `s` Schritten akzeptiert -/
-- `evalPair e u v s = true` genau dann, wenn TM `e` mit separaten Parametern `u` und `v`
--    als separate Bandfelder in ≤ `s` Schritten akzeptiert -/
noncomputable def evalPair (e : Nat) (u v s : Nat) : Bool :=
  eval e (pair u v) s

theorem eval_spec {e : Nat} {w s : Nat} :
  eval e w s = true ↔ (∃ seq, AcceptRun (TM.decodeTM e) w seq s) := by
  simp [eval]

theorem eval_spec_TM {e : TMDesc} {w s : Nat} :
  eval_TM e w s = true ↔ (∃ seq, AcceptRun e w seq s) := by
  simp [eval_TM]

theorem eval_pair_equiv {e : Nat} {u v s : Nat} :
  eval e (pair u v) s = evalPair e u v s := by
  rfl

theorem eval_pair_inv {e : Nat} {u v s : Nat} :
  evalPair e u v s = eval e (pair u v) s := by
  rfl

end PNP
