import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic
import PNP.TM.Core
import PNP.DeltaSigma

namespace PNP

open PNP.TM

/-- `eval e w s = true` genau dann, wenn TM `e` Eingabe `w` in ≤ `s` Schritten akzeptiert -/
axiom eval : Nat → Nat → Nat → Bool

/-- `evalPair e u v s = true` genau dann, wenn TM `e` mit separaten Parametern `u` und `v` in ≤ `s` Schritten akzeptiert -/
axiom evalPair : Nat → Nat → Nat → Nat → Bool

/-- Spezifikation: eval e w s = true genau dann, wenn die TM e die Eingabe w in ≤ s Schritten akzeptiert -/
axiom eval_spec (e w s : Nat) :
  eval e w s = true ↔ ∃ seq, AcceptRun e w seq s

/-- eval und evalPair sind äquivalent für gepaarte Eingaben -/
theorem eval_pair_equiv {e u v s} : eval e (pair u v) s = evalPair e u v s := by
  sorry

/-- Umgekehrte Richtung der eval-evalPair-Äquivalenz -/
theorem eval_pair_inv {e u v s} : evalPair e u v s = eval e (pair u v) s := by
  rw [eval_pair_equiv]

end PNP
