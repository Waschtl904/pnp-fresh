import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic
import PNP.TM.Core

namespace PNP

open PNP.TM

/-- `eval e w s = true` genau dann, wenn TM `e` Eingabe `w` in ≤ `s` Schritten akzeptiert -/
-- Wir postulieren eval als grundlegende undefinierte Funktion
axiom eval : Nat → Nat → Nat → Bool

/-- Spezifikation: eval e w s = true genau dann, wenn die TM e die Eingabe w in ≤ s Schritten akzeptiert -/
axiom eval_spec (e w s : Nat) :
  eval e w s = true ↔ ∃ seq, AcceptRun e w seq s

end PNP
