import PNP.DeltaSigma
import PNP.TM.Core
import PNP.EvalSemantics

namespace PNP

/-- Die Größe einer Zahl n ist die Anzahl der Bits, um n darzustellen -/
def Nat.size (n : Nat) : Nat :=
  if n = 0 then 1 else Nat.log 2 n + 1

/-- Verif(e, x, y, s) : e kann x mit Witness y in ≤ s Schritten verifizieren -/
def Verif (e x y s : Nat) : Prop :=
  evalPair e x y s = true

/-- Zeitbeschränkung p(n,s,c,k) := s ≤ c * n^k -/
def p (n s c k : Nat) : Prop :=
  s ≤ c * n ^ k

/-- Spezifikation zwischen evalPair und Verif ohne Zeitbedingung -/
theorem Verif.evalPair_spec {e u v s : Nat} :
  evalPair e u v s = true ↔ Verif e u v s := by
  -- Da Verif gerade genau evalPair ist, liefert unfold + rfl
  unfold Verif
  rfl

end PNP
