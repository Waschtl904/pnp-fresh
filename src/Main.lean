import Mathlib.Data.Nat.Basic  -- mathlib⁴-Grundlagen
import Mathlib.Data.Nat.Sqrt   --

namespace PNP

/-- Paarungsfunktion: ⟨u,v⟩ = 2^u * (2*v + 1) - 1 -/
def pair (u v : Nat) : Nat :=
  (2 ^ u) * (2 * v + 1) - 1

/-- Basic logarithm function - finds largest k such that 2^k ≤ n -/
def log2 (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else
    let rec find_log (m : Nat) : Nat :=
      if m ≤ 1 then 0
      else 1 + find_log (m / 2)
    find_log n

/-- Projektionsfunktionen π₁ und π₂ für die Paarung -/
def fst (z : Nat) : Nat :=
  log2 (z + 1)

def snd (z : Nat) : Nat :=
  let u := fst z
  ((z + 1) / (2 ^ u) - 1) / 2

namespace TM

end TM

end PNP

def main : IO Unit := do
  -- Test PNP functions
  let p := PNP.pair 3 5
  IO.println s!"Pair of 3 and 5 is {p}"
  let f := PNP.fst p
  let s := PNP.snd p
  IO.println s!"First: {f}, Second: {s}"

  -- Test TM functions
  -- Removed duplicate Config usage since it's now in PNP.TM.Core
  IO.println "Hello, PNP!"
