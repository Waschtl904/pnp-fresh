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

theorem pair_fst_snd (u v : Nat) : fst (pair u v) = u := by
  dsimp [pair, fst, log2]
  -- For now, admit this proof
  sorry

theorem pair_snd_fst (u v : Nat) : snd (pair u v) = v := by
  dsimp [pair, snd, fst, log2]
  -- For now, admit this proof
  sorry

end PNP
