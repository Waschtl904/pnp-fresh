namespace PNP.TM

/-- Konfiguration einer Turing-Maschine -/
structure Config (e : Nat) (w : Nat) (seq : List Nat) (t : Nat) : Prop where
  valid : True -- Platzhalter für TM-Korrektheit
  steps_le : t ≤ t -- triviale Schranke

/-- AcceptRun(e, w, seq, s) : es existiert t ≤ s, sodass Config(e, w, seq, t) -/
def AcceptRun (e w : Nat) (seq : List Nat) (s : Nat) : Prop :=
  ∃ t, Config e w seq t ∧ t ≤ s

end PNP.TM
