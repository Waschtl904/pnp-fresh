namespace PNP.TM

/-- Konfiguration einer Turing-Maschine (Platzhalter) -/
structure Config (e : Nat) (w : Nat) (seq : List Nat) (t : Nat) : Prop where
  valid : True         -- Korrektheit placeholder
  steps_le : t ≤ t     -- triviale Schranke

/-- AcceptRun(e, w, seq, s) : ∃ t ≤ s, Config(e,w,seq,t) -/
def AcceptRun (e w : Nat) (seq : List Nat) (s : Nat) : Prop :=
  ∃ t, Config e w seq t ∧ t ≤ s

end PNP.TM
