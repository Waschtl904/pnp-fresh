import PNP.DeltaSigma
import PNP.TM.Core

namespace PNP.TM

/-- Encode a Turing machine description as a natural number.
    For a TM with s states, a alphabet symbols, we encode the transition table
    as a list of numbers where each transition (state, symbol) -> (new_state, new_symbol, direction)
    is encoded as a triple and then paired together. -/
def encodeTM (tm : TMDesc) : Nat :=
  let states := tm.states
  let alphabet := tm.alphabet
  -- For each state-symbol pair, encode the transition triple
  let transitions : List Nat :=
    (List.range states).flatMap fun state =>
      (List.range alphabet).map fun symbol =>
        let (new_state, new_symbol, direction) := tm.transition state symbol
        -- Encode the triple (new_state, new_symbol, direction) as a single number
        -- using a pairing function: pair (pair new_state new_symbol) direction
        pair (pair new_state new_symbol) direction

  -- Now encode the list of transition encodings into a single number
  -- We'll use a simple encoding: pair the number of transitions with the product of all transition codes
  let num_transitions := transitions.length
  let transition_product := transitions.foldl (· * ·) 1

  -- Final encoding: pair states, alphabet, and transition data
  pair (pair states alphabet) (pair num_transitions transition_product)

end PNP.TM
