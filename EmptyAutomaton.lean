import Automaton

set_option trace.Meta.Tactic.simp.rewrite true

def emptyAutomaton : Automaton :=
{
  Q := Unit,
  «Σ» := Bool,
  δ := fun ((), _) => (),
  q₀ := (),
  F := ∅
}

theorem emptyAutomaton_language_is_the_empty_set : L emptyAutomaton = ∅ := by
  simp [L, accepts, emptyAutomaton]
