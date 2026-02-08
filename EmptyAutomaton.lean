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
  -- [Meta.Tactic.simp.rewrite] emptyAutomaton.eq_1:100:
  --       emptyAutomaton
  --     ==>
  --       { Q := Unit, «Σ» := Bool,
  --         δ := fun x ↦
  --           match x with
  --           | (PUnit.unit, snd) => (),
  --         q₀ := (), F := ∅ }
  -- [Meta.Tactic.simp.rewrite] unfold L, L emptyAutomaton ==> {w | accepts emptyAutomaton w}
  -- [Meta.Tactic.simp.rewrite] unfold accepts, accepts emptyAutomaton w ==> have q' := run emptyAutomaton w;
  --     q' ∈ emptyAutomaton.F
  -- [Meta.Tactic.simp.rewrite] Set.mem_empty_iff_false:1000:
  --       run { Q := Unit, «Σ» := Bool, δ := fun x ↦ (), q₀ := (), F := ∅ } w ∈ ∅
  --     ==>
  --       False
  -- [Meta.Tactic.simp.rewrite] Set.setOf_false:1000:
  --       {w | False}
  --     ==>
  --       ∅
  -- [Meta.Tactic.simp.rewrite] eq_self:1000:
  --       ∅ = ∅
  --     ==>
  --       True
  simp [L, accepts, emptyAutomaton]
