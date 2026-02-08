import Automaton

set_option trace.Meta.Tactic.simp.rewrite true

def M : Automaton :=
{
  Q := Unit,
  «Σ» := Bool,
  δ := fun ((), _) => (),
  q₀ := (),
  F := ∅
}

theorem language_of_M_is_the_empty_set : L M = ∅ := by
  -- [Meta.Tactic.simp.rewrite] M.eq_1:100:
  --       M
  --     ==>
  --       { Q := Unit, «Σ» := Bool,
  --         δ := fun x ↦
  --           match x with
  --           | (PUnit.unit, snd) => (),
  --         q₀ := (), F := ∅ }
  -- [Meta.Tactic.simp.rewrite] unfold L, L M ==> {w | accepts M w}
  -- [Meta.Tactic.simp.rewrite] unfold accepts, accepts M w ==> have q' := run M w;
  --     q' ∈ M.F
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
  simp [L, accepts, M]
