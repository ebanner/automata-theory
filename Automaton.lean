import Mathlib.Data.Set.Basic

set_option trace.Meta.Tactic.simp.rewrite true

structure Automaton where
  Q : Type
  «Σ» : Type
  δ : (Q × «Σ») → Q
  q₀ : Q
  F : Set Q

def emptyAutomaton : Automaton :=
{
  Q := Unit,
  «Σ» := Bool,
  δ := fun ((), _) => (),
  q₀ := (),
  F := ∅
}

def run (M : Automaton) : M.Q → List M.«Σ» → M.Q
| q, []      => q
| q, a :: w  => let q' := M.δ (q, a)
                run M q' w

-- def run (M : DFA) : M.Q → List M.«Σ» → M.Q
-- | q, []      => q
-- | q, a :: w  => run M (M.δ (q, a)) w

-- def run₂ (M : DFA) : (M.Q × List M.«Σ») → M.Q
-- | (q, [])      => q
-- | (q, a :: w)  => run₂ M (M.δ (q, a), w)

-- def run (M : DFA) (q : M.Q) (w : List M.«Σ») : M.Q :=
-- match w with
-- | []      => q
-- | a :: w  => run M (M.δ (q, a)) w

-- def accepts (M : DFA) (w : List M.«Σ») : Prop :=
--   run M M.q₀ w ∈ M.F

def accepts (M : Automaton) (w : List M.«Σ») : Prop :=
  let q' := run M M.q₀ w
  q' ∈ M.F

theorem emptyAutomaton_rejects_all :
  ∀ w, ¬ accepts emptyAutomaton w := by
    intro w
    -- accepts emptyAutomaton w unfolds to (run ... ∈ emptyAutomaton.F),
    -- and emptyAutomaton.F is ∅, so it's impossible.
    simp [accepts, emptyAutomaton]

-- #check run emptyAutomaton

-- #check accepts emptyAutomaton

-- #check emptyAutomaton_rejects_all

-- #print Set.not_mem_empty

def L (M : Automaton) : Set (List M.«Σ») :=
  { w | accepts M w }

theorem emptyAutomaton_language_is_the_empty_set :
  L emptyAutomaton = ∅ := by
    -- ext w: prove set equality by proving membership equivalence for an arbitrary w
    ext w
    -- goal becomes: (w ∈ L emptyAutomaton) ↔ (w ∈ ∅)
    -- i.e. accepts emptyAutomaton w ↔ False
    simp [L, accepts, emptyAutomaton]
