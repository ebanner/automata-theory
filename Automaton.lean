import Mathlib.Data.Set.Basic

set_option trace.Meta.Tactic.simp.rewrite true

structure Automaton where
  Q : Type
  «Σ» : Type
  δ : (Q × «Σ») → Q
  q₀ : Q
  F : Set Q

def run (M : Automaton) (w : List M.«Σ») : M.Q :=
  let rec loop (q : M.Q) : List M.«Σ» → M.Q
  | []      => q
  | a :: w  => loop (M.δ (q, a)) w

  loop M.q₀ w

def accepts (M : Automaton) (w : List M.«Σ») : Prop :=
  let q' := run M w
  q' ∈ M.F

def L (M : Automaton) : Set (List M.«Σ») :=
  { w | accepts M w }
