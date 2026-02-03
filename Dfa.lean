import Mathlib.Data.Set.Basic

structure DFA («Σ» : Type) (Q : Type) where
  q₀ : Q
  δ : Q → «Σ» → Q
  F : Set Q
