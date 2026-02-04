import Mathlib.Data.Set.Basic

structure DFA where
  Q : Type
  «Σ» : Type
  δ : (Q × «Σ») → Q
  q₀ : Q
  F : Set Q
