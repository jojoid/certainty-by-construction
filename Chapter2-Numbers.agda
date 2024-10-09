module Chapter2-Numbers where
import Chapter1-Agda

module Definition-Naturals where
  
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)
  open Chapter1-Agda
    using (Bool; true; false)
  
  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false
  
  n=2? : ℕ → Bool
  n=2? (suc (suc zero)) = true
  n=2? _ = false
  
  even? : ℕ → Bool
  even? zero = true
  even? (suc zero) = false
  even? (suc (suc x)) = even? x
  