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
  
  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three
  
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
  
  data IsEven : ℕ → Set where
    zero-even    : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))
  
  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)
  
  data IsOdd : ℕ → Set where
    one-odd     : IsOdd one
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))
  
  data IsOdd′ : ℕ → Set where
    is-odd : {n : ℕ} → IsEven n → IsOdd′ (suc n)
  
  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even = one-odd
  evenOdd (suc-suc-even x) = suc-suc-odd (evenOdd x)
  
  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing :     Maybe A
  
  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x = just (suc-suc-even x)
  ... | nothing = nothing
  
  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)
  
  infixl 6 _+_
  