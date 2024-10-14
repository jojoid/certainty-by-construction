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
  n=0? zero    = true
  n=0? (suc x) = false
  
  n=2? : ℕ → Bool
  n=2? (suc (suc zero)) = true
  n=2? _                = false
  
  even? : ℕ → Bool
  even? zero          = true
  even? (suc zero)    = false
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
  evenOdd zero-even        = one-odd
  evenOdd (suc-suc-even x) = suc-suc-odd (evenOdd x)
  
  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing :     Maybe A
  
  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero       = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x      = just (suc-suc-even x)
  ... | nothing     = nothing
  
  infixl 6 _+_

  _+_ : ℕ → ℕ → ℕ
  zero  + y = y
  suc x + y = suc (x + y)

  module Example-Silly where
    open Chapter1-Agda
      using (Bool; true; false; not)
    
    data ℕ′ : Set where
      zero : ℕ′
      suc  : ℕ′ → ℕ′
      2suc : ℕ′ → ℕ′
    
    even?′ : ℕ′ → Bool
    even?′ zero            = true
    even?′ (suc n)         = not (even?′ n)
    even?′ (2suc zero)     = true
    even?′ (2suc (suc n))  = not (even?′ n)
    even?′ (2suc (2suc n)) = even?′ n
  
  infixl 7 _*_
  
  _*_ : ℕ → ℕ → ℕ
  zero  * b  = zero
  suc a * b = b + a * b
  
  _^_ : ℕ → ℕ → ℕ
  a ^ zero  = one
  a ^ suc b = a * a ^ b
  
  _∸_ : ℕ → ℕ → ℕ
  x     ∸ zero      = x
  zero  ∸ suc y  = zero
  suc x ∸ suc y = x ∸ y

module Misstep-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)
  
  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ
  
  normalize : ℤ → ℤ
  normalize (mkℤ zero y)          = mkℤ zero y
  normalize (mkℤ (suc x) zero)    = mkℤ (suc x) zero
  normalize (mkℤ (suc x) (suc y)) = mkℤ x y
  
  infixl 5 _+_

  _+_ : ℤ → ℤ → ℤ
  mkℤ pos neg + mkℤ pos₁ neg₁
    = normalize (mkℤ (pos ℕ.+ pos₁) (neg ℕ.+ neg₁))
  
  infixl 5 _-_

  _-_ : ℤ → ℤ → ℤ
  mkℤ pos neg - mkℤ pos₁ neg₁
    = normalize (mkℤ (pos ℕ.+ neg₁) (neg ℕ.+ pos₁))
  
  _*_ : ℤ → ℤ → ℤ
  mkℤ pos neg * mkℤ pos₁ neg₁
    = normalize
        (mkℤ (pos ℕ.* pos₁ ℕ.+ neg ℕ.* neg₁)
             (pos ℕ.* neg₁ ℕ.+ pos₁ ℕ.* neg))

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)
  
  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ
  
  pattern [1+_] n  = ℕ.suc n
  pattern +[0]     = + 0
  pattern -[0]     = + 0
  pattern +[1]     = + 1
  pattern -[1]     = -[1+ 0 ]
  pattern +[1+_] n = + [1+ n ]
  pattern +[2+_] n = +[1+ [1+ n ] ]
  pattern -[2+_] n = -[1+ [1+ n ] ]
  
  -_ : ℤ → ℤ
  - +[0]     = -[0]
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]
  
  suc : ℤ → ℤ
  suc +[0]     = +[1]
  suc +[1+ x ] = +[2+ x ]
  suc -[1+ x ] = - (+ x)
  
  pred : ℤ → ℤ
  pred +[0]     = -[1]
  pred +[1+ x ] = + x  
  pred -[1+ x ] = -[2+ x ]
  
  _⊖_ : ℕ → ℕ → ℤ
  0       ⊖ 0       = +[0]
  0       ⊖ [1+ n ] = -[1+ n ]
  [1+ n ] ⊖ 0       = +[1+ n ]
  [1+ m ] ⊖ [1+ n ] = m ⊖ n
  
  infixl 5 _+_

  _+_ : ℤ → ℤ → ℤ
  + x      + + y      = + (x ℕ.+ y)
  + x      + -[1+ y ] = x ⊖ [1+ y ]
  -[1+ x ] + + y      = y ⊖ [1+ x ]
  -[1+ x ] + -[1+ y ] = -[2+ x ℕ.+ y ]
  
  infixl 5 _-_

  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)
  
  infixl 6 _*_

  _*_ : ℤ → ℤ → ℤ
  x * +[0]      = +[0]
  x * +[1+ 0 ]  = x
  x * -[1+ 0 ]  = - x
  x * +[2+ x₁ ] = +[1+ x₁ ] * x + x
  x * -[2+ x₁ ] = -[1+ x₁ ] * x - x

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public
open Sandbox-Naturals
  using (one; two; three; four)
  public
open Sandbox-Naturals
  using (IsEven)
  renaming ( zero-even    to z-even
           ; suc-suc-even to ss-even
           )
  public
open import Data.Maybe
  using (Maybe; just; nothing)
  public
