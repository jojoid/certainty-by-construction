module Chapter3-Proofs where
open import Chapter1-Agda
  using (Bool; true; false; _∨_; _∧_; not)
open import Chapter2-Numbers
  using (ℕ; zero; suc)

module Definition where
  
  infix 4 _≡_

  data _≡_ {A : Set} : A → A → Set where
    refl : (x : A) → x ≡ x

module Playground where
  open Definition
  open Chapter2-Numbers
  
  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl 3
  
  _ : three ≡ suc (suc (suc zero))
  _ = refl 3
  
  _ : 3 ≡ 1 + 2
  _ = refl three
  
  0+x≡x : (x : ℕ) → 0 + x ≡ x
  0+x≡x = refl
  
  cong
    : {A B : Set}
    → {x y : A}
    → (f : A → B)
    → x ≡ y
    → f x ≡ f y
  cong f (refl _) = refl (f _)
  
  x+0≡x : (x : ℕ) → x + 0 ≡ x
  x+0≡x zero = refl 0
  x+0≡x (suc x) = cong suc (x+0≡x x)
  