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
  x+0≡x 0       = refl 0
  x+0≡x (suc x) = cong suc (x+0≡x x)
  
  +-identityˡ : (x : ℕ) → 0 + x ≡ x
  +-identityˡ = 0+x≡x

  +-identityʳ : (x : ℕ) → x + 0 ≡ x
  +-identityʳ = x+0≡x
  
  *-identityˡ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ = +-identityʳ
  
  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ 0       = refl 0
  *-identityʳ (suc x) = cong suc (*-identityʳ x)
  
  ∸-identityʳ : (x : ℕ) → x ∸ 0 ≡ x
  ∸-identityʳ x = refl x
  
  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x
  ^-identityʳ 0       = refl 0
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)
  
  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ x = refl x

  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false = refl false
  ∨-identityʳ true  = refl true
  
  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ x = refl x
  
  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ false = refl false
  ∧-identityʳ true  = refl true
  
  *-zeroˡ : (x : ℕ) → 0 * x ≡ 0
  *-zeroˡ x = refl 0

  *-zeroʳ : (x : ℕ) → x * 0 ≡ 0
  *-zeroʳ 0       = refl 0 
  *-zeroʳ (suc x) = *-zeroʳ x
  
  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ x = refl true
  
  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl true
  ∨-zeroʳ true  = refl true
  
  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ x = refl false

  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ false = refl false
  ∧-zeroʳ true  = refl false
  
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym (refl _) = refl _
  
  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x
  *-identityˡ′ _ = sym (*-identityˡ _)
  
  sym-involutive
    : {A : Set} → {x y : A}
    → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive (refl _) = refl _
  
  not-ininvolutive : (x : Bool) → not (not x) ≡ x
  not-ininvolutive false = refl false
  not-ininvolutive true = refl true
  