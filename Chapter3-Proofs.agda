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
  
  sym
    : {A : Set} → {x y : A}
    → x ≡ y
    → y ≡ x
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
  
  trans
    : {A : Set} → {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
  trans (refl _) (refl _) = refl _
  
  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * zero
  a^1≡a+b*0 a b
    = trans (^-identityʳ a)
    (trans
      (sym (+-identityʳ a))
      (cong (λ φ → a + φ) (sym (*-zeroʳ b)))
    )
  
  a^1≡a+b*0′ : (a b : ℕ) → a ^ 1 ≡ a + b * zero
  a^1≡a+b*0′ a b
    = trans (^-identityʳ a)
    (trans
      (sym (+-identityʳ a))
      (cong (a +_) (sym (*-zeroʳ b)))
    )
  
  _! : ℕ → ℕ
  zero !  = 1
  suc n ! = suc n * n !
  
  infixr 20 ∣_

  ∣_ : ℕ → ℕ
  ∣_ = suc

  □ : ℕ
  □ = zero
  
  five : ℕ
  five = ∣ ∣ ∣ ∣ ∣ □

  infixr 20 _‽_⦂_
  
  _‽_⦂_ : {A : Set} → Bool → A → A → A
  false ‽ t ⦂ f = f
  true  ‽ t ⦂ f = t
  
  _ : ℕ
  _ = not true ‽ 4 ⦂ 1

  infixr 20 if_then_else_
  
  if_then_else_ : {A : Set} → Bool → A → A → A
  if_then_else_ = _‽_⦂_
  
  _ : ℕ
  _ = if not true then 4 else 1
  
  _ : ℕ
  _ =
    if not true
      then 4
    else if true
      then 1
    else
      0
  
  case_of_ : {A B : Set} → A → (A → B) → B
  case e of f = f e
  
  _ : ℕ
  _ =
    case not true of λ
      { false → 1
      ; true  → 4
      }
  
  _is-equal-to_ : {A : Set} → A → A → Set
  x is-equal-to y = x ≡ y
  
  module ≡-Reasoning where
  
    infix 3 _∎
    infixr 2 _≡⟨⟩_
    infixr 2 _≡⟨_⟩_
    infix 1 begin_
    
    _∎ : {A : Set} → (x : A) → x ≡ x
    x ∎ = refl x
    
    _≡⟨⟩_
      : {A : Set} {y : A}
      → (x : A)
      → x ≡ y
      → x ≡ y
    x ≡⟨⟩ p = p
    
    _ : 4 ≡ suc (1 + 2)
    _ =
      4           ≡⟨⟩
      2 + 2       ≡⟨⟩
      suc 1 + 2   ≡⟨⟩
      suc (1 + 2) ∎

    _≡⟨_⟩_
      : {A : Set} {y z : A}
      → (x : A)
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ j ⟩ p = trans j p

    begin_
      : {A : Set} {x y : A}
      → x ≡ y
      → x ≡ y
    begin_ p = p
    
  a^1≡a+b*0′′ : (a b : ℕ) → a ^ 1 ≡ a + b * zero
  a^1≡a+b*0′′ a b = begin
    a ^ 1     ≡⟨ ^-identityʳ a ⟩
    a         ≡⟨ sym (+-identityʳ a) ⟩
    a + 0     ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
    a + b * 0 ∎
    where open ≡-Reasoning
  
  ∨-assoc
    : (a b c : Bool)
    → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl (b ∨ c)
  ∨-assoc true  b c = refl true
  
  ∧-assoc
    : (a b c : Bool)
    → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl false
  ∧-assoc true  b c = refl (b ∧ c)
  
  +-assoc
    : (x y z : ℕ)
    → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z    = refl (y + z)
  +-assoc (suc x) y z = begin
    suc x + y + z     ≡⟨⟩
    suc (x + y + z)   ≡⟨ cong suc (+-assoc x y z) ⟩
    suc (x + (y + z)) ≡⟨⟩
    suc x + (y + z)   ∎
    where open ≡-Reasoning
  
  +-suc
    : (x y : ℕ)
    → x + suc y ≡ suc (x + y)
  +-suc zero    y = refl (suc y)
  +-suc (suc x) y = cong suc (+-suc x y)
  
  +-comm
    : (x y : ℕ)
    → x + y ≡ y + x
  +-comm zero    y = sym (+-identityʳ y)
  +-comm (suc x) y = begin
    suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x) ≡⟨ sym (+-suc y x) ⟩
    y + suc x ∎
    where open ≡-Reasoning
  