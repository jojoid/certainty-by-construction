module Chapter4-Relations where

open import Chapter1-Agda
  using (Bool; false; true; not; _×_)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs

_ : Set₁
_ = Set

_ : Set₂
_ = Set₁

_ = Set₉₈₆₀₂₅₀

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)

module Playground-Level where

  data Maybe₀ (A : Set) : Set where
    just₀    : A → Maybe₀ A
    nothing₀ : Maybe₀ A
  
  data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
    just₁    : A → Maybe₁ A
    nothing₁ : Maybe₁ A
  
  _ = just₁ ℕ
  
  private variable
    ℓ : Level
  
  data Maybe₂ (A : Set ℓ) : Set ℓ where
    just₂    : A → Maybe₂ A
    nothing₂ : Maybe₂ A

module Definition-DependentPair where

  open Chapter3-Proofs
  
  record Σ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : A → Set ℓ₂)
    : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁
  
  ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , PropEq.refl

open import Data.Product
  using (Σ; _,_)

module Sandbox-Relations where

  REL : {a b : Level} → Set a → Set b → (ℓ : Level)
    → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ

  data _maps_↦_ {a b : Level} {A : Set a} {B : Set b} : (A → B) → REL A B (a ⊔ b) where
    app : {f : A → B} {x : A} → f maps x ↦ f x
  
  _ : not maps false ↦ true
  _ = app
  
  _ : not maps true ↦ false
  _ = app
  
  Functional : {a b : Level} {A : Set a} {B : Set b}
    → (REL A B (a ⊔ b))
    → Set (a ⊔ b)
  Functional {A = A} {B = B} _~_
    = {x : A} {y z : B} → x ~ y → x ~ z → y ≡ z
  
  Total : {a b : Level} {A : Set a} {B : Set b}
    → (REL A B (a ⊔ b))
    → Set (a ⊔ b)
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (λ y → x ~ y)
  
  relToFn : {a b : Level} {A : Set a} {B : Set b}
    → (_~_ : REL A B (a ⊔ b))
    → Functional _~_
    → Total _~_
    → A
    → B
  relToFn _~_ _ total x
    with total x
  ... | y , _ = y
  
  Rel : {a : Level}
    → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ
  
  module Example₂ where

    data _≡₂_ {a : Level} {A : Set a} : Rel A a where
      refl : {x : A} → x ≡₂ x
  
  Reflexive : {a ℓ : Level} {A : Set a}
    → Rel A ℓ → Set (a ⊔ ℓ)
  Reflexive {A = A} _~_
    = {x : A} → x ~ x
  
  Symmetric : {a ℓ : Level} {A : Set a}
    → Rel A ℓ → Set (a ⊔ ℓ)
  Symmetric {A = A} _~_
    = {x y : A} → x ~ y → y ~ x
  
  Transitive : {a ℓ : Level} {A : Set a}
    → Rel A ℓ → Set (a ⊔ ℓ)
  Transitive {A = A} _~_
    = {x y z : A} → x ~ y → y ~ z → x ~ z

open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric)

module Naive-≤₁ where
  
  infix 4 _≤_
  
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  
  _ : 2 ≤ 5
  _ = lte 2 3
  
  suc-mono : {x y : ℕ}
    → x ≤ y
    → suc x ≤ suc y
  suc-mono (lte x b) = lte (suc x) b
  
  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = lte 0 0 
  ≤-refl {suc x}
    with ≤-refl {x}
  ... | x≤x = suc-mono x≤x
  
  open Chapter3-Proofs
    using (+-identityʳ)
  
  subst : {a ℓ : Level} {A : Set a} {x y : A}
    → (P : A → Set ℓ)
    → x ≡ y
    → P x
    → P y
  subst P PropEq.refl px = px

  ≤-refl′ : Reflexive _≤_
  ≤-refl′ {x} = subst (λ φ → x ≤ φ) (+-identityʳ x) (lte x 0)
  