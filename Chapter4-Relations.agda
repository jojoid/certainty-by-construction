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

  data Unrelated {a b : Level} {A : Set a} {B : Set b} : REL A B lzero where
  
  data Related {A : Set} {B : Set} : REL A B lzero where
    related : {x : A} {y : B} → Related x y
  
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
  
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  infix 4 _≤_
  
  _ : 2 ≤ 5
  _ = lte 2 3
  
  suc-mono : {x y : ℕ}
    → x ≤ y
    → suc x ≤ suc y
  suc-mono (lte x b) = lte (suc x) b
  
  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = lte zero zero
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
  
  suc-mono′ : {x y : ℕ}
    → x ≤ y
    → suc x ≤ suc y
  suc-mono′ {x} {.(x + b)} (lte .x b) = lte (suc x) b
  
  suc-mono-mono : {x : ℕ}
    → x ≤ x
    → suc x ≤ suc x
  suc-mono-mono = suc-mono′

module Definition-LessThanOrEqualTo where
  
  infix 4 _≤_

  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
  
open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where
  
  _ : 2 ≤ 5
  _ = s≤s (s≤s z≤n)
  
  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono = s≤s
  
  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl {zero}  = z≤n
  ≤-refl {suc x} = s≤s ≤-refl
  
  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n       y≤z       = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

module Sandbox-Preorders where

  open Sandbox-≤

  record IsPreorder {a ℓ : Level} {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl  : Reflexive  _~_
      trans : Transitive _~_

  ≤-preorder : IsPreorder _≤_
  IsPreorder.refl  ≤-preorder = ≤-refl
  IsPreorder.trans ≤-preorder = ≤-trans

  ≡-preorder : {a : Level} {A : Set a} → IsPreorder (_≡_ {A = A})
  IsPreorder.refl  ≡-preorder = PropEq.refl
  IsPreorder.trans ≡-preorder = PropEq.trans

  open Sandbox-Relations using (Related; related)

  Related-preorder : {A : Set} → IsPreorder (Related {A = A})
  Related-preorder = record { refl = related ; trans = λ _ _ → related }

  module Preorder-Reasoning
    {a ℓ : Level} {A : Set a} {_~_ : Rel A ℓ}
    (~-preorder : IsPreorder _~_) where

    open IsPreorder ~-preorder public

    infix 1 begin_
    infix 3 _∎
    infixr 2 _≡⟨⟩_
    infixr 2 _≈⟨_⟩_
    infixr 2 _≡⟨_⟩_

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y

    _∎ : (x : A) → x ~ x
    x ∎ = refl

    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z

  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero    = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  open Chapter3-Proofs using (+-comm)

  module ≤-Reasoning where

    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public

  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n = begin
    n     ≤⟨ n≤1+n n ⟩
    1 + n ≡⟨ +-comm 1 n ⟩
    n + 1 ∎
    where open ≤-Reasoning

  module Reachability
    {ℓ₁ ℓ₂ : Level} {V : Set ℓ₁}
    (_⇒_ : Rel V ℓ₂) where

    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_  : {v₁ v₂ : V}
        → v₁ ⇒ v₂
        → Path v₁ v₂
      here : {v : V}
        → Path v v
      connect : {v₁ v₂ v₃ : V}
        → Path v₁ v₂
        → Path v₂ v₃
        → Path v₁ v₃

    Path-preorder : IsPreorder Path
    Path-preorder = record { refl = here ; trans = connect }

  module Example-AboutABoy where

    data Person : Set where
      ellie fiona marcus rachel susie will : Person
    
    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will  : marcus IsFriendsWith will
      marcus-fiona : marcus IsFriendsWith fiona
      fiona-susie  : fiona  IsFriendsWith susie
      sym : {p₁ p₂ : Person}
        → p₁ IsFriendsWith p₂
        → p₂ IsFriendsWith p₁
    
    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie : marcus IsInterestedIn ellie
      will-rachel  : will   IsInterestedIn rachel
      rachel-will  : rachel IsInterestedIn will
      susie-will   : susie  IsInterestedIn will
    
    data SocialTie : Rel Person lzero where
      friendship : {p₁ p₂ : Person}
        → p₁ IsFriendsWith p₂
        → SocialTie p₁ p₂
      interest : {p₁ p₂ : Person}
        → p₁ IsInterestedIn p₂
        → SocialTie p₁ p₂
    
    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona = begin
      will   ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus ≈⟨ ↪ friendship marcus-fiona ⟩
      fiona ∎
      where open Preorder-Reasoning Path-preorder
    
    rachel-ellie : Path rachel ellie
    rachel-ellie = begin
      rachel ≈⟨ ↪ interest rachel-will ⟩
      will   ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus ≈⟨ ↪ interest marcus-ellie ⟩
      ellie ∎
      where open Preorder-Reasoning Path-preorder
  
  ≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl 
  ≤-antisym (s≤s m≤n) (s≤s n≤m) =
    PropEq.cong suc (≤-antisym m≤n n≤m)
  
  Antisymmetric : {a ℓ₁ ℓ₂ : Level} {A : Set a}
    → Rel A ℓ₁
    → Rel A ℓ₂
    → Set _
  Antisymmetric _≈_ _≤_ =
    ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
  
  _ : Antisymmetric _≡_ _≤_
  _ = ≤-antisym

  module _
    {a ℓ : Level} {A : Set a}
    (_~_ : Rel A ℓ) where

    record IsEquivalence : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        sym        : Symmetric  _~_
      
      open IsPreorder isPreorder public
    
    record IsPartialOrder : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        antisym    : Antisymmetric _≡_ _~_
  
  ≡-equiv : {a : Level}  {A : Set a} → IsEquivalence (_≡_ {a} {A})
  IsEquivalence.isPreorder ≡-equiv = ≡-preorder
  IsEquivalence.sym        ≡-equiv = PropEq.sym

  ≤-poset : IsPartialOrder _≤_
  IsPartialOrder.isPreorder ≤-poset = ≤-preorder
  IsPartialOrder.antisym    ≤-poset = ≤-antisym

  _<_ : Rel ℕ lzero
  m < n = m ≤ suc n
  infix 4 _<_

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
  public

open import Relation.Binary
  using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric)
  public

open import Relation.Binary.PropositionalEquality
  using (subst)
  public

open import Data.Nat
  using (_≤_; z≤n; s≤s; _<_)
  public

open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning)
  public

open Sandbox-Preorders
  using (
    IsPreorder;
    IsEquivalence;
    IsPartialOrder;
    module Preorder-Reasoning;
    ≡-preorder;
    ≡-equiv;
    ≤-preorder;
    ≤-poset
    )
  public