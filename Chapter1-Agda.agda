module Chapter1-Agda where
  
module Example-Imports where
  open import Data.Bool

  _ : Bool
  _ = false

module Booleans where

  data Bool : Set where
    false : Bool
    true  : Bool
  
  not : Bool → Bool
  not false = true 
  not true  = false

  open import Relation.Binary.PropositionalEquality
  
  _ : not (not false) ≡ false
  _ = refl
  
  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true ∨ other  = true
  
  _∧_ : Bool → Bool → Bool
  false ∧ other = false
  true ∧ other  = other

module Example-Employees where
  open Booleans
  open import Data.String
    using (String)
  
  data Department : Set where
    administrative : Department
    engineering    : Department
    finance        : Department
    marketing      : Department
    sales          : Department

  record Employee : Set where
    field
      name        : String
      department  : Department
      is-new-hire : Bool
  
  tillman : Employee
  tillman = record
    { name        = "Tillman"
    ; department  = engineering
    ; is-new-hire = false
    }

module Sandbox-Tuples where
  open Booleans
  
  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A
      proj₂ : B
  
  infixr 2 _×_

  open _×_
  
  my-tuple : Bool × Bool
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }
  
  first : Bool × Bool → Bool
  first record { proj₁ = x } = x
  
  my-tuple-first : Bool
  my-tuple-first = my-tuple .proj₁

  my-tuple-second : Bool
  my-tuple-second = proj₂ my-tuple
  
  my-copattern : Bool × Bool
  my-copattern .proj₁ = true
  my-copattern .proj₂ = true

  nested-copattern : Bool × (Bool × Bool)
  nested-copattern .proj₁        = true
  nested-copattern .proj₂ .proj₁ = true
  nested-copattern .proj₂ .proj₂ = true

  _,_ : {A B : Set} → A → B → A × B
  x , x₁ = record { proj₁ = x ; proj₂ = x₁ }

  infixr 4 _,_
  
  my-tuple′ : Bool × Bool
  my-tuple′ = true ∨ true , not true

module Sandbox-Tuples₂ where
  open Booleans
  
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B
  
  infixr 2 _×_

  open _×_

  my-tuple′ : Bool × Bool
  my-tuple′ = false , true
  
  data _⊎_ (A : Set) (B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B
  
  infixr 1 _⊎_
  
  module Example-Pets where
    open import Data.String
      using (String)
    
    data Species : Set where
      bird cat dog reptile : Species
    
    data Temperament : Set where
      anxious   : Temperament
      chill     : Temperament
      excitable : Temperament
      grumpy    : Temperament
    
    record Pet : Set where
      constructor makePet
      field
        species     : Species
        temperament : Temperament
        name        : String
    
    makeGrumpyCat : String → Pet
    makeGrumpyCat = makePet cat grumpy
  
  or : Bool × Bool → Bool
  or (false , y) = y
  or (true , y)  = true
  
  _ : Bool
  _ = or (true , false)
  
  curry : {A B C : Set} → (A × B → C) → A → B → C
  curry f = λ a b → f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → A × B → C
  uncurry f = λ x → f (x .proj₁) (x .proj₂)
  
  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)
  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming
      ( _,′_ to _,_
      ; curry′ to curry
      ; uncurry′ to uncurry
      )
  
  mk-tuple : (A B : Set) → A → B → A × B
  mk-tuple A B x x₁ = x , x₁
  
  _ : Bool × Bool
  _ = mk-tuple Bool Bool false true
  
  data PrimaryColor : Set where
    red green blue : PrimaryColor
  
  color-bool-tuple : PrimaryColor × Bool
  color-bool-tuple  = mk-tuple _ _ red false
  
  mk-color-bool-tuple
    : PrimaryColor
    → Bool
    → PrimaryColor × Bool
  mk-color-bool-tuple = _,_ {A = PrimaryColor} {B = Bool}

open import Data.Bool
  using (Bool; false; true; not; _∨_; _∧_)
  public
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; curry; uncurry)
  public
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public
