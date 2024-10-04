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

  _∨₁_ : Bool → Bool → Bool
  false ∨₁ false = false
  false ∨₁ true  = true
  true ∨₁ false  = true
  true ∨₁ true   = true
  
  _∨₂_ : Bool → Bool → Bool
  false ∨₂ other = other
  true ∨₂ other  = true
  
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
  my-tuple = record { proj₁ = true ∨₂ true ; proj₂ = not true }
  
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
  my-tuple′ = true ∨₂ true , not true

module Sandbox-Tuples₂ where
  open Booleans
  
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B
  
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
  