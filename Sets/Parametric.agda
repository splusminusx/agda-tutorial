module Sets.Parametric where

open import Data.Nat
open import Sets.Enumerated using (Bool; true; false)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A → Maybe A

data BinTree (A : Set) : Set where
  leaf : A → BinTree A
  node : A → BinTree A → BinTree A → BinTree A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set  where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B) where
  [] : List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B) where
  _∷_ : B → List₁ A B → List₂ A B

data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero  : A → Square A
  suc   : Square (T4 A) → Square A
