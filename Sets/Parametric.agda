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
