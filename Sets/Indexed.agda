module Sets.Indexed where

open import Data.Empty using (⊥)
open import Data.Unit  using (⊤; tt)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Bool  using (Bool; true; false)
open import Data.Nat   using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

data IndexedUnit : Bool → Set where
  unit : IndexedUnit true

data Evens : ℕ → Set where
  start : Evens zero
  next  : (n : ℕ) → Evens n → Evens (suc (suc n))

data Vec (A : Set) : ℕ → Set where
  []    : Vec A zero
  cons  : (n : ℕ) → A → Vec A n → Vec A (suc n)

data IndexedSum (A B : Set) : Bool → Set where
  left  : A → IndexedSum A B false
  right : B → IndexedSum A B true
