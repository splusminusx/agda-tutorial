module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data ℕ⁺ : Set where
  one       : ℕ⁺
  double    : ℕ⁺ → ℕ⁺
  double+1  : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id   : ℕ⁺ → ℕ₂

data ℤ : Set where
  zero : ℤ
  suc  : ℤ → ℤ
  pev  : ℤ → ℤ

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

data BinTree'ℕ : Set where
  leaf : ℕ → BinTree'ℕ
  node : BinTree'ℕ → BinTree'ℕ → BinTree'ℕ

data Listℕ : Set where
  empty : Listℕ
  cons  : ℕ → Listℕ → Listℕ

data NonEmptyListℕ : Set where
  one   : ℕ → NonEmptyListℕ
  cons  : ℕ → NonEmptyListℕ → NonEmptyListℕ
