module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)
open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 6 _+_

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
n ∸ 0 = n
zero ∸ suc x = suc x
suc n ∸ m = suc (n ∸ m)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc n * m = m + (n * m)

infixl 6 _⊔_
_⊔_ : ℕ → ℕ → ℕ
0 ⊔ n = n
n ⊔ 0 = n
(suc n) ⊔ (suc m) = suc (n ⊔ m)

infixl 7 _⊓_
_⊓_ : ℕ → ℕ → ℕ
0 ⊓ n = 0
n ⊓ 0 = 0
(suc n) ⊓ (suc m) = suc (n ⊓ m)

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋ = 0
⌊ 1 /2⌋ = 0
⌊ (suc (suc n)) /2⌋ = suc (⌊ n /2⌋)

-- odd : ℕ → Bool
-- odd 0 = false
-- odd 1 = true
-- odd (suc (suc n)) = odd n
--
-- even : ℕ → Bool
-- even 0 = true
-- even 1 = false
-- even (suc (suc n)) = even n

odd : ℕ → Bool
even : ℕ → Bool

odd (suc n) = even n
odd 0 = false
even (suc n) = odd n
even 0 = true

_≡?_ : ℕ → ℕ → Bool
0 ≡? 0 = true
suc n ≡? 0 = false
0 ≡? suc n = false
suc n ≡? suc m = n ≡? m

_≤?_ : ℕ → ℕ → Bool
0 ≤? _ = true
suc n ≤? 0 = false
suc n ≤? suc m = n ≤? m

from : ℕ₂ → ℕ
from zero = 0
from (id (one)) = 1
from (id (double n)) = 2 * from (id n)
from (id (double+1 n)) = suc (2 * from (id n))

data ℤ : Set where
  ℤ-zero  : ℤ
  ℤ-suc   : ℤ → ℤ
  ℤ-pre   : ℤ → ℤ

_+′_ : ℤ → ℤ → ℤ
ℤ-zero +′ n = n
ℤ-suc n +′ m = ℤ-suc (n +′ m)
ℤ-pre n +′ m = n +′ ℤ-pre m

data BinaryTree : Set where
  leaf : BinaryTree
  node : BinaryTree → BinaryTree → BinaryTree

mirror : BinaryTree → BinaryTree
mirror leaf = leaf
mirror (node a b) = node b a
