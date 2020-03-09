module Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)

-- data _≤′_ (m : ℕ) : ℕ -> Set where
--   ≤′-refl : m ≤′ m
--   ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n

-- data _≤″_ (m : ℕ) (k : ℕ) : Set where
--   ≤+ : ∀ {n} → m + n ≡ k → m ≤″ k

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set} (x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

data _⊆_ {A : Set}: List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs ys y} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : ∀ {xs ys x} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

infix 4 _⊆_

e0 : 1 ∷ [] ⊆ 1 ∷ []
e0 = keep stop

e1 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
e1 = keep (keep (drop stop))
