module Term_Inference where

open import Data.Empty using (⊥)
open import Data.Unit  using (⊤; tt)
open import Data.Sum   using (_⊎_; inj₁; inj₂)
open import Data.Nat   using (ℕ; zero; suc)

data  Fin' : ℕ → Set where
  zero : (n : _) → Fin' (suc n)
  suc  : (n : _) → Fin' n → Fin' (suc n)

x : Fin' 3
x = suc _ (zero _)

data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)

x′ : Fin 3
x′ = suc {_} (zero {_})

x′′ : Fin 3
x′′ = suc zero
