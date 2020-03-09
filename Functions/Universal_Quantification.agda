module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero     = z≤n
≤-refl (suc n)  = s≤s (≤-refl n)

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n _ = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

total : ∀ m n → m ≤ n ⊎ n ≤ m
total zero _ = inj₁ z≤n
total _ zero = inj₂ z≤n
total (suc m) (suc n)
  = [_,_]′
      (λ m≤n → inj₁ (s≤s m≤n))
      (λ n≤m → inj₂ (s≤s n≤m))
      (total m n)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {_} {_} {zero} n≤m = n≤m
≤-mono {m} {n} {suc k} n≤m = s≤s (≤-mono {m} {n} {k} n≤m)

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤′⇒≤ ≤′-refl = ≤-refl _
≤′⇒≤ (≤′-step a≤′b) = ≤-step (≤′⇒≤ a≤′b)

z≤′n : ∀ n → zero ≤′ n
z≤′n zero = ≤′-refl
z≤′n (suc n) = ≤′-step (z≤′n n)

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤′ z≤n = z≤′n _
≤⇒≤′ (s≤s a≤b) = s≤′s (≤⇒≤′ a≤b)

fin≤ : ∀ {n}(m : Fin n) → toℕ m < n
fin≤ zero = s≤s z≤n
fin≤ (suc i) = s≤s (fin≤ i)
