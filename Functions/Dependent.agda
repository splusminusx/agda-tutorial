module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

_-_ : (n : ℕ) → Fin (suc n) → ℕ
n - zero = n
suc n - suc m = n - m

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc n) = suc (toℕ n)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ (s≤s (z≤n)) = zero
fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ n zero = zero
inject+ n (suc i) = suc (inject+ n i)

four : Fin 66
four = suc (suc (suc (suc zero)))

raise : ∀ {m} n → Fin m → Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)

head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (x ∷ _) = x

tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (a ∷ as) = (f a) ∷ (maps fs as)

replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {zero} _ = []
replicate {suc n} a = a ∷ replicate {n} a

map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (a ∷ as) = (f a) ∷ (map f as)

zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (a ∷ as) (b ∷ bs) = (a , b) ∷ (zip as bs)

_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
(a ∷ as) ! zero = a
(a ∷ as) ! (suc i) = as ! i
 
