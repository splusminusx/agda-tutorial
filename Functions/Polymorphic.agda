module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit  using (⊤; tt)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x

tail : {A : Set} → List A → Maybe (List A)
tail [] = nothing
tail (x ∷ xs) = just xs

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

maps : {A B : Set} → List (A → B) → List A → List B
maps [] _ = []
maps _ [] = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

[_] : {A : Set} → A → List A
[ a ] = a ∷ []

id : {A : Set} → A → A
id a = a

const : {A B : Set} → A → B → A
const a _ = a

flip : {A B C : Set} → (A → B → C) → (B → A → C)
flip f = λ b a → f a b

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

swap : {A B : Set} → A × B → B × A
swap (a , b) = (b , a)

proj₁ : {A B : Set} → A × B → A
proj₁ (a , _) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (_ , b) = b

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

uswap : {A B : Set} → A ⊎ B → B ⊎ A
uswap (inj₁ a) = inj₂ a
uswap (inj₂ b) = inj₁ b

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_] f g (inj₁ a) = f a
[_,_] f g (inj₂ b) = g b
