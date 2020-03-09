module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

0≤1 : 1 ≤ 10
0≤1 = s≤s z≤n

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

plus : ℕ → ℕ → ℕ
plus zero m = m
plus (suc n) m = plus n (suc m)

data _isDoubleOf_ : ℕ → ℕ → Set where
  zIsDoubleOfZ : zero isDoubleOf zero
  doubleIsDouble : {n : ℕ} → (plus n n) isDoubleOf n

infix 4 _isDoubleOf_

8isDoubelOf4 : 8 isDoubleOf 4
8isDoubelOf4 = doubleIsDouble

9isNotDoubleOf4 : 9 isDoubleOf 4 → ⊥
9isNotDoubleOf4 ()

data Odd : ℕ → Set where
  one   : Odd (suc zero)
  next  : {n : ℕ} → Odd n → Odd (suc (suc n))

9isOdd : Odd 9
9isOdd = next (next (next (next one)))

8isNotOdd : Odd 8 → ⊥
8isNotOdd (next (next (next (next ()))))

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : ∀ {m}   → m ≤′ m
  ≤′-step : ∀ {m n} → m ≤′ n → m ≤′ suc n

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  snn : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

5+5≡10 : 5 + 5 ≡ 10
5+5≡10 = snn (snn (snn (snn (snn znn))))

2+2≢5 : 2 + 2 ≡ 5 → ⊥
2+2≢5 (snn (snn ()))

data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  ⊓-zero : ∀ {n} → zero ⊓ n ≡ zero
  ⊓-sym : ∀ {n m} → n ⊓ m ≡ n → m ⊓ n ≡ n
  ⊓-succ : ∀ {m n} → m ⊓ n ≡ m → suc (m) ⊓ suc (n) ≡ suc (m)

3⊓5≡3 : 3 ⊓ 5 ≡ 3
3⊓5≡3 = ⊓-succ (⊓-succ (⊓-succ (⊓-zero)))

3⊓5≢5 : 5 ⊓ 3 ≡ 5 → ⊥
3⊓5≢5 (⊓-succ (⊓-succ (⊓-succ ())))

data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

data _isDoubleOfEq_ : ℕ → ℕ → Set where
  isDouble+ : ∀ {m n} → m + m ≡ n → n isDoubleOfEq m

8isDoubleOfEq4 : 8 isDoubleOfEq 4
8isDoubleOfEq4 = isDouble+ (snn (snn (snn (snn (znn)))))

9isNotDoubleOfEq4 : 9 isDoubleOfEq 4 → ⊥
9isNotDoubleOfEq4 (isDouble+ (snn (snn (snn (snn ())))))

data _*_≡_ : ℕ → ℕ → ℕ → Set where
  *-zero : ∀ {n} → zero * n ≡ zero
  *-suc : ∀ {m n k l} → m * n ≡ k → k + n ≡ l → suc (m) * n ≡ l

2*2≡4 : 2 * 2 ≡ 4
2*2≡4 = *-suc (*-suc *-zero znn) (snn (snn znn))
