Chuangjie Xu

-------------------------
    A minimal library
-------------------------

for the course "Executing Proofs as Computer Programs"

\begin{code}

module Preliminaries where

open import Agda.Primitive using (Level ; _⊔_)


infix 10 _∈_

_∈_ : {X : Set} → X → (X → Set) → Set
x ∈ A = A x


infixr 10 _,_

record Σ {i j : Level} {A : Set i} (B : A → Set j) : Set (i ⊔ j) where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infixl 20 _×_
infixl 15 _+_
infixl 10 _↔_

_×_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
A × B = Σ \(_ : A) → B

_↔_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

data _+_ {i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 inl : A → A + B
 inr : B → A + B

case : {i j k : Level} {A : Set i} {B : Set j} {C : Set k}
     → (A → C) → (B → C) → A + B → C
case f g (inl a) = f a
case f g (inr b) = g b

cases : {i j k l : Level} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
      → (A → C) → (B → D) → A + B → C + D
cases f g (inl a) = inl (f a)
cases f g (inr b) = inr (g b)

infix 1 _≡_

data _≡_ {i : Level} {A : Set i} (a : A) : A → Set i where
 refl : a ≡ a

transport : {i j : Level} {A : Set i} (P : A → Set j) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

ap : {i j : Level} {A : Set i} {B : Set j}
   → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

sym : {i : Level} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : {i : Level} {A : Set i} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

pair⁼ : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'}
      → (e : a ≡ a') → transport B e b ≡ b'
      → (a , b) ≡ (a' , b')
pair⁼ refl refl = refl

pairˣ⁼ : {A B : Set} {a a' : A} {b b' : B}
       → a ≡ a' → b ≡ b'
       → (a , b) ≡ (a' , b')
pairˣ⁼ refl refl = refl

data 𝟘 : Set where

𝟘-elim : {i : Level} {A : Set i} → 𝟘 → A
𝟘-elim ()

¬_ : {i : Level} → Set i → Set i
¬_ A = A → 𝟘

infix 10 _≢_

_≢_ : {i : Level} {A : Set i} → A → A → Set i
x ≢ y = ¬ (x ≡ y)

data 𝟙 : Set where
 ⋆ : 𝟙

data 𝟚 : Set where
 𝟎 𝟏 : 𝟚

𝟚-discrete : {x y : 𝟚} → (x ≡ y) + (x ≢ y)
𝟚-discrete {𝟎} {𝟎} = inl refl
𝟚-discrete {𝟎} {𝟏} = inr (λ ())
𝟚-discrete {𝟏} {𝟎} = inr (λ ())
𝟚-discrete {𝟏} {𝟏} = inl refl

Lemma[b≡0∨b≡1] : (b : 𝟚) → (b ≡ 𝟎) + (b ≡ 𝟏)
Lemma[b≡0∨b≡1] 𝟎 = inl refl
Lemma[b≡0∨b≡1] 𝟏 = inr refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred  0       = 0
pred (succ n) = n

ℕ-discrete : {n m : ℕ} → (n ≡ m) + (n ≢ m)
ℕ-discrete {0}      {0}      = inl refl
ℕ-discrete {0}      {succ m} = inr (λ ())
ℕ-discrete {succ n} {0}      = inr (λ ())
ℕ-discrete {succ n} {succ m} = step ℕ-discrete
 where
  step : (n ≡ m) + (n ≢ m) → (succ n ≡ succ m) + (succ n ≢ succ m)
  step (inl e) = inl (ap succ e)
  step (inr f) = inr (λ e → f (ap pred e))

infixl 10 _+ᴺ_
infixl 9  _-_

_+ᴺ_ : ℕ → ℕ → ℕ
0 +ᴺ m = m
(succ n) +ᴺ m = succ (n +ᴺ m)

_-_ : ℕ → ℕ → ℕ
0 - m = 0
(succ n) - 0 = succ n
(succ n) - (succ m) = n - m


infix 50 _≤_
infix 50 _<_

data _≤_ : ℕ → ℕ → Set where
 zero≤ : {n : ℕ} → 0 ≤ n
 succ≤ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

pred≤ : {n m : ℕ} → succ n ≤ succ m → n ≤ m
pred≤ (succ≤ r) = r

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = zero≤
≤-refl {succ n} = succ≤ ≤-refl

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ  zero≤    = zero≤
≤-r-succ (succ≤ r) = succ≤ (≤-r-succ r)

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans  zero≤     _        = zero≤
≤-trans (succ≤ r) (succ≤ s) = succ≤ (≤-trans r s)

Lemma[n≯m→n≤m] : {n m : ℕ} → ¬ (m < n) → n ≤ m
Lemma[n≯m→n≤m] {0}      {m}      _ = zero≤
Lemma[n≯m→n≤m] {succ n} {0}      f = 𝟘-elim (f (succ≤ zero≤))
Lemma[n≯m→n≤m] {succ n} {succ m} f = succ≤ (Lemma[n≯m→n≤m] (λ r → f (succ≤ r)))

Lemma[n≤m∧m≤n→n≡m] : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
Lemma[n≤m∧m≤n→n≡m]  zero≤     zero≤    = refl
Lemma[n≤m∧m≤n→n≡m] (succ≤ r) (succ≤ s) = ap succ (Lemma[n≤m∧m≤n→n≡m] r s)

Lemma[n≤m→n<m∨n≡m] : {n m : ℕ} → n ≤ m → (n < m) + (n ≡ m)
Lemma[n≤m→n<m∨n≡m] {0}      {0}       zero≤    = inr refl
Lemma[n≤m→n<m∨n≡m] {0}      {succ m}  zero≤    = inl (succ≤ zero≤)
Lemma[n≤m→n<m∨n≡m] {succ n} {0}      ()
Lemma[n≤m→n<m∨n≡m] {succ n} {succ m} (succ≤ r) = cases succ≤ (ap succ) (Lemma[n≤m→n<m∨n≡m] r)

Lemma[≤-decidable] : {n m : ℕ} → (n ≤ m) + ¬ (n ≤ m)
Lemma[≤-decidable] {0}      {m}      = inl zero≤
Lemma[≤-decidable] {succ n} {0}      = inr (λ ())
Lemma[≤-decidable] {succ n} {succ m} = cases succ≤ (λ f r → f (pred≤ r)) Lemma[≤-decidable]


max : ℕ → ℕ → ℕ
max  0        m       = m
max (succ n)  0       = succ n
max (succ n) (succ m) = succ (max n m)

max-spec₀ : (n m : ℕ) → n ≤ max n m
max-spec₀  0        m       = zero≤
max-spec₀ (succ n)  0       = ≤-refl
max-spec₀ (succ n) (succ m) = succ≤ (max-spec₀ n m)

max-spec₁ : (n m : ℕ) → m ≤ max n m
max-spec₁  0        m       = ≤-refl
max-spec₁ (succ n)  0       = zero≤
max-spec₁ (succ n) (succ m) = succ≤ (max-spec₁ n m)

\end{code}

-------------------------------------------------
    Propositions and propositional truncation
-------------------------------------------------

\begin{code}

isProp : {ℓ : Level} → Set ℓ → Set ℓ
isProp P = (x y : P) → x ≡ y

postulate
 ∥_∥ : {ℓ : Level} → Set ℓ → Set ℓ
 ∣_∣ : {ℓ : Level} {A : Set ℓ} → A → ∥ A ∥
 ∥∥-isProp : {ℓ : Level} {A : Set ℓ} → isProp ∥ A ∥
 ∥∥-elim : {ℓ ℓ' : Level} {A : Set ℓ} {P : Set ℓ'} → isProp P → (A → P) → ∥ A ∥ → P

∥∥-functor : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A → B) → ∥ A ∥ → ∥ B ∥
∥∥-functor f = ∥∥-elim ∥∥-isProp (λ a → ∣ f a ∣)

\end{code}

-------------------------------
    Function extensionality
-------------------------------

\begin{code}

postulate
 funext : {ℓ ℓ' : Level} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
        → (∀ x → f x ≡ g x) → f ≡ g

\end{code}
