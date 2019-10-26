
■ Preliminaries

\begin{code}

module Preliminaries where

data ⊥ : Set where

data _∨_ (A B : Set) : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B

data _≡_ {A : Set} (a : A) : A → Set where
 refl : a ≡ a

cong : {A B : Set} {x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

_≢_ : {A : Set} → A → A → Set
x ≢ y = (x ≡ y) → ⊥

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 40 _+_
infixl 40 _-_

_+_ : ℕ → ℕ → ℕ
n + 0      = n
n + succ m = succ (n + m)

_-_ : ℕ → ℕ → ℕ
n      - 0      = n
0      - succ m = 0
succ n - succ m = n - m

pred : ℕ → ℕ
pred  0       = 0
pred (succ n) = n

_≟ℕ_ : (n m : ℕ) → (n ≡ m) ∨ (n ≢ m)
0      ≟ℕ 0      = inl refl
0      ≟ℕ succ m = inr (λ ())
succ n ≟ℕ 0      = inr (λ ())
succ n ≟ℕ succ m with n ≟ℕ m
...              | inl n=m = inl (cong succ n=m)
...              | inr n≠m = inr (λ e → n≠m (cong pred e))

data _≤_ : ℕ → ℕ → Set where
 ≤zero : {n : ℕ} → 0 ≤ n
 ≤succ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

≤pred : {n m : ℕ} → succ n ≤ succ m → n ≤ m
≤pred (≤succ r) = r

_≰_ : ℕ → ℕ → Set
n ≰ m = (n ≤ m) → ⊥

_≤?_ : (n m : ℕ) → (n ≤ m) ∨ (n ≰ m)
0      ≤? m      = inl ≤zero
succ n ≤? 0      = inr (λ ())
succ n ≤? succ m with n ≤? m
...              | inl n≤m = inl (≤succ n≤m)
...              | inr n≰m = inr (λ r → n≰m (≤pred r))

infixl 20 _,_
infixr 19 _++_

data _* (A : Set) : Set where
 ε   : A *
 _,_ : A * → A → A *

_++_ : {A : Set} → A * → A * → A *
u ++ ε     = u
u ++ v , x = (u ++ v) , x

∣_∣ : {A : Set} → A * → ℕ
∣ ε ∣     = 0
∣ u , x ∣ = succ ∣ u ∣

--
-- gen n m is the list [n,n+1,...,m-1] if n ≤ m
--
gen : ℕ → ℕ → ℕ *
gen n  0       = ε
gen n (succ m) with n ≤? m
...            | inl n≤m+1 = gen n m , m
...            | inr n≰m+1 = ε

--
-- If x ∈ u, then idx x u is the index of the right most occurrence of x in u
-- otherwise, idx x u = |u|+1.
--
idx : ℕ → ℕ * → ℕ
idx x  ε      = 1
idx x (u , y) with x ≟ℕ y
...           | inl x=y = 0
...           | inr x≠y = succ (idx x u)

\end{code}
