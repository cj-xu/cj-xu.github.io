

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                  Continuity in Type Theory I
                  ---------------------------
                       
                         Chuangjie Xu

           14-16 Monday 6th November 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/


---------------------
    Preliminaries
---------------------

A minimal library for today's lecture

\begin{code}

record Σ {A : Set} (B : A → Set) : Set where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infix 1 _≡_

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
 refl : a ≡ a

transport : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
transport P refl p = p

ap : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

infixr 5 _∙_

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 10 _+_

_+_ : ℕ → ℕ → ℕ
n + zero   = n
n + succ m = succ (n + m)

\end{code}

-----------------------------------------
  Infinite sequences of natural numbers
-----------------------------------------

\begin{code}

ℕᴺ : Set
ℕᴺ = ℕ → ℕ

-- α ≡[ n ] β represents that the first n bits of α and β are equal.
_≡[_]_ : ℕᴺ → ℕ → ℕᴺ → Set
_≡[_]_ = {!!}

-- The infinite sequence of 0's
0ʷ : ℕ → ℕ
0ʷ i = 0

-- n zeros-and-then k consists of n 0's followed by infinitely many k's.
_zeros-and-then_ : ℕ → ℕ → ℕᴺ
_zeros-and-then_ = {!!}

zeros-and-then-spec₀ : ∀ n {k} → (n zeros-and-then k) n ≡ k
zeros-and-then-spec₀ = {!!}

zeros-and-then-spec₁ : ∀ n {k} → 0ʷ ≡[ n ] (n zeros-and-then k)
zeros-and-then-spec₁ = {!!}

\end{code}

The Curry-Howard interpretation of Brouwer's continuity principle fails.

\begin{code}

CH-Cont : Set
CH-Cont = (f : ℕᴺ → ℕ) (α : ℕᴺ) → Σ \(m : ℕ) → (β : ℕᴺ) → α ≡[ m ] β → f α ≡ f β

Thm : CH-Cont → 0 ≡ 1
Thm cont = {!!}

\end{code}
