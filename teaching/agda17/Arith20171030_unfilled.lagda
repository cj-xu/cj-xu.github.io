

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                          Arithmetic
                          ----------
                       
                         Chuangjie Xu

           14-16 Monday 30th October 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/


---------------------
    Preliminaries
---------------------

A minimal library for today's lecture

Logic

\begin{code}

infixr 20 _,_

-- another definition of Σ-types as an Agda record

record Σ {A : Set} (P : A → Set) : Set where
 constructor _,_
 field
  pr₁ : A
  pr₂ : P pr₁

open Σ

∃ : {A : Set} → (A → Set) → Set
∃ = Σ

infixr 5 _∧_
infixr 4 _∨_

_∧_ : Set → Set → Set
A ∧ B = Σ \(_ : A) → B    -- treating B as a constant type family A → Set

data _∨_ (A B : Set) : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B

case : {A B C : Set}
     → (A → C) → (B → C) → A ∨ B → C
case f g (inl a) = f a
case f g (inr b) = g b

data ⊥ : Set where

⊥-elim : {A : Set}
       → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

\end{code}

Equality

\begin{code}

infixr 10 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
 refl : a ≡ a

sym : {A : Set} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

ap : {A B : Set} {x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

transport : {A : Set} (P : A → Set) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

\end{code}

-----------------------
    Natural numbers
-----------------------

\begin{code}

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}

Recursion

\begin{code}

rec : {A : Set}
    → A → (ℕ → A → A)
    → ℕ → A
rec = {!!}

\end{code}

Induction

\begin{code}

ind : {P : ℕ → Set}
    → P 0 → (∀ n → P n → P (succ n))
    → ∀ n → P n
ind = {!!}

\end{code}

Addition

\begin{code}

infixl 20 _+_

_+_ : ℕ → ℕ → ℕ
n + 0      = n
n + succ m = {!!}

associativity-+ : (n m k : ℕ)
                → n + m + k ≡ n + (m + k)
associativity-+ = {!!}

0-right-identity-+ : (n : ℕ)
                   → n + 0 ≡ n
0-right-identity-+ = {!!}

0-left-identity-+ : (n : ℕ)
                  → 0 + n ≡ n
0-left-identity-+ = {!!}

commutativity-+ : (n m : ℕ)
                → n + m ≡ m + n
commutativity-+ = {!!}

\end{code}

Multiplication

\begin{code}

infixl 30 _×_

_×_ : ℕ → ℕ → ℕ
n × 0      = 0
n × succ m = {!!}

distributivity : (n m k : ℕ)
               → n × (m + k) ≡ n × m + n × k
distributivity = {!!}

associativity-× : (n m k : ℕ)
                → n × m × k ≡ n × (m × k)
associativity-× = {!!}

1-right-identity-× : (n : ℕ)
                   → n × 1 ≡ n
1-right-identity-× = {!!}

1-left-identity-×  : (n : ℕ)
                   → 1 × n ≡ n
1-left-identity-×  = {!!}

commutativity-× : (n m : ℕ)
                → n × m ≡ m × n
commutativity-× = {!!}

\end{code}
