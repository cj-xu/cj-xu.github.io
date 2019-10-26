

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
rec a f  0       = a
rec a f (succ n) = f n (rec a f n)

\end{code}

Induction

\begin{code}

ind : {P : ℕ → Set}
    → P 0 → (∀ n → P n → P (succ n))
    → ∀ n → P n
ind base step  0       = base
ind base step (succ n) = step n (ind base step n)

\end{code}

Addition

\begin{code}

infixl 20 _+_

_+_ : ℕ → ℕ → ℕ
n + 0      = n
n + succ m = succ (n + m)

associativity-+ : (n m k : ℕ)
                → n + m + k ≡ n + (m + k)
associativity-+ n m  0       = refl
associativity-+ n m (succ k) = goal
 where
  IH : n + m + k ≡ n + (m + k)
  IH = associativity-+ n m k
  goal : succ (n + m + k) ≡ succ (n + (m + k))
  goal = ap succ IH

0-right-identity-+ : (n : ℕ)
                   → n + 0 ≡ n
0-right-identity-+ n = refl

0-left-identity-+ : (n : ℕ)
                  → 0 + n ≡ n
0-left-identity-+  0       = refl
0-left-identity-+ (succ n) = goal
 where
  IH : 0 + n ≡ n
  IH = 0-left-identity-+ n
  goal : succ (0 + n) ≡ succ n
  goal = ap succ IH

Lm[succ-+] : (n m : ℕ)
           → succ (m + n) ≡ succ m + n
Lm[succ-+]  0       m = refl
Lm[succ-+] (succ n) m = goal
 where
  IH : succ (m + n) ≡ succ m + n
  IH = Lm[succ-+] n m
  goal : succ (succ (m + n)) ≡ succ (succ m + n)
  goal = ap succ IH

commutativity-+ : (n m : ℕ)
                → n + m ≡ m + n
commutativity-+ n  0       = sym (0-left-identity-+ n)
commutativity-+ n (succ m) = goal
 where
  IH : n + m ≡ m + n
  IH = commutativity-+ n m
  claim₀ : succ (n + m) ≡ m + succ n -- = succ (m + n)
  claim₀ = ap succ IH
  claim₁ : succ (m + n) ≡ succ m + n
  claim₁ = Lm[succ-+] n m
  goal : succ (n + m) ≡ (succ m) + n
  goal = trans claim₀ claim₁

\end{code}

Multiplication

\begin{code}

infixl 30 _×_

_×_ : ℕ → ℕ → ℕ
n × 0      = 0
n × succ m = n × m + n

distributivity : (n m k : ℕ)
               → n × (m + k) ≡ n × m + n × k
distributivity n m  0       = refl
distributivity n m (succ k) = goal
 where
  IH : n × (m + k) ≡ n × m +  n × k
  IH = distributivity n m k
  claim₀ : n × (m + k) + n ≡ n × m + n × k + n
  claim₀ = ap (λ x → x + n) IH
  claim₁ : n × m + n × k + n ≡ n × m + (n × k + n)
  claim₁ = associativity-+ (n × m) (n × k) n
  goal : n × (m + k) + n ≡ n × m + (n × k + n)
     -- n × (m + succ k) ≡ n × m + n × succ k
  goal = trans claim₀ claim₁

\end{code}

Exercises

\begin{code}

associativity-× : (n m k : ℕ)
                → n × m × k ≡ n × (m × k)
associativity-× = {!!}


1-right-identity-× : (n : ℕ)
                   → n × 1 ≡ n
1-right-identity-× = {!!}


1-left-identity-× : (n : ℕ)
                  → 1 × n ≡ n
1-left-identity-× = {!!}


right-zero-for-× : (n : ℕ)
                 → n × 0 ≡ 0
right-zero-for-× = {!!}


left-zero-for-× : (n : ℕ)
                → 0 × n ≡ 0
left-zero-for-× = {!!}


commutativity-× : (n m : ℕ)
                → n × m ≡ m × n
commutativity-× = {!!}

\end{code}















--------------------------------
    Constructive Mathematics
--------------------------------

An example of a non-constructive proof

  There exist irrational numbers a, b such that aᵇ is rational.


The BHK-interpretation (Brouwer-Heyting-Kolmogorov) of logic:

• There is no proofs of "⊥"

• A proof of "P ∧ Q" is a pair <p,q> where p is a proof of P and
                                           q is a proof of Q

• A proof of "P ∨ Q" is a pair <i,p> where if i=0 then p is a proof of P and
                                           if i=1 then p is a proof of Q

• A proof of "P → Q" is an algorithm converting a proof of P into a proof of Q

• A proof of "∀xᴬ.P(x)" is an algorithm converting an element a:A into a proof of P(a)

• A proof of "∃xᴬ.P(x)" is a pair <a,p> where a:A is an element and p is a proof of P(a)


Varieties of Constructive Mathematics

‣ Intuitionistic Mathematics (INT)

‣ Recursive Constructive Mathematics (RUSS)

‣ Bishop's Constructive Mathematics (BISH)


REFERENCE

◦ Douglas Bridges and Fred Richman, Varieties of Constructive Mathematics.
  London Math. Soc. Lecture Notes 97, Cambridge Univ. Press (1987) 160 pp.
