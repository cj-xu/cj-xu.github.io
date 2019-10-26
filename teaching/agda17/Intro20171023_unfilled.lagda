

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                       Introduction  II
                       ----------------
                       
                         Chuangjie Xu

           14-16 Monday 23th October 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/


------------------------------
    Martin-Löf type theory
------------------------------

We firstly recall the Agda definitions of MLTT types.

In Agda, types are called sets.

\begin{code}

Type : Set₁
Type = Set

\end{code}

Notice that Type has a type "Set₁".

The type of types is called a universe. Agda has a tower of universes

    Set ≡ Set₀ : Set₁ : Set₂ : ....

Π-types are primitive in Agda, and Π(x:A).P(x) is written as (x : A) → P x.

Non-dependent function types are a special case of Π-types, written as A → B.

Let's define Σ-types.

\begin{code}

infixr 5 _,_ -- mixfix operator
             -- associative to the right

data Σ {A : Type} (P : A → Type) : Type where  -- {A : Type} is an implicit argument
 _,_ : (a : A) → P a → Σ \(x : A) → P x    -- the constructor of Σ-types

pr₁ : {A : Type} {P : A → Type}
    → (Σ \(x : A) → P x) → A
pr₁ w = ?

pr₂ : {A : Type} {P : A → Type}
    → (w : Σ \(x : A) → P x) → P (pr₁ w)
pr₂ w = ?

\end{code}

Notice that the following notations are equivalent:

    Σ P   ≡   Σ \(x : A) → P x   ≡   Σ \x → P

Binary products are a special case of Σ-types.

\begin{code}

infixr 10 _×_

_×_ : Type → Type → Type
A × B = Σ \(_ : A) → B    -- treating B as a constant type family A → Type

\end{code}

Coproducts can be defined using data declaration.

\begin{code}

data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B

case : {A B C : Type}
     → (A → C) → (B → C) → A + B → C
case f g w = ?

\end{code}

Empty type and unit type

\begin{code}

data 𝟘 : Type where

𝟘-elim : {A : Type}
       → 𝟘 → A
𝟘-elim x = ?

data 𝟙 : Type where
 ⋆ : 𝟙

\end{code}

---------------------------------------
    The Curry-Howard correspondence
---------------------------------------

A proposition is true iff its corresponding type is inhabited.

                Propositions  │  Types
           ───────────────────┼───────────────────
                           ⊥  │  𝟘
                           ⊤  │  𝟙
                       P → Q  │  P → Q
                       P ∧ Q  │  P × Q
                       P ∨ Q  │  P + Q
                 ∀(x:A).P(x)  │  Π(x:A).P(x)
                 ∃(x:A).P(x)  │  Σ(x:A).P(x)
            Leibniz equality  │  identity types
        inductive predicates  │  (dependent) W-types
      coinductive predicates  │  (dependent) M-types

\begin{code}

ℙ : Set₁
ℙ = Type

-- A predicate P on variables of type A is ℙ/Type-value function
--
--     P : A → ℙ
--
-- This is also called a type family.

⊥ : ℙ
⊥ = 𝟘

⊤ : ℙ
⊤ = 𝟙

-- We use function types A → B to represent "A implies B".

infixr 10 _∧_
infixr 5  _∨_

_∧_ : ℙ → ℙ → ℙ
A ∧ B = A × B

_∨_ : ℙ → ℙ → ℙ
A ∨ B = A + B

-- The symbol ∀ is reserved.
-- The following notations are equivalent:
--
--   (x : A) → P x   ≡   ∀(x : A) → P x   ≡   ∀ x → P x
--
-- We're now doing logic. So I prefer to use the last one.

∃ : {A : Type} → (A → ℙ) → ℙ
∃ = Σ

-- Similarly to ∀, we write ∃ \x → P x instead of the others.

\end{code}

Now let's prove some simple logical axioms and rules!

0. ⊥ → A

\begin{code}

Axiom₀ : {A : ℙ}
       → ⊥ → A
Axiom₀ = ?

\end{code}

1. A → A ∧ A

\begin{code}

Axiom₁ : {A : ℙ}
       → A → A ∧ A
Axiom₁ = ?

\end{code}

2. A ∨ A → A

\begin{code}

Axiom₂ : {A : ℙ}
       → A ∨ A → A
Axiom₂ = ?

\end{code}

3. A ∧ B → B ∧ A

\begin{code}

Axiom₃ : {A B : ℙ}
       → A ∧ B → B ∧ A
Axiom₃ = ?

\end{code}

4. A ∨ B → B ∨ A

\begin{code}

Axiom₄ : {A B : ℙ}
       → A ∨ B → B ∨ A
Axiom₄ = ?

\end{code}

5. (A → B) → (B → C) → A → C

\begin{code}

Axiom₅ : {A B C : ℙ}
       → (A → B) → (B → C) → A → C
Axiom₅ = ?

\end{code}

6. A → (A → B) → B

\begin{code}

Axiom₆ : {A B : ℙ}
       → A → (A → B) → B
Axiom₆ = ?

\end{code}

7. (a : A) → (∀ x → P x) → P a

\begin{code}

Axiom₇ : {A : Type} {P : A → ℙ}
       → (a : A) → (∀ x → P x) → P a
Axiom₇ = ?

\end{code}

Here are some exercises:

(A ∧ B → C) → A → B → C

(A → B) → C ∨ A → C ∨ B

(∀ x → Q → P x) → Q → ∀ x → P x

(a : A) → P a → ∃ \x → P x

(∀ x → P x → Q) → (∃ \x → P x) → Q







----------------
    Equality
----------------

\begin{code}

data _≡_ {A : Type} : A → A → Type where
 refl : {a : A} → a ≡ a

\end{code}

------------------
    Arithmetic
------------------

Natural numbers

\begin{code}

data ℕ : Type where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}
