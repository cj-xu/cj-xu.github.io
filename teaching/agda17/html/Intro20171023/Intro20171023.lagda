

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                       Introduction  II
                       ----------------
                       
                         Chuangjie Xu

           14-16 Monday 23rd October 2017, HS B 252

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
pr₁ (a , p) = a

pr₂ : {A : Type} {P : A → Type}
    → (w : Σ \(x : A) → P x) → P (pr₁ w)
pr₂ (a , p) = p

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

case : {A B C : Type} → (A → C) → (B → C) → A + B → C
case f g (inl a) = f a
case f g (inr b) = g b

\end{code}

Empty type and unit type

\begin{code}

data 𝟘 : Type where

𝟘-elim : {A : Type} → 𝟘 → A
𝟘-elim ()

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

Prop : Set₁
Prop = Type

-- A predicate P on variables of type A is Prop/Type-value function
--
--     P : A → Prop
--
-- This is also called a type family.

⊥ : Prop
⊥ = 𝟘

⊤ : Prop
⊤ = 𝟙

-- We use function types A → B to represent "A implies B".

infixr 10 _∧_
infixr 5  _∨_

_∧_ : Prop → Prop → Prop
A ∧ B = A × B

_∨_ : Prop → Prop → Prop
A ∨ B = A + B

-- The symbol ∀ is reserved.
-- The following notations are equivalent:
--
--   (x : A) → P x   ≡   ∀(x : A) → P x   ≡   ∀ x → P x
--
-- We're now doing logic. So I prefer to use the last one.

∃ : {A : Type} → (A → Prop) → Prop
∃ = Σ

-- Similarly to ∀, we write ∃ \x → P x instead of the others.

\end{code}

Now let's prove some simple logical axioms and rules!

0. ⊥ → A

\begin{code}

Axiom₀ : {A : Prop}
       → ⊥ → A
Axiom₀ ()

\end{code}

1. A → A ∧ A

\begin{code}

Axiom₁ : {A : Prop}
       → A → A ∧ A
Axiom₁ a = (a , a)

\end{code}

2. A ∨ A → A

\begin{code}

Axiom₂ : {A : Prop}
       → A ∨ A → A
Axiom₂ (inl a) = a
Axiom₂ (inr a) = a

\end{code}

3. A ∧ B → B ∧ A

\begin{code}

Axiom₃ : {A B : Prop}
       → A ∧ B → B ∧ A
Axiom₃ (a , b) = (b , a)

\end{code}

4. A ∨ B → B ∨ A

\begin{code}

Axiom₄ : {A B : Prop}
       → A ∨ B → B ∨ A
Axiom₄ (inl a) = inr a
Axiom₄ (inr b) = inl b

\end{code}

5. (A → B) → (B → C) → A → C

\begin{code}

Axiom₅ : {A B C : Prop}
       → (A → B) → (B → C) → A → C
Axiom₅ f g a = g (f a)

\end{code}

6. A → (A → B) → B

\begin{code}

Axiom₆ : {A B : Prop}
       → A → (A → B) → B
Axiom₆ a f = f a

\end{code}

7. (a : A) → (∀ x → P x) → P a

\begin{code}

Axiom₇ : {A : Type} {P : A → Prop}
       → (a : A) → (∀ x → P x) → P a
Axiom₇ a f = f a

\end{code}

Answers of the exercises

\begin{code}

Axiom₈ : {A B C : Prop}
       → (A ∧ B → C) → A → B → C
Axiom₈ f a b = f (a , b)

Axiom₉ : {A B C : Prop}
       → (A → B) → C ∨ A → C ∨ B
Axiom₉ f (inl c) = inl c
Axiom₉ f (inr a) = inr (f a)

Axiom₁₀ : {A : Type} {P : A → Prop} {Q : Prop}
        → (∀ x → Q → P x) → Q → ∀ x → P x
Axiom₁₀ f q x = f x q

Axiom₁₁ : {A : Type} {P : A → Prop}
        → (a : A) → P a → ∃ \x → P x
Axiom₁₁ a p = (a , p)

Axiom₁₂ : {A : Type} {P : A → Prop} {Q : Prop}
        → (∀ x → P x → Q) → (∃ \x → P x) → Q
Axiom₁₂ f (a , p) = f a p

\end{code}

----------------
    Equality
----------------

\begin{code}

data _≡_ {A : Type} (a : A) : A → Type where
 refl : a ≡ a

sym : {A : Type} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Type} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

ap : {A B : Type} {x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

transport : {A : Type} (P : A → Type) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

\end{code}
