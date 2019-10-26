

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                        The Fan Theorem
                        ---------------

                         Chuangjie Xu

           14-16 Monday 4th December 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/

\begin{code}

open import Preliminaries

\end{code}

-------------------------------------------------
  Brouwer's Fan Theorem:  Every bar is uniform.
-------------------------------------------------

■ It's mainly for justifying pointwise analysis (Brouwer's motivation).

■ Brouwer proved it using his Bar Theorem.

■ It is classically true (see e.g. Dr. Berger's lecture notes).

■ It is refuted in constructive recursive math (RUSS).




In this course, we will study

1. the type-theoretic formulations of the Fan Theorem,

2. some non-classical principles related to the Fan Theorem, and

3. some constructively provalbe variants of the Fan Theorem.



To formulate the Fan theorem, we need the following definitions.

------------
-- Subset --
------------

\begin{code}

Subset : Set → Set₁
Subset X = X → Set
        -- X → Prop   more precisely

_∈_ : {X : Set} → X → Subset X → Set
x ∈ A = A x

detachable : {X : Set} → Subset X → Set
detachable A = ∀ x → A x + ¬ (A x)

\end{code}

----------------------
-- Finite sequences --
----------------------

Design choice:  lists  VS  vectors

\begin{code}

data _* (A : Set) : Set where
 ε    : A *
 _::_ : A → A * → A *

-- Length of finite sequences
│_│ : {A : Set} → A * → ℕ
│ u │ = {!!}

-- Restriction (or finite prefix) of infinite sequences
_⌜_⌝ : {A : Set} → A ᴺ → ℕ → A *
α ⌜ n ⌝ = {!!}

\end{code}

---------
-- Bar --
---------

A subset B of 𝟚* is a bar if any infinite binary sequence α has some
restriction in B.

\begin{code}

𝟚* : Set
𝟚* = 𝟚 *

CH-Bar : Subset 𝟚* → Set
CH-Bar B = {!!}

Bar : Subset 𝟚* → Set
Bar B = {!!}

\end{code}

A subset B of 𝟚* is a uniform bar if there exists N such that every
sequence α has some restriction in B with length smaller than N.

\begin{code}

CH-UniformBar : Subset 𝟚* → Set
CH-UniformBar B = {!!}

UniformBar : Subset 𝟚* → Set
UniformBar B = {!!}

\end{code}

-------------------
-- Two questions --
-------------------

before formulating the Fan Theorem:

(1) for detachable bars? (Kleene's example)

(2) for bars closed under extension (Berger's lecture notes)



A subset B of 𝟚* is closed under extension if every extension of u in
B is also in B.

Design choice:  extension function  VS  extension relation

\begin{code}

ext-closed : Subset 𝟚* → Set
ext-closed B = {!!}

\end{code}

---------------------------------------------------------
  Four type-theoretic variants of Brouwer's Fan Theorem
---------------------------------------------------------

\begin{code}

CH-Fan : Set₁
CH-Fan = {!!}

Fan : Set₁
Fan = {!!}

CH-Fanᴰ : Set₁
CH-Fanᴰ = {!!}

Fanᴰ : Set₁
Fanᴰ = {!!}

\end{code}
