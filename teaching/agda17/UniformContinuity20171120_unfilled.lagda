

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

               Uniform Continuity in Type Theory
               ---------------------------------

                         Chuangjie Xu

           14-16 Monday 20th November 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/


---------------------
    Preliminaries
---------------------

A minimal library for today's lecture

\begin{code}

open import Agda.Primitive

infixr 10 _,_

record Σ {i j : Level} {A : Set i} (B : A → Set j) : Set (i ⊔ j) where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infixl 20 _×_
infixl 15 _+_

_×_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
A × B = Σ \(_ : A) → B

data _+_ {i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 inl : A → A + B
 inr : B → A + B

infix 1 _≡_

data _≡_ {i : Level} {A : Set i} (a : A) : A → Set i where
 refl : a ≡ a

transport : {i j : Level} {A : Set i} (P : A → Set j) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

ap : {i j : Level} {A : Set i} {B : Set j}
   → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

infixr 5 _∙_

_∙_ : {i : Level} {A : Set i} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

data 𝟘 : Set where

¬ : Set → Set
¬ A = A → 𝟘

data 𝟚 : Set where
 𝟎 𝟏 : 𝟚

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data _≤_ : ℕ → ℕ → Set where
 zero≤ : {n : ℕ} → 0 ≤ n
 succ≤ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

_ᴺ : Set → Set
A ᴺ = ℕ → A

𝟚ᴺ : Set
𝟚ᴺ = 𝟚 ᴺ

head : {A : Set} → A ᴺ → A
head α = α 0

tail : {A : Set} → A ᴺ → A ᴺ
tail α = λ i → α (succ i)

-- α ≡[ n ] β represents that the first n bits of α and β are equal.
data _≡[_]_ {A : Set} : A ᴺ → ℕ → A ᴺ → Set where
 ≡[zero] : {α β : A ᴺ} → α ≡[ 0 ] β
 ≡[succ] : {α β : A ᴺ} {n : ℕ} → head α ≡ head β → tail α ≡[ n ] tail β → α ≡[ succ n ] β

≡[pred] : {A : Set} {α β : A ᴺ} (n : ℕ)
        → α ≡[ succ n ] β → α ≡[ n ] β
≡[pred]  0        _            = ≡[zero]
≡[pred] (succ n) (≡[succ] r e) = ≡[succ] r (≡[pred] n e)

\end{code}

-------------------------------------------------
    Propositions and propositional truncation
-------------------------------------------------

\begin{code}

Type₁ : Set₂
Type₁ = Set₁

Type  : Type₁
Type  = Set

isProp : Type → Type
isProp P = (x y : P) → x ≡ y

postulate
 ∥_∥ : Type → Type
 ∣_∣ : {A : Type} → A → ∥ A ∥
 ∥∥-isProp : {A : Type} → isProp ∥ A ∥
 ∥∥-elim : {A P : Type} → isProp P → (A → P) → ∥ A ∥ → P

\end{code}

------------------------------------------------------------
    Two formulations of the uniform-continuity principle
------------------------------------------------------------

\begin{code}

CH-UC : Type
CH-UC = (f : 𝟚ᴺ → ℕ) → Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

UC : Type
UC = (f : 𝟚ᴺ → ℕ) → ∥ (Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

\end{code}

-------------------------------------------
    The two formulations are equivalent
-------------------------------------------

One direction is easy.

\begin{code}

Theorem[CH-UC→UC] : CH-UC → UC
Theorem[CH-UC→UC] = {!!}

\end{code}

For the converse, we need the following:

MainLemma. For any type family A : ℕ → Type such that

    (1) A(n) is a proposition for all n,

    (2) if A(n) then A(m) is decidable for all i < n,

  we have

      ∥ Σ(n:ℕ).A(n) ∥ → Σ(n:ℕ).A(n).

Proof sketch: Given n with A(n), we can find the minimal k with A(k),
using the decidability of A(m) for m < n. Since “having a minimal k
with A(k)” is a proposition (proved using function extensionality),
the elimination rule of ∥-∥ gives the desired result.

\begin{code}

postulate
 funext : {A : Type} {B : A → Type} {f g : (x : A) → B x}
        → (∀ x → f x ≡ g x) → f ≡ g

Σ-min : (ℕ → Type) → Type
Σ-min = {!!}

Lemma[Σ-min] : {A : ℕ → Type}
             → (n : ℕ) → A n
             → ((m : ℕ) → m ≤ n → (A m) + ¬ (A m))
             → Σ-min \(k : ℕ) → A k
Lemma[Σ-min] = {!!}

Σ-min-isProp : (A : ℕ → Type)
             → isProp (Σ-min \(n : ℕ) → A n)
Σ-min-isProp A = {!!}

MainLemma : (A : ℕ → Type)
          → ((n : ℕ) → isProp (A n))
          → ((n : ℕ) → A n → (m : ℕ) → m ≤ n → A m + ¬ (A m))
          → ∥ (Σ \(n : ℕ) → A n) ∥ → Σ \(n : ℕ) → A n
MainLemma = {!!}

\end{code}

Since Uc(f) : ℕ → Type, defined by

  Uc(f,n) = (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

satisfies (1) and (2), with the aid of function extensionality, the
two formulations of the uniform-continuity principle are equivalent.

\begin{code}

Uc : (𝟚ᴺ → ℕ) → ℕ → Type
Uc f n = (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

Uc-isProp : (f : 𝟚ᴺ → ℕ)
          → (n : ℕ) → isProp (Uc f n)
Uc-isProp = {!!}

Uc-≤-decidable : (f : 𝟚ᴺ → ℕ)
               → (n : ℕ) → Uc f n → (m : ℕ) → m ≤ n → Uc f m + ¬ (Uc f m)
Uc-≤-decidable = {!!}

Theorem[UC→CH-UC] : UC → CH-UC
Theorem[UC→CH-UC] = {!!}

\end{code}
