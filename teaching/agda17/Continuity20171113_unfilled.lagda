

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                  Continuity in Type Theory II
                  ----------------------------
                       
                         Chuangjie Xu

           14-16 Monday 13th November 2017, HS B 252

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

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_ᴺ : Set → Set
A ᴺ = ℕ → A

ℕᴺ : Set
ℕᴺ = ℕ ᴺ

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

The Curry-Howard interpretation of Brouwer's continuity principle fails.

\begin{code}

module CH-Cont where

 infixr 10 _+_

 _+_ : ℕ → ℕ → ℕ
 n + zero   = n
 n + succ m = succ (n + m)

 -- The infinite sequence of 0's
 0ʷ : ℕᴺ
 0ʷ = λ i → 0

 -- n zeros-and-then k consists of n 0's followed by infinitely many k's.
 _zeros-and-then_ : ℕ → ℕ → ℕᴺ
 (0 zeros-and-then k)       i       = k
 (succ n zeros-and-then k)  0       = 0
 (succ n zeros-and-then k) (succ i) = (n zeros-and-then k) i

 zeros-and-then-spec₀ : ∀ n {k} → (n zeros-and-then k) n ≡ k
 zeros-and-then-spec₀  0       = refl
 zeros-and-then-spec₀ (succ n) = zeros-and-then-spec₀ n

 zeros-and-then-spec₁ : ∀ n {k} → 0ʷ ≡[ n ] (n zeros-and-then k)
 zeros-and-then-spec₁  0       = ≡[zero]
 zeros-and-then-spec₁ (succ n) = ≡[succ] refl (zeros-and-then-spec₁ n)

 CH-Cont : Set
 CH-Cont = (f : ℕᴺ → ℕ) (α : ℕᴺ) → Σ \(n : ℕ) → (β : ℕᴺ) → α ≡[ n ] β → f α ≡ f β

 Thm : CH-Cont → 0 ≡ 1
 Thm cont = goal
  where
   M : (ℕᴺ → ℕ) → ℕ
   M f = pr₁ (cont f 0ʷ)

   m : ℕ
   m = M (λ α → 0)

   f : ℕᴺ → ℕ
   f β = M (λ α → β (α m))

   claim₀ : f 0ʷ ≡ m
   claim₀ = refl

   claim₁ : (β : ℕᴺ) → 0ʷ ≡[ M f ] β → m ≡ f β
   claim₁ = pr₂ (cont f 0ʷ)

   β : ℕᴺ
   β = (M f + 1) zeros-and-then 1

   claim₂ : 0ʷ ≡[ M f ] β
   claim₂ = ≡[pred] (M f) (zeros-and-then-spec₁ (M f + 1))

   claim₃ : m ≡ f β
   claim₃ = claim₁ β claim₂

   claim₄ : (α : ℕᴺ) → 0ʷ ≡[ m ] α → β 0 ≡ β (α m)
   claim₄ α em = pr₂ (cont (λ α → β (α m)) 0ʷ) α em'
    where
     em' : 0ʷ ≡[ f β ] α
     em' = transport (λ x → 0ʷ ≡[ x ] α) claim₃ em

   α : ℕᴺ
   α = m zeros-and-then (M f + 1)

   claim₅ : 0ʷ ≡[ m ] α
   claim₅ = zeros-and-then-spec₁ m

   goal : 0 ≡ 1
   goal = e₀ ∙ e₁ ∙ e₂
    where
     e₀ : 0 ≡ β (α m)
     e₀ = claim₄ α claim₅
     e₁ : β (α m) ≡ β (M f + 1)
     e₁ = ap β (zeros-and-then-spec₀ m)
     e₂ : β (M f + 1) ≡ 1
     e₂ = zeros-and-then-spec₀ (M f + 1)

\end{code}

Propositions and propositional truncation

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

Logic of propositions

\begin{code}

module PropLogic where

 Prop : Type₁
 Prop = Σ \(P : Type) → isProp P

-----------
-- Truth --
-----------

 data 𝟙 : Type where
  ⋆ : 𝟙

 ⊤ : Prop
 ⊤ = {!!}

-------------
-- Falsity --
-------------

 data 𝟘 : Type where

 ⊥ : Prop
 ⊥ = {!!}

-----------------
-- Conjunction --
-----------------

 infixr 20 _×_
 infixr 20 _∧_

 _×_ : Type → Type → Type
 A × B = Σ \(_ : A) → B

 _∧_ : Prop → Prop → Prop
 (A , pA) ∧ (B , pB) =  (A × B) , {!!}

-----------------
-- Disjunction --
-----------------

 infixr 19 _+_
 infixr 19 _∨_

 data _+_ (A B : Type) : Type where
  inl : A → A + B
  inr : B → A + B

 _∨_ : Prop → Prop → Prop
 (A , pA) ∨ (B , pB) = (A + B) , {!!}

-----------------
-- Implication --
-----------------

 infixr 18 _⇒_

 _⇒_ : Prop → Prop → Prop
 (A , pA) ⇒ (B , pB) = (A → B) , {!!}

------------------------------
-- Universal quantification --
------------------------------

 ∀ᴾ : {X : Type} → (X → Prop) → Prop
 ∀ᴾ A = {!!}

--------------------------------
-- Existential quantification --
--------------------------------

 ∃ᴾ : {X : Type} → (X → Prop) → Prop
 ∃ᴾ A = {!!}


\end{code}

A consistent formulation of the continuity principle

\begin{code}

open PropLogic

Cont : Prop
Cont = {!!}

\end{code}
