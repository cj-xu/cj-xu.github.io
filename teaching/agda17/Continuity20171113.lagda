

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

-----------------------
    CH-Cont → 0 = 1
-----------------------

The Curry-Howard interpretation of Brouwer's continuity principle fails.

\begin{code}

CH-Cont : Set
CH-Cont = (f : ℕᴺ → ℕ) (α : ℕᴺ) → Σ \(n : ℕ) → (β : ℕᴺ) → α ≡[ n ] β → f α ≡ f β

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
 ∥∥-comp : {A P : Type} (p : isProp P) (f : A → P)
         → (x : A) → f x ≡ ∥∥-elim p f ∣ x ∣
 funext : {A : Type} {B : A → Type} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

\end{code}

-----------------------------
    Logic of propositions
-----------------------------

             ⊥  :=  𝟘
             ⊤  :=  𝟙
         P → Q  :=  P → Q
         P ∧ Q  :=  P × Q
         P ∨ Q  :=  ∥ P + Q ∥
   ∀(x:A).P(x)  :=  Π(x:A).P(x)
   ∃(x:A).P(x)  :=  ∥ Σ(x:A).P(x) ∥

\begin{code}

module PropLogic where

 ℙ : Type₁
 ℙ = Σ \(P : Type) → isProp P

 Prf : ℙ → Type
 Prf = pr₁

-----------
-- Truth --
-----------

 data 𝟙 : Type where
  ⋆ : 𝟙

 𝟙isProp : isProp 𝟙
 𝟙isProp ⋆ ⋆ = refl

 ⊤ : ℙ
 ⊤ = 𝟙 , 𝟙isProp

-------------
-- Falsity --
-------------

 data 𝟘 : Type where

 𝟘isProp : isProp 𝟘
 𝟘isProp ()

 ⊥ : ℙ
 ⊥ = 𝟘 , 𝟘isProp

-----------------
-- Conjunction --
-----------------

 infixr 20 _×_
 infixr 20 _∧_

 _×_ : Type → Type → Type
 A × B = Σ \(_ : A) → B

-- ap² : {A B C : Type} {a a' : A} {b b' : B}
--     → (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
-- ap² f refl refl = refl

 pair⁼ : {A B : Type} {a a' : A} {b b' : B}
       → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
 pair⁼ refl refl = refl

 ×-preserves-prop : {A B : Type} → isProp A → isProp B → isProp (A × B)
 ×-preserves-prop pA pB (a , b) (a' , b') = pair⁼ (pA a a') (pB b b')

 _∧_ : ℙ → ℙ → ℙ
 (A , pA) ∧ (B , pB) = (A × B) , ×-preserves-prop pA pB

-----------------
-- Disjunction --
-----------------

 infixr 19 _+_
 infixr 19 _∨_

 data _+_ (A B : Type) : Type where
  inl : A → A + B
  inr : B → A + B

 _∨_ : ℙ → ℙ → ℙ
 (A , pA) ∨ (B , pB) = ∥ A + B ∥ , ∥∥-isProp

 ∨-inl : {A B : ℙ} → Prf A → Prf (A ∨ B)
 ∨-inl a = ∣ inl a ∣

 ∨-inr : {A B : ℙ} → Prf B → Prf (A ∨ B)
 ∨-inr b = ∣ inr b ∣

-----------------
-- Implication --
-----------------

 infixr 18 _⇒_

 →-preserves-prop : {A B : Type} → isProp B → isProp (A → B)
 →-preserves-prop pB f g = funext (λ x → pB (f x) (g x))

 _⇒_ : ℙ → ℙ → ℙ
 (A , pA) ⇒ (B , pB) = (A → B) , →-preserves-prop pB

------------------------------
-- Universal quantification --
------------------------------

 Π-preserves-prop : {A : Type} {B : A → Type} → (∀ x → isProp (B x)) → isProp ((x : A) → B x)
 Π-preserves-prop pB f g = funext (λ x → pB x (f x) (g x))

 ∀ᴾ : {X : Type} → (X → ℙ) → ℙ
 ∀ᴾ {X} A = Φ , ΦisProp
  where
   Φ : Type
   Φ = (x : X) → pr₁ (A x)
   ΦisProp : isProp Φ
   ΦisProp = Π-preserves-prop (λ x → pr₂ (A x))

--------------------------------
-- Existential quantification --
--------------------------------

 ∃ᴾ : {X : Type} → (X → ℙ) → ℙ
 ∃ᴾ {X} A = Φ , ∥∥-isProp
  where
   Φ : Type
   Φ = ∥ (Σ \x → pr₁ (A x)) ∥

---------------------------------------------
-- Some rules in the logic of propositions --
---------------------------------------------

 ∨-introᴸ : (A B : ℙ)
          → Prf A → Prf (A ∨ B)
 ∨-introᴸ _ _ a = ∣ inl a ∣

 ∨-introᴿ : (A B : ℙ)
          → Prf B → Prf (A ∨ B)
 ∨-introᴿ _ _ b = ∣ inr b ∣

 ∨-elim : (A B C : ℙ)
        → Prf (A ⇒ C) → Prf (B ⇒ C) → Prf (A ∨ B) → Prf C
 ∨-elim (A , pA) (B , pB) (C , pC) f g = ∥∥-elim pC claim
  where
   claim : A + B → C
   claim (inl a) = f a
   claim (inr b) = g b

 ∃ᴾ-intro : (X : Type) (A : X → ℙ)
          → (x : X) → Prf (A x) → Prf (∃ᴾ \x → A x)
 ∃ᴾ-intro _ _ x p = ∣ (x , p) ∣

 ∃ᴾ-elim : (X : Type) (A : X → ℙ) (B : ℙ)
         → Prf (∀ᴾ \x → (A x ⇒ B)) → Prf ((∃ᴾ \x → A x) ⇒ B) 
 ∃ᴾ-elim X A (B , pB) f = ∥∥-elim pB claim
  where
   claim : (Σ \x → pr₁ (A x)) → B
   claim (x , p) = f x p

\end{code}

-----------------------
    Axiom of choice
-----------------------

\begin{code}

AC : Type₁
AC = (A : Type) (P : A → Type)
   → ((x : A) → ∥ P x ∥) → ∥ ((x : A) → P x) ∥

-- You may expect the following to be called the axiom of choice.
AC' : Type₁
AC' = (A B : Type) (P : A → B → Type)
    → ((x : A) → ∥ (Σ \(y : B) → P x y) ∥) → ∥ (Σ \(f : A → B) → (x : A) → P x (f x)) ∥

-- But they are actually equivalent!
AC→AC' : AC → AC'
AC→AC' ac A B P φ = ∥∥-elim ∥∥-isProp claim₀ claim₁
 where
  Q : A → Type
  Q x = Σ \(y : B) → P x y
  claim₀ : ((x : A) → Q x) → ∥ (Σ \(f : A → B) → (x : A) → P x (f x)) ∥
  claim₀ f = ∣ (λ x → pr₁ (f x)) , (λ x → pr₂ (f x)) ∣
  claim₁ : ∥ ((x : A) → Q x) ∥
  claim₁ = ac A Q φ

AC'→AC : AC' → AC
AC'→AC ac' A P ψ = ∥∥-elim ∥∥-isProp claim₀ claim₂
 where
  Q : A → A → Type
  Q x _ = P x
  claim₀ : (Σ \(f : A → A) → (x : A) → P x) → ∥ ((x : A) → P x) ∥
  claim₀ (_ , h) = ∣ h ∣
  claim₁ : (x : A) → ∥ (Σ \(_ : A) → P x) ∥
  claim₁ x = ∥∥-elim ∥∥-isProp (λ p → ∣ x , p ∣) (ψ x)
  claim₂ : ∥ (Σ \(f : A → A) → (x : A) → Q x (f x)) ∥
  claim₂ = ac' A A Q claim₁

\end{code}

------------------------------------------------------------
    A consistent formulation of the continuity principle
------------------------------------------------------------

\begin{code}

Cont : Type
Cont = (f : ℕᴺ → ℕ) (α : ℕᴺ) → ∥ (Σ \(n : ℕ) → (β : ℕᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

\end{code}
