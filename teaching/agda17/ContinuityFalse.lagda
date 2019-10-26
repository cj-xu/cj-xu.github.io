

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

_ᴺ : Set → Set
A ᴺ = ℕ → A

ℕᴺ : Set
ℕᴺ = ℕ ᴺ

{- Exercises

data _≤_ : ℕ → ℕ → Set where
 zero≤ : {n : ℕ} → 0 ≤ n
 succ≤ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

_≤'_ : ℕ → ℕ → Set
n ≤' m = Σ \(k : ℕ) → n + k ≡ m

Prop[≤→≤'] : (n m : ℕ) → n ≤ m → n ≤' m
Prop[≤→≤'] = {!!}

Prop[≤'→≤] : (n m : ℕ) → n ≤' m → n ≤ m
Prop[≤'→≤] = {!!}

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

-}

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

{- Exercise

_≡'[_]_ : {A : Set} → A ᴺ → ℕ → A ᴺ → Set
α ≡'[ n ] β = (i : ℕ) → i < n → α i ≡ β i

Prop[≡[]→≡'[]] : (A : Set) (α β : A ᴺ) (n : ℕ)
               → α ≡[ n ] β → α ≡'[ n ] β
Prop[≡[]→≡'[]] = ?

Prop[≡'[]→≡[]] : (A : Set) (α β : A ᴺ) (n : ℕ)
               → α ≡'[ n ] β → α ≡[ n ] β
Prop[≡'[]→≡[]] = ?

-}

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

\end{code}

The Curry-Howard interpretation of Brouwer's continuity principle fails.

\begin{code}

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
