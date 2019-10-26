Chuangjie Xu

--------------------------------------
    A minimal library of sequences
--------------------------------------

for the course "Executing Proofs as Computer Programs"

\begin{code}

module Sequence where

open import Preliminaries

\end{code}

------------------------
-- Infinite sequences --
------------------------

\begin{code}

_ᴺ : Set → Set
A ᴺ = ℕ → A

𝟚ᴺ : Set
𝟚ᴺ = 𝟚 ᴺ

0ʷ 1ʷ : 𝟚ᴺ
0ʷ i = 𝟎
1ʷ i = 𝟏

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

≡[succ]' : {A : Set} {α β : A ᴺ} {n : ℕ}
         → α ≡[ n ] β → α n ≡ β n → α ≡[ succ n ] β
≡[succ]'  ≡[zero]      e = ≡[succ] e ≡[zero]
≡[succ]' (≡[succ] h t) e = ≡[succ] h (≡[succ]' t e)

Lemma[≡[]-≤] : {n m : ℕ} {α β : 𝟚ᴺ}
             → α ≡[ n ] β → m ≤ n → α ≡[ m ] β
Lemma[≡[]-≤]  en             zero≤    = ≡[zero]
Lemma[≡[]-≤] (≡[succ] e en) (succ≤ r) = ≡[succ] e (Lemma[≡[]-≤] en r)

≡[]-refl : {A : Set} {α : A ᴺ} {n : ℕ}
         → α ≡[ n ] α
≡[]-refl {_} {_} {0}      = ≡[zero]
≡[]-refl {_} {_} {succ n} = ≡[succ] refl ≡[]-refl

≡[]-sym : {A : Set} {α β : A ᴺ} {n : ℕ}
        → α ≡[ n ] β → β ≡[ n ] α
≡[]-sym  ≡[zero]      = ≡[zero]
≡[]-sym (≡[succ] e r) = ≡[succ] (sym e) (≡[]-sym r)

≡[]-trans : {A : Set} {α β γ : A ᴺ} {n : ℕ}
          → α ≡[ n ] β → β ≡[ n ] γ → α ≡[ n ] γ
≡[]-trans  ≡[zero]       ≡[zero]        = ≡[zero]
≡[]-trans (≡[succ] e r) (≡[succ] e' r') = ≡[succ] (trans e e') (≡[]-trans r r')

\end{code}

----------------------
-- Finite sequences --
----------------------

\begin{code}

infixr 30 _::_
infixl 40 _^_
infixr 26 _✦_
infixr 27 _✧_

data _^_ (A : Set) : ℕ → Set where
 ε    : A ^ 0
 _::_ : {n : ℕ} → A → A ^ n → A ^ succ n

Vec : Set → ℕ → Set
Vec A n = A ^ n

Vec⁼ : {A : Set} {x y : A} {n : ℕ} {u v : A ^ n}
    → x ≡ y → u ≡ v → (x :: u) ≡ (y :: v)
Vec⁼ refl refl = refl

head⁼ : {A : Set} {x y : A} {n : ℕ} {u v : A ^ n}
      → (x :: u) ≡ (y :: v) → x ≡ y
head⁼ refl = refl

tail⁼ : {A : Set} {x y : A} {n : ℕ} {u v : A ^ n}
      → (x :: u) ≡ (y :: v) → u ≡ v
tail⁼ refl = refl

_✦_ : {A : Set} {n m : ℕ} → A ^ n → A ^ m → A ^ (n +ᴺ m)
ε ✦ v = v
(a :: u) ✦ v = a :: (u ✦ v)

⟨_⟩ : {A : Set} → A → A ^ 1
⟨ a ⟩ = a :: ε

_✧_ : {A : Set} {n : ℕ} → A ^ n → A → A ^ succ n
ε ✧ a = ⟨ a ⟩
h :: u ✧ a = h :: (u ✧ a)


infix 90 _⌜_⌝

_⌜_⌝ : {A : Set} → A ᴺ → (n : ℕ) → A ^ n
α ⌜ 0 ⌝      = ε
α ⌜ succ n ⌝ = head α :: tail α ⌜ n ⌝


𝟚^_ : ℕ → Set
𝟚^ n = 𝟚 ^ n

𝟚*-discrete : {n : ℕ} {u v : 𝟚^ n} → (u ≡ v) + (u ≢ v)
𝟚*-discrete {_} {ε}      {ε}      = inl refl
𝟚*-discrete {_} {a :: u} {b :: v} = case c₀ c₁ 𝟚-discrete
 where
  c₀ : a ≡ b → ((a :: u) ≡ (b :: v)) + ((a :: u) ≢ (b :: v))
  c₀ refl = cases d₀ d₁ 𝟚*-discrete
   where
    d₀ : u ≡ v → (a :: u) ≡ (b :: v)
    d₀ refl = refl
    d₁ : u ≢ v → (a :: u) ≢ (b :: v)
    d₁ f e = f (tail⁼ e)
  c₁ : a ≢ b → ((a :: u) ≡ (b :: v)) + ((a :: u) ≢ (b :: v))
  c₁ f = inr (λ e → f (head⁼ e))

max* : {n : ℕ} → (𝟚^ n → ℕ) → ℕ
max* {0}      ν = ν ε
max* {succ n} ν = max (max* (λ u → ν (𝟎 :: u))) (max* (λ u → ν (𝟏 :: u)))

max*-spec : {n : ℕ} (ν : 𝟚^ n → ℕ) (u : 𝟚^ n) → ν u ≤ max* ν
max*-spec ν  ε       = ≤-refl
max*-spec ν (𝟎 :: u) = ≤-trans claim₀ claim₁
 where
  claim₀ : ν (𝟎 :: u) ≤ max* (λ z → ν (𝟎 :: z))
  claim₀ = max*-spec (λ v → ν (𝟎 :: v)) u
  claim₁ : max* (λ z → ν (𝟎 :: z)) ≤ max* ν
  claim₁ = max-spec₀ (max* (λ z → ν (𝟎 :: z))) (max* (λ z → ν (𝟏 :: z)))
max*-spec ν (𝟏 :: u) = ≤-trans claim₀ claim₁
 where
  claim₀ : ν (𝟏 :: u) ≤ max* (λ z → ν (𝟏 :: z))
  claim₀ = max*-spec (λ v → ν (𝟏 :: v)) u
  claim₁ : max* (λ z → ν (𝟏 :: z)) ≤ max* ν
  claim₁ = max-spec₁ (max* (λ z → ν (𝟎 :: z))) (max* (λ z → ν (𝟏 :: z)))

Subset-of-𝟚* : Set₁
Subset-of-𝟚* = {n : ℕ} → 𝟚^ n → Set

detachable : Subset-of-𝟚* → Set
detachable B = {n : ℕ} (u : 𝟚^ n) → B u + ¬ B u

\end{code}

The following operations and lemmas are for proving the equivalence of
the two formulations of uniform bars.

\begin{code}

-- Concatenation of a finite with an infinite sequence
cons : {A : Set} {n : ℕ} → A ^ n → A ᴺ → A ᴺ
cons  ε       α          = α
cons (a :: u) α  0       = a
cons (a :: u) α (succ i) = cons u α i

Lemma[⌜⌝-cons] : {A : Set} {n : ℕ} (u : A ^ n) {α : A ᴺ}
               → cons u α ⌜ n ⌝ ≡ u
Lemma[⌜⌝-cons]  ε       = refl
Lemma[⌜⌝-cons] (a :: u) = Vec⁼ refl (Lemma[⌜⌝-cons] u)

Lemma[𝟚*-dec] : (B : Subset-of-𝟚*) → detachable B
              → (n : ℕ) → ((u : 𝟚^ n) → u ∈ B) + ¬ ((u : 𝟚^ n) → u ∈ B)
Lemma[𝟚*-dec] B dB 0 = cases c₀ c₁ (dB ε)
 where
  c₀ : ε ∈ B → (u : 𝟚^ 0) → u ∈ B
  c₀ b ε = b
  c₁ : ¬ (ε ∈ B) → ¬ ((u : 𝟚^ 0) → u ∈ B)
  c₁ f h = f (h ε)
Lemma[𝟚*-dec] B dB (succ n) = case c₀ c₁ IH₀
 where
  IH₀ : ((u : 𝟚^ n) → (𝟎 :: u) ∈ B) + ¬ ((u : 𝟚^ n) → (𝟎 :: u) ∈ B)
  IH₀ = Lemma[𝟚*-dec] (λ u → B (𝟎 :: u)) (λ u → dB (𝟎 :: u)) n
  IH₁ : ((u : 𝟚^ n) → (𝟏 :: u) ∈ B) + ¬ ((u : 𝟚^ n) → (𝟏 :: u) ∈ B)
  IH₁ = Lemma[𝟚*-dec] (λ u → B (𝟏 :: u)) (λ u → dB (𝟏 :: u)) n
  c₀ : ((u : 𝟚^ n) → (𝟎 :: u) ∈ B)
     → ((u : 𝟚^ succ n) → u ∈ B) + ¬ ((u : 𝟚^ succ n) → u ∈ B)
  c₀ ψ₀ = cases d₀ d₁ IH₁
   where
    d₀ : ((u : 𝟚^ n) → (𝟏 :: u) ∈ B)
       → ((u : 𝟚^ succ n) → u ∈ B)
    d₀ ψ₁ (𝟎 :: u) = ψ₀ u
    d₀ ψ₁ (𝟏 :: u) = ψ₁ u
    d₁ : ¬ ((u : 𝟚^ n) → (𝟏 :: u) ∈ B)
       → ¬ ((u : 𝟚^ succ n) → u ∈ B)
    d₁ φ₁ ψ = φ₁ (λ u → ψ (𝟏 :: u))
  c₁ : ¬ ((u : 𝟚^ n) → (𝟎 :: u) ∈ B)
     → ((u : 𝟚^ succ n) → u ∈ B) + ¬ ((u : 𝟚^ succ n) → u ∈ B)
  c₁ φ₀ = inr (λ ψ → φ₀ (λ u → ψ (𝟎 :: u)))


infix 25 _⊑_

-- u ⊑ v means u is an extension of v. Example:
-- Consider "0" as the 'set' of all α such that α₀ = 0, and
-- "01" as the 'set' of all α such that α₀ = 0 and α₁ = 1.
-- Then "01" is a 'subset' of "0" and hence "01" ⊑ "0".

data _⊑_ {A : Set} : {n : ℕ} → A ^ n → {m : ℕ} → A ^ m → Set where
 ⊑-ε    : {n : ℕ} {u : A ^ n} → u ⊑ ε
 ⊑-cons : {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {a : A} → u ⊑ v → (a :: u) ⊑ (a :: v) 

Lemma[⊑→≤] : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m}
           → u ⊑ v → m ≤ n
Lemma[⊑→≤]  ⊑-ε       = zero≤
Lemma[⊑→≤] (⊑-cons r) = succ≤ (Lemma[⊑→≤] r)

Lemma[⌜≤⌝-⊑] : {A : Set} {α : A ᴺ} {n m : ℕ} → n ≤ m → α ⌜ m ⌝ ⊑ α ⌜ n ⌝
Lemma[⌜≤⌝-⊑]  zero≤    = ⊑-ε
Lemma[⌜≤⌝-⊑] (succ≤ r) = ⊑-cons (Lemma[⌜≤⌝-⊑] r)

ext-closed : Subset-of-𝟚* → Set
ext-closed B = {n : ℕ} (u : 𝟚^ n) {m : ℕ} (v : 𝟚^ m) → u ⊑ v → v ∈ B → u ∈ B



Lemma[≡[]→⌜⌝] : {A : Set} {α β : A ᴺ} {n : ℕ}
              → α ≡[ n ] β → α ⌜ n ⌝ ≡ β ⌜ n ⌝
Lemma[≡[]→⌜⌝]  ≡[zero]       = refl
Lemma[≡[]→⌜⌝] (≡[succ] e en) = Vec⁼ e (Lemma[≡[]→⌜⌝] en)

headᵛ : {A : Set} {n : ℕ} → A ^ succ n → A
headᵛ (a :: _) = a

tailᵛ : {A : Set} {n : ℕ} → A ^ succ n → A ^ n
tailᵛ (_ :: u) = u

Lemma[⌜⌝→≡[]] : {A : Set} {α β : A ᴺ} {n : ℕ}
              → α ⌜ n ⌝ ≡ β ⌜ n ⌝ → α ≡[ n ] β
Lemma[⌜⌝→≡[]] {_} {_} {_} {0}      refl = ≡[zero]
Lemma[⌜⌝→≡[]] {A} {α} {β} {succ n} esn  = ≡[succ] (ap headᵛ esn) (Lemma[⌜⌝→≡[]] (ap tailᵛ esn))

Lemma[≡[]-cons-⌜⌝] : {A : Set} {α β : A ᴺ} (n : ℕ)
                   → α ≡[ n ] cons (α ⌜ n ⌝) β
Lemma[≡[]-cons-⌜⌝]  0       = ≡[zero]
Lemma[≡[]-cons-⌜⌝] (succ n) = ≡[succ] refl (Lemma[≡[]-cons-⌜⌝] n)

⊑-refl : {A : Set} {n : ℕ} {u : A ^ n}
       → u ⊑ u
⊑-refl {_} {_} {ε}      = ⊑-ε
⊑-refl {_} {_} {a :: u} = ⊑-cons ⊑-refl

⊑-trans : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {k : ℕ} {w : A ^ k}
        → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans  r          ⊑-ε       = ⊑-ε
⊑-trans (⊑-cons r) (⊑-cons s) = ⊑-cons (⊑-trans r s)

\end{code}
