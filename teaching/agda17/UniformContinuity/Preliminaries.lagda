Chuangjie Xu, 22.11.2017

-------------------------
    A minimal library
-------------------------

for proving that the two type-theoretic formulations of Brouwer's
uniform-continuity principle are equivalent.

\begin{code}

module Preliminaries where

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

case : {i j k : Level} {A : Set i} {B : Set j} {C : Set k}
     → (A → C) → (B → C) → A + B → C
case f g (inl a) = f a
case f g (inr b) = g b

cases : {i j k l : Level} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
      → (A → C) → (B → D) → A + B → C + D
cases f g (inl a) = inl (f a)
cases f g (inr b) = inr (g b)

infix 1 _≡_

data _≡_ {i : Level} {A : Set i} (a : A) : A → Set i where
 refl : a ≡ a

transport : {i j : Level} {A : Set i} (P : A → Set j) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

ap : {i j : Level} {A : Set i} {B : Set j}
   → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

sym : {i : Level} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

trans : {i : Level} {A : Set i} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

pair⁼ : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'}
      → (e : a ≡ a') → transport B e b ≡ b'
      → (a , b) ≡ (a' , b')
pair⁼ refl refl = refl

pairˣ⁼ : {A B : Set} {a a' : A} {b b' : B}
       → a ≡ a' → b ≡ b'
       → (a , b) ≡ (a' , b')
pairˣ⁼ refl refl = refl

data 𝟘 : Set where

𝟘-elim : {i : Level} {A : Set i} → 𝟘 → A
𝟘-elim ()

¬ : {i : Level} → Set i → Set i
¬ A = A → 𝟘

infix 10 _≢_

_≢_ : {i : Level} {A : Set i} → A → A → Set i
x ≢ y = ¬ (x ≡ y)

data 𝟙 : Set where
 ⋆ : 𝟙

data 𝟚 : Set where
 𝟎 𝟏 : 𝟚

Thm[0≢1] : 𝟎 ≢ 𝟏
Thm[0≢1] e = fact ⋆
 where
  A : 𝟚 → Set
  A 𝟎 = 𝟘
  A 𝟏 = 𝟙
  fact : A 𝟏 → A 𝟎
  fact = transport A (sym e)

𝟚-discrete : {x y : 𝟚} → (x ≡ y) + (x ≢ y)
𝟚-discrete {𝟎} {𝟎} = inl refl
𝟚-discrete {𝟎} {𝟏} = inr (λ ())
𝟚-discrete {𝟏} {𝟎} = inr (λ ())
𝟚-discrete {𝟏} {𝟏} = inl refl

Lemma[b≢0→b≡1] : {b : 𝟚} → b ≢ 𝟎 → b ≡ 𝟏
Lemma[b≢0→b≡1] {𝟎} f = 𝟘-elim (f refl)
Lemma[b≢0→b≡1] {𝟏} _ = refl

Lemma[b≢1→b≡0] : {b : 𝟚} → b ≢ 𝟏 → b ≡ 𝟎
Lemma[b≢1→b≡0] {𝟎} _ = refl
Lemma[b≢1→b≡0] {𝟏} f = 𝟘-elim (f refl)


data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred  0       = 0
pred (succ n) = n

ℕ-discrete : {n m : ℕ} → (n ≡ m) + (n ≢ m)
ℕ-discrete {0}      {0}      = inl refl
ℕ-discrete {0}      {succ m} = inr (λ ())
ℕ-discrete {succ n} {0}      = inr (λ ())
ℕ-discrete {succ n} {succ m} = step ℕ-discrete
 where
  step : (n ≡ m) + (n ≢ m) → (succ n ≡ succ m) + (succ n ≢ succ m)
  step (inl e) = inl (ap succ e)
  step (inr f) = inr (λ e → f (ap pred e))

infix 50 _≤_
infix 50 _<_

data _≤_ : ℕ → ℕ → Set where
 zero≤ : {n : ℕ} → 0 ≤ n
 succ≤ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = zero≤
≤-refl {succ n} = succ≤ ≤-refl

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ  zero≤    = zero≤
≤-r-succ (succ≤ r) = succ≤ (≤-r-succ r)

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans  zero≤     _        = zero≤
≤-trans (succ≤ r) (succ≤ s) = succ≤ (≤-trans r s)

Lemma[n≰m→m<n] : {n m : ℕ} → ¬ (n ≤ m) → m < n
Lemma[n≰m→m<n] {0}      {m}      f = 𝟘-elim (f zero≤)
Lemma[n≰m→m<n] {succ n} {0}      f = succ≤ zero≤
Lemma[n≰m→m<n] {succ n} {succ m} f = succ≤ (Lemma[n≰m→m<n] (λ z → f (succ≤ z)))

Lemma[n≤m+1→n≤m∨n≡m+1] : {n m : ℕ} → n ≤ succ m → (n ≤ m) + (n ≡ succ m)
Lemma[n≤m+1→n≤m∨n≡m+1] {0}      {m}      r = inl zero≤
Lemma[n≤m+1→n≤m∨n≡m+1] {succ 0} {0}      r = inr refl
Lemma[n≤m+1→n≤m∨n≡m+1] {succ (succ n)} {0} (succ≤ ())
Lemma[n≤m+1→n≤m∨n≡m+1] {succ n} {succ m} (succ≤ r) = cases c₀ c₁ IH
 where
  c₀ : n ≤ m → succ n ≤ succ m
  c₀ = succ≤
  c₁ : n ≡ succ m → succ n ≡ succ (succ m)
  c₁ e = ap succ e
  IH : (n ≤ m) + (n ≡ succ m)
  IH = Lemma[n≤m+1→n≤m∨n≡m+1] r

Lemma[n≤m∧m≤n→n=m] : {n m : ℕ}
                   → n ≤ m → m ≤ n → n ≡ m
Lemma[n≤m∧m≤n→n=m]  zero≤     zero≤    = refl
Lemma[n≤m∧m≤n→n=m] (succ≤ r) (succ≤ s) = ap succ (Lemma[n≤m∧m≤n→n=m] r s)

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

ℕ-isSet : {n m : ℕ} → isProp (n ≡ m)
ℕ-isSet refl refl = refl   -- Use Agda's K-axiom (or UIP)

ℕ-≤-isProp : (n m : ℕ) → isProp (n ≤ m)
ℕ-≤-isProp  0        m        zero≤     zero≤     = refl
ℕ-≤-isProp (succ n)  0       ()
ℕ-≤-isProp (succ n) (succ m) (succ≤ r) (succ≤ r') = ap succ≤ IH
 where
  IH : r ≡ r'
  IH = ℕ-≤-isProp n m r r'

\end{code}

-------------------------------
    Function extensionality
-------------------------------

\begin{code}

postulate
 funext : {A : Type} {B : A → Type} {f g : (x : A) → B x}
        → (∀ x → f x ≡ g x) → f ≡ g

\end{code}

-------------------------
    Minimal existence
-------------------------

\begin{code}


Σ-min : (ℕ → Type) → Type
Σ-min A = Σ \(k : ℕ) → A k × ((n : ℕ) → A n → k ≤ n)

CoV-induction : {A : ℕ → Set}
              → (∀ n → (∀ m → m < n → A m) → A n) → ∀ n → A n
CoV-induction {A} step n = step n (claim n)
 where
  claim : ∀ k m → m < k → A m
  claim  0       m ()
  claim (succ k) m (succ≤ r) = step m (λ l s → claim k l (≤-trans s r))

Lemma[≤-dec-∀+∃] : {A : ℕ → Set}
                 → (n : ℕ) → (∀(m : ℕ) → m ≤ n → (A m) + ¬ (A m))
                 → (∀ m → m ≤ n → ¬(A m)) + (Σ \m → m ≤ n × A m)
Lemma[≤-dec-∀+∃] {A} 0 dA = case c₀ c₁ (dA 0 zero≤)
 where
  c₀ : A 0 → (∀ m → m ≤ 0 → ¬ (A m)) + (Σ \m → m ≤ 0 × A m)
  c₀ a0 = inr (0 , zero≤ , a0)
  c₁ : ¬ (A 0) → (∀ m → m ≤ 0 → ¬ (A m)) + (Σ \m → m ≤ 0 × A m)
  c₁ f0 = inl claim
   where
    claim : ∀ m → m ≤ 0 → ¬ (A m)
    claim  0       zero≤ = f0
    claim (succ m) ()
Lemma[≤-dec-∀+∃] {A} (succ n) dA = case c₀ c₁ (dA (succ n) ≤-refl)
 where
  c₀ : A (succ n) → (∀ m → m ≤ succ n → ¬ (A m)) + (Σ \m → m ≤ succ n × A m)
  c₀ asn = inr (succ n , ≤-refl , asn)
  c₁ : ¬ (A (succ n)) → (∀ m → m ≤ succ n → ¬ (A m)) + (Σ \m → m ≤ succ n × A m)
  c₁ fsn = cases d₀ d₁ (Lemma[≤-dec-∀+∃] n dA')
   where
    dA' : (m : ℕ) → m ≤ n → A m + ¬ (A m)
    dA' m r = dA m (≤-r-succ r)
    d₀ : (∀ m → m ≤ n → ¬ (A m)) → ∀ m → m ≤ succ n → ¬ (A m)
    d₀ f m r = case (f m) (λ e am → 𝟘-elim (fsn (transport A e am))) (Lemma[n≤m+1→n≤m∨n≡m+1] r)
    d₁ : (Σ \m → m ≤ n × A m) → Σ \m → m ≤ succ n × A m
    d₁ (m , r , am) = m , ≤-r-succ r , am

Lemma[Σ-min] : (A : ℕ → Type)
             → (n : ℕ) → A n
             → ((m : ℕ) → m ≤ n → (A m) + ¬ (A m))
             → Σ-min \(k : ℕ) → A k
Lemma[Σ-min] A = CoV-induction step
 where
  P : ℕ → Type
  P n = A n → ((m : ℕ) → m ≤ n → (A m) + ¬ (A m)) → Σ-min \(k : ℕ) → A k
  step : ∀ n → (∀ m → m < n → P m) → P n
  step  0       _ a0  dA = 0 , a0 , λ _ _ → zero≤
  step (succ n) φ asn dA = case c₀ c₁ (Lemma[≤-dec-∀+∃] n dAn)
   where
    dAn : (m : ℕ) → m ≤ n → (A m) + ¬ (A m)
    dAn m r = dA m (≤-r-succ r)
    c₀ : (∀ m → m ≤ n → ¬(A m)) → Σ-min \(m : ℕ) → A m
    c₀ f = succ n , asn , min
     where
      min : (m : ℕ) → A m → succ n ≤ m
      min m am = Lemma[n≰m→m<n] (λ r → f m r am)
    c₁ : (Σ \m → m ≤ n × A m) → Σ-min \(m : ℕ) → A m
    c₁ (m , r , am) = φ m (succ≤ r) am dAm
     where
      dAm : (k : ℕ) → k ≤ m → (A k) + ¬ (A k)
      dAm k s = dA k (≤-trans s (≤-r-succ r))

Σ-min-isProp : (A : ℕ → Type)
             → ((n : ℕ) → isProp (A n))
             → isProp (Σ-min \(n : ℕ) → A n)
Σ-min-isProp A pA (k , ak , mk) (k' , ak' , mk') = pair⁼ ek (pairˣ⁼ e₀ e₁)
 where
  ek : k ≡ k'
  ek = Lemma[n≤m∧m≤n→n=m] (mk k' ak') (mk' k ak)
  w w' : A k' × (∀ m → A m → k' ≤ m)
  w  = transport (λ x → A x × (∀ m → A m → x ≤ m)) ek (ak , mk)
  w' = (ak' , mk')
  e₀ : pr₁ w ≡ ak'
  e₀ = pA k' (pr₁ w) ak'
  e₁ : pr₂ w ≡ mk'
  e₁ = funext (λ m → funext (λ am → ℕ-≤-isProp k' m (pr₂ w m am) (mk' m am)))

\end{code}

Finite sequences

\begin{code}

infixl 60 _::_

data Vec (A : Set) : ℕ → Set where
 ε    : Vec A 0
 _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

𝟚^ : ℕ → Set
𝟚^ n = Vec 𝟚 n

infixl 55 _*_

_*_ : {A : Set} {n : ℕ}
    → Vec A n → A ᴺ → A ᴺ
ε * α = α
(x :: v * α)  0       = x
(x :: v * α) (succ i) = (v * α) i

Lemma[*-≡[]] : {A : Set} {n : ℕ} (s : Vec A n) {α β : A ᴺ}
             → (s * α) ≡[ n ] (s * β)
Lemma[*-≡[]]  ε       = ≡[zero]
Lemma[*-≡[]] (a :: s) = ≡[succ] refl (Lemma[*-≡[]] s)

take : {A : Set} → (n : ℕ) → A ᴺ → Vec A n
take  0       α = ε
take (succ n) α = α 0 :: take n (tail α)

Lemma[*-take-≡[]] : {α β : 𝟚ᴺ} (n : ℕ)
                  → α ≡[ n ] (take n α) * β
Lemma[*-take-≡[]]  0       = ≡[zero]
Lemma[*-take-≡[]] (succ n) = ≡[succ] refl (Lemma[*-take-≡[]] n)

Lemma[≡[]-*-take-≡[]] : {α β γ : 𝟚ᴺ} {n : ℕ}
                      → α ≡[ n ] β → β ≡[ n ] (take n α) * γ
Lemma[≡[]-*-take-≡[]]  ≡[zero]       = ≡[zero]
Lemma[≡[]-*-take-≡[]] (≡[succ] e en) = ≡[succ] (sym e) (Lemma[≡[]-*-take-≡[]] en)

Lemma[*-take-0] : {α β : 𝟚ᴺ} (n : ℕ)
                → β 0 ≡ (take n α * β) n
Lemma[*-take-0]  0       = refl
Lemma[*-take-0] (succ n) = Lemma[*-take-0] n

Lemma[𝟚^-dec] : (n : ℕ) {P : 𝟚^ n → Type}
              → (∀ s → P s + ¬ (P s)) → (∀ s → P s) + ¬ (∀ s → P s)
Lemma[𝟚^-dec] 0 {P} d = cases c₀ c₁ (d ε) 
 where
  c₀ : P ε → ∀ s → P s
  c₀ p ε = p
  c₁ : ¬ (P ε) → ¬ (∀ s → P s)
  c₁ f g = f (g ε)
Lemma[𝟚^-dec] (succ n) {P} d = case c₀ c₁ IH₀
 where
  P₀  : 𝟚^ n → Type
  P₀  s = P (𝟎 :: s)
  d₀  : ∀ s → P₀ s + ¬ (P₀ s)
  d₀  s = d (𝟎 :: s)
  IH₀ : (∀ s → P₀ s) + ¬ (∀ s → P₀ s)
  IH₀ = Lemma[𝟚^-dec] n d₀
  P₁  : 𝟚^ n → Type
  P₁  s = P (𝟏 :: s)
  d₁  : ∀ s → P₁ s + ¬ (P₁ s)
  d₁  s = d (𝟏 :: s)
  IH₁ : (∀ s → P₁ s) + ¬ (∀ s → P₁ s)
  IH₁ = Lemma[𝟚^-dec] n d₁
  c₀ : (∀ s → P₀ s) → (∀ s → P s) + ¬ (∀ s → P s)
  c₀ ψ₀ = cases c₀₀ c₀₁ IH₁
   where
    c₀₀ : (∀ s → P₁ s) → (∀ s → P s)
    c₀₀ ψ₁ (𝟎 :: s) = ψ₀ s
    c₀₀ ψ₁ (𝟏 :: s) = ψ₁ s
    c₀₁ : ¬ (∀ s → P₁ s) → ¬ (∀ s → P s)
    c₀₁ φ₁ ψ = φ₁ (λ s → ψ (𝟏 :: s))
  c₁ : ¬ (∀ s → P₀ s) → (∀ s → P s) + ¬ (∀ s → P s)
  c₁ φ₀ = inr (λ ψ → φ₀ (λ s → ψ (𝟎 :: s)))


\end{code}
