Chuangjie Xu

"Untruncate" ∥ Σ P ∥ for detachbale P using Theorem[KECA-TLCA'2013]

\begin{code}

module Untruncation where

open import Preliminaries
open import KECA


Σ-min : (ℕ → Set) → Set
Σ-min P = Σ \(k : ℕ) → P k × (∀ n → P n → k ≤ n)

CoV-induction : {A : ℕ → Set}
              → (∀ n → (∀ m → m < n → A m) → A n) → ∀ n → A n
CoV-induction {A} step n = step n (claim n)
 where
  claim : ∀ k m → m < k → A m
  claim  0       m ()
  claim (succ k) m (succ≤ r) = step m (λ l s → claim k l (≤-trans s r))

Lemma[≤-dec-∀+∃] : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
                 → ∀ n → (∀ m → m < n → ¬ P m) + (Σ \m → m < n × P m)
Lemma[≤-dec-∀+∃] {P} dP  0       = inl (λ _ ())
Lemma[≤-dec-∀+∃] {P} dP (succ n) = case c₀ c₁ (dP n)
 where
  c₀ : P n → (∀ m → m < succ n → ¬ P m) + (Σ \m → m < succ n × P m)
  c₀ pn = inr (n , ≤-refl , pn)
  c₁ : ¬ P n → (∀ m → m < succ n → ¬ P m) + (Σ \m → m < succ n × P m)
  c₁ fn = cases d₀ d₁ (Lemma[≤-dec-∀+∃] dP n)
   where
    d₀ : (∀ m → m < n → ¬ P m) → (∀ m → m < succ n → ¬ P m)
    d₀ φ m (succ≤ r) = case e₀ e₁ (Lemma[n≤m→n<m∨n≡m] r)
     where
      e₀ : m < n → ¬ P m
      e₀ s = φ m s
      e₁ : m ≡ n → ¬ P m
      e₁ e = transport (λ x → ¬ P x) (sym e) fn
    d₁ : (Σ \m → m < n × P m) → (Σ \m → m < succ n × P m)
    d₁ (m , r , pm) = (m , ≤-r-succ r , pm)

ν : {A : Set} → A + ¬ A → A → A
ν (inl a) _ = a
ν (inr f) a = 𝟘-elim (f a)

ν-constant : {A : Set} (w : A + ¬ A) {x y : A} → ν w x ≡ ν w y
ν-constant (inl a)     = refl
ν-constant (inr f) {x} = 𝟘-elim (f x)

Σ-min-step : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
           → ∀ n → (∀ m → m < n → P m → Σ-min P) → P n → Σ-min P
Σ-min-step {P} dP n f pn = case c₀ c₁ (Lemma[≤-dec-∀+∃] dP n)
 where
  c₀ : (∀ m → m < n → ¬ P m) → Σ-min P
  c₀ φ = n , (ν (dP n) pn) , (λ k pk → Lemma[n≯m→n≤m] (λ g → φ k g pk))
  c₁ : (Σ \m → m < n × P m) → Σ-min P
  c₁ (m , r , pm) = f m r pm

Lemma[Σ-min] : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
             → Σ P → Σ-min P
Lemma[Σ-min] dP (n , p) = CoV-induction (Σ-min-step dP) n p

toΣ : {P : ℕ → Set} → Σ-min P → Σ P
toΣ (n , p , _) = (n , p)

μ : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
  → Σ P → Σ P
μ dP u = toΣ (Lemma[Σ-min] dP u)

-- Question: is μ constant?
-- The first component of μ is constant
μ₁-constant : {P : ℕ → Set} (dP : ∀ n → P n + ¬ P n)
            → (u v : Σ P) → pr₁ (μ dP u) ≡ pr₁ (μ dP v)
μ₁-constant dP u v = Lemma[n≤m∧m≤n→n≡m] n≤m m≤n
 where
  n m : ℕ
  n = pr₁ (μ dP u)
  m = pr₁ (μ dP v)
  n≤m : n ≤ m
  n≤m = pr₂ (pr₂ (Lemma[Σ-min] dP u)) m (pr₂ (μ dP v))
  m≤n : m ≤ n
  m≤n = pr₂ (pr₂ (Lemma[Σ-min] dP v)) n (pr₂ (μ dP u))
-- But the second compnent may not be consant, because
--
--    ν (dP n) p ≡ ν (dP m) q
--
-- is needed but not provable.
--
-- Trick: Apply μ twice!!

μ² : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
   → Σ P → Σ P
μ² dP u = μ dP (μ dP u)

equality-cases : {A B C : Set} (w : A + B) 
               → (∀ a → w ≡ inl a → C) → (∀ b → w ≡ inr b → C) → C
equality-cases (inl a) f g = f a refl
equality-cases (inr b) f g = g b refl

μ²-constant : {P : ℕ → Set} (dP : ∀ n → P n + ¬ P n)
            → (u v : Σ P) → μ² dP u ≡ μ² dP v
μ²-constant {P} dP = goal
 where
  lemma : (u v : Σ P) → pr₁ u ≡ pr₁ v → μ dP u ≡ μ dP v
  lemma (n , p) (.n , q) refl = equality-cases fact c₀ c₁
   where
    fact : (∀ m → m < n → ¬ P m) + (Σ \m → m < n × P m)
    fact = Lemma[≤-dec-∀+∃] dP n
    c₀ : (φn : ∀ m → m < n → ¬ P m) → fact ≡ inl φn → μ dP (n , p) ≡ μ dP (n , q)
    c₀ φn e = trans claim₀ (trans claim₁ (sym claim₂))
     where
      claim₀ : μ dP (n , p) ≡ (n , ν (dP n) p)
      claim₀ = ap toΣ (ap (case _ _) e)
      claim₁ : (n , ν (dP n) p) ≡ (n , ν (dP n) q)
      claim₁ = pair⁼ refl (ν-constant (dP n))
      claim₂ : μ dP (n , q) ≡ (n , ν (dP n) q)
      claim₂ = ap toΣ (ap (case _ _) e)
    c₁ : (ψn : Σ \m → m < n × P m) → fact ≡ inr ψn → μ dP (n , p) ≡ μ dP (n , q)
    c₁ (m , r , pm) e = trans claim₀ (sym claim₁)
     where
      □ : Σ P
      □ = _
      claim₀ : μ dP (n , p) ≡ □
      claim₀ = ap toΣ (ap (case _ _) e)
      claim₁ : μ dP (n , q) ≡ □
      claim₁ = ap toΣ (ap (case _ _) e)
  goal : (u v : Σ P) → μ² dP u ≡ μ² dP v
  goal u v = lemma (μ dP u) (μ dP v) (μ₁-constant dP u v)

\end{code}

μ² gives a constant function Σ P → Σ P for detachable P.

Theorem[KECA-TLCA'2013] together with μ² allows us to untruncate ∥ Σ P ∥.

\begin{code}

UntruncationLemma : {P : ℕ → Set} → (∀ n → P n + ¬ P n)
                   → ∥ (Σ \(n : ℕ) → P n) ∥ → Σ \(n : ℕ) → P n
UntruncationLemma dP = Theorem[KECA-TLCA'2013] (μ² dP) (μ²-constant dP)

\end{code}
