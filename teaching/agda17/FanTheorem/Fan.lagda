

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                        The Fan Theorem
                        ---------------

                         Chuangjie Xu

     14-16 Monday 4th, 11th & 18th December 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/

\begin{code}

module Fan where

open import Preliminaries
open import Untruncation

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



We start from the definitions for formulating the Fan Theorem.

--------------------------
-- (In)finite sequences --
--------------------------

● 𝟚ᴺ = ℕ → 𝟚 is the type of infinite binary sequences.

● 𝟚* = Σ \(n : ℕ) → Vec 𝟚 n (≅ List 𝟚) is the type of finite binary sequences.

● Subset-of-𝟚* = {n : ℕ} → 𝟚^ n → Set is the subtype of 𝟚*.

\begin{code}

open import Sequence

\end{code}

---------
-- Bar --
---------

A subset B of 𝟚* is a bar if any infinite binary sequence α has some
restriction in B.

\begin{code}

CH-Bar : Subset-of-𝟚* → Set
CH-Bar B = (α : 𝟚ᴺ) → Σ \(n : ℕ) → α ⌜ n ⌝ ∈ B

Bar : Subset-of-𝟚* → Set
Bar B = (α : 𝟚ᴺ) → ∥ (Σ \(n : ℕ) → α ⌜ n ⌝ ∈ B) ∥

Prop[CH-Bar→Bar] : (B : Subset-of-𝟚*) → CH-Bar B → Bar B
Prop[CH-Bar→Bar] B cb α = ∣ cb α ∣

Propᴰ[Bar→CH-Bar] : (B : Subset-of-𝟚*) → detachable B → Bar B → CH-Bar B
Propᴰ[Bar→CH-Bar] B dB b α = UntruncationLemma dQ (b α)
 where
  Q  : ℕ → Set
  Q  n = α ⌜ n ⌝ ∈ B
  dQ : ∀ n → Q n + ¬ Q n
  dQ n = dB (α ⌜ n ⌝)

\end{code}

A subset B of 𝟚* is a uniform bar if there exists N such that every
sequence α has some restriction in B with length smaller than N.

\begin{code}

CH-UniformBar : Subset-of-𝟚* → Set
CH-UniformBar B = Σ \(n : ℕ) → (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B
-- CH-UniformBar B = Σ \(N : ℕ) → (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (α ⌜ n ⌝ ∈ B)

UniformBar : Subset-of-𝟚* → Set
UniformBar B = ∥ (Σ \(n : ℕ) → (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B) ∥
-- UniformBar B = ∥ (Σ \(N : ℕ) → (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (α ⌜ n ⌝ ∈ B)) ∥

Prop[CH-UniformBar→UniformBar] : (B : Subset-of-𝟚*) → CH-UniformBar B → UniformBar B
Prop[CH-UniformBar→UniformBar] B cub = ∣ cub ∣

Propᴰ[UniformBar→CH-UniformBar] : (B : Subset-of-𝟚*) → detachable B → UniformBar B → CH-UniformBar B
Propᴰ[UniformBar→CH-UniformBar] B dB = UntruncationLemma dQ
 where
  Q : ℕ → Set
  Q n = (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B
  dQ : ∀ n → Q n + ¬ Q n
  dQ n = cases c₀ c₁ (Lemma[𝟚*-dec] B dB n)
   where
    c₀ : ((u : 𝟚^ n) → u ∈ B) → Q n
    c₀ ψ α = ψ (α ⌜ n ⌝)
    c₁ : ¬ ((u : 𝟚^ n) → u ∈ B) → ¬ (Q n)
    c₁ φ f = φ (λ u → transport B (Lemma[⌜⌝-cons] u) (f (cons u 0ʷ)))

\end{code}

---------------------------------------------------------
  Four type-theoretic variants of Brouwer's Fan Theorem
---------------------------------------------------------

\begin{code}

CH-Fan : Set₁
CH-Fan = (B : Subset-of-𝟚*) → ext-closed B → CH-Bar B → CH-UniformBar B

Fan : Set₁
Fan = (B : Subset-of-𝟚*) → ext-closed B → Bar B → UniformBar B

CH-Fanᴰ : Set₁
CH-Fanᴰ = (B : Subset-of-𝟚*) → ext-closed B → detachable B → CH-Bar B → CH-UniformBar B

Fanᴰ : Set₁
Fanᴰ = (B : Subset-of-𝟚*) → ext-closed B → detachable B → Bar B → UniformBar B

\end{code}

We firstly study how they relate to each other.

\begin{code}

Prop[CH-Fan→CH-Fanᴰ] : CH-Fan → CH-Fanᴰ
Prop[CH-Fan→CH-Fanᴰ] chfan B ecB dB cb = chfan B ecB cb

Prop[Fan→Fanᴰ] : Fan → Fanᴰ
Prop[Fan→Fanᴰ] fan B ecB dB b = fan B ecB b

\end{code}

Question: what about CH-Fan and Fan?

Since detachability is needed to show

    CH-Bar ↔ Bar  and  CH-UniformBar ↔ UniformBar

we can only prove  CH-Fan ↔ Fan  for detachable bars.

\begin{code}

Prop[CH-Fanᴰ→Fanᴰ] : CH-Fanᴰ → Fanᴰ
Prop[CH-Fanᴰ→Fanᴰ] chfand B ecB dB b = Prop[CH-UniformBar→UniformBar] B cub
 where
  cb : CH-Bar B
  cb = Propᴰ[Bar→CH-Bar] B dB b
  cub : CH-UniformBar B
  cub = chfand B ecB dB cb

Prop[Fanᴰ→CH-Fanᴰ] : Fanᴰ → CH-Fanᴰ
Prop[Fanᴰ→CH-Fanᴰ] fand B ecB dB cb = Propᴰ[UniformBar→CH-UniformBar] B dB ub
 where
  b : Bar B
  b = Prop[CH-Bar→Bar] B cb
  ub : UniformBar B
  ub = fand B ecB dB b

\end{code}

Then we relate them to

  --------------------------------------------
    Brouwer's (uniform-)continuity principle
  --------------------------------------------

\begin{code}

CH-continuous : (𝟚ᴺ → ℕ) → Set
CH-continuous f = (α : 𝟚ᴺ) → Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

continuous : (𝟚ᴺ → ℕ) → Set
continuous f = (α : 𝟚ᴺ) → ∥ (Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

CH-Cont : Set
CH-Cont = (f : 𝟚ᴺ → ℕ) → CH-continuous f

Cont : Set
Cont = (f : 𝟚ᴺ → ℕ) → continuous f


CH-uniformly-continuous : (𝟚ᴺ → ℕ) → Set
CH-uniformly-continuous f = Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

uniformly-continuous : (𝟚ᴺ → ℕ) → Set
uniformly-continuous f = ∥ (Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

CH-UC : Set
CH-UC = (f : 𝟚ᴺ → ℕ) → CH-uniformly-continuous f

UC : Set
UC = (f : 𝟚ᴺ → ℕ) → uniformly-continuous f

\end{code}

We already proved  CH-UC ↔ UC  a few weeks ago.

\begin{code}

Prop[CH-uc→uc] : {f : 𝟚ᴺ → ℕ} → CH-uniformly-continuous f → uniformly-continuous f
Prop[CH-uc→uc] = ∣_∣

postulate
 Prop[uc→CH-uc] : {f : 𝟚ᴺ → ℕ} → uniformly-continuous f → CH-uniformly-continuous f

Prop[CH-UC→UC] : CH-UC → UC
Prop[CH-UC→UC] chuc f = Prop[CH-uc→uc] (chuc f)

Prop[UC→CH-UC] : UC → CH-UC
Prop[UC→CH-UC] uc f = Prop[uc→CH-uc] (uc f)

\end{code}

But  CH-Cont ↔ Cont  doesn't seem possible...

Let's prove some trivial implications.

\begin{code}

Prop[CH-cont→cont] : {f : 𝟚ᴺ → ℕ} → CH-continuous f → continuous f
Prop[CH-cont→cont] chcf α = ∣ chcf α ∣

Prop[CH-Cont→Cont] : CH-Cont → Cont
Prop[CH-Cont→Cont] chcont f = Prop[CH-cont→cont] (chcont f)

\end{code}

(CH-)UC is acually a very strong principle:

    (CH-)UC implies CH-Cont and CH-Fan.

\begin{code}

Prop[CH-UC→CH-Cont] : CH-UC → CH-Cont
Prop[CH-UC→CH-Cont] chuc f α = pr₁ (chuc f) , pr₂ (chuc f) α


-- The following lemma is needed for proving
--
--     (some variant of) UC implies (some vairant of) Fan.
--
max-image-uc-fun : (f : 𝟚ᴺ → ℕ) → CH-uniformly-continuous f
                 → Σ \(m : ℕ) → (α : 𝟚ᴺ) → f α ≤ m
max-image-uc-fun f (n , un) = claim f n un
 where
  claim : (f : 𝟚ᴺ → ℕ) → (n : ℕ) → ((α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β)
        → Σ \(m : ℕ) → (α : 𝟚ᴺ) → f α ≤ m
  claim f 0 u0 = (m , prf)
   where
    m : ℕ
    m = f 0ʷ
    prf : (α : 𝟚ᴺ) → f α ≤ m
    prf α = transport (λ x → f α ≤ x) (u0 α 0ʷ ≡[zero]) ≤-refl
  claim f (succ n) usn = (m , prf)
   where
    _★_ : 𝟚 → 𝟚ᴺ → 𝟚ᴺ
    (b ★ α)  0       = b
    (b ★ α) (succ i) = α i
    un₀ : (α β : 𝟚ᴺ) → α ≡[ n ] β → f (𝟎 ★ α) ≡ f (𝟎 ★ β)
    un₀ α β en = usn (𝟎 ★ α) (𝟎 ★ β) (≡[succ] refl en)
    IH₀ : Σ \(m : ℕ) → (α : 𝟚ᴺ) → f (𝟎 ★ α) ≤ m
    IH₀ = claim _ n un₀
    m₀ : ℕ
    m₀ = pr₁ IH₀
    un₁ : (α β : 𝟚ᴺ) → α ≡[ n ] β → f (𝟏 ★ α) ≡ f (𝟏 ★ β)
    un₁ α β en = usn (𝟏 ★ α) (𝟏 ★ β) (≡[succ] refl en)
    IH₁ : Σ \(m : ℕ) → (α : 𝟚ᴺ) → f (𝟏 ★ α) ≤ m
    IH₁ = claim _ n un₁
    m₁ : ℕ
    m₁ = pr₁ IH₁
    m : ℕ
    m = max m₀ m₁
    prf : (α : 𝟚ᴺ) → f α ≤ m
    prf α = case c₀ c₁ (Lemma[b≡0∨b≡1] (head α))
     where
      c₀ : head α ≡ 𝟎 → f α ≤ m
      c₀ e = transport (λ x → x ≤ m) (sym claim₀) claim₂
       where
        esn : α ≡[ succ n ] (𝟎 ★ tail α)
        esn = ≡[succ] e ≡[]-refl
        claim₀ : f α ≡ f (𝟎 ★ tail α)
        claim₀ = usn _ _ esn
        claim₁ : f (𝟎 ★ tail α) ≤ m₀
        claim₁ = pr₂ IH₀ (tail α)
        claim₂ : f (𝟎 ★ tail α) ≤ m
        claim₂ = ≤-trans claim₁ (max-spec₀ m₀ m₁)
      c₁ : head α ≡ 𝟏 → f α ≤ m
      c₁ e = transport (λ x → x ≤ m) (sym claim₀) claim₂
       where
        esn : α ≡[ succ n ] (𝟏 ★ tail α)
        esn = ≡[succ] e ≡[]-refl
        claim₀ : f α ≡ f (𝟏 ★ tail α)
        claim₀ = usn _ _ esn
        claim₁ : f (𝟏 ★ tail α) ≤ m₁
        claim₁ = pr₂ IH₁ (tail α)
        claim₂ : f (𝟏 ★ tail α) ≤ m
        claim₂ = ≤-trans claim₁ (max-spec₁ m₀ m₁)


Prop[CH-UC→CH-Fan] : CH-UC → CH-Fan
Prop[CH-UC→CH-Fan] uc B ecB b = n , prf
 where
  f : 𝟚ᴺ → ℕ
  f α = pr₁ (b α)
  MI-f : Σ \(m : ℕ) → (α : 𝟚ᴺ) → f α ≤ m
  MI-f = max-image-uc-fun f (uc f)
  n : ℕ
  n = pr₁ MI-f
  prf : (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B
  prf α = ecB _ _ claim₃ claim₀
   where
    claim₀ : α ⌜ f α ⌝ ∈ B 
    claim₀ = pr₂ (b α)
    claim₂ : f α ≤ n
    claim₂ = pr₂ MI-f α
    claim₃ : α ⌜ n ⌝ ⊑ α ⌜ f α ⌝
    claim₃ = Lemma[⌜≤⌝-⊑] claim₂


\end{code}

CH-Fan and CH-Cont together imply (CH-)UC.

\begin{code}

Prop[CH-Fan∧CH-Cont→CH-UC] : CH-Fan → CH-Cont → CH-UC
Prop[CH-Fan∧CH-Cont→CH-UC] fan cont f = (n , prf)
 where
  B : Subset-of-𝟚*
  B {n} u = (α : 𝟚ᴺ) → u ≡ α ⌜ n ⌝ → f (cons u 0ʷ) ≡ f α
  ecB : ext-closed B
  ecB {n} u {m} v r vB α e = trans (sym claim₁) claim₃
   where
    lemma₀ : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {α : A ᴺ}
           → u ⊑ v → v ≡ cons u α ⌜ m ⌝
    lemma₀  ⊑-ε       = refl
    lemma₀ (⊑-cons r) = Vec⁼ refl (lemma₀ r)
    claim₀ : v ≡ cons u 0ʷ ⌜ m ⌝
    claim₀ = lemma₀ r 
    claim₁ : f (cons v 0ʷ) ≡ f (cons u 0ʷ)
    claim₁ = vB (cons u 0ʷ) claim₀
    lemma₁ : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {α : A ᴺ}
           → u ⊑ v → u ≡ α ⌜ n ⌝ → v ≡ α ⌜ m ⌝
    lemma₁  ⊑-ε       e = refl
    lemma₁ (⊑-cons r) e = Vec⁼ (ap headᵛ e) (lemma₁ r (ap tailᵛ e))
    claim₂ : v ≡ α ⌜ m ⌝
    claim₂ = lemma₁ r e
    claim₃ : f (cons v 0ʷ) ≡ f α
    claim₃ = vB α claim₂
  b : CH-Bar B
  b α = n , prf
   where
    n : ℕ
    n = pr₁ (cont f α)
    prf : (β : 𝟚ᴺ) → α ⌜ n ⌝ ≡ β ⌜ n ⌝ → f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
    prf β en = trans (sym claim₀) claim₁
     where
      en' : α ≡[ n ] β
      en' = Lemma[⌜⌝→≡[]] en
      claim₀ : f α ≡ f (cons (α ⌜ n ⌝) 0ʷ)
      claim₀ = pr₂ (cont f α) (cons (α ⌜ n ⌝) 0ʷ) (Lemma[≡[]-cons-⌜⌝] n)
      claim₁ : f α ≡ f β
      claim₁ = pr₂ (cont f α) β en'
  ub : CH-UniformBar B
  ub = fan B ecB b
  n : ℕ
  n = pr₁ ub
  prf : (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β
  prf α β en = trans (sym claim₀) claim₁
   where
    en' : α ⌜ n ⌝ ≡ β ⌜ n ⌝
    en' = Lemma[≡[]→⌜⌝] en
    claim₀ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f α
    claim₀ = pr₂ ub α α refl
    claim₁ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
    claim₁ = pr₂ ub α β en'

\end{code}

We can actually strengthen the above by using (an equivalent of) CH-Fanᴰ

\begin{code}

CH-UniformBar' : Subset-of-𝟚* → Set
CH-UniformBar' B = Σ \(N : ℕ) → (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (α ⌜ n ⌝ ∈ B)

CH-Fanᴰ' : Set₁
CH-Fanᴰ' = (B : Subset-of-𝟚*) → detachable B → CH-Bar B → CH-UniformBar' B

\end{code}

We need the operation Ā (I write A ᴱ instead) for every subset A of 𝟚*
and prove its properties (Lemma 6 in Dr. Berger's lecutre notes).

\begin{code}

_ᴱ : Subset-of-𝟚* → Subset-of-𝟚*
(B ᴱ) u = Σ \(k : ℕ) → Σ \(v : 𝟚^ k) → (u ⊑ v) × (v ∈ B)

Lemma[ext-closedᴱ] : (B : Subset-of-𝟚*) → ext-closed (B ᴱ)
Lemma[ext-closedᴱ] B u v u⊑v (k , v' , v⊑v' , v'B) = (k , v' , ⊑-trans u⊑v v⊑v' , v'B)

Lemma[⊆ᴱ] : (B : Subset-of-𝟚*) {n : ℕ} (u : 𝟚^ n) → u ∈ B → u ∈ B ᴱ
Lemma[⊆ᴱ] B {n} u uB = n , u , ⊑-refl , uB

Lemma[CH-Barᴱ] : (B : Subset-of-𝟚*) → CH-Bar B → CH-Bar (B ᴱ)
Lemma[CH-Barᴱ] B bB α = n , Lemma[⊆ᴱ] B (α ⌜ n ⌝) αnB
 where
  n : ℕ
  n = pr₁ (bB α)
  αnB : α ⌜ n ⌝ ∈ B
  αnB = pr₂ (bB α)

Lemma[detachableᴱ] : (B : Subset-of-𝟚*) → detachable B → detachable (B ᴱ)
Lemma[detachableᴱ] B dB ε = cases c₀ c₁ (dB ε)
 where
  c₀ : ε ∈ B → ε ∈ B ᴱ
  c₀ = Lemma[⊆ᴱ] B ε
  c₁ : ¬ (ε ∈ B) → ¬ (ε ∈ B ᴱ)
  c₁ f (.0 , .ε , ⊑-ε , b) = f b
Lemma[detachableᴱ] B dB {succ n} u = case c₀ c₁ (dB u) 
 where
  c₀ : u ∈ B → (u ∈ B ᴱ) + ¬ (u ∈ B ᴱ)
  c₀ b = inl (Lemma[⊆ᴱ] B u b)
  c₁ : ¬ (u ∈ B) → (u ∈ B ᴱ) + ¬ (u ∈ B ᴱ)
  c₁ f = cases d₀ d₁ (Lemma[detachableᴱ] B dB {n} u')
   where
    drop : {A : Set} {n : ℕ} → A ^ (succ n) → A ^ n
    drop (_ ::  ε)     = ε
    drop (a :: b :: v) = a :: (drop (b :: v))
    Lemma[drop-⊑] : {A : Set} {n : ℕ} (u : A ^ (succ n)) → u ⊑ drop u
    Lemma[drop-⊑] (_ ::  ε)     = ⊑-ε
    Lemma[drop-⊑] (a :: b :: u) = ⊑-cons (Lemma[drop-⊑] (b :: u))
    Lemma[⊑-cases] : {A : Set} {n : ℕ} (u : A ^ (succ n)) {m : ℕ} (v : A ^ m)
                   → u ⊑ v →  (Σ \(e : succ n ≡ m) → transport (Vec A) e u ≡ v)
                            + (drop u ⊑ v)
    Lemma[⊑-cases] (a :: u) ε ⊑-ε  = inr ⊑-ε
    Lemma[⊑-cases] (a :: ε) (.a :: ε) (⊑-cons ⊑-ε) = inl (refl , refl)
    Lemma[⊑-cases] (a :: ε) (.a :: x :: v) (⊑-cons ())
    Lemma[⊑-cases] {A} {succ n} (a :: b :: u) {succ m} (.a :: v) (⊑-cons r) = cases claim₀ claim₁ IH
     where
      claim₀ : (Σ \(e : succ n ≡ m) → transport (Vec A) e (b :: u) ≡ v)
             → (Σ \(e : succ (succ n) ≡ succ m) → transport (Vec A) e (a :: b :: u) ≡ a :: v)
      claim₀ (refl , refl) = refl , refl
      claim₁ : drop (b :: u) ⊑ v
             → drop (a :: b :: u) ⊑ a :: v
      claim₁ = ⊑-cons
      IH : (Σ \(e : succ n ≡ m) → transport _ e (b :: u) ≡ v) + (drop (b :: u) ⊑ v)
      IH = Lemma[⊑-cases] (b :: u) v r
    u' : 𝟚^ n
    u' = drop u
    d₀ : u' ∈ B ᴱ → u ∈ B ᴱ
    d₀ = Lemma[ext-closedᴱ] B u u' (Lemma[drop-⊑] u)
    d₁ : ¬ (u' ∈ B ᴱ) → ¬ (u ∈ B ᴱ)
    d₁ f' (k , v , u⊑v , vB) = case claim₀ claim₁ claim₂
     where
      claim₀ : (Σ \(e : succ n ≡ k) → transport 𝟚^_ e u ≡ v) → 𝟘
      claim₀ (refl , refl) = f vB
      claim₁ : u' ⊑ v → 𝟘
      claim₁ u'⊑v = f' (k , v , u'⊑v , vB)
      claim₂ : (Σ \(e : succ n ≡ k) → transport 𝟚^_ e u ≡ v) + (u' ⊑ v)
      claim₂ = Lemma[⊑-cases] u v u⊑v

Lemma[CH-UniformBarᴱ] : (B : Subset-of-𝟚*) → CH-UniformBar (B ᴱ) → CH-UniformBar' B
Lemma[CH-UniformBarᴱ] B (N , prf) = N , prf'
 where
  prf' : (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (α ⌜ n ⌝ ∈ B)
  prf' α = n , n≤N , αnB
   where
    w : Σ \(n : ℕ) → Σ \(u : 𝟚^ n) → (α ⌜ N ⌝ ⊑ u) × (u ∈ B)
    w = prf α
    n : ℕ
    n = pr₁ w
    u : 𝟚^ n
    u = pr₁ (pr₂ w)
    αN⊑u : α ⌜ N ⌝ ⊑ u
    αN⊑u = pr₁ (pr₂ (pr₂ w))
    n≤N : n ≤ N
    n≤N = Lemma[⊑→≤] αN⊑u
    uB : u ∈ B
    uB = pr₂ (pr₂ (pr₂ w))
    lemma : {A : Set} {α : A ᴺ} {N n : ℕ} {u : A ^ n} → α ⌜ N ⌝ ⊑ u → u ≡ α ⌜ n ⌝
    lemma  ⊑-ε       = refl
    lemma (⊑-cons r) = Vec⁼ refl (lemma r)
    αnB : α ⌜ n ⌝ ∈ B
    αnB = transport B (lemma αN⊑u) uB


Prop[CH-Fanᴰ→CH-Fanᴰ'] : CH-Fanᴰ → CH-Fanᴰ'
Prop[CH-Fanᴰ→CH-Fanᴰ'] fan B dB bB = uB'
 where
  uBᴱ : CH-UniformBar (B ᴱ)
  uBᴱ = fan (B ᴱ) (Lemma[ext-closedᴱ] B) (Lemma[detachableᴱ] B dB) (Lemma[CH-Barᴱ] B bB)
  uB' : CH-UniformBar' B
  uB' = Lemma[CH-UniformBarᴱ] B uBᴱ


Prop[CH-Fanᴰ'∧CH-Cont→CH-UC] : CH-Fanᴰ' → CH-Cont → CH-UC
Prop[CH-Fanᴰ'∧CH-Cont→CH-UC] fan cont f = N , prf
 where
  M : 𝟚ᴺ → ℕ
  M α = pr₁ (cont f α)
  B : Subset-of-𝟚*
  B {n} u = M (cons u 0ʷ) ≤ n
  dB : detachable B
  dB _ = Lemma[≤-decidable]
  bB : CH-Bar B
  bB α = m , αmB
   where
    n : ℕ
    n = pr₁ (cont M α)
    prnM : (β : 𝟚ᴺ) → α ≡[ n ] β → M α ≡ M β
    prnM = pr₂ (cont M α)
    m : ℕ
    m = max n (M α)
    claim₀ : n ≤ m
    claim₀ = max-spec₀ n (M α)
    prmM : (β : 𝟚ᴺ) → α ≡[ m ] β → M α ≡ M β
    prmM β em = prnM β (Lemma[≡[]-≤] em claim₀)
    claim₁ : M α ≡ M (cons (α ⌜ m ⌝) 0ʷ)
    claim₁ = prmM (cons (α ⌜ m ⌝) 0ʷ) (Lemma[≡[]-cons-⌜⌝] m)
    claim₂ : M α ≤ m
    claim₂ = max-spec₁ n (M α)
    αmB : α ⌜ m ⌝ ∈ B
       -- M (cons (α ⌜ m ⌝) 0ʷ) ≤ m
    αmB = transport (λ x → x ≤ m) claim₁ claim₂
  uB : CH-UniformBar' B
  uB = fan B dB bB
  N : ℕ
  N = pr₁ uB
  claim : (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (M (cons (α ⌜ n ⌝) 0ʷ) ≤ n)
  claim = pr₂ uB
  prf : (α β : 𝟚ᴺ) → α ≡[ N ] β → f α ≡ f β
  prf α β eN = trans (sym claim₃) claim₇
   where
    n : ℕ
    n = pr₁ (claim α)
    r : n ≤ N
    r = pr₁ (pr₂ (claim α))
    m : ℕ
    m = M (cons (α ⌜ n ⌝) 0ʷ)
    claim₀ : m ≤ n
    claim₀ = pr₂ (pr₂ (claim α))
    claim₁ : cons (α ⌜ n ⌝) 0ʷ ≡[ n ] α
    claim₁ = ≡[]-sym (Lemma[≡[]-cons-⌜⌝] n)
    claim₂ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] α
    claim₂ = Lemma[≡[]-≤] claim₁ claim₀
    claim₃ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f α
    claim₃ = pr₂ (cont f (cons (α ⌜ n ⌝) 0ʷ)) α claim₂
    claim₄ : m ≤ N
    claim₄ = ≤-trans claim₀ r
    claim₅ : α ≡[ m ] β
    claim₅ = Lemma[≡[]-≤] eN claim₄
    claim₆ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] β
    claim₆ = ≡[]-trans claim₂ claim₅
    claim₇ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
    claim₇ = pr₂ (cont f (cons (α ⌜ n ⌝) 0ʷ)) β claim₆


Prop[CH-Fanᴰ∧CH-Cont→CH-UC] : CH-Fanᴰ → CH-Cont → CH-UC
Prop[CH-Fanᴰ∧CH-Cont→CH-UC] fan = Prop[CH-Fanᴰ'∧CH-Cont→CH-UC] (Prop[CH-Fanᴰ→CH-Fanᴰ'] fan)

\end{code}

Fan and Cont together also imply (CH-)UC.

\begin{code}

Prop[Fan∧Cont→UC] : Fan → Cont → UC
Prop[Fan∧Cont→UC] fan cont f = goal
 where
  B : Subset-of-𝟚*
  B {n} u = (α : 𝟚ᴺ) → u ≡ α ⌜ n ⌝ → f (cons u 0ʷ) ≡ f α
  ecB : ext-closed B
  ecB {n} u {m} v r vB α e = trans (sym claim₁) claim₃
   where
    lemma₀ : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {α : A ᴺ}
           → u ⊑ v → v ≡ cons u α ⌜ m ⌝
    lemma₀  ⊑-ε       = refl
    lemma₀ (⊑-cons r) = Vec⁼ refl (lemma₀ r)
    claim₀ : v ≡ cons u 0ʷ ⌜ m ⌝
    claim₀ = lemma₀ r 
    claim₁ : f (cons v 0ʷ) ≡ f (cons u 0ʷ)
    claim₁ = vB (cons u 0ʷ) claim₀
    lemma₁ : {A : Set} {n : ℕ} {u : A ^ n} {m : ℕ} {v : A ^ m} {α : A ᴺ}
           → u ⊑ v → u ≡ α ⌜ n ⌝ → v ≡ α ⌜ m ⌝
    lemma₁  ⊑-ε       e = refl
    lemma₁ (⊑-cons r) e = Vec⁼ (ap headᵛ e) (lemma₁ r (ap tailᵛ e))
    claim₂ : v ≡ α ⌜ m ⌝
    claim₂ = lemma₁ r e
    claim₃ : f (cons v 0ʷ) ≡ f α
    claim₃ = vB α claim₂
  bB : Bar B
  bB α = ∥∥-functor claim (cont f α)
   where
    claim : (Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β)
          → Σ \(n : ℕ) → α ⌜ n ⌝ ∈ B
    claim (n , prn) = n , prf
     where
      prf : (β : 𝟚ᴺ) → α ⌜ n ⌝ ≡ β ⌜ n ⌝ → f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
      prf β en = trans (sym claim₀) claim₁
       where
        en' : α ≡[ n ] β
        en' = Lemma[⌜⌝→≡[]] en
        claim₀ : f α ≡ f (cons (α ⌜ n ⌝) 0ʷ)
        claim₀ = prn (cons (α ⌜ n ⌝) 0ʷ) (Lemma[≡[]-cons-⌜⌝] n)
        claim₁ : f α ≡ f β
        claim₁ = prn β en'
  uB : UniformBar B
  uB = fan B ecB bB
  claim : CH-UniformBar B → CH-uniformly-continuous f
  claim (n , p) = (n , prf)
   where
    prf : (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β
    prf α β en = trans (sym claim₀) claim₁
     where
      en' : α ⌜ n ⌝ ≡ β ⌜ n ⌝
      en' = Lemma[≡[]→⌜⌝] en
      claim₀ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f α
      claim₀ = p α α refl
      claim₁ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
      claim₁ = p α β en'
  goal : uniformly-continuous f
  goal = ∥∥-functor claim uB

\end{code}

This can be strengthen to "c-Fan ∧ Cont → UC" (see Berger's lecture notes).

Question: What about "Fanᴰ ∧ Cont → UC"?



Now we study some weakenings of UC and relate them to the Fan theorem.

The first weakening of UC is the following

  (WUC) Every continuous function f : 𝟚ᴺ → ℕ is uniformly continuous.

Dr. Berger calls it UC in his course.

\begin{code}

CH-WUC : Set
CH-WUC = (f : 𝟚ᴺ → ℕ) → CH-continuous f → CH-uniformly-continuous f

WUC : Set
WUC = (f : 𝟚ᴺ → ℕ) → continuous f → uniformly-continuous f

Prop[WUC→CH-WUC] : WUC → CH-WUC
Prop[WUC→CH-WUC] wuc f chcf = Prop[uc→CH-uc] ucf
 where
  cf : continuous f
  cf = Prop[CH-cont→cont] chcf
  ucf : uniformly-continuous f
  ucf = wuc f cf

Prop[UC→WUC] : UC → WUC
Prop[UC→WUC] uc f _ = uc f

Prop[WUC∧Cont→UC] : WUC → Cont → UC
Prop[WUC∧Cont→UC] wuc cont f = wuc f (cont f)

Prop[CH-WUC∧CH-Cont→CH-UC] : CH-WUC → CH-Cont → CH-UC
Prop[CH-WUC∧CH-Cont→CH-UC] wuc cont f = wuc f (cont f)

-- Prop[CH-WUC→CH-Fanᴰ] : CH-WUC → CH-Fanᴰ
-- The proof is given later by a weakening MUC

\end{code}

Another weakening of UC:

  (MUC) Every function f : 𝟚ᴺ → ℕ which has a pointwise continuous
  modulus of pointwise continuity is uniformly continuous.

\begin{code}

CH-MUC : Set
CH-MUC = (f : 𝟚ᴺ → ℕ)
       → (M : 𝟚ᴺ → ℕ) → ((α β : 𝟚ᴺ) → α ≡[ M α ] β → f α ≡ f β) → CH-continuous M
       → CH-uniformly-continuous f

MUC : Set
MUC = (f : 𝟚ᴺ → ℕ)
    → (M : 𝟚ᴺ → ℕ) → ((α β : 𝟚ᴺ) → α ≡[ M α ] β → f α ≡ f β) → continuous M
    → uniformly-continuous f

Prop[MUC→CH-MUC] : MUC → CH-MUC
Prop[MUC→CH-MUC] muc f M M-spec chcM = Prop[uc→CH-uc] (muc f M M-spec (Prop[CH-cont→cont] chcM))

-- Prop[CH-MUC→MUC] : CH-MUC → MUC
-- The proof is given later by the one of
--
--     CH-MUC ↔ CH-Fanᴰ ↔ Fanᴰ ↔ MUC

\end{code}

Now we prove the following chain of implications:

    CH-WUC → CH-MUC → CH-Fanᴰ

\begin{code}

Prop[CH-WUC→CH-MUC] : CH-WUC → CH-MUC
Prop[CH-WUC→CH-MUC] wuc f M M-spec cM = wuc f (λ α → M α , M-spec α)

-- The following proof is essentially the same as the one of
--
--     CH-UC → CH-Fan
--
Prop[CH-MUC→CH-Fanᴰ] : CH-MUC → CH-Fanᴰ
Prop[CH-MUC→CH-Fanᴰ] muc B ecB dB bB = (n , prf)
 where
  f : 𝟚ᴺ → ℕ
  f α = pr₁ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (bB α))
  f-spec : (α : 𝟚ᴺ) → α ⌜ f α ⌝ ∈ B
  f-spec α = pr₁ (pr₂ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (bB α)))
  f-min : (α : 𝟚ᴺ) (n : ℕ) → α ⌜ n ⌝ ∈ B → f α ≤ n
  f-min α = pr₂ (pr₂ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (bB α)))
  f-modu : (α β : 𝟚ᴺ) → α ≡[ f α ] β → f α ≡ f β
  f-modu α β eα = Lemma[n≤m∧m≤n→n≡m] claim₅ claim₂
   where
    claim₀ : α ⌜ f α ⌝ ≡ β ⌜ f α ⌝
    claim₀ = Lemma[≡[]→⌜⌝] eα
    claim₁ : β ⌜ f α ⌝ ∈ B
    claim₁ = transport B claim₀ (f-spec α)
    claim₂ : f β ≤ f α
    claim₂ = f-min β (f α) claim₁
    claim₃ : α ⌜ f β ⌝ ≡ β ⌜ f β ⌝
    claim₃ = Lemma[≡[]→⌜⌝] (Lemma[≡[]-≤] eα claim₂)
    claim₄ : α ⌜ f β ⌝ ∈ B
    claim₄ = transport B (sym claim₃) (f-spec β)
    claim₅ : f α ≤ f β
    claim₅ = f-min α (f β) claim₄
  cf : (α : 𝟚ᴺ) → Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β
  cf α = f α , f-modu α 
  ucf : Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β
  ucf = muc f f f-modu cf
  MI-f : Σ \(m : ℕ) → (α : 𝟚ᴺ) → f α ≤ m
  MI-f = max-image-uc-fun f ucf
  n : ℕ
  n = pr₁ MI-f
  prf : (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B
  prf α = ecB _ _ claim₃ claim₀
   where
    claim₀ : α ⌜ f α ⌝ ∈ B 
    claim₀ = f-spec α
    claim₂ : f α ≤ n
    claim₂ = pr₂ MI-f α
    claim₃ : α ⌜ n ⌝ ⊑ α ⌜ f α ⌝
    claim₃ = Lemma[⌜≤⌝-⊑] claim₂


Prop[CH-WUC→CH-Fanᴰ] : CH-WUC → CH-Fanᴰ
Prop[CH-WUC→CH-Fanᴰ] wuc = Prop[CH-MUC→CH-Fanᴰ] (Prop[CH-WUC→CH-MUC] wuc)

\end{code}

To prove

    CH-Fanᴰ → CH-MUC

we need Lemma 8 of Berger's lecture notes, which shows how to
construct a (CH-)bar from a (CH-)continuous function.

\begin{code}

Lemma[CH-B8] : (F : 𝟚ᴺ → ℕ) → CH-continuous F
             → CH-Bar (λ {n} u → F (cons u 0ʷ) ≤ n)
Lemma[CH-B8] F cF = bB
 where
  B : Subset-of-𝟚*
  B {n} u = F (cons u 0ʷ) ≤ n
  bB : CH-Bar B
  bB α = (m , prf)
   where
    n : ℕ
    n = pr₁ (cF α)
    prn : (β : 𝟚ᴺ) → α ≡[ n ] β → F α ≡ F β
    prn = pr₂ (cF α)
    m : ℕ
    m = max n (F α)
    claim₀ : α ≡[ m ] cons (α ⌜ m ⌝) 0ʷ
    claim₀ = Lemma[≡[]-cons-⌜⌝] m
    claim₁ : α ≡[ n ] cons (α ⌜ m ⌝) 0ʷ
    claim₁ = Lemma[≡[]-≤] claim₀ (max-spec₀ n (F α))
    claim₂ : F α ≡ F (cons (α ⌜ m ⌝) 0ʷ)
    claim₂ = prn (cons (α ⌜ m ⌝) 0ʷ) claim₁
    claim₃ : F α ≤ m
    claim₃ = max-spec₁ n (F α)
    prf : α ⌜ m ⌝ ∈ B
       -- F (cons (α ⌜ m ⌝) 0ʷ) ≤ m
    prf = transport (λ x → x ≤ m) claim₂ claim₃


Lemma[B8] : (F : 𝟚ᴺ → ℕ) → continuous F
          → Bar (λ {n} u → F (cons u 0ʷ) ≤ n)
Lemma[B8] F cF α = ∥∥-functor claim (cF α)
 where
  B : Subset-of-𝟚*
  B {n} u = F (cons u 0ʷ) ≤ n
  claim : (Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → F α ≡ F β)
        → Σ \(n : ℕ) → α ⌜ n ⌝ ∈ B
  claim (n , prn) = m , prf
   where
    m : ℕ
    m = max n (F α)
    claim₀ : α ≡[ m ] cons (α ⌜ m ⌝) 0ʷ
    claim₀ = Lemma[≡[]-cons-⌜⌝] m
    claim₁ : α ≡[ n ] cons (α ⌜ m ⌝) 0ʷ
    claim₁ = Lemma[≡[]-≤] claim₀ (max-spec₀ n (F α))
    claim₂ : F α ≡ F (cons (α ⌜ m ⌝) 0ʷ)
    claim₂ = prn (cons (α ⌜ m ⌝) 0ʷ) claim₁
    claim₃ : F α ≤ m
    claim₃ = max-spec₁ n (F α)
    prf : α ⌜ m ⌝ ∈ B
       -- F (cons (α ⌜ m ⌝) 0ʷ) ≤ m
    prf = transport (λ x → x ≤ m) claim₂ claim₃


Prop[CH-Fanᴰ'→CH-MUC] : CH-Fanᴰ' → CH-MUC
Prop[CH-Fanᴰ'→CH-MUC] fan f M M-spec cM = (N , prf)
 where
  B : Subset-of-𝟚*
  B {n} u = M (cons u 0ʷ) ≤ n
  dB : detachable B
  dB _ = Lemma[≤-decidable]
  bB : CH-Bar B
  bB = Lemma[CH-B8] M cM
  uB : CH-UniformBar' B
  uB = fan B dB bB
  N : ℕ
  N = pr₁ uB
  claim : (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (M (cons (α ⌜ n ⌝) 0ʷ) ≤ n)
  claim = pr₂ uB
  prf : (α β : 𝟚ᴺ) → α ≡[ N ] β → f α ≡ f β
  prf α β eN = trans (sym claim₃) claim₇
   where
    n : ℕ
    n = pr₁ (claim α)
    r : n ≤ N
    r = pr₁ (pr₂ (claim α))
    m : ℕ
    m = M (cons (α ⌜ n ⌝) 0ʷ)
    claim₀ : m ≤ n
    claim₀ = pr₂ (pr₂ (claim α))
    claim₁ : cons (α ⌜ n ⌝) 0ʷ ≡[ n ] α
    claim₁ = ≡[]-sym (Lemma[≡[]-cons-⌜⌝] n)
    claim₂ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] α
    claim₂ = Lemma[≡[]-≤] claim₁ claim₀
    claim₃ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f α
    claim₃ = M-spec (cons (α ⌜ n ⌝) 0ʷ) α claim₂
    claim₄ : m ≤ N
    claim₄ = ≤-trans claim₀ r
    claim₅ : α ≡[ m ] β
    claim₅ = Lemma[≡[]-≤] eN claim₄
    claim₆ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] β
    claim₆ = ≡[]-trans claim₂ claim₅
    claim₇ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
    claim₇ = M-spec (cons (α ⌜ n ⌝) 0ʷ) β claim₆


Prop[CH-Fanᴰ→CH-MUC] : CH-Fanᴰ → CH-MUC
Prop[CH-Fanᴰ→CH-MUC] fan = Prop[CH-Fanᴰ'→CH-MUC] (Prop[CH-Fanᴰ→CH-Fanᴰ'] fan)

\end{code}

Now let's prove non-CH-version

    MUC ↔ Fanᴰ

\begin{code}

Prop[MUC→Fanᴰ] : MUC → Fanᴰ
Prop[MUC→Fanᴰ] muc B ecB dB bB = uB
 where
  cbB : CH-Bar B
  cbB = Propᴰ[Bar→CH-Bar] B dB bB
  f : 𝟚ᴺ → ℕ
  f α = pr₁ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (cbB α))
  f-spec : (α : 𝟚ᴺ) → α ⌜ f α ⌝ ∈ B
  f-spec α = pr₁ (pr₂ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (cbB α)))
  f-min : (α : 𝟚ᴺ) (n : ℕ) → α ⌜ n ⌝ ∈ B → f α ≤ n
  f-min α = pr₂ (pr₂ (Lemma[Σ-min] (λ n → dB (α ⌜ n ⌝)) (cbB α)))
  f-modu : (α β : 𝟚ᴺ) → α ≡[ f α ] β → f α ≡ f β
  f-modu α β eα = Lemma[n≤m∧m≤n→n≡m] claim₅ claim₂
   where
    claim₀ : α ⌜ f α ⌝ ≡ β ⌜ f α ⌝
    claim₀ = Lemma[≡[]→⌜⌝] eα
    claim₁ : β ⌜ f α ⌝ ∈ B
    claim₁ = transport B claim₀ (f-spec α)
    claim₂ : f β ≤ f α
    claim₂ = f-min β (f α) claim₁
    claim₃ : α ⌜ f β ⌝ ≡ β ⌜ f β ⌝
    claim₃ = Lemma[≡[]→⌜⌝] (Lemma[≡[]-≤] eα claim₂)
    claim₄ : α ⌜ f β ⌝ ∈ B
    claim₄ = transport B (sym claim₃) (f-spec β)
    claim₅ : f α ≤ f β
    claim₅ = f-min α (f β) claim₄
  chcf : CH-continuous f
  chcf α = f α , f-modu α
  cf : continuous f
  cf = Prop[CH-cont→cont] chcf
  ucf : uniformly-continuous f
  ucf = muc f f f-modu cf
  chucf : CH-uniformly-continuous f
  chucf = Prop[uc→CH-uc] ucf
  MI-f : Σ \(m : ℕ) → (α : 𝟚ᴺ) → f α ≤ m
  MI-f = max-image-uc-fun f chucf
  n : ℕ
  n = pr₁ MI-f
  prf : (α : 𝟚ᴺ) → α ⌜ n ⌝ ∈ B
  prf α = ecB _ _ claim₃ claim₀
   where
    claim₀ : α ⌜ f α ⌝ ∈ B 
    claim₀ = f-spec α
    claim₂ : f α ≤ n
    claim₂ = pr₂ MI-f α
    claim₃ : α ⌜ n ⌝ ⊑ α ⌜ f α ⌝
    claim₃ = Lemma[⌜≤⌝-⊑] claim₂
  chuB : CH-UniformBar B
  chuB = n , prf
  uB : UniformBar B
  uB = Prop[CH-UniformBar→UniformBar] B chuB


Prop[CH-Fanᴰ'→MUC] : CH-Fanᴰ' → MUC
Prop[CH-Fanᴰ'→MUC] fan f M M-spec cM = ucf
 where
  B : Subset-of-𝟚*
  B {n} u = M (cons u 0ʷ) ≤ n
  dB : detachable B
  dB _ = Lemma[≤-decidable]
  bB : Bar B
  bB = Lemma[B8] M cM
  chbB : CH-Bar B
  chbB = Propᴰ[Bar→CH-Bar] B dB bB
  chuB : CH-UniformBar' B
  chuB = fan B dB chbB
  N : ℕ
  N = pr₁ chuB
  claim : (α : 𝟚ᴺ) → Σ \(n : ℕ) → (n ≤ N) × (M (cons (α ⌜ n ⌝) 0ʷ) ≤ n)
  claim = pr₂ chuB
  prf : (α β : 𝟚ᴺ) → α ≡[ N ] β → f α ≡ f β
  prf α β eN = trans (sym claim₃) claim₇
   where
    n : ℕ
    n = pr₁ (claim α)
    r : n ≤ N
    r = pr₁ (pr₂ (claim α))
    m : ℕ
    m = M (cons (α ⌜ n ⌝) 0ʷ)
    claim₀ : m ≤ n
    claim₀ = pr₂ (pr₂ (claim α))
    claim₁ : cons (α ⌜ n ⌝) 0ʷ ≡[ n ] α
    claim₁ = ≡[]-sym (Lemma[≡[]-cons-⌜⌝] n)
    claim₂ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] α
    claim₂ = Lemma[≡[]-≤] claim₁ claim₀
    claim₃ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f α
    claim₃ = M-spec (cons (α ⌜ n ⌝) 0ʷ) α claim₂
    claim₄ : m ≤ N
    claim₄ = ≤-trans claim₀ r
    claim₅ : α ≡[ m ] β
    claim₅ = Lemma[≡[]-≤] eN claim₄
    claim₆ : cons (α ⌜ n ⌝) 0ʷ ≡[ m ] β
    claim₆ = ≡[]-trans claim₂ claim₅
    claim₇ : f (cons (α ⌜ n ⌝) 0ʷ) ≡ f β
    claim₇ = M-spec (cons (α ⌜ n ⌝) 0ʷ) β claim₆
  chucf : CH-uniformly-continuous f
  chucf = (N , prf)
  ucf : uniformly-continuous f
  ucf = Prop[CH-uc→uc] chucf


Prop[Fanᴰ→MUC] : Fanᴰ → MUC
Prop[Fanᴰ→MUC] fan = Prop[CH-Fanᴰ'→MUC] (Prop[CH-Fanᴰ→CH-Fanᴰ'] (Prop[Fanᴰ→CH-Fanᴰ] fan))

\end{code}

Hence we have

    CH-MUC ↔ MUC

\begin{code}

Prop[CH-MUC→MUC] : CH-MUC → MUC
Prop[CH-MUC→MUC] chmuc = muc
 where
  chfan : CH-Fanᴰ
  chfan = Prop[CH-MUC→CH-Fanᴰ] chmuc
  fan : Fanᴰ
  fan = Prop[CH-Fanᴰ→Fanᴰ] chfan
  muc : MUC
  muc = Prop[Fanᴰ→MUC] fan

\end{code}
