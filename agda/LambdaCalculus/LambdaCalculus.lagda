
    ----------------------------------------------
         Various approaches to closed λ-terms 
    ----------------------------------------------

            Chuangjie Xu, 6 April 2019


After defining the algebra Λᵣ of raw λ-terms, I present 4 inductive
definitions to denote closed λ-terms:

 □ Λ₁ is a predicate on Λᵣ, defined using a weakening function on Λᵣ

 □ Λ₂ is a predicate on Λᵣ, defined using a strengthening function

 □ Λᶜ is a predicate on Λᵣ such that every sub-term of K ∈ Λᶜ is closed

 □ Λ[u] is a type of terms in context u

However, I don't have time to verify the following conjectures

 (C1) Λ₁ and Λ₂ are equivalent to Prof. Sato's Λ.

 (C2) Λᶜ is isomorphic to Λ₁.

 (C3) Λ[] is isomorphic to Λᶜ.

The source file is available at

  http://cj-xu.github.io/agda/lambda/LambdaCalculus.lagda


\begin{code}

module LambdaCalculus where

\end{code}

■ Preliminaries

\begin{code}

infixr 2 _∈_

_∈_ : {A : Set} → A → (A → Set) → Set
a ∈ P = P a

data ⊥ : Set where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
 refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set} {x y : A}
     → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}

■ Finite lists

\begin{code}

infixl 20 _,_
infixr 15 _++_

data _* (A : Set) : Set where
 ε   : A *
 _,_ : A * → A → A *

_++_ : {A : Set} → A * → A * → A *
u ++ ε       = u
u ++ (v , x) = (u ++ v) , x

--
-- Prefix relation: u ≼ v means u is a prefix of v.
--
data _≼_ {A : Set} (u : A *) : A * → Set where
 ≼-refl : u ≼ u
 ≼-cons : {v : A *} {x : A} → u ≼ v → u ≼ (v , x)

--
-- Drop a prefix of a list
--
drop : {A : Set} (u : A *) {v : A *} → v ≼ u → A *
drop  u       ≼-refl    = ε
drop (u , y) (≼-cons r) = drop u r , y

drop-spec : {A : Set} (u v : A *) (r : v ≼ u) → v ++ drop u r ≡ u
drop-spec  u     .u  ≼-refl    = refl
drop-spec (u , x) v (≼-cons r) = cong (λ w → w , x) (drop-spec u v r)

--
-- List membership e.g. i : ∥ x ∈ u ∥ is the index of x in u.
--
data ∥_∈_∥ {A : Set} (a : A) : A * → Set where
 zero : {u : A *} → ∥ a ∈ (u , a) ∥
 succ : {u : A *} {b : A} → ∥ a ∈ u ∥ → ∥ a ∈ (u , b) ∥

_∉_ : {A : Set} → A → A * → Set
x ∉ u = ∥ x ∈ u ∥ → ⊥

\end{code}

■ The algebra of raw λ-terms

\begin{code}

𝕏 : Set
𝕏 = ℕ

data Λᵣ : Set where
 [_]      : 𝕏 * → 𝕏 → Λᵣ
 [_]₍_·_₎ : 𝕏 * → Λᵣ → Λᵣ → Λᵣ

cxt : Λᵣ → 𝕏 *
cxt ([ u ] x)        = u
cxt ([ u ]₍ K · L ₎) = u

--
-- weakening function
--
⟨_⟩ : 𝕏 * → Λᵣ → Λᵣ
⟨ v ⟩ ([ u ] x)        = [ v ++ u ] x
⟨ v ⟩ ([ u ]₍ K · L ₎) = [ v ++ u ]₍ K · L ₎

--
-- strengthening function
--
str : (K : Λᵣ) {v : 𝕏 *} → v ≼ cxt K → Λᵣ
str ([ u ] x)        r = [ drop u r ] x
str ([ u ]₍ K · L ₎) r = [ drop u r ]₍ K · L ₎

\end{code}

■ 1st definition of the subset Λ of closed λ-terms

This is basically Prof. Sato's Λ but its second rule uses an
inductively defined weakening function in the premise.

\begin{code}

data Λ₁ : Λᵣ → Set where
 Var : (u : 𝕏 *) (x : 𝕏) → .(∥ x ∈ u ∥)  -- the position of x in u is not needed
     → [ u ] x ∈ Λ₁
 App : (u : 𝕏 *) (K L : Λᵣ)
     → ⟨ u ⟩ K ∈ Λ₁ → ⟨ u ⟩ L ∈ Λ₁
     → [ u ]₍ K · L ₎ ∈ Λ₁

\end{code}

■ 2nd definition of the subset Λ of closed λ-terms

The second rule uses a strengthening function in the conclusion.

\begin{code}

data Λ₂ : Λᵣ → Set where
 Var : (u : 𝕏 *) (x : 𝕏) → .(∥ x ∈ u ∥)
     → [ u ] x ∈ Λ₂
 App : (u : 𝕏 *) (K L : Λᵣ)
     → K ∈ Λ₂ → L ∈ Λ₂ → (r : u ≼ cxt K) → (s : u ≼ cxt L)
     → [ u ]₍ str K r · str L s ₎ ∈ Λ₂

\end{code}

■ Another definition of closed λ-terms

This definition Λᶜ corresponds to Prof. Sato's 𝕃.

\begin{code}

data Λᶜ : Λᵣ → Set where
 Var : (u v : 𝕏 *) (x : 𝕏) → x ∉ v
     → [ u , x ++ v ] x ∈ Λᶜ
 App : (u : 𝕏 *) (K L : Λᵣ)
     → K ∈ Λᶜ → L ∈ Λᶜ → u ≼ cxt K → u ≼ cxt L
     → [ u ]₍ K · L ₎ ∈ Λᶜ

\end{code}

■ A type family of λ-terms in context

  x ∈ u          ux ⊢ M          u ⊢ M  u ⊢ N
 -------(Var)  ----------(Lam)  --------------(App)
  u ⊢ x         u ⊢ λx.M            u ⊢ MN

\begin{code}

data Λ[_] (u : 𝕏 *) : Set where
 Var : (x : 𝕏) → .(∥ x ∈ u ∥) → Λ[ u ]
 Lam : (x : 𝕏) → Λ[ u , x ] → Λ[ u ]
 App : Λ[ u ] → Λ[ u ] → Λ[ u ]

\end{code}
