
      ---------------------------
        Theorem[KECA-TLCA'2013]
      ---------------------------

  N. Kraus, M. Escardó, T. Coquand, and T. Altenkirch.
  Generalizations of Hedberg’s theorem.  In Typed Lambda Calculi and
  Applications, volume 7941 of Lecture Notes in Computer Science,
  pages 173-188.  Springer Berlin Heidelberg, 2013.

\begin{code}

module KECA where

open import Preliminaries

\end{code}

Some definitions and lemmas

\begin{code}

constant : {A B : Set} → (A → B) → Set
constant f = ∀ x y → f x ≡ f y

infix  30 _⁻¹
infixr 25 _•_

_⁻¹ : {A : Set} {x y : A}
    → x ≡ y → y ≡ x
_⁻¹ = sym

_•_ : {A : Set} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
_•_ = trans

infix  1 finally
infixr 0 _≡⟨_⟩_

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p • q

finally : {A : Set} (x y : A) → x ≡ y → x ≡ y
finally _ _ p = p

syntax finally x y p = x ≡⟨ p ⟩∎ y ∎

sym-is-inverse : {X : Set} {x y : X} (p : x ≡ y)
               → refl ≡ p ⁻¹ • p
sym-is-inverse refl = refl

ap-id-is-id : {X : Set} {x y : X} (p : x ≡ y)
            → ap (λ z → z) p ≡ p
ap-id-is-id refl = refl

refl-is-left-id : {X : Set} {x y : X} (p : x ≡ y)
                → p ≡ refl • p
refl-is-left-id refl = refl

refl-is-right-id : {X : Set} {x y : X} (p : x ≡ y)
                 → p ≡ p • refl
refl-is-right-id refl = refl

sym-trans : {X : Set} {x y z : X} (p : x ≡ y) (q : y ≡ z)
          → (q ⁻¹) • (p ⁻¹) ≡ (p • q)⁻¹
sym-trans refl refl = refl

sym-sym-trivial : {X : Set} {x y : X} (p : x ≡ y)
                → p ≡ (p ⁻¹)⁻¹
sym-sym-trivial refl = refl

trans-assoc : {X : Set} {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
            → (p • q) • r ≡ p • (q • r)
trans-assoc refl refl refl = refl

Kraus-Lemma₀ : {X Y : Set} (f : X → Y) (cf : constant f) {x y : X} (p : x ≡ y)
             → ap f p ≡ (cf x x) ⁻¹ • (cf x y) 
Kraus-Lemma₀ f cf {x} refl = sym-is-inverse (cf x x)

Kraus-Lemma₁ : {X Y : Set} (f : X → Y) → constant f → {x : X} (p : x ≡ x)
             → ap f p ≡ refl
Kraus-Lemma₁ f cf {x} p = (Kraus-Lemma₀ f cf p) • (sym-is-inverse (cf x x)) ⁻¹

transport-paths-along-paths : {X Y : Set} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x) 
                           → transport (λ z → h z ≡ k z) p q ≡ (ap h p) ⁻¹ • q • (ap k p)
transport-paths-along-paths {X} {Y} {x} {.x} refl h k q = claim₀ • claim₁
 where
  claim₀ : q ≡ q • refl
  claim₀ = refl-is-right-id q
  claim₁ : q • refl ≡ refl • q • refl
  claim₁ = refl-is-left-id (q • refl)

transport-paths-along-paths' : {X : Set} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x) 
                             → transport (λ z → z ≡ f z) p q ≡ p ⁻¹ • q • (ap f p)
transport-paths-along-paths' {X} {x} p f q = claim₀ • claim₁
 where
  claim₀ : transport (λ z → z ≡ f z) p q ≡ (ap (λ z → z) p) ⁻¹ • q • (ap f p)
  claim₀ = transport-paths-along-paths p (λ z → z) f q
  claim₁ : (ap (λ z → z) p) ⁻¹ • q • (ap f p) ≡ p ⁻¹ • q • (ap f p)
  claim₁ = ap (λ pr → pr ⁻¹ • q • (ap f p)) (ap-id-is-id p)

\end{code}

The main lemma and the theorem

\begin{code}

fix : {X : Set} → (X → X) → Set
fix f = Σ \x → x ≡ f x

Kraus-Lemma : {X : Set} (f : X → X) → constant f → isProp (fix f)
Kraus-Lemma {X} f g (x , p) (y , q) =
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ pair⁼ r refl ⟩
  (y , p')       ≡⟨ pair⁼ s t ⟩∎           
  (y , q) ∎
    where
     r : x ≡ y
     r = x ≡⟨ p ⟩
       f x ≡⟨ g x y ⟩
       f y ≡⟨ q ⁻¹ ⟩∎
         y ∎
     p' : y ≡ f y
     p' = transport (λ z → z ≡ f z) r p
     s : y ≡ y
     s = y   ≡⟨ p' ⟩
         f y ≡⟨ q ⁻¹ ⟩∎
         y   ∎
     q' : y ≡ f y
     q' = transport (λ z → z ≡ f z) s p'
     t : q' ≡ q
     t = q'                         ≡⟨ transport-paths-along-paths' s f p' ⟩
         s ⁻¹ • (p' • ap f s)       ≡⟨ ap (λ pr → s ⁻¹ • (p' • pr)) (Kraus-Lemma₁ f g s) ⟩
         s ⁻¹ • (p' • refl)         ≡⟨ ap (λ pr → s ⁻¹ • pr) ((refl-is-right-id p')⁻¹)  ⟩
         s ⁻¹ • p'                  ≡⟨ refl  ⟩
         (p' • (q ⁻¹))⁻¹ • p'       ≡⟨ ap (λ pr → pr • p') ((sym-trans p' (q ⁻¹))⁻¹)  ⟩
         ((q ⁻¹)⁻¹ • (p' ⁻¹)) • p'  ≡⟨ ap (λ pr → (pr • (p' ⁻¹)) • p') ((sym-sym-trivial q)⁻¹) ⟩
         (q • (p' ⁻¹)) • p'         ≡⟨ trans-assoc q (p' ⁻¹) p'  ⟩
         q • ((p' ⁻¹) • p')         ≡⟨ ap (λ pr → q • pr) ((sym-is-inverse p')⁻¹) ⟩
         q • refl                   ≡⟨ (refl-is-right-id q)⁻¹  ⟩∎
         q  ∎


Theorem[KECA-TLCA'2013] : {A : Set} (f : A → A) → constant f → ∥ A ∥ → A
Theorem[KECA-TLCA'2013] {A} f cf x = pr₁ (hA2F x)
 where
  F : Set
  F = fix f
  hF : isProp F
  hF = Kraus-Lemma f cf
  A2F : A → F
  A2F a = f a , cf a (f a)
  hA2F : ∥ A ∥ → F
  hA2F = ∥∥-elim hF A2F

\end{code}

