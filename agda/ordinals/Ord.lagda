
        -------------------------------------------------
            Ordinal notations via induction-recursion
        -------------------------------------------------

                   Chuangjie Xu, August 2018
            updated in October 2018 & February 2019
                    corrected in April 2019


Each ordinal a can be uniquely written as the sum ωᵃ⁰ + ... + ωᵃⁱ
where a₀ ≥ ... ≥ aᵢ are also ordinals, and hence can be equivalently
represented by the decreasing list a₀, ... , aᵢ.  We define such a
datatype as an inductive-inductive-recursive definition in Agda.

The source file is available at

    http://cj-xu.github.io/agda/ordinals/Ord.lagda


Reference.

[1] Wilfried Buchholz. Notation systems for infinitary derivations.
    Archive for Mathematical Logic, 30:277–296, 1991.

[2] Pierre Castéran and Évelyne Contejean. On ordinal notations,
    http://coq.inria.fr/V8.2pl1/contribs/Cantor.html.

[3] Panagiotis Manolios and Daron Vroon. Ordinal arithmetic:
    algorithms and mechanization. Journal of Automated Reasoning 34
    (2005), no. 4, 387-423.

[4] Gaisi Takeuti. Proof Theory (2nd ed.). North-Holland Publ. Comp.,
    Amsterdam 1987.


This file consists of

(1) a type 𝒪 of ordinals below ε₀ and a strict total order ≺ on 𝓞

(2) a show function for 𝒪

(3) arithemtic of 𝒪: addition, subtraction, multiplication and exponentiation


\begin{code}

module Ord where

open import Agda.Builtin.Equality
open import Data.Empty.Irrelevant
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; cong)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_; [_,_]′ to case)
open import Data.String.Base as String using (String; primStringAppend)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)

\end{code}

■ Preliminaries

\begin{code}

case-spec₀ : {A B C : Set} {f : .A → C} {g : .B → C}
           → .(A → ¬ B) → (w : A ∨ B) .(a : A) → case f g w ≡ f a
case-spec₀ h (inj₁ _) _ = refl
case-spec₀ h (inj₂ b) a = ⊥-elim (h a b)

case-spec₁ : {A B C : Set} {f : .A → C} {g : .B → C}
           → .(A → ¬ B) → (w : A ∨ B) .(b : B) → case f g w ≡ g b
case-spec₁ h (inj₁ a) b = ⊥-elim (h a b)
case-spec₁ h (inj₂ _) _ = refl

\end{code}

■ An inductive-inductive-recursive definition of ordinals (< ε₀)
  in Cantor normal form

\begin{code}

infix 30 _≺_
infix 30 _≼_
infix 30 _≻_
infix 30 _≽_

mutual 

 data 𝒪 : Set where
  𝟎 : 𝒪
  ω^_+_[_] : (a b : 𝒪) → .(a ≽ fst b) → 𝒪

 data _≺_ : 𝒪 → 𝒪 → Set where
  ≺₁ : {a : 𝒪}
     → a ≢ 𝟎 → 𝟎 ≺ a
  ≺₂ : {a b c d : 𝒪} .{r : a ≽ fst c} .{s : b ≽ fst d}
     → a ≺ b → ω^ a + c [ r ] ≺ ω^ b + d [ s ]
  ≺₃ : {a b c : 𝒪} .{r : a ≽ fst b} .{s : a ≽ fst c}
     → b ≺ c → ω^ a + b [ r ] ≺ ω^ a + c [ s ]

 fst : 𝒪 → 𝒪
 fst  𝟎               = 𝟎
 fst (ω^ a + _ [ _ ]) = a

 _≻_ _≽_ _≼_ : 𝒪 → 𝒪 → Set
 a ≻ b =  b ≺ a
 a ≽ b = (a ≻ b) ∨ (a ≡ b)
 a ≼ b =  b ≽ a

lst : 𝒪 → 𝒪
lst  𝟎               = 𝟎
lst (ω^ a + 𝟎 [ _ ]) = a
lst (ω^ a + b [ _ ]) = lst b

data ⊥ : Set where

isSuc : 𝒪 → Set
isSuc 𝟎 = ⊥
isSuc a = lst a ≡ 𝟎

\end{code}

■ Showing ordinals

\begin{code}

infixl 10 _++_

_++_ : String → String → String
_++_ = primStringAppend

toℕ : 𝒪 → ℕ
toℕ 𝟎 = 0
toℕ ω^ _ + b [ _ ] = suc (toℕ b)

mutual
 show : 𝒪 → String
 show 𝟎 = "0"
 show ω^ 𝟎 + b [ _ ] = showℕ (suc (toℕ b))
 show ω^ (ω^ 𝟎 + 𝟎 [ _ ]) + b [ _ ] = "ω" ++ end b
 show ω^ (ω^ a + c [ r ]) + b [ _ ] = "ω^" ++ bracket (ω^ a + c [ r ]) ++ end b

 end : 𝒪 → String
 end 𝟎 = ""
 end a = " + " ++ show a

 bracket : 𝒪 → String
 bracket 𝟎 = "0"
 bracket a @ (ω^ 𝟎 + _ [ _ ]) = show a
 bracket a @ (ω^ _ + 𝟎 [ _ ]) = show a
 bracket a @ (ω^ _ + ω^ _ + _ [ _ ] [ _ ]) = "(" ++ show a ++ ")"

\end{code}

■ _≺_ is a strict total order on 𝒪.

\begin{code}

≺₃' : {a b c d : 𝒪} .{r : a ≽ fst c} .{s : b ≽ fst d}
    → a ≡ b → c ≺ d → ω^ a + c [ r ] ≺ ω^ b + d [ s ]
≺₃' refl = ≺₃

𝒪⁼ : {a b c d : 𝒪} .{r : a ≽ fst c} .{s : b ≽ fst d}
   → a ≡ b → c ≡ d → ω^ a + c [ r ] ≡ ω^ b + d [ s ]
𝒪⁼ refl refl = refl

--
-- _≺_ is irreflexive
--
≺-irrefl : {a : 𝒪} → ¬ (a ≺ a)
≺-irrefl (≺₁ f) = f refl
≺-irrefl (≺₂ r) = ≺-irrefl r
≺-irrefl (≺₃ r) = ≺-irrefl r

--
-- _≺_ is transitive
--
≺-trans : {a b c : 𝒪} → a ≺ b → b ≺ c → a ≺ c
≺-trans (≺₁ f) (≺₁ g) = ≺₁ g
≺-trans (≺₁ f) (≺₂ s) = ≺₁ (λ ())
≺-trans (≺₁ f) (≺₃ s) = ≺₁ (λ ())
≺-trans (≺₂ r) (≺₂ s) = ≺₂ (≺-trans r s)
≺-trans (≺₂ r) (≺₃ s) = ≺₂ r
≺-trans (≺₃ r) (≺₂ s) = ≺₂ s
≺-trans (≺₃ r) (≺₃ s) = ≺₃ (≺-trans r s)

--
-- _≺_ is trichotomous
--
≺-tri : {a b : 𝒪} → (a ≺ b) ∨ (a ≻ b) ∨ (a ≡ b)
≺-tri {𝟎}              {𝟎}              = inj₂ (inj₂ refl)
≺-tri {𝟎}              {ω^ b + d [ _ ]} = inj₁ (≺₁ (λ ()))
≺-tri {ω^ a + c [ _ ]} {𝟎}              = inj₂ (inj₁ (≺₁ (λ ())))
≺-tri {ω^ a + c [ _ ]} {ω^ b + d [ _ ]} with ≺-tri
...                                     | inj₁       a<b                    = inj₁ (≺₂ a<b)
...                                     | inj₂ (inj₁ a>b)                   = inj₂ (inj₁ (≺₂ a>b))
...                                     | inj₂ (inj₂ a=b) with ≺-tri
...                                                       | inj₁       c<d  = inj₁ (≺₃' a=b c<d)
...                                                       | inj₂ (inj₁ c>d) = inj₂ (inj₁ (≺₃' (sym a=b) c>d))
...                                                       | inj₂ (inj₂ c=d) = inj₂ (inj₂ (𝒪⁼ a=b c=d))

Lm[≺→¬≽] : {a b : 𝒪} → a ≺ b → ¬ (a ≽ b)
Lm[≺→¬≽] a<b (inj₁ a>b)  = ≺-irrefl (≺-trans a<b a>b)
Lm[≺→¬≽] a<b (inj₂ refl) = ≺-irrefl a<b

Lm[≽→¬≺] : {a b : 𝒪} → a ≽ b → ¬ (a ≺ b)
Lm[≽→¬≺] (inj₁ b<a) a<b = ≺-irrefl (≺-trans a<b b<a)
Lm[≽→¬≺] (inj₂ refl) = ≺-irrefl

Lm[¬≺→≽] : {a b : 𝒪} → ¬ (a ≺ b) → a ≽ b
Lm[¬≺→≽] {a} {b} f with ≺-tri
...                | inj₁       a<b  = ⊥-elim (f a<b)
...                | inj₂ (inj₁ a>b) = inj₁ a>b
...                | inj₂ (inj₂ a=b) = inj₂ a=b

--
-- _≺_ is decidable
--
≺-dec : (a b : 𝒪) → (a ≺ b) ∨ ¬ (a ≺ b)
≺-dec a b with ≺-tri
...       | inj₁ a<b = inj₁ a<b
...       | inj₂ a≥b = inj₂ (Lm[≽→¬≺] a≥b)

\end{code}

■ Examples of ordinals

\begin{code}

Lm[≽𝟎] : {a : 𝒪} → a ≽ 𝟎
Lm[≽𝟎] {𝟎}              = inj₂ refl
Lm[≽𝟎] {ω^ a + b [ _ ]} = inj₁ (≺₁ (λ ()))

ω^⟨_⟩ : 𝒪 → 𝒪
ω^⟨ a ⟩ = ω^ a + 𝟎 [ Lm[≽𝟎] ]

𝟏 : 𝒪
𝟏 = ω^⟨ 𝟎 ⟩

ω : 𝒪
ω = ω^⟨ 𝟏 ⟩

\end{code}

■ Addition

Because of the mutual definition, we have to simultaneously define
addition of ordinals and prove a lemma of a property of addition.

\begin{code}

infixl 35 _+_

mutual

 _+_ : 𝒪 → 𝒪 → 𝒪
 𝟎                + b                = b
 a                + 𝟎                = a
 (ω^ a + c [ r ]) + (ω^ b + d [ s ]) = case u₀ u₁ ≺-tri
  where
   u₀ : .(a ≺ b) → 𝒪
   u₀ _ = ω^ b + d [ s ]
   u₁ : .(a ≽ b) → 𝒪
   u₁ h = ω^ a + (c + ω^ b + d [ s ]) [ Lm[≽+] a c _ r h ]

 {-# TERMINATING #-}
 Lm[≽+] : (a b c : 𝒪) → a ≽ fst b → a ≽ fst c → a ≽ fst (b + c)
 Lm[≽+] a  𝟎                c               r s = s
 Lm[≽+] a (ω^ b + d [ u ])  𝟎               r s = r
 Lm[≽+] a (ω^ b + d [ u ]) (ω^ c + e [ v ]) r s = case w₀ w₁ ≺-tri
  where
   lemma : {x y z : 𝒪} → x ≽ y → z ≡ y → x ≽ z
   lemma r refl = r 
   w₀ : b ≺ c → a ≽ fst (ω^ b + d [ u ] + ω^ c + e [ v ])
   w₀ w = lemma s (cong fst p)
    where
     p : ω^ b + d [ u ] + ω^ c + e [ v ] ≡ ω^ c + e [ v ]
     p = case-spec₀ Lm[≺→¬≽] ≺-tri w
   w₁ : b ≽ c → a ≽ fst (ω^ b + d [ u ] + ω^ c + e [ v ])
   w₁ w = lemma r (cong fst p)
    where
     p : ω^ b + d [ u ] + ω^ c + e [ v ] ≡ ω^ b + _ [ _ ]
     p = case-spec₁ Lm[≺→¬≽] ≺-tri w

--
-- Embedding of ℕ into 𝒪
--
to𝒪 : ℕ → 𝒪
to𝒪  0      = 𝟎
to𝒪 (suc n) = to𝒪 n + 𝟏

\end{code}

■ Substraction

\begin{code}

infixl 35 _-_

_-_ : 𝒪 → 𝒪 → 𝒪
𝟎 - b = 𝟎
a - 𝟎 = a
(ω^ a + c [ r ]) - (ω^ b + d [ s ]) with ≺-tri {a} {b}
...                                 | inj₁       a<b  = 𝟎
...                                 | inj₂ (inj₁ a>b) = ω^ a + c [ r ]
...                                 | inj₂ (inj₂ a=b) = c - d

\end{code}

■ Multiplication

\begin{code}

infixl 40 _·_

_·_ : 𝒪 → 𝒪 → 𝒪
𝟎              · b              = 𝟎
a              · 𝟎              = 𝟎
a              · ω^ 𝟎 + d [ _ ] = a + a · d
ω^ a + c [ r ] · ω^ b + d [ _ ] = ω^⟨ a + b ⟩ + (ω^ a + c [ r ]) · d

\end{code}

■ Exponentiation

We adapted the algorithm from [2] to define the following.

\begin{code}

_^_ : 𝒪 → 𝒪 → 𝒪
x                    ^ 𝟎                               = 𝟏
𝟎                    ^ y                               = 𝟎
(ω^ 𝟎 + 𝟎 [ _ ])     ^ y                               = 𝟏
x                    ^ (ω^ 𝟎 + z [ _ ])                = x · (x ^ z)
x @ (ω^ 𝟎 + c [ _ ]) ^ (ω^ (ω^ 𝟎 + 𝟎 [ _ ]) + z [ _ ]) = ω · (x ^ z)
x @ (ω^ 𝟎 + c [ _ ]) ^ (ω^ b + z [ _ ])                = ω^⟨ b - 𝟏 ⟩ · (x ^ z)
x @ (ω^ a + c [ _ ]) ^ (ω^ b + z [ _ ])                = ω^⟨ a · ω^⟨ b ⟩ ⟩ · (x ^ z)

\end{code}
