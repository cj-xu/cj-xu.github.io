
        ---------------------------------------------------
            An inductive-recursive approach to ordinals
        ---------------------------------------------------

                   Chuangjie Xu, August 2018
             updated in October 2018, February 2019


Each ordinal a < ε₀ can be uniquely written as the sum ωᵃ⁰ + ... + ωᵃⁱ
where a₀ ≥ ... ≥ aᵢ are also ordinals, and hence can be equivalently
represented by the decreasing list a₀, ... , aᵢ.  We define such a
datatype as an inductive-inductive-recursive definition in Agda.

The source file is available at

    http://cj-xu.github.io/agda/ordinals/OrdSelfContained.lagda


References.

[1] Wilfried Buchholz. Notation systems for infinitary derivations.
    Archive for Mathematical Logic, 30:277–296, 1991.

[2] Panagiotis Manolios and Daron Vroon. Ordinal arithmetic:
    algorithms and mechanization. Journal of Automated Reasoning 34
    (2005), no. 4, 387-423.

[3] Gaisi Takeuti. Proof Theory (2nd ed.). North-Holland Publ. Comp.,
    Amsterdam 1987.


This is a self-contained version consisting of

(1) a type 𝒪 of ordinals below ε₀ and a strict total order ≺ on 𝓞

(2) addition of 𝒪

(3) multiplication of 𝒪

The version with a show function for 𝒪 making use of Agda's standard
library is available at 

    http://cj-xu.github.io/agda/ordinals/Ord.html


\begin{code}

module OrdSelfContained where

\end{code}

■ Preliminaries

\begin{code}

data ℕ : Set where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Set where

⊥-elim : {A : Set} → . ⊥ → A
⊥-elim ()

infix 3 ¬_

¬_ : Set → Set
¬ A = A → ⊥

infix 4 _≡_
infix 4 _≢_

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

infixr 1 _∨_

data _∨_ (A B : Set) : Set where
 inj₁ : A → A ∨ B
 inj₂ : B → A ∨ B

case : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C 
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

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

infixr 35 _+ᴼ_

{-# TERMINATING #-}
mutual

 _+ᴼ_ : 𝒪 → 𝒪 → 𝒪
 𝟎                +ᴼ b                = b
 a                +ᴼ 𝟎                = a
 (ω^ a + c [ r ]) +ᴼ (ω^ b + d [ s ]) = case u₀ u₁ ≺-tri
  where
   u₀ : .(a ≺ b) → 𝒪
   u₀ _ = ω^ b + d [ s ]
   u₁ : .(a ≽ b) → 𝒪
   u₁ h = ω^ a + (c +ᴼ ω^ b + d [ s ]) [ Lm[≽+ᴼ] a c _ r h ]

 Lm[≽+ᴼ] : (a b c : 𝒪) → a ≽ fst b → a ≽ fst c → a ≽ fst (b +ᴼ c)
 Lm[≽+ᴼ] a  𝟎                c               r s = s
 Lm[≽+ᴼ] a (ω^ b + d [ u ])  𝟎               r s = r
 Lm[≽+ᴼ] a (ω^ b + d [ u ]) (ω^ c + e [ v ]) r s = case w₀ w₁ ≺-tri
  where
   lemma : {x y z : 𝒪} → x ≽ y → z ≡ y → x ≽ z
   lemma r refl = r 
   w₀ : b ≺ c → a ≽ fst (ω^ b + d [ u ] +ᴼ ω^ c + e [ v ])
   w₀ w = lemma s (cong fst p)
    where
     p : ω^ b + d [ u ] +ᴼ ω^ c + e [ v ] ≡ ω^ c + e [ v ]
     p = case-spec₀ Lm[≺→¬≽] ≺-tri w
   w₁ : b ≽ c → a ≽ fst (ω^ b + d [ u ] +ᴼ ω^ c + e [ v ])
   w₁ w = lemma r (cong fst p)
    where
     p : ω^ b + d [ u ] +ᴼ ω^ c + e [ v ] ≡ ω^ b + _ [ _ ]
     p = case-spec₁ Lm[≺→¬≽] ≺-tri w

--
-- Successor
--
sucᴼ : 𝒪 → 𝒪
sucᴼ a = a +ᴼ 𝟏

--
-- Embedding of ℕ into 𝒪
--
to𝒪 : ℕ → 𝒪
to𝒪  0      = 𝟎
to𝒪 (suc n) = sucᴼ (to𝒪 n)

\end{code}

■ Multiplication

\begin{code}

infixr 40 _×ᴼ_

_×ᴼ_ : 𝒪 → 𝒪 → 𝒪
𝟎              ×ᴼ b              = 𝟎
a              ×ᴼ 𝟎              = 𝟎
ω^ a + c [ r ] ×ᴼ ω^ b + d [ s ] = ω^⟨ a +ᴼ b ⟩ +ᴼ c ×ᴼ ω^⟨ b ⟩ +ᴼ (ω^ a + c [ r ]) ×ᴼ d

{-

The last case can be equivalently defined by

 ω^ a + c [ r ] ×ᴼ ω^ b + d [ s ] = (ω^(a +ᴼ b) + c ×ᴼ ω^⟨ b ⟩ [ Lm[≽×ᴼ] a ω^⟨ b ⟩ c r ]) +ᴼ (ω^ a + c [ r ]) ×ᴼ d

which requries to simultaneously prove the following two lemmas

 Lm[fst×ᴼ] : (a b : 𝒪) → fst a +ᴼ fst b ≽ fst (a ×ᴼ b)
 Lm[≽×ᴼ]   : (a b c : 𝒪) → a ≽ fst c → a +ᴼ fst b ≽ fst (c ×ᴼ b)

-}

\end{code}

■ More examples to test

\begin{code}

e0 : 𝒪
e0 = (ω^⟨ ω ⟩ +ᴼ 𝟏) ×ᴼ (ω +ᴼ ω)

e1 : 𝒪
e1 = ω^⟨ ω ⟩ ×ᴼ ω

e2 : 𝒪
e2 = ω ×ᴼ ω^⟨ ω ⟩

e3 : 𝒪
e3 = ω^⟨ ω ×ᴼ ω ×ᴼ ω ⟩

\end{code}
