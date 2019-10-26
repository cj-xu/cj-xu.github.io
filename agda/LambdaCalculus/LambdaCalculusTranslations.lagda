
  --------------------------------
    Translations between Λ and 𝕃
  --------------------------------

     Chuangjie Xu, 7 April 2019


■ A mini libaray

\begin{code}

open import Preliminaries

\end{code}

■ The algebra Λᵣ of raw λ-terms

\begin{code}

𝕏 : Set
𝕏 = ℕ

data Λᵣ : Set where
 [_]      : 𝕏 * → 𝕏 → Λᵣ
 [_]₍_·_₎ : 𝕏 * → Λᵣ → Λᵣ → Λᵣ

--
-- weakening function
--
⟨_⟩ : 𝕏 * → Λᵣ → Λᵣ
⟨ v ⟩ ([ u ] x)        = [ v ++ u ] x
⟨ v ⟩ ([ u ]₍ M · N ₎) = [ v ++ u ]₍ M · N ₎

\end{code}

■ Prof. Sato's 𝕃 of closed λ-terms

\begin{code}

data 𝕃ᵣ : Set where
 Prj : ℕ → ℕ → 𝕃ᵣ
 App : ℕ → 𝕃ᵣ → 𝕃ᵣ → 𝕃ᵣ

\end{code}

■ Translating 𝕃 → Λ

The trick is the helper function that drops prefices of given length.

\begin{code}

toΛh : ℕ → 𝕃ᵣ → Λᵣ
toΛh m (Prj i j)   = [ gen m (i + j + 1) ] i
toΛh m (App n K L) = [ gen m n ]₍ toΛh n K · toΛh n L ₎

toΛ : 𝕃ᵣ → Λᵣ
toΛ = toΛh 0

\end{code}

■ Translating Λ → 𝕃

The trick is to use the weakening function in the inductive case.

\begin{code}

{-# TERMINATING #-}
to𝕃 : Λᵣ → 𝕃ᵣ
to𝕃 ([ u ] x)        = Prj (∣ u ∣ - (idx x u + 1)) (idx x u)
to𝕃 ([ u ]₍ M · N ₎) = App ∣ u ∣ (to𝕃 (⟨ u ⟩ M)) (to𝕃 (⟨ u ⟩ N))

\end{code}

■ Some examples to test

\begin{code}

M0 M1 M2 M3 M4 M5 : Λᵣ
M0 = [ ε , 0 ] 0
M1 = [ ε , 0 , 1 ] 0
M2 = [ ε , 0 ]₍ [ ε , 1 ] 1 · [ ε , 1 ] 0 ₎
M3 = [ ε , 0 , 1 ]₍ [ ε ] 1 · [ ε ] 0 ₎
M4 = [ ε , 0 ]₍ [ ε ]₍ [ ε , 1 ] 1 · [ ε , 1 ] 0 ₎ · [ ε , 1 ]₍ [ ε ] 1 · [ ε ] 0 ₎ ₎
M5 = [ ε ]₍ [ ε , 0 ]₍ [ ε , 1 ] 1 · [ ε , 1 ] 0 ₎ · [ ε , 0 , 1 ]₍ [ ε ] 1 · [ ε ] 0 ₎ ₎

K0 K1 K2 K3 K4 K5 : 𝕃ᵣ
K0 = Prj 0 0
K1 = Prj 0 1
K2 = App 1 (Prj 1 0) (Prj 0 1)
K3 = App 2 (Prj 1 0) (Prj 0 1)
K4 = App 1 (App 1 (Prj 1 0) (Prj 0 1)) (App 2 (Prj 1 0) (Prj 0 1))
K5 = App 0 (App 1 (Prj 1 0) (Prj 0 1)) (App 2 (Prj 1 0) (Prj 0 1))

E4  : to𝕃 M4 ≡ K4
E4  = refl
E4' : toΛ K4 ≡ M4
E4' = refl

\end{code}
