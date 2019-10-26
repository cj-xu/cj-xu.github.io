

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                        The Fan Theorem
                        ---------------

                         Chuangjie Xu

           14-16 Monday 11th December 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/

\begin{code}

open import Preliminaries
open import Untruncation
open import Fan20171204

\end{code}

Recall the 4 formulations of Brouwer's Fan Theorem we defined last week:

■ CH-Fan  = (B : Subset 𝟚*) → ext-closed B                → CH-Bar B → CH-UniformBar B

■ Fan     = (B : Subset 𝟚*) → ext-closed B                → Bar B    → UniformBar B

■ CH-Fanᴰ = (B : Subset 𝟚*) → ext-closed B → detachable B → CH-Bar B → CH-UniformBar B

■ Fanᴰ    = (B : Subset 𝟚*) → ext-closed B → detachable B → Bar B    → UniformBar B

We firstly study how they relate to each other

\begin{code}

Prop[CH-Fan→CH-Fanᴰ] : CH-Fan → CH-Fanᴰ
Prop[CH-Fan→CH-Fanᴰ] = {!!}

Prop[Fan→Fanᴰ] : Fan → Fanᴰ
Prop[Fan→Fanᴰ] = {!!}

\end{code}

Question: what about CH-Fan and Fan?

Since detachability is needed to show

    CH-Bar ↔ Bar  and  CH-UniformBar ↔ UniformBar

We can only prove  CH-Fan ↔ Fan  for detachable bars.

\begin{code}

Prop[CH-Fanᴰ→Fanᴰ] : CH-Fanᴰ → Fanᴰ
Prop[CH-Fanᴰ→Fanᴰ] = {!!}

Prop[Fanᴰ→CH-Fanᴰ] : Fanᴰ → CH-Fanᴰ
Prop[Fanᴰ→CH-Fanᴰ] = {!!}

\end{code}

Then we relate them to

  ------------------------------------------
    Brouwer's uniform-continuity principle
  ------------------------------------------

\begin{code}

CH-Cont : Set
CH-Cont = (f : 𝟚ᴺ → ℕ) (α : 𝟚ᴺ) → Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

Cont : Set
Cont = (f : 𝟚ᴺ → ℕ) (α : 𝟚ᴺ) → ∥ (Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

CH-UC : Set
CH-UC = (f : 𝟚ᴺ → ℕ) → Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

UC : Set
UC = (f : 𝟚ᴺ → ℕ) → ∥ (Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

\end{code}

We already proved  CH-UC ↔ UC  a few weeks ago.

But  CH-Cont ↔ UC  doesn't seem possible...

Let's prove some trivial implications.

\begin{code}

Prop[CH-Cont→Cont] : CH-Cont → Cont
Prop[CH-Cont→Cont] = {!!}

Prop[CH-UC→CH-Cont] : CH-UC → CH-Cont
Prop[CH-UC→CH-Cont] = {!!}

\end{code}

CH-UC is acually a very strong principle.

\begin{code}

Prop[CH-UC→CH-Fan] : CH-UC → CH-Fan
Prop[CH-UC→CH-Fan] = {!!}

Prop[CH-Fan∧CH-Cont→CH-UC] : CH-Fan → CH-Cont → CH-UC
Prop[CH-Fan∧CH-Cont→CH-UC] = {!!}

\end{code}

Perhaps CH-Fanᴰ (with CH-Cont) is sufficient to derive CH-UC.

Prop[CH-Fanᴰ∧CH-Cont→CH-UC] : CH-Fan → CH-Cont → CH-UC



Let's weaken UC and/or strengthen Fan to enrich the picture

\begin{code}

CH-WUC : Set
CH-WUC = (f : 𝟚ᴺ → ℕ)
       → ((α : 𝟚ᴺ) → Σ \(n : ℕ) → (β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β)
       → (Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β)

-- I conjecture:  CH-WUC ↔ CH-Fanᴰ


c-set : Subset 𝟚* → Set₁
c-set B = Σ \(D : Subset 𝟚*) →  detachable D
                             × (∀ u → (u ∈ B) ↔ (∀ w → w ⊑ u → w ∈ D))

CH-c-Fan : Set₁
CH-c-Fan = (B : Subset 𝟚*) → detachable B → c-set B → CH-Bar B → CH-UniformBar B

-- I conjecture:  CH-WUC ↔ CH-c-Fan

\end{code}

