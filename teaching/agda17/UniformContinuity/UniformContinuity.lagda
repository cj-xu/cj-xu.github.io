

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

               Uniform Continuity in Type Theory
               ---------------------------------

                         Chuangjie Xu

           14-16 Monday 20th November 2017, HS B 252

          http://www.math.lmu.de/~xu/teaching/agda17/

---------------------
    Preliminaries
---------------------

Import the minimal library for today's lecture

\begin{code}

open import Preliminaries

\end{code}

------------------------------------------------------------
    Two formulations of the uniform-continuity principle
------------------------------------------------------------

\begin{code}

CH-UC : Type
CH-UC = (f : 𝟚ᴺ → ℕ) → Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

UC : Type
UC = (f : 𝟚ᴺ → ℕ) → ∥ (Σ \(n : ℕ) → (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β) ∥

\end{code}

-------------------------------------------
    The two formulations are equivalent
-------------------------------------------

One direction is easy.

\begin{code}

Theorem[CH-UC→UC] : CH-UC → UC
Theorem[CH-UC→UC] chuc f = ∣ chuc f ∣

\end{code}

For the converse, we need the following:

MainLemma. For any type family A : ℕ → Type such that

    (1) A(n) is a proposition for all n,

    (2) if A(n) then A(m) is decidable for all i < n,

  we have

      ∥ Σ(n:ℕ).A(n) ∥ → Σ(n:ℕ).A(n).

Proof sketch: Given n with A(n), we can find the minimal k with A(k),
using the decidability of A(m) for m < n. Since “having a minimal k
with A(k)” is a proposition (proved using function extensionality),
the elimination rule of ∥-∥ gives the desired result.

\begin{code}

MainLemma : (A : ℕ → Type)
          → ((n : ℕ) → isProp (A n))
          → ((n : ℕ) → A n → (m : ℕ) → m ≤ n → A m + ¬ (A m))
          → ∥ (Σ \(n : ℕ) → A n) ∥ → Σ \(n : ℕ) → A n
MainLemma A pA dA h = claim₂ (claim₁ h)
 where
  claim₀ : (Σ \(n : ℕ) → A n) → Σ-min \(k : ℕ) → A k
  claim₀ (n , an) = Lemma[Σ-min] A n an (dA n an)
  claim₁ : ∥ (Σ \(n : ℕ) → A n) ∥ → Σ-min \(k : ℕ) → A k
  claim₁ = ∥∥-elim (Σ-min-isProp A pA) claim₀
  claim₂ : (Σ-min \(k : ℕ) → A k) → Σ \(n : ℕ) → A n
  claim₂ (k , ak , _) = k , ak

\end{code}

Since Uc(f) : ℕ → Type, defined by

  Uc(f,n) = (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

satisfies (1) and (2), with the aid of function extensionality, the
two formulations of the uniform-continuity principle are equivalent.

\begin{code}

Uc : (𝟚ᴺ → ℕ) → ℕ → Type
Uc f n = (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β

Uc-isProp : (f : 𝟚ᴺ → ℕ)
          → (n : ℕ) → isProp (Uc f n)
Uc-isProp f n p q = funext (λ α → funext (λ β → funext (λ en → ℕ-isSet (p α β en) (q α β en))))

Uc-≤-decidable : (f : 𝟚ᴺ → ℕ)
               → (n : ℕ) → Uc f n → (m : ℕ) → m ≤ n → Uc f m + ¬ (Uc f m)
Uc-≤-decidable f  0       u0  _ _ = inl (λ α β _ → u0 α β ≡[zero])
Uc-≤-decidable f (succ n) usn m r = case c₀ c₁ (Lemma[n≤m+1→n≤m∨n≡m+1] r)
 where
  c₀ : m ≤ n → Uc f m + ¬ (Uc f m)
  c₀ r' = case sc₀ sc₁ ds
   where
    ds : ((s : 𝟚^ n) → f (s * 0ʷ) ≡ f (s * 1ʷ)) + ¬ ((s : 𝟚^ n) → f (s * 0ʷ) ≡ f (s * 1ʷ))
    ds = Lemma[𝟚^-dec] n (λ _ → ℕ-discrete)
    sc₀ : ((s : 𝟚^ n) → f (s * 0ʷ) ≡ f (s * 1ʷ)) → Uc f m + ¬ (Uc f m)
    sc₀ ψ = Uc-≤-decidable f n un m r'
     where
      un : (α β : 𝟚ᴺ) → α ≡[ n ] β → f α ≡ f β
      un α β en = case d₀ d₁ 𝟚-discrete
       where
        d₀ : α n ≡ β n → f α ≡ f β
        d₀ e = usn α β (≡[succ]' en e)
        d₁ : α n ≢ β n → f α ≡ f β
        d₁ g = case sd₀ sd₁ 𝟚-discrete
         where
          s : 𝟚^ n
          s = take n α
          sd₀ : α n ≡ 𝟎 → f α ≡ f β
          sd₀ eαn = trans claim₁ (trans (ψ s) (sym claim₃))
           where
            eβn : β n ≡ 𝟏
            eβn = Lemma[b≢0→b≡1] (λ e → g (trans eαn (sym e)))
            claim₀ : α ≡[ succ n ] (s * 0ʷ)
            claim₀ = ≡[succ]' (Lemma[*-take-≡[]] n) (trans eαn (Lemma[*-take-0] n))
            claim₁ : f α ≡ f (s * 0ʷ)
            claim₁ = usn α (s * 0ʷ) claim₀
            claim₂ : β ≡[ succ n ] (s * 1ʷ)
            claim₂ = ≡[succ]' (Lemma[≡[]-*-take-≡[]] en) (trans eβn (Lemma[*-take-0] n))
            claim₃ : f β ≡ f (s * 1ʷ)
            claim₃ = usn β (s * 1ʷ) claim₂
          sd₁ : α n ≢ 𝟎 → f α ≡ f β
          sd₁ fαn = trans claim₁ (trans (sym (ψ s)) (sym claim₃))
           where
            eαn : α n ≡ 𝟏
            eαn = Lemma[b≢0→b≡1] fαn
            eβn : β n ≡ 𝟎
            eβn = Lemma[b≢1→b≡0] (λ e → g (trans eαn (sym e)))
            claim₀ : α ≡[ succ n ] (s * 1ʷ)
            claim₀ = ≡[succ]' (Lemma[*-take-≡[]] n) (trans eαn (Lemma[*-take-0] n))
            claim₁ : f α ≡ f (s * 1ʷ)
            claim₁ = usn α (s * 1ʷ) claim₀
            claim₂ : β ≡[ succ n ] (s * 0ʷ)
            claim₂ = ≡[succ]' (Lemma[≡[]-*-take-≡[]] en) (trans eβn (Lemma[*-take-0] n))
            claim₃ : f β ≡ f (s * 0ʷ)
            claim₃ = usn β (s * 0ʷ) claim₂
    sc₁ : ¬ ((s : 𝟚^ n) → f (s * 0ʷ) ≡ f (s * 1ʷ)) → Uc f m + ¬ (Uc f m)
    sc₁ φ = inr goal
     where
      claim : (s : 𝟚^ n) → (s * 0ʷ) ≡[ m ] (s * 1ʷ)
      claim s = Lemma[≡[]-≤] (Lemma[*-≡[]] s) r'
      goal : ¬ ((α β : 𝟚ᴺ) → α ≡[ m ] β → f α ≡ f β)
      goal um = φ (λ s → um (s * 0ʷ) (s * 1ʷ) (claim s))
  c₁ : m ≡ succ n → Uc f m + ¬ (Uc f m)
  c₁ e = inl (transport (Uc f) (sym e) usn)

Theorem[UC→CH-UC] : UC → CH-UC
Theorem[UC→CH-UC] uc f = MainLemma (Uc f) (Uc-isProp f) (Uc-≤-decidable f) (uc f)

\end{code}
