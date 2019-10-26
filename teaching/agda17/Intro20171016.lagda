

      ---------------------------------------------------
             EXECUTING PROOFS AS COMPUTER PROGRAMS
      ---------------------------------------------------

                         Chuangjie Xu

          Monday 14-16, HS B 252, start 16th Oct 2017

          http://www.math.lmu.de/~xu/teaching/agda17/


The objective of this course is to encourage you to make use of proof
assistants in your study of mathematics.  In specific, I will use the
Agda proof assistant for demonstration.


--------------------------
    PLAN of the course
--------------------------

1. Introduction

   (1) Computer assisted formalisation of mathematics

   (2) Martin-Löf type theory & "Proofs as Programs"

   (3) Introduction to the Agda proof assistant

2. Continuity in type theory

   I will present some results about continuity from my PhD thesis to show

   (1) the subtle problem of expressing "existence" in type theory, and

   (2) how to make axioms computational.

3. The Fan theorem

   Dr. Josef Berger will be lecturing a course on the Fan theorem

       Wednesday 14-16, B040, start 18 October

   I plan to attend his course and formalise some results of the Fan
   theorem together with you.

4. Real numbers

   I also plan to develop a basic fragment of the theory of real numbers
   in Agda, following the method of Prof. Helmut Schwichtenberg in his
   previous course on constructive analysis.



------------------
    Literature
------------------

1. Agda and type theory

   (1) The Agda wiki:  http://wiki.portal.chalmers.se/agda/pmwiki.php

   (2) Dependently Typed Programming in Agda.  U. Norell and J. Chapman

   (3) Learn you an Agda  (if you already know e.g. "some" Haskell)

   (4) Chapter 1 of the HoTT book.  Available at

           https://homotopytypetheory.org/book/

2. Continuity and the Fan theorem

   (1) A continuous computational interpretation of type theories.
       Chuangjie Xu, PhD thesis, 2015.  Available at

           http://www.mathematik.uni-muenchen.de/~xu/

   (2) The webpage of Dr. Berger's course

           http://www.math.lmu.de/~jberger/fan.php

3. Analysis

   Constructive analysis with witnesses.  Helmut Schwichtenberg,
   lecture notes, wintersemester 2016/17, LMU.  Available at

      http://www.mathematik.uni-muenchen.de/~schwicht/seminars/semws16/index.php







------------------
    MOTIVATION
------------------

1. Correctness

   (1) To remove deep errors

       E.g. In 2013, Voevodsky discovered a fundamental error in an important
       and widely studied paper of him and Kapranov published in 1989.

   (2) To handle enormous proofs with large computer calculations
   
       E.g. The odd-order theorem was proved originally by Feit and
       Thompson in a 255-page-long paper.

       E.g. The four colour theorem: Appel and Haken’s proof took 139
       pages and depends on long computer calculations.

       E.g. The Kepler conjecture: The proof by Hales consisted of 250
       pages and 3 gigabytes of computer programs and data.

   (3) People trust machines more than human beings?
   
       In some areas of theoretical computer science, it has become a
       standard to publish papers together with computer-verified proofs.

2. Beyond correctness

   (1) Proof automation
   
       Some proof assistants can automatically search for new proofs
       (via various proof tactics), e.g. by testing a number of case
       distinctions.

   (2) Computation extraction
   
       Some proof assistants allow users to extract certified computer
       programs from proofs.

   (3) Other practical features

       User tactics, typeset documents generation, library management, ...

   (4) New mathematics
   
       Voevodsky’s univalent foundations and homotopy type theory

3. My personal experience

   Reviewers gave positive feedback to the Agda proofs for my published papers.
   
   My Agda implementation/formalisation of my PhD. thesis interested
   the examiners and convinced them all my proofs are correct.

   Formalising math is still difficult and time-consuming.

   Correctly formulating mathematics in e.g. type theory is not easy.



-------------------
    Examination
-------------------

Oral exam (+ simple proofs in Agda)



\begin{code}

Type = Set

\end{code}

------------------------------
    Martin-Löf type theory
------------------------------

MLTT is based on the well-known slogan "propositions as types". The
idea is that formulas in intuitionistic logic are interpreted as types
as follows

                Propositions  │  Types
           ───────────────────┼───────────────────
                           ⊥  │  𝟘
                           ⊤  │  𝟙
                       P → Q  │  P → Q
                       P ∧ Q  │  P × Q
                       P ∨ Q  │  P + Q
                 ∀(x:A).P(x)  │  Π(x:A).P(x)
                 ∃(x:A).P(x)  │  Σ(x:A).P(x)
            Leibniz equality  │  identity types
        inductive predicates  │  (dependent) W-types
      coinductive predicates  │  (dependent) M-types

and proofs as terms, known as the Curry-Howard interpretation.
                                  ̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅

There are numerous versions and variants of MLTT. Here we study only
the intensional MLTT because of its computational features:
                                    ̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅
 * Type-checking (or proof-checking) is decidable.

 * Any closed term (no free variables) has a canonical form.

 * Normalisation always terminate.

MLTT can be regarded as a dependently typed programming language.  The
design of a number of proof assistants and programming languages is
based on certain variants of MLTT, including Agda, Coq, Lean and Nuprl.


A type in type theory is usually given by rules of
                                          ̅̅̅̅
 ■ formation    - how a type is formed

 ■ introduction - constructors (also called the closure axiom)

 ■ elimination  - destructors (also called the least-fixed-point axiom)

 ■ computation  - how a term is reduced

Examples given by rules (on blackboard): Π-types, Σ-types.

Π-types are primitive in Agda, and Π(x:A).P(x) is written as (x : A) → P x.
̅̅̅̅̅̅
Σ-types are defined inductively, using e.g. data declaration.
̅̅̅̅̅̅
\begin{code}

infixr 5 _,_

data Σ {A : Type} (P : A → Type) : Type where
 _,_ : (a : A) (b : P a) → Σ P

pr₁ : {A : Type} {P : A → Type}
    → (Σ \(x : A) → P x) → A
pr₁ (a , b) = a

pr₂ : {A : Type} {P : A → Type}
    → (w : Σ P) → P (pr₁ w)
pr₂ (a , b) = b

\end{code}

Binary products are a special case of Σ-types.
̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅
\begin{code}

infixr 10 _×_

_×_ : Type → Type → Type
A × B = Σ \(_ : A) → B

\end{code}

Coproducts can also be defined using data declaration.
̅̅̅̅̅̅̅̅̅̅
\begin{code}

data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B

case : {A B C : Type} → (A → C) → (B → C) → A + B → C
case f g (inl a) = f a
case f g (inr b) = g b

\end{code}

Natural numbers
̅̅̅̅̅̅̅̅̅̅̅̅̅̅
\begin{code}

data ℕ : Type where
 zero : ℕ
 succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data _≤_ : ℕ → ℕ → Type where
 ≤-zero : {n : ℕ} → 0 ≤ n
 ≤-succ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

\end{code}

Agda proofs are already executable programs.
                        ̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅̅
For instance, once we prove that every list has a reversed list, we
can run the proof to reverse given lists.

\begin{code}

infixr 20 _::_
infixl 10 _++_

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

[_] : {A : Type} → A → List A
[ a ] = a :: []

_++_ : {A : Type} → List A → List A → List A
[] ++ v = v
(a :: u) ++ v = a :: (u ++ v)

data reversed {A : Type} : List A → List A → Type where
 r-nil  : reversed [] []
 r-cons : {u v : List A} {a : A} → reversed u v → reversed (a :: u) (v ++ [ a ])

Thm[ListRev] : {A : Type}
             → (u : List A) → Σ \(v : List A) → reversed u v
Thm[ListRev] [] = [] , r-nil
Thm[ListRev] (a :: u) = v ++ [ a ] , r-cons p
 where
  v : List _
  v = pr₁ (Thm[ListRev] u)
  p : reversed u v
  p = pr₂ (Thm[ListRev] u)

exL : List ℕ
exL = 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: []

revL : List ℕ
revL = pr₁ (Thm[ListRev] exL)
-- Evaluate it by typing "Ctrl-c Ctrl-n" and then entering "revL", and get
--
--   7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: 0 :: []

\end{code}
