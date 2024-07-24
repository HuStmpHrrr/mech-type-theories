{-# OPTIONS --without-K --safe #-}

-- This file defines the syntax of Mint
module Mint.Statics.Syntax where

open import Level renaming (suc to succ)

open import Lib
open import LibNonEmpty public

-- O computes the truncation offset of A when truncated by a length
record HasO {i} (A : Set i) : Set i where
  field
    O : A → ℕ → ℕ

open HasO {{...}} public

-- _∥_ computes the truncation of A by a length
record HasTr {i} (A : Set i) : Set i where
  infixl 5 _∥_
  field
    _∥_ : A → ℕ → A

open HasTr {{...}} public

-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

infixl 4.2 _$_
infixl 4.5 _[|_]

mutual
  -- Type is also an expression.
  Typ = Exp

  -- Definition of terms in Mint
  -- Some notable differences with syntax in the paper are:
  --   * We use N instead of Nat for the type of natural numbers.
  --   * We use Se (shortened Set) instead of Ty for the universes.
  --   * We use rec instead of elim for the natural number eliminator.
  --   * We use sub instead of _[_] for the substitution application.
  data Exp : Set where
    -- type constructors
    N     : Typ
    Π     : Typ → Typ → Typ
    Se    : (i : ℕ) → Typ
    □     : Typ → Typ
    v     : (x : ℕ) → Exp
    -- natural numebrs
    ze    : Exp
    su    : Exp → Exp
    rec   : (T : Typ) (s r t : Exp) → Exp
    -- functions
    Λ     : Exp → Exp
    _$_   : Exp → Exp → Exp
    -- modal terms
    box   : Exp → Exp
    unbox : ℕ → Exp → Exp
    -- explicit substitutions
    sub   : Exp → Substs → Exp

  -- Definition of (unified) substitutions in Mint
  infixl 3 _∘_
  infixl 5 _；_
  data Substs : Set where
    -- identity
    I    : Substs
    -- one step weakening
    wk   : Substs
    -- composition
    _∘_  : Substs → Substs → Substs
    -- extension
    _,_  : Substs → Exp → Substs
    -- modal transformation (MoT)
    _；_ : Substs → ℕ → Substs

-- Individual contexts
Ctx : Set
Ctx = List Typ

-- Context stacks are an nonempty list of contexts.
Ctxs : Set
Ctxs = List⁺ Ctx

-- Cons the topmost context
infixr 5 _∺_
_∺_ : Typ → Ctxs → Ctxs
T ∺ (Ψ ∷ Ψs) = (T ∷ Ψ) ∷ Ψs


-- Concatenate the topmost context
infixr 4.5 _++⁻_

_++⁻_ : List Typ → Ctxs → Ctxs
_++⁻_ Ψ (Ψ′ ∷ Γ) = (Ψ ++ Ψ′) ∷ Γ

-- Exp is monotonic and transformed by substitutions
instance
  ExpMonotone : Monotone Exp Substs
  ExpMonotone = record { _[_] = sub }

-- quick helpers
----------------

-- Projection of substitutions
p : Substs → Substs
p σ = wk ∘ σ

-- Nondependent functions
infixr 5 _⟶_
_⟶_ : Typ → Typ → Typ
S ⟶ T = Π S (T [ wk ])

-- Substitute the first open variable of t with s
_[|_] : Exp → Exp → Exp
t [| s ] = t [ I , s ]

-- Weakening of substitutions by one variable
q : Substs → Substs
q σ = (σ ∘ wk) , v 0

-- O (truncation offset) and truncation for syntactic substitutions
S-O : Substs → ℕ → ℕ
S-O σ 0              = 0
S-O I (suc n)        = suc n
S-O wk (suc n)       = suc n
S-O (σ , t) (suc n)  = S-O σ (suc n)
S-O (σ ； m) (suc n) = m + S-O σ n
S-O (σ ∘ δ) (suc n)  = S-O δ (S-O σ (suc n))

instance
  SubstsHasO : HasO Substs
  SubstsHasO = record { O = S-O }

S-Tr : Substs → ℕ → Substs
S-Tr σ 0              = σ
S-Tr I (suc n)        = I
S-Tr wk (suc n)       = I
S-Tr (σ , t) (suc n)  = S-Tr σ (suc n)
S-Tr (σ ； m) (suc n) = S-Tr σ n
S-Tr (σ ∘ δ) (suc n)  = S-Tr σ (suc n) ∘ S-Tr δ (O σ (suc n))

instance
  SubstsHasTr : HasTr Substs
  SubstsHasTr = record { _∥_ = S-Tr }

-- Neutral and normal forms
--
-- Here we define β-η normal form
mutual
  data Ne : Set where
    v     : (x : ℕ) → Ne
    rec   : (T : Nf) (z s : Nf) → Ne → Ne
    _$_   : Ne → (n : Nf) → Ne
    unbox : ℕ → Ne → Ne

  data Nf : Set where
    ne  : (u : Ne) → Nf
    N   : Nf
    Π   : Nf → Nf → Nf
    Se  : (i : ℕ) → Nf
    □   : Nf → Nf
    ze  : Nf
    su  : Nf → Nf
    Λ   : Nf → Nf
    box : Nf → Nf

variable
  S S′ S″ : Typ
  T T′ T″ : Typ
  Ψ Ψ′ Ψ″ : Ctx
  Ψs Ψs′  : List Ctx
  Γ Γ′ Γ″ : Ctxs
  Δ Δ′ Δ″ : Ctxs
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Substs
  τ τ′ τ″ : Substs
  u u′ u″ : Ne
  V V′ V″ : Ne
  w w′ w″ : Nf
  W W′ W″ : Nf

-- Conversion from neutrals/normals to terms
mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (rec T z s u) = rec (Nf⇒Exp T) (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n
  Ne⇒Exp (unbox n u)   = unbox n (Ne⇒Exp u)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)  = Ne⇒Exp u
  Nf⇒Exp ze      = ze
  Nf⇒Exp (su w)  = su (Nf⇒Exp w)
  Nf⇒Exp (Λ w)   = Λ (Nf⇒Exp w)
  Nf⇒Exp N       = N
  Nf⇒Exp (Π S T) = Π (Nf⇒Exp S) (Nf⇒Exp T)
  Nf⇒Exp (Se i)  = Se i
  Nf⇒Exp (□ w)   = □ (Nf⇒Exp w)
  Nf⇒Exp (box w) = box (Nf⇒Exp w)

-- Dependent context lookup
infix 2 _∶_∈!_
data _∶_∈!_ : ℕ → Typ → Ctxs → Set where
  here  : 0 ∶ T [ wk ] ∈! T ∺ Γ
  there : ∀ {n T S} → n ∶ T ∈! Γ → suc n ∶ T [ wk ] ∈! S ∺ Γ
