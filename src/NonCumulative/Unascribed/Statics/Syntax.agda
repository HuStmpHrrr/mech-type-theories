{-# OPTIONS --without-K --safe #-}

-- This file defines the syntax of non-cumulative MLTT
module NonCumulative.Unascribed.Statics.Syntax where

open import Level renaming (suc to succ)

open import Lib
open import LibNonEmpty public

-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

infixl 4.2 _$_
infixl 4.5 _[|_∶_]

mutual
  -- Type is also an expression.
  Typ = Exp

  -- Definition of terms in MLTT
  data Exp : Set where
    -- type constructors
    N      : Typ
    Π      : Typ → Typ → Typ
    Liftt  : ℕ → Typ → Typ
    Se     : (i : ℕ) → Typ
    v      : (x : ℕ) → Exp
    -- natural numebrs
    ze     : Exp
    su     : Exp → Exp
    rec    : (T : Typ) (s r t : Exp) → Exp
    -- functions
    Λ      : Typ → Exp → Exp
    _$_    : Exp → Exp → Exp
    -- lifting of universe
    liftt  : ℕ → Exp → Exp
    unlift : Exp → Exp
    -- explicit substitutions
    sub    : Exp → Subst → Exp

  -- Definition of (unified) substitutions in MLTT
  infixl 3 _∘_
  data Subst : Set where
    -- identity
    I    : Subst
    -- one step weakening
    wk   : Subst
    -- composition
    _∘_  : Subst → Subst → Subst
    -- extension
    _,_∶_  : Subst → Exp → Typ → Subst

-- Individual contexts
Ctx : Set
Ctx = List Typ

lCtx : Set
lCtx = List (ℕ × Typ)

-- Exp is monotonic and transformed by substitutions
instance
  ExpMonotone : Monotone Exp Subst
  ExpMonotone = record { _[_] = sub }

-- quick helpers
----------------

-- Projection of substitutions
p : Subst → Subst
p σ = wk ∘ σ

-- Nondependent functions
infixr 5 _⟶_
_⟶_ : Typ → Typ → Typ
S ⟶ T = Π S (T [ wk ])

-- Substitute the first open variable of t with s
_[|_∶_] : Exp → Exp → Typ → Exp
t [| s ∶ S ] = t [ I , s ∶ S ]

-- Weakening of substitutions by one variable
q : Typ -> Subst → Subst
q T σ = (σ ∘ wk) , v 0 ∶ T


-- Neutral and normal forms
--
-- Here we define β-η normal form
mutual
  data Ne : Set where
    v      : (x : ℕ) → Ne
    rec    : (T : Nf) (z s : Nf) → Ne → Ne
    _$_    : Ne → (n : Nf) → Ne
    unlift : Ne → Ne

  data Nf : Set where
    ne    : (u : Ne) → Nf
    N     : Nf
    Π     : Nf → Nf → Nf
    Liftt : ℕ → Nf → Nf
    Se    : (i : ℕ) → Nf
    ze    : Nf
    su    : Nf → Nf
    Λ     : Nf → Nf → Nf
    liftt : ℕ → Nf → Nf

variable
  S S′ S″ : Typ
  T T′ T″ : Typ
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Subst
  τ τ′ τ″ : Subst
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
  Ne⇒Exp (unlift u)    = unlift (Ne⇒Exp u)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)      = Ne⇒Exp u
  Nf⇒Exp ze          = ze
  Nf⇒Exp (su w)      = su (Nf⇒Exp w)
  Nf⇒Exp (Λ S w)     = Λ (Nf⇒Exp S) (Nf⇒Exp w)
  Nf⇒Exp (liftt n w) = liftt n (Nf⇒Exp w)
  Nf⇒Exp N           = N
  Nf⇒Exp (Π S T)     = Π (Nf⇒Exp S) (Nf⇒Exp T)
  Nf⇒Exp (Liftt n W) = Liftt n (Nf⇒Exp W)
  Nf⇒Exp (Se i)      = Se i

-- Dependent context lookup
infix 2 _∶_∈!_
data _∶_∈!_ : ℕ → Typ → Ctx → Set where
  here  : ∀ {Γ} → 0 ∶ T [ wk ] ∈! T ∷ Γ
  there : ∀ {n T S Γ} → n ∶ T ∈! Γ → suc n ∶ T [ wk ] ∈! S ∷ Γ