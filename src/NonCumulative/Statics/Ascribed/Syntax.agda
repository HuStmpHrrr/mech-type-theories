{-# OPTIONS --without-K --safe #-}

-- This file defines the syntax of non-cumulative MLTT with universe levels ascribed
module NonCumulative.Statics.Ascribed.Syntax where

open import Level renaming (suc to succ)

open import Lib
open import LibNonEmpty public

-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

infix 4.1 _↙_
infixl 4.2 _$_
infixl 4.5 _[|_∶_]
infix 4 _,_∶_

mutual
  -- Type is also an expression.
  Typ = Exp

  -- Type ascribed with its universe level
  record lTyp : Set where
    inductive
    constructor
      _↙_

    field
      ty : Typ
      lv : ℕ

  -- Definition of terms in MLTT
  data Exp : Set where
    -- type constructors
    N      : Typ
    Π      : lTyp → lTyp → Typ
    Liftt  : ℕ → lTyp → Typ
    Se     : (i : ℕ) → Typ
    v      : (x : ℕ) → Exp
    -- natural numebrs
    ze     : Exp
    su     : Exp → Exp
    rec    : (T : lTyp) (s r t : Exp) → Exp
    -- functions
    Λ      : (S : lTyp) → Exp → Exp
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
    I     : Subst
    -- one step weakening
    wk    : Subst
    -- composition
    _∘_   : Subst → Subst → Subst
    -- extension
    _,_∶_ : Subst → Exp → lTyp → Subst

-- Individual contexts
Ctx : Set
Ctx = List lTyp


-- Exp is monotonic and transformed by substitutions
instance
  ExpMonotone : Monotone Exp Subst
  ExpMonotone = record { _[_] = sub }

  lTypMonotone : Monotone lTyp Subst
  lTypMonotone = record { _[_] = λ (T ↙ i) σ → T [ σ ] ↙ i }

-- quick helpers
----------------

-- Projection of substitutions
p : Subst → Subst
p σ = wk ∘ σ

-- Nondependent functions
infixr 5 _⟶_
_⟶_ : lTyp → lTyp → Typ
S ⟶ (T ↙ i) = Π S (T [ wk ] ↙ i)

-- Substitute the first open variable of t with s
_[|_∶_] : Exp → Exp → lTyp → Exp
t [| s ∶ S ] = t [ I , s ∶ S ]

-- Weakening of substitutions by one variable
q : lTyp → Subst → Subst
q T σ = (σ ∘ wk) , v 0 ∶ T


-- Neutral and normal forms
--
-- Here we define β-η normal form
mutual
  record lNf : Set where
    inductive
    constructor
      _↙_

    field
      ty : Nf
      lv : ℕ


  data Ne : Set where
    v      : (x : ℕ) → Ne
    rec    : (T : lNf) (z s : Nf) → Ne → Ne
    _$_    : Ne → (n : Nf) → Ne
    unlift : Ne → Ne

  data Nf : Set where
    ne    : (u : Ne) → Nf
    N     : Nf
    Π     : lNf → lNf → Nf
    Liftt : ℕ → lNf → Nf
    Se    : (i : ℕ) → Nf
    ze    : Nf
    su    : Nf → Nf
    Λ     : lNf → Nf → Nf
    liftt : ℕ → Nf → Nf

pattern N₀ = N ↙ 0

lSe : ℕ → lTyp
lSe i = Se i ↙ suc i

variable
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx
  S S′ S″ : Typ
  T T′ T″ : Typ
  lS lS′ lS″ : lTyp
  lT lT′ lT″ : lTyp
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
  lNf⇒lTyp : lNf → lTyp
  lNf⇒lTyp (W ↙ i) = Nf⇒Exp W ↙ i

  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (rec T z s u) = rec (lNf⇒lTyp T) (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n
  Ne⇒Exp (unlift u)    = unlift (Ne⇒Exp u)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)        = Ne⇒Exp u
  Nf⇒Exp ze            = ze
  Nf⇒Exp (su w)        = su (Nf⇒Exp w)
  Nf⇒Exp (Λ (W ↙ i) w) = Λ (Nf⇒Exp W ↙ i) (Nf⇒Exp w)
  Nf⇒Exp (liftt n w)   = liftt n (Nf⇒Exp w)
  Nf⇒Exp N             = N
  Nf⇒Exp (Π S T)       = Π (lNf⇒lTyp S) (lNf⇒lTyp T)
  Nf⇒Exp (Liftt n W)   = Liftt n (lNf⇒lTyp W)
  Nf⇒Exp (Se i)        = Se i

-- Dependent context lookup
infix 2 _∶[_]_∈!_
data _∶[_]_∈!_ : ℕ → ℕ → Typ → Ctx → Set where
  here  : ∀ {i Γ} → 0 ∶[ i ] S [ wk ] ∈! (S ↙ i) ∷ Γ
  there : ∀ {n i S S′ Γ} → n ∶[ i ] S ∈! Γ → suc n ∶[ i ] S [ wk ] ∈! S′ ∷ Γ
