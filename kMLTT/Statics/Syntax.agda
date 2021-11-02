{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Syntax where

open import Level renaming (suc to succ)

open import Lib
open import LibNonEmpty public

record HasL {i} (A : Set i) : Set i where
  field
    L : A → ℕ → ℕ

open HasL {{...}} public

record HasTr {i} (A : Set i) : Set i where
  infixl 3.5 _∥_
  field
    _∥_ : A → ℕ → A

open HasTr {{...}} public

record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 8 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

infixl 6 _$_
infixl 8 _[|_]

mutual
  Typ = Exp

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

  infixl 3 _∘_
  infixl 5 _；_
  data Substs : Set where
    -- identity
    I    : Substs
    -- weakening
    p    : Substs → Substs
    -- composition
    _∘_  : Substs → Substs → Substs
    -- extension
    _,_  : Substs → Exp → Substs
    -- modal transformation (MoT)
    _；_ : Substs → ℕ → Substs

-- standard contexts
Ctx : Set
Ctx = List Typ

-- context stacks
Ctxs : Set
Ctxs = List⁺ Ctx

-- cons the topmost context
infixr 5 _∺_
_∺_ : Typ → Ctxs → Ctxs
T ∺ (Ψ ∷ Ψs) = (T ∷ Ψ) ∷ Ψs

instance
  ExpMonotone : Monotone Exp Substs
  ExpMonotone = record { _[_] = sub }

-- one step weakening
wk : Substs
wk = p I

-- quick helpers
infixr 5 _⟶_
_⟶_ : Typ → Typ → Typ
S ⟶ T = Π S (T [ wk ])

_[|_] : Exp → Exp → Exp
t [| s ] = t [ I , s ]

q : Substs → Substs
q σ = (σ ∘ p I) , v 0

-- L and truncation for syntactic substitutions
S-L : Substs → ℕ → ℕ
S-L σ 0              = 0
S-L I (suc n)        = suc n
S-L (p σ) (suc n)    = S-L σ (suc n)
S-L (σ , t) (suc n)  = S-L σ (suc n)
S-L (σ ； m) (suc n) = m + S-L σ n
S-L (σ ∘ δ) (suc n)  = S-L δ (S-L σ (suc n))

instance
  SubstsHasL : HasL Substs
  SubstsHasL = record { L = S-L }

S-Tr : Substs → ℕ → Substs
S-Tr σ 0              = σ
S-Tr I (suc n)        = I
S-Tr (p σ) (suc n)    = S-Tr σ (suc n)
S-Tr (σ , t) (suc n)  = S-Tr σ (suc n)
S-Tr (σ ； m) (suc n) = S-Tr σ n
S-Tr (σ ∘ δ) (suc n)  = S-Tr σ (suc n) ∘ S-Tr δ (L σ (suc n))

instance
  SubstsHasTr : HasTr Substs
  SubstsHasTr = record { _∥_ = S-Tr }

-- neutral and normal forms
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
  w w′ w″ : Nf

-- conversion from neutrals/normals to terms
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

-- dependent context lookup
infix 2 _∶_∈!_
data _∶_∈!_ : ℕ → Typ → Ctxs → Set where
  here  : 0 ∶ T [ wk ] ∈! T ∺ Γ
  there : ∀ {n T S} → n ∶ T ∈! Γ → suc n ∶ T [ wk ] ∈! S ∺ Γ
