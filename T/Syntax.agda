{-# OPTIONS --without-K --safe #-}

module T.Syntax where

open import Lib

infixr 5 _⟶_

-- types
data Typ : Set where
  N   : Typ
  _⟶_ : Typ → Typ → Typ

Env : Set
Env = List Typ

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Env
  Δ Δ′ Δ″ : Env

data Exp : Set
data Subst : Set

infixl 10 _$_
infixl 8 _[_]
data Exp where
  v    : (x : ℕ) → Exp
  ze   : Exp
  su   : Exp → Exp
  rec  : (z s t : Exp) → Exp
  Λ    : Exp → Exp
  _$_  : Exp → Exp → Exp
  _[_] : Exp → Subst → Exp

infixl 3 _∙_
data Subst where
  ↑   : Subst
  I   : Subst
  _∙_ : Subst → Subst → Subst
  _,_ : Subst → Exp → Subst

data Ne : Set
data Nf : Set

data Ne where
  v   : (x : ℕ) → Ne
  rec : (z s : Nf) → Ne → Ne
  _$_ : Ne → (n : Nf) → Ne

data Nf where
  ne : (u : Ne) → Nf
  ze : Nf
  su : Nf → Nf
  Λ  : Nf → Nf

pattern v′ x = ne (v x)

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Subst
  τ τ′ τ″ : Subst
  u u′ u″ : Ne
  w w′ w″ : Nf

data D : Set
data Dn : Set

Ctx : Set
Ctx = ℕ → D

data D where
  ze : D
  su : D → D
  Λ  : (t : Exp) → (ρ : Ctx) → D
  ne : Dn → D

data Dn where
  l   : (x : ℕ) → Dn
  rec : (z s : D) → Dn → Dn
  _$_ : Dn → (d : D) → Dn

infixl 10 _$′_
pattern l′ x = ne (l x)
pattern rec′ z s w = ne (rec z s w)
pattern _$′_ x y = ne (_$_ x y)

variable
  a b d f : D
  d′ d″ : D
  e e′ e″ : Dn
  ρ ρ′ ρ″ : Ctx

infixl 8 _↦_
_↦_ : Ctx → D → Ctx
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x

drop : Ctx → Ctx
drop ρ n = ρ (suc n)
