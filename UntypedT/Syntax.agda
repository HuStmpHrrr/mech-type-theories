{-# OPTIONS --without-K --safe #-}

module UntypedT.Syntax where

open import Lib

infixl 10 _$_
data Exp : Set where
  v   : (x : ℕ) → Exp
  ze  : Exp
  su  : Exp → Exp
  rec : (z s t : Exp) → Exp
  Λ   : Exp → Exp
  _$_ : Exp → Exp → Exp

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
  r s : Exp
  u u′ u″ : Ne
  w w′ w″ : Nf

data D : Set
data Dn : Set

Env : Set
Env = ℕ → D

data D where
  ze : D
  su : D → D
  Λ  : (t : Exp) → (ρ : Env) → D
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
  ρ ρ′ ρ″ : Env

infixl 8 _↦_
_↦_ : Env → D → Env
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x
