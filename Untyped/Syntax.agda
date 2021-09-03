{-# OPTIONS --without-K --safe #-}

module Untyped.Syntax where

open import Lib

infixl 10 _$_
data Exp : Set where
  v   : (x : ℕ) → Exp
  Λ   : Exp → Exp
  _$_ : Exp → Exp → Exp

data Ne : Set
data Nf : Set

data Ne where
  v   : (x : ℕ) → Ne
  _$_ : Ne → (n : Nf) → Ne

data Nf where
  ne : (u : Ne) → Nf
  Λ  : Nf → Nf

pattern v′ x = ne (v x)

variable
  t t′ t″ : Exp
  r s : Exp
  u u′ u″ : Ne
  w w′ w″ : Nf

data D : Set
data Dn : Set

Ctx : Set
Ctx = ℕ → D

data D where
  Λ  : (t : Exp) → (ρ : Ctx) → D
  ne : Dn → D

data Dn where
  l   : (x : ℕ) → Dn
  _$_ : Dn → (d : D) → Dn

infixl 10 _$′_
pattern l′ x = ne (l x)
pattern _$′_ x y = ne (_$_ x y)

variable
  a b d f : D
  e e′ e″ : Dn
  ρ ρ′ ρ″ : Ctx


infixl 8 _↦_
_↦_ : Ctx → D → Ctx
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x
