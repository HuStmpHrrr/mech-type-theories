{-# OPTIONS --without-K --safe #-}

module Layered.Typ where

open import Data.List

open import Lib public

infixr 5 _⟶_

-- types
data Typ : Set where
  N   : Typ
  _⟶_ : Typ → Typ → Typ
  □   : Typ → Typ


Ctx : Set
Ctx = List Typ


variable
  S T U   : Typ
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx
  Ψ Ψ′ Ψ″ : Ctx
  Φ Φ′ Φ″ : Ctx

-- Layering predicates
----------------------

data core? : Typ → Set where
  N   : core? N
  _⟶_ : core? S → core? T → core? (S ⟶ T)


data type? : Typ → Set where
  N   : type? N
  _⟶_ : type? S → type? T → type? (S ⟶ T)
  □   : core? T → type? (□ T)


cores? : Ctx → Set
cores? = All core?

types? : Ctx → Set
types? = All type?

core-type : core? T → type? T
core-type N       = N
core-type (S ⟶ T) = core-type S ⟶ core-type T

cores-types : cores? Ψ → types? Ψ
cores-types = All′.map core-type
