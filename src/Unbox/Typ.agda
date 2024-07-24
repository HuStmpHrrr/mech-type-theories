{-# OPTIONS --without-K --safe #-}

module Unbox.Typ where

open import Lib
open import LibNonEmpty

infixr 5 _⟶_

-- types
data Typ : Set where
  B   : Typ
  _⟶_ : Typ → Typ → Typ
  □   : Typ → Typ

Ctx : Set
Ctx = List Typ

Ctxs : Set
Ctxs = List⁺ Ctx

variable
  S T U      : Typ
  Γ Γ′ Γ″    : Ctx
  Δ Δ′ Δ″    : Ctx
  Γs Γs′ Γs″ : List Ctx
  Δs Δs′ Δs″ : List Ctx
  Ψ Ψ′ Ψ″ Ψ‴ : Ctxs
