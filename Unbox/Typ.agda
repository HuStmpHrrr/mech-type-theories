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

Env : Set
Env = List Typ

Envs : Set
Envs = List⁺ Env

variable
  S T U      : Typ
  Γ Γ′ Γ″    : Env
  Δ Δ′ Δ″    : Env
  Γs Γs′ Γs″ : List Env
  Δs Δs′ Δs″ : List Env
  Ψ Ψ′ Ψ″ Ψ‴ : Envs
