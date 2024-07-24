{-# OPTIONS --without-K --safe #-}

module CLayered.Typ where

open import Data.List

open import Lib hiding (lookup) public

infixr 5 _⟶_

mutual

  -- types
  data Typ : Set where
    N   : Typ
    _⟶_ : Typ → Typ → Typ
    □   : LCtx → Typ → Typ

  LCtx : Set
  LCtx = List Typ


GCtx : Set
GCtx = List (LCtx × Typ)


variable
  S T U    : Typ
  S′ T′ U′ : Typ
  Γ Γ′ Γ″  : LCtx
  Δ Δ′ Δ″  : LCtx
  Ψ Ψ′ Ψ″  : GCtx
  Φ Φ′ Φ″  : GCtx


data Layer : Set where
  zer one : Layer

variable
  i : Layer


-- Layering predicates
----------------------

mutual

  data wf? : Layer → Typ → Set where
    N   : wf? i N
    _⟶_ : wf? i S → wf? i T → wf? i (S ⟶ T)
    □   : wfs? zer Γ → wf? zer T → wf? one (□ Γ T)

  wfs? : Layer → LCtx → Set
  wfs? i Γ = All (wf? i) Γ


gwf? : LCtx × Typ → Set
gwf? (Γ , T) = wfs? zer Γ × wf? zer T

gwfs? : GCtx → Set
gwfs? Ψ = All gwf? Ψ

core? : Typ → Set
core? = wf? zer

type? : Typ → Set
type? = wf? one

cores? : LCtx → Set
cores? = wfs? zer

types? : LCtx → Set
types? = wfs? one

wf-lift : core? T → type? T
wf-lift N       = N
wf-lift (S ⟶ T) = wf-lift S ⟶ wf-lift T

wfs-lift : cores? Γ → types? Γ
wfs-lift = All′.map wf-lift

wf-lift′ : wf? zer T → wf? i T
wf-lift′ N       = N
wf-lift′ (S ⟶ T) = wf-lift′ S ⟶ wf-lift′ T

wfs-lift′ : wfs? zer Γ → wfs? i Γ
wfs-lift′ = All′.map wf-lift′
