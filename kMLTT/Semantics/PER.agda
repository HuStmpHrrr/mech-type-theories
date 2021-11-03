{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.PER where

open import Lib
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Readback

Bot : Dn → Dn → Set
Bot c c′ = ∀ ns (κ : UnMoT) → ∃ λ u → Re ns - c [ κ ] ↘ u × Re ns - c′ [ κ ] ↘ u

Top : Df → Df → Set
Top d d′ = ∀ ns (κ : UnMoT) → ∃ λ w → Rf ns - d [ κ ] ↘ w × Rf ns - d′ [ κ ] ↘ w
