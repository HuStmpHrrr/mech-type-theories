{-# OPTIONS --without-K --safe #-}

module STLC.Dynamics where

open import Lib

open import STLC.Statics

data _↦_ : ∀ {Γ T} → Trm Γ
