{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.PER (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import kMLTT.Statics.Syntax
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.PER

open import kMLTT.Semantics.Properties.Domain fext

Top-mon : ∀ (κ : UnMoT) → d ≈ d′ ∈ Top → d [ κ ] ≈ d′ [ κ ] ∈ Top
Top-mon {d} {d′} κ d≈d′ ns κ′
  with d≈d′ ns (κ ø κ′)
...  | res
     rewrite Df-comp d κ κ′
           | Df-comp d′ κ κ′ = res

Bot-mon : ∀ (κ : UnMoT) → c ≈ c′ ∈ Bot → c [ κ ] ≈ c′ [ κ ] ∈ Bot
Bot-mon {c} {c′} κ c≈c′ ns κ′
  with c≈c′ ns (κ ø κ′)
...  | res
     rewrite Dn-comp c κ κ′
           | Dn-comp c′ κ κ′ = res
