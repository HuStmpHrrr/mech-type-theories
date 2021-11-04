{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.PER (fext : Extensionality 0ℓ 0ℓ) where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

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

Top-sym : d ≈ d′ ∈ Top → d′ ≈ d ∈ Top
Top-sym d≈d′ ns κ
  with d≈d′ ns κ
...  | w , ↘w , ↘w′ = w , ↘w′ , ↘w

Bot-sym : c ≈ c′ ∈ Bot → c′ ≈ c ∈ Bot
Bot-sym c≈c′ ns κ
  with c≈c′ ns κ
...  | u , ↘u , ↘u′ = u , ↘u′ , ↘u

Top-trans : d ≈ d′ ∈ Top → d′ ≈ d″ ∈ Top → d ≈ d″ ∈ Top
Top-trans d≈d′ d′≈d″ ns κ
  with d≈d′ ns κ | d′≈d″ ns κ
...  | w  , ↘w₁  , ↘w₂
     | w′ , ↘w′₁ , ↘w′₂
     rewrite Rf-det ↘w₂ ↘w′₁ = w′ , ↘w₁ , ↘w′₂

Bot-trans : c ≈ c′ ∈ Bot → c′ ≈ c″ ∈ Bot → c ≈ c″ ∈ Bot
Bot-trans c≈c′ c′≈c″ ns κ
  with c≈c′ ns κ | c′≈c″ ns κ
...  | u  , ↘u₁  , ↘u₂
     | u′ , ↘u′₁ , ↘u′₂
     rewrite Re-det ↘u₂ ↘u′₁ = u′ , ↘u₁ , ↘u′₂

Top-isPER : IsPartialEquivalence Top
Top-isPER = record
  { sym   = Top-sym
  ; trans = Top-trans
  }

Top-PER : PartialSetoid _ _
Top-PER = record
  { Carrier              = Df
  ; _≈_                  = Top
  ; isPartialEquivalence = Top-isPER
  }

module TopR = PS Top-PER


Bot-isPER : IsPartialEquivalence Bot
Bot-isPER = record
  { sym   = Bot-sym
  ; trans = Bot-trans
  }

Bot-PER : PartialSetoid _ _
Bot-PER = record
  { Carrier              = Dn
  ; _≈_                  = Bot
  ; isPartialEquivalence = Bot-isPER
  }

module BotR = PS Bot-PER

Nat-sym : a ≈ b ∈ Nat → b ≈ a ∈ Nat
Nat-sym ze        = ze
Nat-sym (su a≈b)  = su (Nat-sym a≈b)
Nat-sym (ne c≈c′) = ne (Bot-sym c≈c′)

Nat-trans : a ≈ a′ ∈ Nat → a′ ≈ a″ ∈ Nat → a ≈ a″ ∈ Nat
Nat-trans ze ze                = ze
Nat-trans (su a≈a′) (su a′≈a″) = su (Nat-trans a≈a′ a′≈a″)
Nat-trans (ne c≈c′) (ne c′≈c″) = ne (Bot-trans c≈c′ c′≈c″)

Nat-isPER : IsPartialEquivalence Nat
Nat-isPER = record
  { sym   = Nat-sym
  ; trans = Nat-trans
  }

Nat-PER : PartialSetoid _ _
Nat-PER = record
  { Carrier              = D
  ; _≈_                  = Nat
  ; isPartialEquivalence = Nat-isPER
  }

