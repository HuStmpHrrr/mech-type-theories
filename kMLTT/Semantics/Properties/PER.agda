{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.PER (fext : Extensionality 0ℓ 0ℓ) where

open import Data.Nat.Properties as ℕₚ
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib

open import kMLTT.Statics.Syntax
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
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


𝕌-irrel : ∀ i (A≈B A≈B′ : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A≈B′
𝕌-irrel i (ne _) (ne _) a≈b          = a≈b
𝕌-irrel i N N a≈b                    = a≈b
𝕌-irrel i (U′ j<i) (U j<i′ eq) a≈b
  rewrite ≡-irrelevant eq refl
        | ≤-irrelevant j<i j<i′      = a≈b
𝕌-irrel i (□ A≈A′) (□ A≈A′₁) a≈b n κ = record
  { ua    = ua
  ; ub    = ub
  ; ↘ua   = ↘ua
  ; ↘ub   = ↘ub
  ; ua≈ub = 𝕌-irrel i (A≈A′ κ) (A≈A′₁ κ) ua≈ub
  }
  where open □̂ (a≈b n κ)
𝕌-irrel i (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈b
  with 𝕌-irrel i (iA′ κ) (iA κ) a≈b
...  | a≈b′
     with RT κ a≈b′ | RT′ κ a≈b | f≈f′ κ a≈b′
...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
        | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
        | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
        rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
              | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁  = record
  { fa     = _
  ; fa′    = _
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = 𝕌-irrel i T≈T′ T≈T′₁ fa≈fa′
  ; nat    = nat
  ; nat′   = nat′
  }


private
  module Sym i (rc : ∀ {j A′ B′} → j < i → A′ ≈ B′ ∈ 𝕌 j → B′ ≈ A′ ∈ 𝕌 j) where

    mutual

      𝕌-sym : A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
      𝕌-sym (ne C≈C′)                           = ne (Bot-sym C≈C′)
      𝕌-sym N                                   = N
      𝕌-sym (U′ j<i)                            = U′ j<i
      𝕌-sym (□ A≈A′)                            = □ λ κ → 𝕌-sym (A≈A′ κ)
      𝕌-sym (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (λ κ → 𝕌-sym (iA κ)) helper
        where helper : ∀ κ → a ≈ a′ ∈ El i (𝕌-sym (iA κ)) → ΠRT T′ (ρ′ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 i)
              helper κ a≈a′ = record
                { ⟦T⟧   = ⟦T′⟧
                ; ⟦T′⟧  = ⟦T⟧
                ; ↘⟦T⟧  = ↘⟦T′⟧
                ; ↘⟦T′⟧ = ↘⟦T⟧
                ; T≈T′  = 𝕌-sym T≈T′
                }
                where open ΠRT (RT κ (El-sym (𝕌-sym (iA κ)) (iA κ) a≈a′))

      El-sym : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
      El-sym (ne _) (ne _) (ne c≈c′)    = ne (Bot-sym c≈c′)
      El-sym N N a≈b                    = Nat-sym a≈b
      El-sym (U′ j<i) (U j<i′ eq) a≈b
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′   = {!!}
      El-sym (□ A≈A′) (□ A≈A′₁) a≈b n κ = record
        { ua    = ub
        ; ub    = ua
        ; ↘ua   = ↘ub
        ; ↘ub   = ↘ua
        ; ua≈ub = El-sym (A≈A′ κ) (A≈A′₁ κ) ua≈ub
        }
        where open □̂ (a≈b n κ)
      El-sym (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈b
        with El-sym (iA′ κ) (iA κ) a≈b
      ...  | a≈b′
           with RT κ a≈b′ | RT′ κ a≈b | f≈f′ κ a≈b′
      ... | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
          | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁
                | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁    = record
        { fa     = _
        ; fa′    = _
        ; ↘fa    = ↘fa′
        ; ↘fa′   = ↘fa
        ; fa≈fa′ = El-sym T≈T′₁ T≈T′ fa≈fa′
        ; nat    = nat′
        ; nat′   = nat
        }
