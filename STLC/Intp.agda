{-# OPTIONS --without-K --safe #-}

module STLC.Intp where

open import Lib
open import STLC.Statics

⟦_⟧T : Typ → Set
⟦ * ⟧T     = ⊤
⟦ S X T ⟧T = ⟦ S ⟧T × ⟦ T ⟧T
⟦ S ⟶ T ⟧T = ⟦ S ⟧T → ⟦ T ⟧T

⟦_⟧C : Ctx → Set
⟦ [] ⟧C    = ⊤
⟦ T ∷ Γ ⟧C = ⟦ T ⟧T × ⟦ Γ ⟧C

lookup : T ∈ Γ → ⟦ Γ ⟧C → ⟦ T ⟧T
lookup 0d ρ       = proj₁ ρ
lookup (1+ T∈Γ) ρ = lookup T∈Γ (proj₂ ρ)

⟦_⟧t : Trm Γ T → ⟦ Γ ⟧C → ⟦ T ⟧T
⟦ * ⟧t ρ      = tt
⟦ var x ⟧t ρ  = lookup x ρ
⟦ pr s t ⟧t ρ = ⟦ s ⟧t ρ , ⟦ t ⟧t ρ
⟦ π₁ t ⟧t ρ   = proj₁ (⟦ t ⟧t ρ)
⟦ π₂ t ⟧t ρ   = proj₂ (⟦ t ⟧t ρ)
⟦ t $ s ⟧t ρ  = ⟦ t ⟧t ρ (⟦ s ⟧t ρ)
⟦ Λ t ⟧t ρ    = λ z → ⟦ t ⟧t (z , ρ)
