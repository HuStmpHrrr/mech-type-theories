{-# OPTIONS --without-K --safe #-}


-- Typing judgments are PERs
module MLTT.Statics.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import MLTT.Statics.Full
open import MLTT.Statics.Misc
open import MLTT.Statics.Properties.Contexts
open import MLTT.Statics.CtxEquiv

Exp≈-isPER : IsPartialEquivalence (Γ ⊢_≈_∶ T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : Ctx → Typ → PartialSetoid _ _
Exp≈-PER Γ T = record
  { Carrier              = Exp
  ; _≈_                  = Γ ⊢_≈_∶ T
  ; isPartialEquivalence = Exp≈-isPER
  }

module ER {Γ T} = PS (Exp≈-PER Γ T)

Substs≈-isPER : IsPartialEquivalence (Γ ⊢s_≈_∶ Δ)
Substs≈-isPER = record
  { sym   = s-≈-sym
  ; trans = s-≈-trans
  }

Substs≈-PER : Ctx → Ctx → PartialSetoid _ _
Substs≈-PER Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = Γ ⊢s_≈_∶ Δ
  ; isPartialEquivalence = Substs≈-isPER
  }

module SR {Γ Δ} = PS (Substs≈-PER Γ Δ)

⊢≈-trans : ⊢ Γ ≈ Γ′ → ⊢ Γ′ ≈ Γ″ → ⊢ Γ ≈ Γ″
⊢≈-trans []-≈                            []-≈                                 = []-≈
⊢≈-trans (∷-cong Γ≈Γ′ ⊢T ⊢T′ T≈T′ T≈T′₁) (∷-cong Γ′≈Γ″ ⊢T′₁ ⊢T″ T′≈T″ T′≈T″₁) = ∷-cong (⊢≈-trans Γ≈Γ′ Γ′≈Γ″)
                                                                                       (lift-⊢-Se-max ⊢T)
                                                                                       (lift-⊢-Se-max′ ⊢T″)
                                                                                       (≈-trans (lift-⊢≈-Se-max T≈T′) (lift-⊢≈-Se-max′ (ctxeq-≈ (⊢≈-sym Γ≈Γ′) T′≈T″)))
                                                                                       (≈-trans (lift-⊢≈-Se-max (ctxeq-≈ Γ′≈Γ″ T≈T′₁)) (lift-⊢≈-Se-max′ T′≈T″₁))

Ctxs≈-isPER : IsPartialEquivalence (λ Γ → ⊢ Γ ≈_) -- weird parser bug here
Ctxs≈-isPER = record
  { sym   = ⊢≈-sym
  ; trans = ⊢≈-trans
  }

Ctxs≈-PER : PartialSetoid _ _
Ctxs≈-PER = record
  { Carrier              = Ctx
  ; _≈_                  = ⊢_≈_
  ; isPartialEquivalence = Ctxs≈-isPER
  }

module CR = PS Ctxs≈-PER
