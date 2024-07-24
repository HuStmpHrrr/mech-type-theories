{-# OPTIONS --without-K --safe #-}


-- Typing judgments are PERs
module NonCumulative.Statics.Ascribed.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib
open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.CtxEquiv

Exp≈-isPER : ∀ {i} → IsPartialEquivalence (Γ ⊢_≈_∶[ i ] T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : Ctx → ℕ → Typ → PartialSetoid _ _
Exp≈-PER Γ i T = record
  { Carrier              = Exp
  ; _≈_                  = Γ ⊢_≈_∶[ i ] T
  ; isPartialEquivalence = Exp≈-isPER
  }

module ER {Γ i T} = PS (Exp≈-PER Γ i T)

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
                                                                                       ⊢T
                                                                                       ⊢T″
                                                                                       (≈-trans T≈T′ (ctxeq-≈ (⊢≈-sym Γ≈Γ′) T′≈T″))
                                                                                       (≈-trans (ctxeq-≈ Γ′≈Γ″ T≈T′₁) T′≈T″₁)

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

⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ≈-Ctx-refl ⊢Γ
⊢I-inv (s-conv ⊢I Γ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Γ′≈Δ
