{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Fundamental theorems for semantic judgments
--
-- Essentially it is the semantic soundness of the PER model.
module MLTT.Completeness.Fundamental (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import MLTT.Completeness.Contexts fext
open import MLTT.Completeness.LogRel
open import MLTT.Completeness.Nat fext
open import MLTT.Completeness.Pi fext
open import MLTT.Completeness.Substitutions fext
open import MLTT.Completeness.Terms fext
open import MLTT.Completeness.Universe fext
open import MLTT.Statics

mutual
  fundamental-⊢Γ : ⊢ Γ → ⊨ Γ
  fundamental-⊢Γ ⊢[]        = []-≈′
  fundamental-⊢Γ (⊢∷ ⊢Γ ⊢T) = ∷-cong′ (fundamental-⊢Γ ⊢Γ) (fundamental-⊢t ⊢T)

  fundamental-⊢t : Γ ⊢ t ∶ T → Γ ⊨ t ∶ T
  fundamental-⊢t (N-wf _ ⊢Γ)           = N-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (Se-wf _ ⊢Γ)          = Se-≈′ _ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (Π-wf ⊢S ⊢T)          = Π-cong′ (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢T)
  fundamental-⊢t (vlookup ⊢Γ x∈)       = v-≈′ (fundamental-⊢Γ ⊢Γ) x∈
  fundamental-⊢t (ze-I ⊢Γ)             = ze-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (su-I ⊢t)             = su-cong′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (N-E ⊢T ⊢s ⊢r ⊢t)     = rec-cong′ (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢s) (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢t)
  fundamental-⊢t (Λ-I ⊢t)              = Λ-cong′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (Λ-E ⊢r ⊢s)           = $-cong′ (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢s)
  fundamental-⊢t (t[σ] ⊢t ⊢σ)          = []-cong′ (fundamental-⊢t ⊢t) (fundamental-⊢σ ⊢σ)
  fundamental-⊢t (cumu ⊢t)             = ≈-cumu′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (conv ⊢t S≈T)         = ≈-conv′ (fundamental-⊢t ⊢t) (fundamental-t≈t′ S≈T)

  fundamental-⊢σ : Γ ⊢s σ ∶ Δ → Γ ⊨s σ ∶ Δ
  fundamental-⊢σ (s-I ⊢Γ)               = I-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢σ (s-wk ⊢TΔ)             = wk-≈′ (fundamental-⊢Γ ⊢TΔ)
  fundamental-⊢σ (s-∘ ⊢σ ⊢τ)            = ∘-cong′ (fundamental-⊢σ ⊢σ) (fundamental-⊢σ ⊢τ)
  fundamental-⊢σ (s-, ⊢σ ⊢T ⊢t)         = ,-cong′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢t)
  fundamental-⊢σ (s-conv ⊢σ Δ₁≈Δ)       = s-≈-conv′ (fundamental-⊢σ ⊢σ) (fundamental-Γ≈Γ′ Δ₁≈Δ)

  fundamental-Γ≈Γ′ : ⊢ Γ ≈ Γ′ → ⊨ Γ ≈ Γ′
  fundamental-Γ≈Γ′ []-≈               = []-≈′
  fundamental-Γ≈Γ′ (∷-cong Γ≈Γ′ T≈T′) = ∷-cong′ (fundamental-Γ≈Γ′ Γ≈Γ′) (fundamental-t≈t′ T≈T′)

  fundamental-t≈t′ : Γ ⊢ t ≈ t′ ∶ T → Γ ⊨ t ≈ t′ ∶ T
  fundamental-t≈t′ (N-[] _ ⊢σ)                    = N-[]′ _ (fundamental-⊢σ ⊢σ)
  fundamental-t≈t′ (Se-[] _ ⊢σ)                   = Se-[]′ _ (fundamental-⊢σ ⊢σ)
  fundamental-t≈t′ (Π-[] ⊢σ ⊢S ⊢T)                = Π-[]′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢T)
  fundamental-t≈t′ (Π-cong S≈S′ T≈T′)             = Π-cong′ (fundamental-t≈t′ S≈S′) (fundamental-t≈t′ T≈T′)
  fundamental-t≈t′ (v-≈ ⊢Γ x∈)                    = v-≈′ (fundamental-⊢Γ ⊢Γ) x∈
  fundamental-t≈t′ (ze-≈ ⊢Γ)                      = ze-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-t≈t′ (su-cong t≈t′)                 = su-cong′ (fundamental-t≈t′ t≈t′)
  fundamental-t≈t′ (rec-cong T≈T′ s≈s′ r≈r′ t≈t′) = rec-cong′ (fundamental-t≈t′ T≈T′) (fundamental-t≈t′ s≈s′) (fundamental-t≈t′ r≈r′) (fundamental-t≈t′ t≈t′)
  fundamental-t≈t′ (Λ-cong t≈t′)                  = Λ-cong′ (fundamental-t≈t′ t≈t′)
  fundamental-t≈t′ ($-cong r≈r′ s≈s′)             = $-cong′ (fundamental-t≈t′ r≈r′) (fundamental-t≈t′ s≈s′)
  fundamental-t≈t′ ([]-cong t≈t′ σ≈σ′)            = []-cong′ (fundamental-t≈t′ t≈t′) (fundamental-σ≈σ′ σ≈σ′)
  fundamental-t≈t′ (ze-[] ⊢σ)                     = ze-[]′ (fundamental-⊢σ ⊢σ)
  fundamental-t≈t′ (su-[] ⊢σ ⊢t)                  = su-[]′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)        = rec-[]′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢s) (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ (Λ-[] ⊢σ ⊢t)                   = Λ-[]′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ ($-[] ⊢σ ⊢r ⊢s)                = $-[]′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢s)
  fundamental-t≈t′ (rec-β-ze ⊢T ⊢s ⊢r)            = rec-β-ze′ (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢s) (fundamental-⊢t ⊢r)
  fundamental-t≈t′ (rec-β-su ⊢T ⊢s ⊢r ⊢t)         = rec-β-su′ (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢s) (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ (Λ-β ⊢t ⊢s)                    = Λ-β′ (fundamental-⊢t ⊢t) (fundamental-⊢t ⊢s)
  fundamental-t≈t′ (Λ-η ⊢t)                       = Λ-η′ (fundamental-⊢t ⊢t)
  fundamental-t≈t′ ([I] ⊢t)                       = [I]′ (fundamental-⊢t ⊢t)
  fundamental-t≈t′ ([wk] ⊢SΓ x∈)                  = [wk]′ (fundamental-⊢Γ ⊢SΓ) x∈
  fundamental-t≈t′ ([∘] ⊢τ ⊢σ ⊢t)                 = [∘]′ (fundamental-⊢σ ⊢τ) (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ ([,]-v-ze ⊢σ ⊢S ⊢t)            = [,]-v-ze′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢t)
  fundamental-t≈t′ ([,]-v-su ⊢σ ⊢S ⊢s x∈)         = [,]-v-su′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢s) x∈
  fundamental-t≈t′ (≈-cumu t≈t′)                  = ≈-cumu′ (fundamental-t≈t′ t≈t′)
  fundamental-t≈t′ (≈-conv S≈T t≈t′)              = ≈-conv′ (fundamental-t≈t′ S≈T) (fundamental-t≈t′ t≈t′)
  fundamental-t≈t′ (≈-sym t′≈t)                   = ≈-sym′ (fundamental-t≈t′ t′≈t)
  fundamental-t≈t′ (≈-trans t≈t′₁ t′₁≈t′)         = ≈-trans′ (fundamental-t≈t′ t≈t′₁) (fundamental-t≈t′ t′₁≈t′)

  fundamental-σ≈σ′ : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊨s σ ≈ σ′ ∶ Δ
  fundamental-σ≈σ′ (I-≈ ⊢Γ)                    = I-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-σ≈σ′ (wk-≈ ⊢Γ)                   = wk-≈′ (fundamental-⊢Γ ⊢Γ)
  fundamental-σ≈σ′ (∘-cong σ≈σ′ τ≈τ′)          = ∘-cong′ (fundamental-σ≈σ′ σ≈σ′) (fundamental-σ≈σ′ τ≈τ′)
  fundamental-σ≈σ′ (,-cong σ≈σ′ ⊢T t≈t′)       = ,-cong′ (fundamental-σ≈σ′ σ≈σ′) (fundamental-⊢t ⊢T) (fundamental-t≈t′ t≈t′)
  fundamental-σ≈σ′ (I-∘ ⊢σ)                    = I-∘′ (fundamental-⊢σ ⊢σ)
  fundamental-σ≈σ′ (∘-I ⊢σ)                    = ∘-I′ (fundamental-⊢σ ⊢σ)
  fundamental-σ≈σ′ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)        = ∘-assoc′ (fundamental-⊢σ ⊢σ) (fundamental-⊢σ ⊢σ′) (fundamental-⊢σ ⊢σ″)
  fundamental-σ≈σ′ (,-∘ ⊢σ ⊢T ⊢t ⊢τ)           = ,-∘′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢t) (fundamental-⊢σ ⊢τ)
  fundamental-σ≈σ′ (p-, ⊢σ ⊢T ⊢t)              = p-,′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢t)
  fundamental-σ≈σ′ (,-ext ⊢σ)                  = ,-ext′ (fundamental-⊢σ ⊢σ)
  fundamental-σ≈σ′ (s-≈-sym σ≈σ′)              = s-≈-sym′ (fundamental-σ≈σ′ σ≈σ′)
  fundamental-σ≈σ′ (s-≈-trans σ≈σ′₁ σ′₁≈σ′)    = s-≈-trans′ (fundamental-σ≈σ′ σ≈σ′₁) (fundamental-σ≈σ′ σ′₁≈σ′)
  fundamental-σ≈σ′ (s-≈-conv σ≈σ′ Δ₁≈Δ)        = s-≈-conv′ (fundamental-σ≈σ′ σ≈σ′) (fundamental-Γ≈Γ′ Δ₁≈Δ)
