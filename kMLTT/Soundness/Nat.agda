{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext


N-wf′ : ∀ i →
        ⊩ Γ →
        -------------
        Γ ⊩ N ∶ Se i
N-wf′ i ⊩Γ = record
  { ⊩Γ   = ⊩Γ
  ; lvl  = 1 + i
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp (1 + i) Δ N (Se i) σ ρ
        helper σ∼ρ = record
          { ⟦T⟧   = U i
          ; ⟦t⟧   = N
          ; ↘⟦T⟧  = ⟦Se⟧ i
          ; ↘⟦t⟧  = ⟦N⟧
          ; T∈𝕌   = U′ ≤-refl
          ; t∼⟦t⟧ = record
            { t∶T = t[σ] (N-wf i (⊩⇒⊢ ⊩Γ)) ⊢σ
            ; T≈  = Se-[] i ⊢σ
            ; A∈𝕌 = N
            ; rel = N-[] i ⊢σ
            }
          }
          where ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ


ze-I′ : ⊩ Γ →
        -----------
        Γ ⊩ ze ∶ N
ze-I′ ⊩Γ = record
  { ⊩Γ   = ⊩Γ
  ; lvl  = 0
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp 0 Δ ze N σ ρ
        helper σ∼ρ = record
          { ⟦T⟧   = N
          ; ⟦t⟧   = ze
          ; ↘⟦T⟧  = ⟦N⟧
          ; ↘⟦t⟧  = ⟦ze⟧
          ; T∈𝕌   = N
          ; t∼⟦t⟧ = ze (ze-[] ⊢σ) , N-[] 0 ⊢σ
          }
          where ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ


su-I′ : Γ ⊩ t ∶ N →
        -------------
        Γ ⊩ su t ∶ N
su-I′ {_} {t} ⊩t = record
  { ⊩Γ   = ⊩Γ
  ; lvl  = lvl
  ; krip = helper
  }
  where open _⊩_∶_ ⊩t
        ⊢t = ⊩⇒⊢-tm ⊩t
        helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp lvl Δ (su t) N σ ρ
        helper σ∼ρ
          with krip σ∼ρ
        ... | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = N ; t∼⟦t⟧ = t∼⟦t⟧ , _ }
          = record
          { ⟦T⟧   = N
          ; ⟦t⟧   = su ⟦t⟧
          ; ↘⟦T⟧  = ⟦N⟧
          ; ↘⟦t⟧  = ⟦su⟧ ↘⟦t⟧
          ; T∈𝕌   = N
          ; t∼⟦t⟧ = su (su-[] ⊢σ ⊢t) t∼⟦t⟧ , N-[] lvl ⊢σ
          }
          where ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ

N-E-hepler : ∀ {i} (⊩Γ : ⊩ Γ) →
             N ∺ Γ ⊩ T ∶ Se i →
             (⊩s : Γ ⊩ s ∶ T [| ze ])
             (⊩r : T ∺ N ∺ Γ ⊩ r ∶ T [ (wk ∘ wk) , su (v 1) ]) →
             Δ ⊢s σ ∶ ⊩Γ ® ρ →
             Δ ⊢ t [ σ ] ∶N® a ∈Nat →
             ⟦ t ⟧ ρ ↘ a →
             GluExp (max i (max (_⊩_∶_.lvl ⊩s) (_⊩_∶_.lvl ⊩r))) Δ (rec T s r t) (T [| t ]) σ ρ
N-E-hepler {_} {T} {s} {r} {Δ} {σ} {ρ} {t} {_} {i} ⊩Γ ⊩T ⊩s ⊩r σ∼ρ (ze ≈ze) ↘a = helper
  where module ⊩s = _⊩_∶_ ⊩s
        module ⊩r = _⊩_∶_ ⊩r
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        helper : GluExp _ Δ (rec T s r t) (T [| t ]) σ ρ
        helper
          with ⊩s.krip (s®-irrel ⊩Γ ⊩s.⊩Γ σ∼ρ)
        ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
            = record
              { ⟦T⟧   = ⟦T⟧
              ; ⟦t⟧   = ⟦t⟧
              ; ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘a) ↘⟦T⟧
              ; ↘⟦t⟧  = ⟦rec⟧ ↘⟦t⟧ ↘a ze↘
              ; T∈𝕌   = T∈𝕌′
              ; t∼⟦t⟧ = ®El-cumu T∈𝕌 (®El-resp-T≈ T∈𝕌 (®El-resp-≈ T∈𝕌 t∼⟦t⟧ eq₁) {!!}) {!!}
              }
          where T∈𝕌′ = 𝕌-cumu (≤-trans (m≤m⊔n _ ⊩r.lvl) (m≤n⊔m i _)) T∈𝕌
                open ER
                eq₁ : Δ ⊢ s [ σ ] ≈ rec T s r t [ σ ] ∶ T [| ze ] [ σ ]
                eq₁ = ≈-conv {!⊢σ!}
                      {!!}

-- []-cong (begin
--                   s            ≈˘⟨ rec-β-ze ⊢T ⊩s.t∶T ⊩r.t∶T ⟩
--                   rec T s r ze ≈⟨ rec-cong (≈-refl ⊢T) (≈-refl ⊩s.t∶T) (≈-refl ⊩r.t∶T) {!≈ze!} ⟩
--                   rec T s r t  ∎)
--                              (s-≈-refl ⊢σ)
N-E-hepler {_} {T} {s} {r} {Δ} {σ} {ρ} {t} {_} {i} ⊩Γ ⊩T ⊩s ⊩r σ∼ρ (su x t∼a) ↘a  = {!!}
N-E-hepler {_} {T} {s} {r} {Δ} {σ} {ρ} {t} {_} {i} ⊩Γ ⊩T ⊩s ⊩r σ∼ρ (ne c∈ rel) ↘a = {!x!}


N-E′ : ∀ {i} →
       N ∺ Γ ⊩ T ∶ Se i →
       Γ ⊩ s ∶ T [| ze ] →
       T ∺ N ∺ Γ ⊩ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
       Γ ⊩ t ∶ N →
       --------------------------
       Γ ⊩ rec T s r t ∶ T [| t ]
N-E′ ⊩T ⊩s ⊩r ⊩t = record
  { ⊩Γ   = ⊩t.⊩Γ
  ; lvl  = _⊩_∶_.lvl ⊩t
  ; krip = {!!}
  }
  where module ⊩t = _⊩_∶_ ⊩t
