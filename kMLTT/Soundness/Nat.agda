{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
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
             Γ ⊢ t ∶ N →
             Δ ⊢ t [ σ ] ∶N® a ∈Nat →
             ⟦ t ⟧ ρ ↘ a →
             GluExp i Δ (rec T s r t) (T [| t ]) σ ρ
N-E-hepler {_} {T} {s} {r} {Δ} {σ} {ρ} {t} {_} {i} ⊩Γ ⊩T ⊩s ⊩r σ∼ρ ⊢t t∼a ↘a = recurse t∼a ↘a
  where module ⊩T = _⊩_∶_ ⊩T
        module ⊩s = _⊩_∶_ ⊩s
        module ⊩r = _⊩_∶_ ⊩r
        ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Γ   = ⊩⇒⊢ ⊩Γ
        ⊢Δ   = proj₁ (presup-s ⊢σ)
        ⊢T   = ⊩⇒⊢-tm ⊩T
        ⊢s   = ⊩⇒⊢-tm ⊩s
        ⊢r   = ⊩⇒⊢-tm ⊩r
        ⊢qσ  = ⊢q-N ⊢σ
        ⊢qqσ = ⊢q ⊢qσ ⊢T
        ⊢Tqσ = t[σ]-Se ⊢T ⊢qσ
        ⊢ze′ = conv (ze-I ⊢Δ) (≈-sym (N-[] 0 ⊢σ))

        open ER

        gen-eq₁ : Δ ⊢ T [ σ , ze ] ≈ T [| ze ] [ σ ] ∶ Se i
        gen-eq₁ = ≈-sym ([]-I,ze-∘ ⊢T ⊢σ)

        gen-eq₂ : Δ ⊢ T [ σ , ze ] ≈ T [ q σ ] [| ze ] ∶ Se i
        gen-eq₂ = []-q-∘-,′ ⊢T ⊢σ ⊢ze′

        ⊢sqσ = conv (t[σ] ⊢s ⊢σ) (≈-trans (≈-sym gen-eq₁) gen-eq₂)
        ⊢rqqσ = conv (t[σ] ⊢r ⊢qqσ) (rec-β-su-T-swap ⊢T ⊢σ)

        recurse : Δ ⊢ t [ σ ] ∶N® a ∈Nat → ⟦ t ⟧ ρ ↘ a → GluExp i Δ (rec T s r t) (T [| t ]) σ ρ
        recurse (ze ≈ze) ↘a
          with ⊩T.⊩Γ | ⊩T.krip
        ... | ⊩NΓ@(⊩∺ ⊩Γ₁ ⊢N _) | krip = helper
          where σ,ze∼ρ,ze : Δ ⊢s σ , ze ∶ ⊩NΓ ® ρ ↦ ze
                σ,ze∼ρ,ze = record
                  { ⊢σ   = s-, ⊢σ ⊢N ⊢ze′
                  ; pσ   = σ
                  ; v0σ  = ze
                  ; ⟦T⟧  = N
                  ; ≈pσ  = p-, ⊢σ ⊢N ⊢ze′
                  ; ≈v0σ = [,]-v-ze ⊢σ ⊢N ⊢ze′
                  ; ↘⟦T⟧ = ⟦N⟧
                  ; T∈𝕌  = N
                  ; t∼ρ0 = ze (ze-≈ ⊢Δ) , N-[] _ ⊢σ
                  ; step = subst (_ ⊢s _ ∶ _ ®_) (sym (drop-↦ ρ ze)) (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ)
                  }

                open ER
                eq₀ : Δ ⊢ T [ σ , ze ] ≈ T [ σ , t [ σ ] ] ∶ Se i
                eq₀ = []-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) ⊢N (≈-conv (≈-sym ≈ze) (≈-sym (N-[] 0 ⊢σ))))

                eq₁ : Δ ⊢ T [ σ , ze ] ≈ T [ I , t ] [ σ ] ∶ Se i
                eq₁ = begin
                  T [ σ , ze ]      ≈⟨ eq₀ ⟩
                  T [ σ , t [ σ ] ] ≈˘⟨ []-I,-∘ ⊢T ⊢σ ⊢t ⟩
                  T [ I , t ] [ σ ] ∎

                eq₂ : Δ ⊢ s [ σ ] ≈ rec T s r t [ σ ] ∶ T [| ze ] [ σ ]
                eq₂ = ≈-conv (begin
                  s [ σ ]                                             ≈˘⟨ ≈-conv (rec-β-ze ⊢Tqσ ⊢sqσ ⊢rqqσ) (≈-sym gen-eq₂) ⟩
                  -- s [ σ ]                                          ≈˘⟨ ≈-conv ([]-cong (rec-β-ze ⊢T ⊢s ⊢r) (s-≈-refl ⊢σ)) (≈-sym gen-eq₁) ⟩
                  -- rec T s r ze [ σ ]                               ≈⟨ ≈-conv (rec-[] ⊢σ ⊢T ⊢s ⊢r (ze-I ⊢Γ))
                  --                                                                ([]-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) ⊢N (≈-conv (ze-[] ⊢σ) (≈-sym (N-[] 0 ⊢σ))))) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) ze        ≈˘⟨ ≈-conv (rec-cong (≈-refl ⊢Tqσ) (≈-refl ⊢sqσ) (≈-refl ⊢rqqσ) ≈ze)
                                                                                 (≈-trans ([]-cong-Se″ ⊢Tqσ (,-cong (I-≈ ⊢Δ) (N-wf 0 ⊢Δ) (≈-conv ≈ze (≈-sym ([I] (N-wf 0 ⊢Δ))))))
                                                                                          (≈-sym gen-eq₂)) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ≈˘⟨ ≈-conv (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t) (≈-sym eq₀) ⟩
                  rec T s r t [ σ ]                                   ∎) gen-eq₁

                helper : GluExp i Δ (rec T s r t) (T [| t ]) σ ρ
                helper
                  with ⊩s.krip (s®-irrel ⊩Γ ⊩s.⊩Γ σ∼ρ)
                     | krip σ,ze∼ρ,ze
                ...  | record { ⟦T⟧ = ⟦T⟧′ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧′ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
                     | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ }
                     rewrite Glu-wellfounded-≡ i<l
                           | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                      { ⟦T⟧   = ⟦T⟧
                      ; ⟦t⟧   = ⟦t⟧
                      ; ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘a) ↘⟦T⟧
                      ; ↘⟦t⟧  = ⟦rec⟧ ↘⟦t⟧ ↘a ze↘
                      ; T∈𝕌   = A∈𝕌
                      ; t∼⟦t⟧ = ®El-master T∈𝕌 A∈𝕌 A∈𝕌
                                           (®-resp-≈ A∈𝕌 rel eq₁)
                                           (®El-resp-≈ T∈𝕌 t∼⟦t⟧ eq₂)
                                           (≈-trans (≈-sym gen-eq₁) eq₁)
                      }
                      where open GluU T∼⟦T⟧

        recurse (su ≈sut′ t′∼a) ↘a = {!!}
        recurse (ne c∈ rel) ↘a     = {!!}


-- N-E′ : ∀ {i} →
--        N ∺ Γ ⊩ T ∶ Se i →
--        Γ ⊩ s ∶ T [| ze ] →
--        T ∺ N ∺ Γ ⊩ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
--        Γ ⊩ t ∶ N →
--        --------------------------
--        Γ ⊩ rec T s r t ∶ T [| t ]
-- N-E′ ⊩T ⊩s ⊩r ⊩t = record
--   { ⊩Γ   = ⊩t.⊩Γ
--   ; lvl  = _⊩_∶_.lvl ⊩t
--   ; krip = {!!}
--   }
--   where module ⊩t = _⊩_∶_ ⊩t
