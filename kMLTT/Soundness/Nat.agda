{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Evaluation
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


N-E-hepler : ∀ {i} (⊩Γ : ⊩ Γ) (⊢Δ : ⊢ Δ) →
             N ∺ Γ ⊢ T ∶ Se i →
             Γ ⊢ s ∶ T [| ze ] →
             T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
             Δ ⊢s σ ∶ ⊩Γ ® ρ →
             (gT : ∀ {t a} → Δ ⊢ t ∶N® a ∈Nat → GluTyp i Δ T (σ , t) (ρ ↦ a)) →
             (gs : GluExp i Δ s (T [| ze ]) σ ρ) →
             (∀ {t a t′ b} →
               (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
               (let open GluTyp (gT t∼a) in Δ ⊢ t′ ∶ T [ σ , t ] ®[ i ] b ∈El T∈𝕌) →
               GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ]) ((σ , t) , t′) (ρ ↦ a ↦ b)) →
             (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
             let open GluExp gs hiding (T∈𝕌)
                 open GluTyp (gT t∼a)
             in ∃ λ ra → rec∙ T , ⟦t⟧ , r , ρ , a ↘ ra
                       × Δ ⊢ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t ∶ T [ σ , t ] ®[ i ] ra ∈El T∈𝕌
N-E-hepler {Γ} {Δ} {T} {s} {r} {σ} {ρ} {_} {_} {i}
           ⊩Γ ⊢Δ ⊢T ⊢s ⊢r σ∼ρ gT gs gr t∼a = recurse gs t∼a
  where ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Γ   = ⊩⇒⊢ ⊩Γ
        ⊢qσ  = ⊢q-N ⊢σ
        ⊢qqσ = ⊢q ⊢qσ ⊢T
        ⊢Tqσ = t[σ]-Se ⊢T ⊢qσ
        ⊢ze′ = conv (ze-I ⊢Δ) (≈-sym (N-[] 0 ⊢σ))
        Γ⊢N  = N-wf 0 ⊢Γ

        open ER

        gen-eq₁ : Δ ⊢ T [ σ , ze ] ≈ T [| ze ] [ σ ] ∶ Se i
        gen-eq₁ = ≈-sym ([]-I,ze-∘ ⊢T ⊢σ)

        gen-eq₂ : Δ ⊢ T [ σ , ze ] ≈ T [ q σ ] [| ze ] ∶ Se i
        gen-eq₂ = []-q-∘-,′ ⊢T ⊢σ ⊢ze′

        ⊢sqσ = conv (t[σ] ⊢s ⊢σ) (≈-trans (≈-sym gen-eq₁) gen-eq₂)
        ⊢rqqσ = conv (t[σ] ⊢r ⊢qqσ) (rec-β-su-T-swap ⊢T ⊢σ)

        recurse : (gs : GluExp i Δ s (T [| ze ]) σ ρ) →
                  (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
                  let open GluTyp (gT t∼a)
                      open GluExp gs using (⟦t⟧)
                  in ∃ λ ra → rec∙ T , ⟦t⟧ , r , ρ , a ↘ ra
                            × Δ ⊢ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t ∶ T [ σ , t ] ®[ i ] ra ∈El T∈𝕌
        recurse {t} {.ze} record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } (ze ≈ze)
          with gT (ze ≈ze)
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ }
             rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ⟦t⟧ , ze↘
                                       , ®El-one-sided T∈𝕌 T∈𝕌′
                                                       (®El-resp-T≈ T∈𝕌 (®El-resp-≈ T∈𝕌 t∼⟦t⟧ eq₂) eq₁)
          where eq₀ : Δ ⊢ T [ σ , ze ] ≈ T [ σ , t ] ∶ Se i
                eq₀ = []-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-conv (≈-sym ≈ze) (≈-sym (N-[] 0 ⊢σ))))

                eq₁ : Δ ⊢ T [| ze ] [ σ ] ≈ T [ σ , t ] ∶ Se i
                eq₁ = begin
                  T [| ze ] [ σ ] ≈⟨ []-I,ze-∘ ⊢T ⊢σ ⟩
                  T [ σ , ze ] ≈⟨ []-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-sym (≈-conv ≈ze (≈-sym (N-[] 0 ⊢σ))))) ⟩
                  T [ σ , t ] ∎

                eq₂ : Δ ⊢ s [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t ∶ T [| ze ] [ σ ]
                eq₂ = ≈-conv (begin
                  s [ σ ]                                      ≈˘⟨ ≈-conv (rec-β-ze ⊢Tqσ ⊢sqσ ⊢rqqσ) (≈-sym gen-eq₂) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) ze ≈˘⟨ ≈-conv (rec-cong (≈-refl ⊢Tqσ) (≈-refl ⊢sqσ) (≈-refl ⊢rqqσ) ≈ze)
                                                                          (≈-trans ([]-cong-Se″ ⊢Tqσ (,-cong (I-≈ ⊢Δ) (N-wf 0 ⊢Δ) (≈-conv ≈ze (≈-sym ([I] (N-wf 0 ⊢Δ))))))
                                                                                   (≈-sym gen-eq₂)) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t  ∎) gen-eq₁


        recurse {t} {su a} gs (su ≈sut′ t′∼a) = {!!}
        recurse {t} {↑ N c} gs (ne c∈ rel)    = {!!}

--         recurse {su a} t∼sua@(su ≈sut′ t′∼a) ↘a
--           with ⊩T.⊩Γ | ⊩T.krip
--         ... | ⊩NΓ@(⊩∺ ⊩Γ₁ ⊢N _) | krip = {!recurse t′∼a!}
--           where ⊢tσ = t[σ] ⊢t ⊢σ
--                 σ,t∼ρ,sua : Δ ⊢s σ , t [ σ ] ∶ ⊩NΓ ® ρ ↦ su a
--                 σ,t∼ρ,sua = record
--                   { ⊢σ   = s-, ⊢σ ⊢N ⊢tσ
--                   ; pσ   = σ
--                   ; v0σ  = t [ σ ]
--                   ; ⟦T⟧  = N
--                   ; ≈pσ  = p-, ⊢σ ⊢N ⊢tσ
--                   ; ≈v0σ = [,]-v-ze ⊢σ ⊢N ⊢tσ
--                   ; ↘⟦T⟧ = ⟦N⟧
--                   ; T∈𝕌  = N
--                   ; t∼ρ0 = t∼sua , N-[] _ ⊢σ
--                   ; step = subst (_ ⊢s _ ∶ _ ®_) (sym (drop-↦ ρ (su a))) (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ)
--                   }

--                 -- helper : GluExp i Δ (rec T s r t) (T [| t ]) σ ρ
--                 -- helper
--                 --   with ⊩s.krip (s®-irrel ⊩Γ ⊩s.⊩Γ σ∼ρ)
--                 --      | krip  σ,ze∼ρ,ze
--                 -- ...  | record { ⟦T⟧ = ⟦T⟧′ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧′ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
--                 --      | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ }
--                 --      rewrite Glu-wellfounded-≡ i<l
--                 --            | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ?

--         recurse (ne c∈ rel) ↘a     = {!!}


-- -- N-E′ : ∀ {i} →
-- --        N ∺ Γ ⊩ T ∶ Se i →
-- --        Γ ⊩ s ∶ T [| ze ] →
-- --        T ∺ N ∺ Γ ⊩ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- --        Γ ⊩ t ∶ N →
-- --        --------------------------
-- --        Γ ⊩ rec T s r t ∶ T [| t ]
-- -- N-E′ ⊩T ⊩s ⊩r ⊩t = record
-- --   { ⊩Γ   = ⊩t.⊩Γ
-- --   ; lvl  = _⊩_∶_.lvl ⊩t
-- --   ; krip = {!!}
-- --   }
-- --   where module ⊩t = _⊩_∶_ ⊩t
