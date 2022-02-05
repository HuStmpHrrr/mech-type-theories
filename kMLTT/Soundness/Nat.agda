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
open import kMLTT.Soundness.Realizability fext
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
           ⊩Γ ⊢Δ ⊢T ⊢s ⊢r σ∼ρ
           gT gs@record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } gr t∼a = recurse t∼a
  where rec′ : Exp → Exp
        rec′ t = rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t
        ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Γ   = ⊩⇒⊢ ⊩Γ
        ⊢qσ  = ⊢q-N ⊢σ
        ⊢qqσ = ⊢q ⊢qσ ⊢T
        ⊢Tqσ = t[σ]-Se ⊢T ⊢qσ
        ≈N   = ≈-sym (N-[] 0 ⊢σ)
        ⊢ze′ = conv (ze-I ⊢Δ) ≈N
        Γ⊢N  = N-wf 0 ⊢Γ
        ⊢NΓ  = ⊢∺ ⊢Γ Γ⊢N
        ⊢TNΓ = ⊢∺ ⊢NΓ ⊢T
        ⊢wk   = s-wk ⊢NΓ
        ⊢wk′  = s-wk ⊢TNΓ
        ⊢wkwk = s-∘ ⊢wk′ ⊢wk

        open ER

        gen-eq₁ : Δ ⊢ T [ σ , ze ] ≈ T [| ze ] [ σ ] ∶ Se i
        gen-eq₁ = ≈-sym ([]-I,ze-∘ ⊢T ⊢σ)

        gen-eq₂ : Δ ⊢ T [ σ , ze ] ≈ T [ q σ ] [| ze ] ∶ Se i
        gen-eq₂ = []-q-∘-,′ ⊢T ⊢σ ⊢ze′

        ⊢sσ   = conv (t[σ] ⊢s ⊢σ) (≈-trans (≈-sym gen-eq₁) gen-eq₂)
        ⊢rqqσ = conv (t[σ] ⊢r ⊢qqσ) (rec-β-su-T-swap ⊢T ⊢σ)

        gen-eq₃ : Δ ⊢ t ∶ N → Δ ⊢ T [ σ , t ] ≈ T [ q σ ] [| t ] ∶ Se i
        gen-eq₃ ⊢t = []-q-∘-,′ ⊢T ⊢σ (conv ⊢t ≈N)

        rec-cong′ : Δ ⊢ t ≈ t′ ∶ N →
                    Δ ⊢ rec′ t ≈ rec′ t′ ∶ T [ q σ ] [| t ]
        rec-cong′ = rec-cong (≈-refl ⊢Tqσ) (≈-refl ⊢sσ) (≈-refl ⊢rqqσ)

        N-E′ : Δ ⊢ t ∶ N →
               Δ ⊢ rec′ t ∶ T [ q σ ] [| t ]
        N-E′ = N-E ⊢Tqσ ⊢sσ ⊢rqqσ

        recurse : (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
                  let open GluTyp (gT t∼a) renaming (T∈𝕌 to T∈𝕌′)
                  in ∃ λ ra → rec∙ T , ⟦t⟧ , r , ρ , a ↘ ra
                            × Δ ⊢ rec′ t ∶ T [ σ , t ] ®[ i ] ra ∈El T∈𝕌′
        recurse {t} {.ze} (ze ≈ze)
          with gT (ze ≈ze)
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ }
             rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ⟦t⟧ , ze↘
                                       , ®El-one-sided T∈𝕌 T∈𝕌′
                                                       (®El-resp-T≈ T∈𝕌 (®El-resp-≈ T∈𝕌 t∼⟦t⟧ eq₂) eq₁)
          where eq₁ : Δ ⊢ T [| ze ] [ σ ] ≈ T [ σ , t ] ∶ Se i
                eq₁ = begin
                  T [| ze ] [ σ ] ≈⟨ []-I,ze-∘ ⊢T ⊢σ ⟩
                  T [ σ , ze ] ≈⟨ []-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-sym (≈-conv ≈ze ≈N))) ⟩
                  T [ σ , t ] ∎

                eq₂ : Δ ⊢ s [ σ ] ≈ rec′ t ∶ T [| ze ] [ σ ]
                eq₂ = ≈-conv (begin
                  s [ σ ]                                      ≈˘⟨ ≈-conv (rec-β-ze ⊢Tqσ ⊢sσ ⊢rqqσ) (≈-sym gen-eq₂) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) ze ≈˘⟨ ≈-conv (rec-cong′ ≈ze)
                                                                          (≈-trans ([]-cong-Se″ ⊢Tqσ (,-cong (I-≈ ⊢Δ) (N-wf 0 ⊢Δ) (≈-conv ≈ze (≈-sym ([I] (N-wf 0 ⊢Δ))))))
                                                                                   (≈-sym gen-eq₂)) ⟩
                  rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t  ∎) gen-eq₁


        recurse {t} {su a} t∼a@(su {t′ = t′} ≈sut′ t′∼a)
          with recurse t′∼a
        ...  | ra , ↘ra , rect′∼ra
             with gT t∼a
                | gr t′∼a rect′∼ra
        ...     | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ }
                | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
                rewrite drop-↦ (ρ ↦ a) ra
                      | drop-↦ ρ a
                      | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ⟦t⟧ , su↘ ↘ra ↘⟦t⟧
                                          , ®El-one-sided T∈𝕌 T∈𝕌′
                                                          (®El-resp-≈ T∈𝕌 (®El-resp-T≈ T∈𝕌 t∼⟦t⟧ eq₃) eq₅)
          where ⊢t      = ®Nat⇒∶Nat t∼a ⊢Δ
                ⊢t′     = ®Nat⇒∶Nat t′∼a ⊢Δ
                ⊢t′₁    = conv ⊢t′ ≈N
                ⊢I,t′   = ⊢I,t ⊢t′
                ⊢v1     = ⊢vn∶N L.[ T ] ⊢TNΓ refl
                ⊢suv1   = conv (su-I ⊢v1) (≈-sym (N-[] 0 ⊢wkwk))
                ⊢σ,t′   = s-, ⊢σ Γ⊢N (conv ⊢t′ ≈N)
                ⊢rect′  = conv (N-E′ ⊢t′) (≈-sym (gen-eq₃ ⊢t′))
                ⊢σt′rec = s-, ⊢σ,t′ ⊢T ⊢rect′

                eq₃ : Δ ⊢ T [ (wk ∘ wk) , su (v 1) ] [ (σ , t′) , rec′ t′ ] ≈ T [ σ , t ] ∶ Se i
                eq₃ = begin
                  T [ (wk ∘ wk) , su (v 1) ] [ (σ , t′) , rec′ t′ ]   ≈⟨ [∘]-Se ⊢T (s-, ⊢wkwk Γ⊢N ⊢suv1) ⊢σt′rec ⟩
                  T [ ((wk ∘ wk) , su (v 1)) ∘ ((σ , t′) , rec′ t′) ] ≈⟨ []-cong-Se″ ⊢T (,-∘ ⊢wkwk Γ⊢N ⊢suv1 ⊢σt′rec) ⟩
                  _                                                   ≈⟨ []-cong-Se″ ⊢T (,-cong (wk∘wk∘,, ⊢σ Γ⊢N ⊢T ⊢t′₁ ⊢rect′)
                                                                                        Γ⊢N
                                                                                        (≈-conv (≈-trans (su-[] ⊢σt′rec ⊢v1)
                                                                                                (≈-trans (su-cong (≈-conv ([,]-v-su ⊢σ,t′ ⊢T ⊢rect′ here)
                                                                                                                  (≈-trans ([]-cong-Se′ (N-[] 0 ⊢wk) ⊢σ,t′)
                                                                                                                           (N-[] 0 ⊢σ,t′))))
                                                                                                (≈-trans (su-cong (≈-conv ([,]-v-ze ⊢σ Γ⊢N ⊢t′₁) (N-[] 0 ⊢σ)))
                                                                                                         (≈-sym ≈sut′))))
                                                                                                (≈-sym (N-[] 0 (s-∘ ⊢σt′rec ⊢wkwk))))) ⟩
                  T [ σ , t ]                                         ∎

                eq₄ : Δ ⊢s (q σ ∘ (I , t′)) , rec′ t′ ≈ (σ , t′) , rec′ t′ ∶ T ∺ N ∺ Γ
                eq₄ = s-≈-sym (,-cong (s-≈-sym (qI,≈, ⊢σ Γ⊢N ⊢t′₁)) ⊢T (≈-refl ⊢rect′))

                eq₅ : Δ ⊢ r [ (σ , t′) , rec′ t′ ] ≈ rec′ t ∶ T [ σ , t ]
                eq₅ = begin
                  r [ (σ , t′) , rec′ t′ ]             ≈⟨ ≈-conv ([]-cong (≈-refl ⊢r) (s-≈-sym eq₄)) eq₃ ⟩
                  r [ (q σ ∘ (I , t′)) , rec′ t′ ]     ≈˘⟨ ≈-conv ([]-q-, ⊢qσ ⊢T ⊢I,t′ (N-E′ ⊢t′) ⊢r)
                                                                  (≈-trans ([]-cong-Se″ (t[σ]-Se ⊢T (s-, ⊢wkwk Γ⊢N ⊢suv1)) eq₄)
                                                                           eq₃) ⟩
                  r [ q (q σ) ] [ (I , t′) , rec′ t′ ] ≈˘⟨ ≈-conv (rec-β-su ⊢Tqσ ⊢sσ ⊢rqqσ ⊢t′)
                                                                  (≈-trans (≈-sym (gen-eq₃ (su-I ⊢t′)))
                                                                           ([]-cong-Se″ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-sym (≈-conv ≈sut′ ≈N))))) ⟩
                  rec′ (su t′)                         ≈˘⟨ ≈-conv (rec-cong′ ≈sut′) (≈-sym (gen-eq₃ ⊢t)) ⟩
                  rec′ t                               ∎

        recurse {t} {↑ N c} t∼a@(ne c∈ rel)
          with gT (ne c∈ rel)
        ... | record { ⟦T⟧ = ⟦T⟧′ ; ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ } = ↑ ⟦T⟧′ (rec T ⟦t⟧ r ρ c) , rec∙ ↘⟦T⟧′
                                                                                 , ®↓El⇒®El T∈𝕌′ record
                                                                                 { t∶T  = conv (N-E′ ⊢t) (≈-sym (gen-eq₃ ⊢t))
                                                                                 ; T∼A  = T∼⟦T⟧′
                                                                                 ; c∈⊥  = {!!}
                                                                                 ; krip = λ {Δ′} {τ} ⊢τ → {!!}
                                                                                 }
          where ⊢t = ®Nat⇒∶Nat t∼a ⊢Δ


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
