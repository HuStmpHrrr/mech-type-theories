{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Fundamental fext
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


cons-N-type : ⊩ N ∺ Γ → Set
cons-N-type ⊩NΓ@(⊩∺ ⊩Γ _ _) =
  ∀ {Δ σ ρ t a} →
  Δ ⊢s σ ∶ ⊩Γ ® ρ →
  Δ ⊢ t ∶N® a ∈Nat →
  Δ ⊢s σ , t ∶ ⊩NΓ ® ρ ↦ a

cons-N : (⊩NΓ : ⊩ N ∺ Γ) → cons-N-type ⊩NΓ
cons-N ⊩NΓ@(⊩∺ ⊩Γ ⊢N _) {_} {σ} {_} {t} σ∼ρ t∼a
  with s®⇒⊢s ⊩Γ σ∼ρ
...  | ⊢σ
     with presup-s ⊢σ
...     | ⊢Δ , _ = record
  { ⊢σ   = s-, ⊢σ ⊢N ⊢t′
  ; pσ   = σ
  ; v0σ  = t
  ; ⟦T⟧  = N
  ; ≈pσ  = p-, ⊢σ ⊢N ⊢t′
  ; ≈v0σ = [,]-v-ze ⊢σ ⊢N ⊢t′
  ; ↘⟦T⟧ = ⟦N⟧
  ; T∈𝕌  = N
  ; t∼ρ0 = t∼a , ≈N
  ; step = subst (_ ⊢s _ ∶ ⊩Γ ®_) (sym (drop-↦ _ _)) σ∼ρ
  }
  where ⊢t  = ®Nat⇒∶Nat t∼a ⊢Δ
        ≈N  = N-[] _ ⊢σ
        ⊢t′ = conv ⊢t (≈-sym ≈N)

module NatTyping {i} (⊢T : N ∺ Γ ⊢ T ∶ Se i) (⊢σ : Δ ⊢s σ ∶ Γ) where

  ⊢Δ     = proj₁ (presup-s ⊢σ)
  ⊢Γ     = proj₂ (presup-s ⊢σ)
  ⊢qσ    = ⊢q-N ⊢σ
  ⊢qqσ   = ⊢q ⊢qσ ⊢T
  ⊢Tqσ   = t[σ]-Se ⊢T ⊢qσ
  ⊢NΓ    = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
  ⊢TNΓ   = ⊢∺ ⊢NΓ ⊢T
  ⊢NΔ    = ⊢∺ ⊢Δ (N-wf 0 ⊢Δ)
  ⊢TqσNΔ = ⊢∺ ⊢NΔ ⊢Tqσ
  ⊢wk    = s-wk ⊢NΓ
  ⊢wk′   = s-wk ⊢TNΓ
  ⊢wkwk  = s-∘ ⊢wk′ ⊢wk

module _ (⊢σ : Δ ⊢s σ ∶ Γ) (⊢τ : Δ′ ⊢s τ ∶ Δ) where
  private
    ⊢Δ  = proj₁ (presup-s ⊢σ)
    ⊢Γ  = proj₂ (presup-s ⊢σ)
    ⊢Δ′ = proj₁ (presup-s ⊢τ)

  q∘q-N : N ∺ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ N ∺ Γ
  q∘q-N = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ (N-wf 0 ⊢Γ) ⊢τwk
                                   (conv (vlookup ⊢NΔ′ here)
                                         (≈-trans (N-[] 0 ⊢wk) (≈-sym (≈-trans ([]-cong-Se′ (N-[] 0 ⊢σ) ⊢τwk) (N-[] 0 ⊢τwk))))) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) (N-wf 0 ⊢Γ)
                                    (≈-refl (conv (vlookup ⊢NΔ′ here) (≈-trans (N-[] 0 ⊢wk) (≈-sym (N-[] 0 (s-∘ ⊢wk (s-∘ ⊢τ ⊢σ))))))) ⟩
    q (σ ∘ τ)            ∎
    where open SR
          ⊢NΔ′ = ⊢∺ ⊢Δ′ (N-wf 0 ⊢Δ′)
          ⊢wk = s-wk ⊢NΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ


  q∘q : ∀ {i} → Γ ⊢ T ∶ Se i → (T [ σ ∘ τ ]) ∺ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ T ∺ Γ
  q∘q {T} {i} ⊢T = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ ⊢T ⊢τwk (conv (vlookup ⊢TΔ′ here) eq) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) ⊢T
                                    (≈-refl (conv (vlookup ⊢TΔ′ here) ([∘]-Se ⊢T ⊢στ ⊢wk))) ⟩
    q (σ ∘ τ)            ∎
    where ⊢στ = s-∘ ⊢τ ⊢σ
          ⊢TΔ′ = ⊢∺ ⊢Δ′ (t[σ]-Se ⊢T ⊢στ)
          ⊢wk  = s-wk ⊢TΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ
          eq : (T [ σ ∘ τ ]) ∺ Δ′ ⊢ T [ σ ∘ τ ] [ wk ] ≈ T [ σ ] [ τ ∘ wk ] ∶ Se i
          eq = let open ER in begin
            T [ σ ∘ τ ] [ wk ] ≈⟨ [∘]-Se ⊢T ⊢στ ⊢wk ⟩
            T [ σ ∘ τ ∘ wk ] ≈⟨ []-cong-Se″ ⊢T (∘-assoc ⊢σ ⊢τ ⊢wk) ⟩
            T [ σ ∘ (τ ∘ wk) ] ≈˘⟨ [∘]-Se ⊢T ⊢σ ⊢τwk ⟩
            T [ σ ] [ τ ∘ wk ] ∎

          open SR

N-E-helper-type : ⊩ T ∺ N ∺ Γ → Set
N-E-helper-type {T} {Γ} ⊩TNΓ@(⊩∺ {i = i} ⊩NΓ@(⊩∺ ⊩Γ _ _) _ gT) =
  ∀ {Δ s r σ ρ t a} →
  N ∺ Γ ⊢ T ∶ Se i →
  Γ ⊢ s ∶ T [| ze ] →
  T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
  (σ∼ρ : Δ ⊢s σ ∶ ⊩Γ ® ρ) →
  (gs : GluExp i Δ s (T [| ze ]) σ ρ) →
  (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩TNΓ ® ρ → GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ]) σ ρ) →
  (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
  let open GluExp gs hiding (T∈𝕌)
      open GluTyp (gT (cons-N ⊩NΓ σ∼ρ t∼a))
  in ∃ λ ra → rec∙ T , ⟦t⟧ , r , ρ , a ↘ ra
            × Δ ⊢ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t ∶ T [ σ , t ] ®[ i ] ra ∈El T∈𝕌


N-E-hepler : (⊩TNΓ : ⊩ T ∺ N ∺ Γ) →
             N-E-helper-type ⊩TNΓ
N-E-hepler {T} {Γ} ⊩TNΓ@(⊩∺ {i = i} ⊩NΓ@(⊩∺ ⊩Γ _ _) _ gT′) {Δ} {s} {r} {σ} {ρ} {_} {_}
           ⊢T ⊢s ⊢r σ∼ρ
           gs@record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } gr′ t∼a = recurse t∼a
  where rec′ : Exp → Exp
        rec′ t = rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) t
        ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ
        open NatTyping ⊢T ⊢σ
        ≈N   = ≈-sym (N-[] 0 ⊢σ)
        ⊢ze′ = conv (ze-I ⊢Δ) ≈N
        Γ⊢N  = N-wf 0 ⊢Γ

        gT : Δ ⊢ t ∶N® a ∈Nat → GluTyp i Δ T (σ , t) (ρ ↦ a)
        gT t∼a = gT′ (cons-N ⊩NΓ σ∼ρ t∼a)

        gr : (t∼a : Δ ⊢ t ∶N® a ∈Nat) →
              (let open GluTyp (gT t∼a) renaming (T∈𝕌 to T∈𝕌′) in Δ ⊢ t′ ∶ T [ σ , t ] ®[ i ] b ∈El T∈𝕌′) →
              GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ]) ((σ , t) , t′) (ρ ↦ a ↦ b)
        gr t∼a t′∼b = gr′ (s®-cons ⊩TNΓ (cons-N ⊩NΓ σ∼ρ t∼a) t′∼b)

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
          with gT t∼a
        ...  | record { ⟦T⟧ = ⟦T⟧′ ; ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ } = helper
          where ⊢t = ®Nat⇒∶Nat t∼a ⊢Δ

                helper : ∃ λ ra → rec∙ T , ⟦t⟧ , r , ρ , ↑ N c ↘ ra × Δ ⊢ rec′ t ∶ T [ σ , t ] ®[ i ] ra ∈El T∈𝕌′
                helper
                  with s®⇒⟦⟧ρ ⊩Γ σ∼ρ
                ... | ⊨Γ , ρ∈
                  = ↑ ⟦T⟧′ (rec T ⟦t⟧ r ρ c) , rec∙ ↘⟦T⟧′
                  , ®↓El⇒®El T∈𝕌′ record
                  { t∶T  = conv (N-E′ ⊢t) (≈-sym (gen-eq₃ ⊢t))
                  ; T∼A  = T∼⟦T⟧′
                  ; c∈⊥  = rec∈⊥
                  ; krip = krip′
                  }
                  where -- first step is to readback T
                        module Trb where

                          T-eval : ∀ ns (κ : UMoT) → ∃₂ λ A W → ⟦ T ⟧ ρ [ κ ] ↦ l′ N (head ns) ↘ A × Rty inc ns - A ↘ W
                          T-eval ns κ
                            with fundamental-⊢t ⊢T
                          ... | ⊨NΓ@(∺-cong ⊨Γ₁ evN) , _ , Trel = helper′
                            where ρ∈′ = subst (_∈′ ⟦ ⊨Γ₁ ⟧ρ) (sym (drop-↦ _ _)) (⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-mon ⊨Γ κ ρ∈))
                                  ρl∈ : ρ [ κ ] ↦ l′ N (head ns) ∈′ ⟦ ⊨NΓ ⟧ρ
                                  ρl∈ = ρ∈′ , l∈ (evN ρ∈′)
                                    where l∈ : (rt : RelTyp _ N _ N _) → l′ N (head ns) ∈′ El _ (RelTyp.T≈T′ rt)
                                          l∈ record { ↘⟦T⟧ = ⟦N⟧ ; T≈T′ = N } = ne (Bot-l (head ns))

                                  helper′ : ∃₂ λ A W → ⟦ T ⟧ ρ [ κ ] ↦ l′ N (head ns) ↘ A × Rty inc ns - A ↘ W
                                  helper′
                                    with Trel ρl∈
                                  ... | record { ↘⟦T⟧ = ⟦Se⟧ .i ; T≈T′ = U i< _ }
                                      , record { ⟦t⟧ = ⟦T⟧₁ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; t≈t′ = T≈T′₁ }
                                      rewrite 𝕌-wellfounded-≡-𝕌 _ i<
                                      with realizability-Rty T≈T′₁ (inc ns) vone
                                  ...    | W , ↘W , _
                                         rewrite D-ap-vone ⟦T⟧₁ = ⟦T⟧₁ , W , ↘⟦T⟧₁ , ↘W

                        -- second step is to readback s
                        module srb where
                          open _⊢_∶_®↑[_]_∈El_ (®El⇒®↑El T∈𝕌 t∼⟦t⟧) public

                          ↘⟦Ts⟧ : (κ : UMoT) → ⟦ T ⟧ ρ [ κ ] ↦ ze ↘ ⟦T⟧ [ κ ]
                          ↘⟦Ts⟧ κ
                            with ⟦⟧-mon κ ↘⟦T⟧
                          ...  | ↘⟦T⟧κ
                               rewrite ↦-mon ρ ze κ = ↘⟦T⟧κ

                        -- third step is to readback r
                        module rrb where

                          r-eval : ∀ ns (κ : UMoT) →
                                   let A , _ = Trb.T-eval ns κ in
                                   ∃₂ λ a A′ →
                                   ∃ λ w → ⟦ r ⟧ ρ [ κ ] ↦ l′ N (head ns) ↦ l′ A (suc (head ns)) ↘ a
                                         × ⟦ T ⟧ ρ [ κ ] ↦ su (l′ N (head ns)) ↘ A′
                                         × Rf (inc (inc ns)) - ↓ A′ a ↘ w
                          r-eval ns κ
                            with fundamental-⊢t ⊢r | Trb.T-eval ns κ
                          ...  | ⊨TNΓ@(∺-cong ⊨NΓ@(∺-cong ⊨Γ₁ evN) evT) , _ , rrel
                               | A , _ , ↘A , _ = helper′
                            where ρ∈′ = subst (_∈′ ⟦ ⊨Γ₁ ⟧ρ) (sym (drop-↦ _ _)) (⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-mon ⊨Γ κ ρ∈))

                                  ρl∈ : ρ [ κ ] ↦ l′ N (head ns) ∈′ ⟦ ⊨NΓ ⟧ρ
                                  ρl∈ = ρ∈′ , l∈ (evN ρ∈′)
                                    where l∈ : (rt : RelTyp _ N _ N _) → l′ N (head ns) ∈′ El _ (RelTyp.T≈T′ rt)
                                          l∈ record { ↘⟦T⟧ = ⟦N⟧ ; T≈T′ = N } = ne (Bot-l (head ns))
                                  ρl∈′ = subst (_∈′ ⟦ ⊨NΓ ⟧ρ) (sym (drop-↦ _ _)) ρl∈

                                  ρll∈ : ρ [ κ ] ↦ l′ N (head ns) ↦ l′ A (suc (head ns)) ∈′ ⟦ ⊨TNΓ ⟧ρ
                                  ρll∈ = ρl∈′ , l∈ (evT ρl∈′)
                                    where l∈ : (rt : RelTyp _ T _ T _) → l′ A (suc (head ns)) ∈′ El _ (RelTyp.T≈T′ rt)
                                          l∈ record { ⟦T⟧ = ⟦T⟧₁ ; ⟦T′⟧ = ⟦T′⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                                            with subst (⟦ T ⟧_↘ ⟦T⟧₁)  (drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ A (suc (head ns)))) ↘⟦T⟧₁
                                               | subst (⟦ T ⟧_↘ ⟦T′⟧₁) (drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ A (suc (head ns)))) ↘⟦T′⟧₁
                                          ...  | ↘⟦T⟧₁ | ↘⟦T′⟧₁
                                               rewrite ⟦⟧-det ↘⟦T⟧₁ ↘A
                                                     | ⟦⟧-det ↘⟦T′⟧₁ ↘A = realizability-Re T≈T′₁ (Bot-l (suc (head ns)))

                                  helper′ : ∃₂ λ a A′ →
                                            ∃ λ w → ⟦ r ⟧ ρ [ κ ] ↦ l′ N (head ns) ↦ l′ A (suc (head ns)) ↘ a
                                                  × ⟦ T ⟧ ρ [ κ ] ↦ su (l′ N (head ns)) ↘ A′
                                                  × Rf (inc (inc ns)) - ↓ A′ a ↘ w
                                  helper′
                                    with rrel ρll∈
                                  ...  | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                                       , record { ⟦t⟧ = ⟦t⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; t≈t′ = t≈t′ }
                                       rewrite drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ A (suc (head ns)))
                                             | drop-↦ (ρ [ κ ]) (l′ N (head ns))
                                             with realizability-Rf T≈T′ t≈t′ (inc (inc ns)) vone
                                  ...           | w , ↘w , _
                                                rewrite D-ap-vone ⟦t⟧
                                                      | D-ap-vone ⟦T⟧ = ⟦t⟧ , ⟦T⟧ , w , ↘⟦t⟧ , ↘⟦T⟧ , ↘w


                        rec∈⊥ : rec T ⟦t⟧ r ρ c ∈′ Bot
                        rec∈⊥ ns κ
                          with Trb.T-eval ns κ
                             | srb.a∈⊤ ns κ
                             | rrb.r-eval ns κ
                             | c∈ ns κ
                        ...  | A , W , ↘A , ↘W
                             | sw , ↘sw , _
                             | a , A′ , w , ↘a , ↘A′ , ↘w
                             | cu , ↘cu , _ = recne , ↘recne , ↘recne
                          where recne = rec W sw w cu
                                ↘recne : Re ns - rec T (⟦t⟧ [ κ ]) r (ρ [ κ ]) (c [ κ ]) ↘ recne
                                ↘recne = Rr ns ↘A ↘W (srb.↘⟦Ts⟧ κ) ↘sw ↘a ↘A′ ↘w ↘cu

                        krip′ : Δ′ ⊢r τ ∶ Δ → let u , _ = rec∈⊥ (map len Δ′) (mt τ) in Δ′ ⊢ rec′ t [ τ ] ≈ Ne⇒Exp u ∶ T [ σ , t ] [ τ ]
                        krip′ {Δ′} {τ} ⊢τ
                          with presup-s (⊢r⇒⊢s ⊢τ)
                        ...  | ⊢Δ′ , _
                          -- abstraction for the neutral term
                            with Trb.T-eval (map len Δ′) (mt τ)
                               | srb.a∈⊤ (map len Δ′) (mt τ)
                               | rrb.r-eval (map len Δ′) (mt τ)
                               | c∈ (map len Δ′) (mt τ)
                               | srb.krip ⊢τ
                               | rel ⊢τ
                        ...    | A , W , ↘A , ↘W
                               | sw , ↘sw , _
                               | a , A′ , w , ↘a , ↘A′ , ↘w
                               | cu , ↘cu , _
                               | eqs | eqc = eq
                          where ⊢τ′      = ⊢r⇒⊢s ⊢τ
                                open NatTyping ⊢Tqσ ⊢τ′
                                  using ()
                                  renaming ( ⊢NΔ    to ⊢NΔ′
                                           ; ⊢qσ    to ⊢qτ
                                           ; ⊢Tqσ   to ⊢Tqσqτ
                                           ; ⊢TqσNΔ to ⊢TqστNΔ′)

                                ⊢qτqσ     = s-∘ ⊢qτ ⊢qσ
                                ⊢Tqσqτ′   = t[σ]-Se ⊢T ⊢qτqσ
                                ⊢TqσqτNΔ′ = ⊢∺ ⊢NΔ′ ⊢Tqσqτ′


                                qσqτ∼ρτl : N ∺ Δ′ ⊢s q σ ∘ q τ ∶ ⊩NΓ ® ρ [ mt τ ] ↦ l′ N (len (head Δ′))
                                qσqτ∼ρτl
                                  with v0®x N (N-≈ 0 ⊢Δ′) | s®-mon ⊩Γ ⊢τ σ∼ρ
                                ...  | v0∼l , _ | στ∼ρτ
                                     with s®-mon ⊩Γ (⊢rwk ⊢NΔ′) στ∼ρτ
                                ...     | qστ∼ρτl
                                        rewrite ρ-ap-vone (ρ [ mt τ ]) = s®-resp-s≈ ⊩NΓ (cons-N ⊩NΓ qστ∼ρτl v0∼l) (s-≈-sym (q∘q-N ⊢σ ⊢τ′))

                                qqσqqτ∼ρτll : (T [ q σ ∘ q τ ]) ∺ N ∺ Δ′ ⊢s q (q σ) ∘ q (q τ) ∶ ⊩TNΓ ® ρ [ mt τ ] ↦ l′ N (len (head Δ′)) ↦ l′ (GluTyp.⟦T⟧ (gT′ qσqτ∼ρτl)) (suc (len (head Δ′)))
                                qqσqqτ∼ρτll
                                  with s®-mon ⊩NΓ (⊢rwk ⊢TqσqτNΔ′) qσqτ∼ρτl
                                ...  | qσqτwk∼ρτl
                                     rewrite ρ-ap-vone (ρ [ mt τ ] ↦ l′ N (len (head Δ′)))
                                     with  gT′ qσqτwk∼ρτl | gT′ qσqτ∼ρτl | s®-cons ⊩TNΓ {a = l′ (GluTyp.⟦T⟧ (gT′ qσqτ∼ρτl)) (suc (len (head Δ′)))} qσqτwk∼ρτl
                                ...     | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T∈𝕌 = T∈𝕌₁ ; T∼⟦T⟧ = T∼⟦T⟧₁ }
                                        | record { ↘⟦T⟧ = ↘⟦T⟧  ; T∈𝕌 = T∈𝕌  ; T∼⟦T⟧ = T∼⟦T⟧ }
                                        | cons
                                        rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = s®-resp-s≈ ⊩TNΓ
                                                                               (cons (®El-one-sided T∈𝕌 T∈𝕌₁ (®El-resp-T≈ T∈𝕌 (v0®x _ T∼⟦T⟧) ([∘]-Se ⊢T ⊢qτqσ (s-wk ⊢TqσqτNΔ′)))))
                                                                               (s-≈-sym (q∘q ⊢qσ ⊢qτ ⊢T))

                                eq : Δ′ ⊢ rec′ t [ τ ] ≈ rec (Nf⇒Exp W) (Nf⇒Exp sw) (Nf⇒Exp w) (Ne⇒Exp cu) ∶ T [ σ , t ] [ τ ]
                                eq
                                  with gT′ qσqτ∼ρτl | gr′ qqσqqτ∼ρτll
                                ...  | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
                                     | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧′ ; ↘⟦t⟧ = ↘⟦t⟧′ ; T∈𝕌 = T∈𝕌′ ; t∼⟦t⟧ = t∼⟦t⟧ }
                                     rewrite drop-↦ (ρ [ mt τ ] ↦ l′ N (len (head Δ′))) (l′ ⟦T⟧ (suc (len (head Δ′))))
                                           | drop-↦ (ρ [ mt τ ]) (l′ N (len (head Δ′)))
                                           | ⟦⟧-det ↘⟦T⟧′ ↘A′
                                           | ⟦⟧-det ↘⟦T⟧ ↘A
                                           | ⟦⟧-det ↘⟦t⟧′ ↘a
                                           with ®⇒®↑ T∈𝕌 T∼⟦T⟧ | ®El⇒®↑El T∈𝕌′ t∼⟦t⟧
                                ...           | record { A∈⊤ = A∈⊤ ; krip = krip }
                                              | record { T∼A = T∼A ; a∈⊤ = a∈⊤ ; krip = krip′ }
                                              with A∈⊤ (inc (map len Δ′)) vone | krip (⊢rI ⊢NΔ′)
                                                 | a∈⊤ (inc (inc (map len Δ′))) vone | krip′ (⊢rI ⊢TqσqτNΔ′)
                                ...              | _ , ↘B , _ | eq₁
                                                 | _ , ↘w′ , _ | eq₂
                                                 rewrite D-ap-vone A
                                                       | D-ap-vone A′
                                                       | D-ap-vone a
                                                       | Rty-det ↘B ↘W
                                                       | Rf-det ↘w′ ↘w = {!!}


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
