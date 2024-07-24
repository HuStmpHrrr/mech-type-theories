{-# OPTIONS --without-K --safe #-}

-- Full formulation and Concise formulation are equivalent.
module MLTT.Statics.Equiv where

open import Lib
open import MLTT.Statics.Full as F
open import MLTT.Statics.Concise as C
open import MLTT.Statics.CtxEquiv
open import MLTT.Statics.Presup
open import MLTT.Statics.Misc
open import MLTT.Statics.Properties.Pi

mutual
  F⇒C-⊢ : F.⊢ Γ →
          -------
          C.⊢ Γ
  F⇒C-⊢ ⊢[]        = ⊢[]
  F⇒C-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (F⇒C-⊢ ⊢Γ) (F⇒C-tm ⊢T)


  F⇒C-tm : Γ F.⊢ t ∶ T →
           -------------
           Γ C.⊢ t ∶ T
  F⇒C-tm (N-wf i ⊢Γ)         = N-wf i (F⇒C-⊢ ⊢Γ)
  F⇒C-tm (Se-wf i ⊢Γ)        = Se-wf i (F⇒C-⊢ ⊢Γ)
  F⇒C-tm (Π-wf ⊢S ⊢T)        = Π-wf (F⇒C-tm ⊢S) (F⇒C-tm ⊢T)
  F⇒C-tm (vlookup ⊢Γ T∈Γ)    = vlookup (F⇒C-⊢ ⊢Γ) T∈Γ
  F⇒C-tm (ze-I ⊢Γ)           = ze-I (F⇒C-⊢ ⊢Γ)
  F⇒C-tm (su-I ⊢t)           = su-I (F⇒C-tm ⊢t)
  F⇒C-tm (N-E ⊢T ⊢s ⊢r ⊢t)   = N-E (F⇒C-tm ⊢T) (F⇒C-tm ⊢s) (F⇒C-tm ⊢r) (F⇒C-tm ⊢t)
  F⇒C-tm (Λ-I _ ⊢t)          = Λ-I (F⇒C-tm ⊢t)
  F⇒C-tm (Λ-E _ _ ⊢t ⊢r)     = Λ-E (F⇒C-tm ⊢t) (F⇒C-tm ⊢r)
  F⇒C-tm (t[σ] ⊢t ⊢σ)        = t[σ] (F⇒C-tm ⊢t) (F⇒C-s ⊢σ)
  F⇒C-tm (cumu ⊢t)           = cumu (F⇒C-tm ⊢t)
  F⇒C-tm (conv ⊢t T≈T′)      = conv (F⇒C-tm ⊢t) (F⇒C-≈ T≈T′)


  F⇒C-s : Γ F.⊢s σ ∶ Δ →
          --------------
          Γ C.⊢s σ ∶ Δ
  F⇒C-s (s-I ⊢Γ)           = s-I (F⇒C-⊢ ⊢Γ)
  F⇒C-s (s-wk ⊢Γ)          = s-wk (F⇒C-⊢ ⊢Γ)
  F⇒C-s (s-∘ ⊢σ ⊢δ)        = s-∘ (F⇒C-s ⊢σ) (F⇒C-s ⊢δ)
  F⇒C-s (s-, ⊢σ ⊢T ⊢t)     = s-, (F⇒C-s ⊢σ) (F⇒C-tm ⊢T) (F⇒C-tm ⊢t)
  F⇒C-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (F⇒C-s ⊢σ) (F⇒C-⊢≈ Δ′≈Δ)


  F⇒C-⊢≈ : F.⊢ Γ ≈ Δ →
           -----------
           C.⊢ Γ ≈ Δ
  F⇒C-⊢≈ []-≈                    = []-≈
  F⇒C-⊢≈ (∷-cong Γ≈Δ _ _ T≈T′ _) = ∷-cong (F⇒C-⊢≈ Γ≈Δ) (F⇒C-≈ T≈T′)


  F⇒C-≈ : Γ F.⊢ t ≈ t′ ∶ T →
          ------------------
          Γ C.⊢ t ≈ t′ ∶ T
  F⇒C-≈ (N-[] i ⊢σ)                       = N-[] i (F⇒C-s ⊢σ)
  F⇒C-≈ (Se-[] i ⊢σ)                      = Se-[] i (F⇒C-s ⊢σ)
  F⇒C-≈ (Π-[] ⊢σ ⊢S ⊢T)                   = Π-[] (F⇒C-s ⊢σ) (F⇒C-tm ⊢S) (F⇒C-tm ⊢T)
  F⇒C-≈ (Π-cong ⊢S S≈S′ T≈T′)             = Π-cong (F⇒C-≈ S≈S′) (F⇒C-≈ T≈T′)
  F⇒C-≈ (v-≈ ⊢Γ T∈Γ)                      = v-≈ (F⇒C-⊢ ⊢Γ) T∈Γ
  F⇒C-≈ (ze-≈ ⊢Γ)                         = ze-≈ (F⇒C-⊢ ⊢Γ)
  F⇒C-≈ (su-cong t≈t′)                    = su-cong (F⇒C-≈ t≈t′)
  F⇒C-≈ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′) = rec-cong (F⇒C-≈ T≈T′) (F⇒C-≈ s≈s′) (F⇒C-≈ r≈r′) (F⇒C-≈ t≈t′)
  F⇒C-≈ (Λ-cong ⊢S t≈t′)                  = Λ-cong (F⇒C-≈ t≈t′)
  F⇒C-≈ ($-cong _ _ t≈t′ r≈r′)            = $-cong (F⇒C-≈ t≈t′) (F⇒C-≈ r≈r′)
  F⇒C-≈ ([]-cong t≈t′ σ≈σ′)               = []-cong (F⇒C-≈ t≈t′) (F⇒C-s-≈ σ≈σ′)
  F⇒C-≈ (ze-[] ⊢σ)                        = ze-[] (F⇒C-s ⊢σ)
  F⇒C-≈ (su-[] ⊢σ ⊢t)                     = su-[] (F⇒C-s ⊢σ) (F⇒C-tm ⊢t)
  F⇒C-≈ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)           = rec-[] (F⇒C-s ⊢σ) (F⇒C-tm ⊢T) (F⇒C-tm ⊢s) (F⇒C-tm ⊢r) (F⇒C-tm ⊢t)
  F⇒C-≈ (Λ-[] ⊢σ ⊢t)                      = Λ-[] (F⇒C-s ⊢σ) (F⇒C-tm ⊢t)
  F⇒C-≈ ($-[] _ _ ⊢σ ⊢t ⊢s)               = $-[] (F⇒C-s ⊢σ) (F⇒C-tm ⊢t) (F⇒C-tm ⊢s)
  F⇒C-≈ (rec-β-ze ⊢T ⊢s ⊢r)               = rec-β-ze (F⇒C-tm ⊢T) (F⇒C-tm ⊢s) (F⇒C-tm ⊢r)
  F⇒C-≈ (rec-β-su ⊢T ⊢s ⊢r ⊢t)            = rec-β-su (F⇒C-tm ⊢T) (F⇒C-tm ⊢s) (F⇒C-tm ⊢r) (F⇒C-tm ⊢t)
  F⇒C-≈ (Λ-β _ _ ⊢t ⊢s)                   = Λ-β (F⇒C-tm ⊢t) (F⇒C-tm ⊢s)
  F⇒C-≈ (Λ-η _ _ ⊢t)                      = Λ-η (F⇒C-tm ⊢t)
  F⇒C-≈ ([I] ⊢t)                          = [I] (F⇒C-tm ⊢t)
  F⇒C-≈ ([wk] ⊢SΓ T∈Γ)                    = [wk] (F⇒C-⊢ ⊢SΓ) T∈Γ
  F⇒C-≈ ([∘] ⊢δ ⊢σ ⊢t)                    = [∘] (F⇒C-s ⊢δ) (F⇒C-s ⊢σ) (F⇒C-tm ⊢t)
  F⇒C-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)               = [,]-v-ze (F⇒C-s ⊢σ) (F⇒C-tm ⊢S) (F⇒C-tm ⊢t)
  F⇒C-≈ ([,]-v-su ⊢σ ⊢S ⊢t T∈Δ)           = [,]-v-su (F⇒C-s ⊢σ) (F⇒C-tm ⊢S) (F⇒C-tm ⊢t) T∈Δ
  F⇒C-≈ (≈-cumu t≈t′)                     = ≈-cumu (F⇒C-≈ t≈t′)
  F⇒C-≈ (≈-conv t≈t′ S≈T)                 = ≈-conv (F⇒C-≈ t≈t′) (F⇒C-≈ S≈T)
  F⇒C-≈ (≈-sym t≈t′)                      = ≈-sym (F⇒C-≈ t≈t′)
  F⇒C-≈ (≈-trans t≈t′ t′≈t″)              = ≈-trans (F⇒C-≈ t≈t′) (F⇒C-≈ t′≈t″)


  F⇒C-s-≈ : Γ F.⊢s σ ≈ σ′ ∶ Δ →
            ------------------
            Γ C.⊢s σ ≈ σ′ ∶ Δ
  F⇒C-s-≈ (I-≈ ⊢Γ)                = I-≈ (F⇒C-⊢ ⊢Γ)
  F⇒C-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (F⇒C-⊢ ⊢TΓ)
  F⇒C-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (F⇒C-s-≈ σ≈σ′) (F⇒C-s-≈ δ≈δ′)
  F⇒C-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (F⇒C-s-≈ σ≈σ′) (F⇒C-tm ⊢T) (F⇒C-≈ t≈t′)
  F⇒C-s-≈ (I-∘ ⊢σ)                = I-∘ (F⇒C-s ⊢σ)
  F⇒C-s-≈ (∘-I ⊢σ)                = ∘-I (F⇒C-s ⊢σ)
  F⇒C-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (F⇒C-s ⊢σ) (F⇒C-s ⊢σ′) (F⇒C-s ⊢σ″)
  F⇒C-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (F⇒C-s ⊢σ) (F⇒C-tm ⊢T) (F⇒C-tm ⊢t) (F⇒C-s ⊢δ)
  F⇒C-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (F⇒C-s ⊢σ) (F⇒C-tm ⊢T) (F⇒C-tm ⊢t)
  F⇒C-s-≈ (,-ext ⊢σ)              = ,-ext (F⇒C-s ⊢σ)
  F⇒C-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (F⇒C-s-≈ σ≈σ′)
  F⇒C-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (F⇒C-s-≈ σ≈σ′) (F⇒C-s-≈ σ′≈σ″)
  F⇒C-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (F⇒C-s-≈ σ≈σ′) (F⇒C-⊢≈ Δ′≈Δ)


mutual
  C⇒F-⊢ : C.⊢ Γ →
          -------
          F.⊢ Γ
  C⇒F-⊢ ⊢[]        = ⊢[]
  C⇒F-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T)


  C⇒F-tm : Γ C.⊢ t ∶ T →
           -------------
           Γ F.⊢ t ∶ T
  C⇒F-tm (N-wf i ⊢Γ)                              = N-wf i (C⇒F-⊢ ⊢Γ)
  C⇒F-tm (Se-wf i ⊢Γ)                             = Se-wf i (C⇒F-⊢ ⊢Γ)
  C⇒F-tm (Π-wf ⊢S ⊢T)                             = Π-wf (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
  C⇒F-tm (vlookup ⊢Γ T∈Γ)                         = vlookup (C⇒F-⊢ ⊢Γ) T∈Γ
  C⇒F-tm (ze-I ⊢Γ)                                = ze-I (C⇒F-⊢ ⊢Γ)
  C⇒F-tm (su-I ⊢t)                                = su-I (C⇒F-tm ⊢t)
  C⇒F-tm (N-E ⊢T ⊢s ⊢r ⊢t)                        = N-E (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
  C⇒F-tm (Λ-I ⊢t)
    with ⊢∷ ⊢Γ ⊢S ← proj₁ (presup-tm (C⇒F-tm ⊢t)) = Λ-I ⊢S (C⇒F-tm ⊢t)
  C⇒F-tm (Λ-E ⊢t ⊢r)
    with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)       = Λ-E (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t) (C⇒F-tm ⊢r)
  C⇒F-tm (t[σ] ⊢t ⊢σ)                             = t[σ] (C⇒F-tm ⊢t) (C⇒F-s ⊢σ)
  C⇒F-tm (cumu ⊢t)                                = cumu (C⇒F-tm ⊢t)
  C⇒F-tm (conv ⊢t T≈T′)                           = conv (C⇒F-tm ⊢t) (C⇒F-≈ T≈T′)


  C⇒F-s : Γ C.⊢s σ ∶ Δ →
          --------------
          Γ F.⊢s σ ∶ Δ
  C⇒F-s (s-I ⊢Γ)           = s-I (C⇒F-⊢ ⊢Γ)
  C⇒F-s (s-wk ⊢TΓ)         = s-wk (C⇒F-⊢ ⊢TΓ)
  C⇒F-s (s-∘ ⊢σ ⊢δ)        = s-∘ (C⇒F-s ⊢σ) (C⇒F-s ⊢δ)
  C⇒F-s (s-, ⊢σ ⊢T ⊢t)     = s-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
  C⇒F-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (C⇒F-s ⊢σ) (C⇒F-⊢≈ Δ′≈Δ)


  C⇒F-⊢≈ : C.⊢ Γ ≈ Δ →
           -----------
           F.⊢ Γ ≈ Δ
  C⇒F-⊢≈ []-≈                                        = []-≈
  C⇒F-⊢≈ (∷-cong Γ≈Δ T≈T′)
    with T≈T′₁ ← ctxeq-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-≈ T≈T′)
       with _ , ⊢T , _       ← presup-≈ (C⇒F-≈ T≈T′)
          | _ , _  , ⊢T′ , _ ← presup-≈ T≈T′₁        = ∷-cong (C⇒F-⊢≈ Γ≈Δ) ⊢T ⊢T′ (C⇒F-≈ T≈T′) T≈T′₁


  C⇒F-≈ : Γ C.⊢ t ≈ t′ ∶ T →
          ------------------
          Γ F.⊢ t ≈ t′ ∶ T
  C⇒F-≈ (N-[] i ⊢σ)                                 = N-[] i (C⇒F-s ⊢σ)
  C⇒F-≈ (Se-[] i ⊢σ)                                = Se-[] i (C⇒F-s ⊢σ)
  C⇒F-≈ (Π-[] ⊢σ ⊢S ⊢T)                             = Π-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
  C⇒F-≈ (Π-cong S≈S′ T≈T′)
    with _ , ⊢S , _ ← presup-≈ (C⇒F-≈ S≈S′)         = Π-cong ⊢S (C⇒F-≈ S≈S′) (C⇒F-≈ T≈T′)
  C⇒F-≈ (v-≈ ⊢Γ T∈Γ)                                = v-≈ (C⇒F-⊢ ⊢Γ) T∈Γ
  C⇒F-≈ (ze-≈ ⊢Γ)                                   = ze-≈ (C⇒F-⊢ ⊢Γ)
  C⇒F-≈ (su-cong t≈t′)                              = su-cong (C⇒F-≈ t≈t′)
  C⇒F-≈ (rec-cong T≈T′ s≈s′ r≈r′ t≈t′)
    with _ , ⊢T , _ ← presup-≈ (C⇒F-≈ T≈T′)         = rec-cong ⊢T (C⇒F-≈ T≈T′) (C⇒F-≈ s≈s′) (C⇒F-≈ r≈r′) (C⇒F-≈ t≈t′)
  C⇒F-≈ (Λ-cong t≈t′)
    with ⊢∷ ⊢Γ ⊢S , _ ← presup-≈ (C⇒F-≈ t≈t′)       = Λ-cong ⊢S (C⇒F-≈ t≈t′)
  C⇒F-≈ ($-cong t≈t′ r≈r′)
    with _ , _ , _ , _ , ⊢Π ← presup-≈ (C⇒F-≈ t≈t′) = $-cong (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-≈ t≈t′) (C⇒F-≈ r≈r′)
  C⇒F-≈ ([]-cong t≈t′ σ≈σ′)                         = []-cong (C⇒F-≈ t≈t′) (C⇒F-s-≈ σ≈σ′)
  C⇒F-≈ (ze-[] ⊢σ)                                  = ze-[] (C⇒F-s ⊢σ)
  C⇒F-≈ (su-[] ⊢σ ⊢t)                               = su-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
  C⇒F-≈ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)                     = rec-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
  C⇒F-≈ (Λ-[] ⊢σ ⊢t)                                = Λ-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
  C⇒F-≈ ($-[] ⊢σ ⊢t ⊢s)
    with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = $-[] (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
  C⇒F-≈ (rec-β-ze ⊢T ⊢s ⊢r)                         = rec-β-ze (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r)
  C⇒F-≈ (rec-β-su ⊢T ⊢s ⊢r ⊢t)                      = rec-β-su (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
  C⇒F-≈ (Λ-β ⊢t ⊢s)
    with ⊢∷ ⊢Γ ⊢S , _ , ⊢T ← presup-tm (C⇒F-tm ⊢t)  = Λ-β (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
  C⇒F-≈ (Λ-η ⊢t)
    with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = Λ-η (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t)
  C⇒F-≈ ([I] ⊢t)                                    = [I] (C⇒F-tm ⊢t)
  C⇒F-≈ ([wk] ⊢SΓ T∈Γ)                              = [wk] (C⇒F-⊢ ⊢SΓ) T∈Γ
  C⇒F-≈ ([∘] ⊢δ ⊢σ ⊢t)                              = [∘] (C⇒F-s ⊢δ) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
  C⇒F-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)                         = [,]-v-ze (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t)
  C⇒F-≈ ([,]-v-su ⊢σ ⊢S ⊢t T∈Δ)                     = [,]-v-su (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t) T∈Δ
  C⇒F-≈ (≈-cumu t≈t′)                               = ≈-cumu (C⇒F-≈ t≈t′)
  C⇒F-≈ (≈-conv t≈t′ S≈T)                           = ≈-conv (C⇒F-≈ t≈t′) (C⇒F-≈ S≈T)
  C⇒F-≈ (≈-sym t≈t′)                                = ≈-sym (C⇒F-≈ t≈t′)
  C⇒F-≈ (≈-trans t≈t′ t′≈t″)                        = ≈-trans (C⇒F-≈ t≈t′) (C⇒F-≈ t′≈t″)


  C⇒F-s-≈ : Γ C.⊢s σ ≈ σ′ ∶ Δ →
            ------------------
            Γ F.⊢s σ ≈ σ′ ∶ Δ
  C⇒F-s-≈ (I-≈ ⊢Γ)                = I-≈ (C⇒F-⊢ ⊢Γ)
  C⇒F-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (C⇒F-⊢ ⊢TΓ)
  C⇒F-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ δ≈δ′)
  C⇒F-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-tm ⊢T) (C⇒F-≈ t≈t′)
  C⇒F-s-≈ (I-∘ ⊢σ)                = I-∘ (C⇒F-s ⊢σ)
  C⇒F-s-≈ (∘-I ⊢σ)                = ∘-I (C⇒F-s ⊢σ)
  C⇒F-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (C⇒F-s ⊢σ) (C⇒F-s ⊢σ′) (C⇒F-s ⊢σ″)
  C⇒F-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t) (C⇒F-s ⊢δ)
  C⇒F-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
  C⇒F-s-≈ (,-ext ⊢σ)              = ,-ext (C⇒F-s ⊢σ)
  C⇒F-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (C⇒F-s-≈ σ≈σ′)
  C⇒F-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ σ′≈σ″)
  C⇒F-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (C⇒F-s-≈ σ≈σ′) (C⇒F-⊢≈ Δ′≈Δ)
