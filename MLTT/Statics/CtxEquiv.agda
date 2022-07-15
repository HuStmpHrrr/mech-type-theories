{-# OPTIONS --without-K --safe #-}

-- If ⊢ Γ ≈ Δ and Γ ⊢ 𝒥 for any judgment 𝒥, then Δ ⊢ 𝒥
module MLTT.Statics.CtxEquiv where

open import Lib

open import MLTT.Statics.Full
open import MLTT.Statics.Refl
open import MLTT.Statics.Misc
open import MLTT.Statics.Properties.Contexts

mutual
  ctxeq-tm : ⊢ Γ ≈ Δ →
             Γ ⊢ t ∶ T →
             -----------
             Δ ⊢ t ∶ T
  ctxeq-tm Γ≈Δ (N-wf i _)        = N-wf i (proj₂ (presup-⊢≈ Γ≈Δ))
  ctxeq-tm Γ≈Δ (Se-wf i _)       = Se-wf i (proj₂ (presup-⊢≈ Γ≈Δ))
  ctxeq-tm Γ≈Δ (Π-wf ⊢S ⊢T)      = Π-wf (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢T)
  ctxeq-tm Γ≈Δ (vlookup ⊢Γ T∈Γ)
    with ∈!⇒ty≈ Γ≈Δ T∈Γ
  ...  | _ , T′∈Δ , _ , _ , T≈T′ = conv (vlookup (proj₂ (presup-⊢≈ Γ≈Δ)) T′∈Δ) (≈-sym T≈T′)
  ctxeq-tm Γ≈Δ (ze-I _)          = ze-I (proj₂ (presup-⊢≈ Γ≈Δ))
  ctxeq-tm Γ≈Δ (su-I ⊢t)         = su-I (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-tm Γ≈Δ (N-E ⊢T ⊢s ⊢r ⊢t)
    with presup-⊢≈ Γ≈Δ
  ...  | ⊢Γ , ⊢Δ                 = N-E (ctxeq-tm NΓ≈NΔ ⊢T)
                                       (ctxeq-tm Γ≈Δ ⊢s)
                                       (ctxeq-tm (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) ⊢r)
                                       (ctxeq-tm Γ≈Δ ⊢t)
    where NΓ≈NΔ                  = ∷-cong Γ≈Δ (N-wf 0 ⊢Γ) (N-wf 0 ⊢Δ) (≈-refl (N-wf 0 ⊢Γ)) (≈-refl (N-wf 0 ⊢Δ))
  ctxeq-tm Γ≈Δ (Λ-I ⊢S ⊢t)       = Λ-I (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢t)
  ctxeq-tm Γ≈Δ (Λ-E ⊢S ⊢T ⊢t ⊢s) = Λ-E ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm Γ≈Δ ⊢t) (ctxeq-tm Γ≈Δ ⊢s)
    where ⊢S′                    = ctxeq-tm Γ≈Δ ⊢S
  ctxeq-tm Γ≈Δ (t[σ] ⊢t ⊢σ)      = t[σ] ⊢t (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-tm Γ≈Δ (cumu ⊢t)         = cumu (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-tm Γ≈Δ (conv ⊢t T≈T′)    = conv (ctxeq-tm Γ≈Δ ⊢t) (ctxeq-≈ Γ≈Δ T≈T′)


  ctxeq-≈ : ⊢ Γ ≈ Δ →
            Γ ⊢ t ≈ t′ ∶ T →
            -----------------
            Δ ⊢ t ≈ t′ ∶ T
  ctxeq-≈ Γ≈Δ (N-[] i ⊢σ)              = N-[] i (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-≈ Γ≈Δ (Se-[] i ⊢σ)             = Se-[] i (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-≈ Γ≈Δ (Π-[] ⊢σ ⊢S ⊢T)          = Π-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢S ⊢T
  ctxeq-≈ Γ≈Δ (Π-cong ⊢S S≈S′ T≈T′)    = Π-cong (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-≈ Γ≈Δ S≈S′) (ctxeq-≈ (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) T≈T′)
  ctxeq-≈ Γ≈Δ (v-≈ ⊢Γ T∈Γ)
    with ∈!⇒ty≈ Γ≈Δ T∈Γ
  ...  | _ , T′∈Δ , _ , _ , T≈T′       = ≈-refl (conv (vlookup (proj₂ (presup-⊢≈ Γ≈Δ)) T′∈Δ) (≈-sym T≈T′))
  ctxeq-≈ Γ≈Δ (ze-≈ _)                 = ze-≈ (proj₂ (presup-⊢≈ Γ≈Δ))
  ctxeq-≈ Γ≈Δ (su-cong t≈t′)           = su-cong (ctxeq-≈ Γ≈Δ t≈t′)
  ctxeq-≈ Γ≈Δ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′)
    with presup-⊢≈ Γ≈Δ
  ...  | ⊢Γ , ⊢Δ                       = rec-cong (ctxeq-tm NΓ≈NΔ ⊢T)
                                                  (ctxeq-≈ NΓ≈NΔ T≈T′)
                                                  (ctxeq-≈ Γ≈Δ s≈s′)
                                                  (ctxeq-≈ (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) r≈r′)
                                                  (ctxeq-≈ Γ≈Δ t≈t′)
    where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf 0 ⊢Γ) (N-wf 0 ⊢Δ) (≈-refl (N-wf 0 ⊢Γ)) (≈-refl (N-wf 0 ⊢Δ))
  ctxeq-≈ Γ≈Δ (Λ-cong ⊢S t≈t′)         = Λ-cong (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-≈ (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) t≈t′)
  ctxeq-≈ Γ≈Δ ($-cong ⊢S ⊢T t≈t′ s≈s′) = $-cong ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ s≈s′)
    where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
  ctxeq-≈ Γ≈Δ ([]-cong t≈t′ σ≈σ′)      = []-cong t≈t′ (ctxeq-s-≈ Γ≈Δ σ≈σ′)
  ctxeq-≈ Γ≈Δ (ze-[] ⊢σ)               = ze-[] (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-≈ Γ≈Δ (su-[] ⊢σ ⊢t)            = su-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢t
  ctxeq-≈ Γ≈Δ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)  = rec-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢T ⊢s ⊢r ⊢t
  ctxeq-≈ Γ≈Δ (Λ-[] ⊢σ ⊢t)             = Λ-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢t
  ctxeq-≈ Γ≈Δ ($-[] ⊢S ⊢T ⊢σ ⊢t ⊢s)    = $-[] ⊢S ⊢T (ctxeq-s Γ≈Δ ⊢σ) ⊢t ⊢s
  ctxeq-≈ Γ≈Δ (rec-β-ze ⊢T ⊢s ⊢r)
    with presup-⊢≈ Γ≈Δ
  ...  | ⊢Γ , ⊢Δ                       = rec-β-ze (ctxeq-tm NΓ≈NΔ ⊢T)
                                                  (ctxeq-tm Γ≈Δ ⊢s)
                                                  (ctxeq-tm (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) ⊢r)
    where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf 0 ⊢Γ) (N-wf 0 ⊢Δ) (≈-refl (N-wf 0 ⊢Γ)) (≈-refl (N-wf 0 ⊢Δ))
  ctxeq-≈ Γ≈Δ (rec-β-su ⊢T ⊢s ⊢r ⊢t)
    with presup-⊢≈ Γ≈Δ
  ...  | ⊢Γ , ⊢Δ                       = rec-β-su (ctxeq-tm NΓ≈NΔ ⊢T)
                                                  (ctxeq-tm Γ≈Δ ⊢s)
                                                  (ctxeq-tm (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) ⊢r)
                                                  (ctxeq-tm Γ≈Δ ⊢t)
    where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf 0 ⊢Γ) (N-wf 0 ⊢Δ) (≈-refl (N-wf 0 ⊢Γ)) (≈-refl (N-wf 0 ⊢Δ))
  ctxeq-≈ Γ≈Δ (Λ-β ⊢S ⊢T ⊢t ⊢s)        = Λ-β ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢t) (ctxeq-tm Γ≈Δ ⊢s)
    where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
  ctxeq-≈ Γ≈Δ (Λ-η ⊢S ⊢T ⊢t)           = Λ-η ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm Γ≈Δ ⊢t)
    where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
  ctxeq-≈ Γ≈Δ ([I] ⊢t)                 = [I] (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-≈ (∷-cong Γ≈Δ _ ⊢T′ _ _) ([wk] ⊢Γ T∈Γ)
    with ∈!⇒ty≈ Γ≈Δ T∈Γ | presup-⊢≈ Γ≈Δ
  ...  | _ , T′∈Δ , _ , _ , T≈T′
       | _ , ⊢Δ                        = ≈-conv ([wk] (⊢∷ ⊢Δ ⊢T′) T′∈Δ) ([]-cong-Se′ (≈-sym T≈T′) (s-wk (⊢∷ ⊢Δ ⊢T′)))
  ctxeq-≈ Γ≈Δ ([∘] ⊢δ ⊢σ ⊢t)           = [∘] (ctxeq-s Γ≈Δ ⊢δ) ⊢σ ⊢t
  ctxeq-≈ Γ≈Δ ([,]-v-ze ⊢σ ⊢S ⊢t)      = [,]-v-ze (ctxeq-s Γ≈Δ ⊢σ) ⊢S (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-≈ Γ≈Δ ([,]-v-su ⊢σ ⊢S ⊢s T∈Γ′) = [,]-v-su (ctxeq-s Γ≈Δ ⊢σ) ⊢S (ctxeq-tm Γ≈Δ ⊢s) T∈Γ′
  ctxeq-≈ Γ≈Δ (≈-cumu t≈t′)            = ≈-cumu (ctxeq-≈ Γ≈Δ t≈t′)
  ctxeq-≈ Γ≈Δ (≈-conv t≈t′ T≈T′)       = ≈-conv (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ T≈T′)
  ctxeq-≈ Γ≈Δ (≈-sym t≈t′)             = ≈-sym (ctxeq-≈ Γ≈Δ t≈t′)
  ctxeq-≈ Γ≈Δ (≈-trans t≈t′ t′≈t″)     = ≈-trans (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ t′≈t″)


  ctxeq-s : ⊢ Γ ≈ Δ →
            Γ ⊢s σ ∶ Γ′ →
            -----------
            Δ ⊢s σ ∶ Γ′
  ctxeq-s Γ≈Δ (s-I _)                        = s-conv (s-I (proj₂ (presup-⊢≈ Γ≈Δ))) (⊢≈-sym Γ≈Δ)
  ctxeq-s ⊢≈@(∷-cong Γ≈Δ _ _ _ _) (s-wk ⊢TΓ) = s-conv (s-wk (proj₂ (presup-⊢≈ ⊢≈))) (⊢≈-sym Γ≈Δ)
  ctxeq-s Γ≈Δ (s-∘ ⊢σ ⊢δ)                    = s-∘ (ctxeq-s Γ≈Δ ⊢σ) ⊢δ
  ctxeq-s Γ≈Δ (s-, ⊢σ ⊢T ⊢t)                 = s-, (ctxeq-s Γ≈Δ ⊢σ) ⊢T (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-s Γ≈Δ (s-conv ⊢σ Γ″≈Γ′)              = s-conv (ctxeq-s Γ≈Δ ⊢σ) Γ″≈Γ′


  ctxeq-s-≈ : ⊢ Γ ≈ Δ →
              Γ ⊢s σ ≈ σ′ ∶ Γ′ →
              ------------------
              Δ ⊢s σ ≈ σ′ ∶ Γ′
  ctxeq-s-≈ Γ≈Δ (I-≈ _)                          = s-≈-conv (I-≈ (proj₂ (presup-⊢≈ Γ≈Δ))) (⊢≈-sym Γ≈Δ)
  ctxeq-s-≈ ⊢≈@(∷-cong Γ≈Δ _ ⊢T′ _ _) (wk-≈ ⊢TΓ) = s-≈-conv (wk-≈ (proj₂ (presup-⊢≈ ⊢≈))) ((⊢≈-sym Γ≈Δ))
  ctxeq-s-≈ Γ≈Δ (∘-cong σ≈σ′ δ≈δ′)               = ∘-cong (ctxeq-s-≈ Γ≈Δ σ≈σ′) δ≈δ′
  ctxeq-s-≈ Γ≈Δ (,-cong σ≈σ′ ⊢T t≈t′)            = ,-cong (ctxeq-s-≈ Γ≈Δ σ≈σ′) ⊢T (ctxeq-≈ Γ≈Δ t≈t′)
  ctxeq-s-≈ Γ≈Δ (I-∘ ⊢σ)                         = I-∘ (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-s-≈ Γ≈Δ (∘-I ⊢σ)                         = ∘-I (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-s-≈ Γ≈Δ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)             = ∘-assoc ⊢σ ⊢σ′ (ctxeq-s Γ≈Δ ⊢σ″)
  ctxeq-s-≈ Γ≈Δ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)                = ,-∘ ⊢σ ⊢T ⊢t (ctxeq-s Γ≈Δ ⊢δ)
  ctxeq-s-≈ Γ≈Δ (p-, ⊢σ ⊢T ⊢t)                   = p-, (ctxeq-s Γ≈Δ ⊢σ) ⊢T (ctxeq-tm Γ≈Δ ⊢t)
  ctxeq-s-≈ Γ≈Δ (,-ext ⊢σ)                       = ,-ext (ctxeq-s Γ≈Δ ⊢σ)
  ctxeq-s-≈ Γ≈Δ (s-≈-sym σ≈σ′)                   = s-≈-sym (ctxeq-s-≈ Γ≈Δ σ≈σ′)
  ctxeq-s-≈ Γ≈Δ (s-≈-trans σ≈σ′ σ′≈σ″)           = s-≈-trans (ctxeq-s-≈ Γ≈Δ σ≈σ′) (ctxeq-s-≈ Γ≈Δ σ′≈σ″)
  ctxeq-s-≈ Γ≈Δ (s-≈-conv σ≈σ′ Γ″≈Γ′)            = s-≈-conv (ctxeq-s-≈ Γ≈Δ σ≈σ′) Γ″≈Γ′
