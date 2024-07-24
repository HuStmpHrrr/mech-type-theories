
module NonCumulative.Statics.Unascribed.Equiv where

open import Lib
open import NonCumulative.Statics.Unascribed.Full as F
open import NonCumulative.Statics.Unascribed.Anno as A

mutual
  F⇒A-⊢ : F.⊢ Γ →
          -------
          A.⊢ Γ
  F⇒A-⊢ ⊢[]        = ⊢[]
  F⇒A-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (F⇒A-⊢ ⊢Γ) {!F⇒A-tm ⊢T!} -- (proj₂ (F⇒A-tm ⊢T))


  F⇒A-tm : Γ F.⊢ t ∶ T →
           -------------
           ∃ λ i → Γ A.⊢ t ∶[ i ] T
  F⇒A-tm = {!!}

  F⇒A-s : Γ F.⊢s σ ∶ Δ →
          --------------
          Γ A.⊢s σ ∶ Δ
  F⇒A-s (s-I ⊢Γ)           = s-I (F⇒A-⊢ ⊢Γ)
  F⇒A-s (s-wk ⊢Γ)          = s-wk (F⇒A-⊢ ⊢Γ)
  F⇒A-s (s-∘ ⊢σ ⊢δ)        = s-∘ (F⇒A-s ⊢σ) (F⇒A-s ⊢δ)
  F⇒A-s (s-, ⊢σ ⊢T ⊢t)     = s-, (F⇒A-s ⊢σ) {!!} {!!}
  F⇒A-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (F⇒A-s ⊢σ) (F⇒A-⊢≈ Δ′≈Δ)


  F⇒A-⊢≈ : F.⊢ Γ ≈ Δ →
           -----------
           A.⊢ Γ ≈ Δ
  F⇒A-⊢≈ []-≈                    = []-≈
  F⇒A-⊢≈ (∷-cong Γ≈Δ _ _ T≈T′ _) = {!!}


  F⇒A-≈ : Γ F.⊢ t ≈ t′ ∶ T →
          ------------------
          ∃ λ i → Γ A.⊢ t ≈ t′ ∶[ i ] T
  F⇒A-≈ = {!!}

  F⇒A-s-≈ : Γ F.⊢s σ ≈ σ′ ∶ Δ →
            ------------------
            Γ A.⊢s σ ≈ σ′ ∶ Δ
  F⇒A-s-≈ (I-≈ ⊢Γ)                = I-≈ (F⇒A-⊢ ⊢Γ)
  F⇒A-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (F⇒A-⊢ ⊢TΓ)
  F⇒A-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (F⇒A-s-≈ σ≈σ′) (F⇒A-s-≈ δ≈δ′)
  F⇒A-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (F⇒A-s-≈ σ≈σ′) {!!} {!!}
  F⇒A-s-≈ (I-∘ ⊢σ)                = I-∘ (F⇒A-s ⊢σ)
  F⇒A-s-≈ (∘-I ⊢σ)                = ∘-I (F⇒A-s ⊢σ)
  F⇒A-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (F⇒A-s ⊢σ) (F⇒A-s ⊢σ′) (F⇒A-s ⊢σ″)
  F⇒A-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (F⇒A-s ⊢σ) {!!} {!!} {!!}
  F⇒A-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (F⇒A-s ⊢σ) {!!} {!!}
  F⇒A-s-≈ (,-ext ⊢σ)              = ,-ext (F⇒A-s ⊢σ)
  F⇒A-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (F⇒A-s-≈ σ≈σ′)
  F⇒A-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (F⇒A-s-≈ σ≈σ′) (F⇒A-s-≈ σ′≈σ″)
  F⇒A-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (F⇒A-s-≈ σ≈σ′) (F⇒A-⊢≈ Δ′≈Δ)


-- mutual
--   C⇒F-⊢ : A.⊢ Γ →
--           -------
--           F.⊢ Γ
--   C⇒F-⊢ ⊢[]        = ⊢[]
--   C⇒F-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T)


--   C⇒F-tm : Γ A.⊢ t ∶ T →
--            -------------
--            Γ F.⊢ t ∶ T
--   C⇒F-tm (N-wf i ⊢Γ)                              = N-wf i (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (Se-wf i ⊢Γ)                             = Se-wf i (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (Π-wf ⊢S ⊢T)                             = Π-wf (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
--   C⇒F-tm (vlookup ⊢Γ T∈Γ)                         = vlookup (C⇒F-⊢ ⊢Γ) T∈Γ
--   C⇒F-tm (ze-I ⊢Γ)                                = ze-I (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (su-I ⊢t)                                = su-I (C⇒F-tm ⊢t)
--   C⇒F-tm (N-E ⊢T ⊢s ⊢r ⊢t)                        = N-E (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-tm (Λ-I ⊢t)
--     with ⊢∷ ⊢Γ ⊢S ← proj₁ (presup-tm (C⇒F-tm ⊢t)) = Λ-I ⊢S (C⇒F-tm ⊢t)
--   C⇒F-tm (Λ-E ⊢t ⊢r)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)       = Λ-E (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t) (C⇒F-tm ⊢r)
--   C⇒F-tm (t[σ] ⊢t ⊢σ)                             = t[σ] (C⇒F-tm ⊢t) (C⇒F-s ⊢σ)
--   C⇒F-tm (cumu ⊢t)                                = cumu (C⇒F-tm ⊢t)
--   C⇒F-tm (conv ⊢t T≈T′)                           = conv (C⇒F-tm ⊢t) (C⇒F-≈ T≈T′)


--   C⇒F-s : Γ A.⊢s σ ∶ Δ →
--           --------------
--           Γ F.⊢s σ ∶ Δ
--   C⇒F-s (s-I ⊢Γ)           = s-I (C⇒F-⊢ ⊢Γ)
--   C⇒F-s (s-wk ⊢TΓ)         = s-wk (C⇒F-⊢ ⊢TΓ)
--   C⇒F-s (s-∘ ⊢σ ⊢δ)        = s-∘ (C⇒F-s ⊢σ) (C⇒F-s ⊢δ)
--   C⇒F-s (s-, ⊢σ ⊢T ⊢t)     = s-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
--   C⇒F-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (C⇒F-s ⊢σ) (C⇒F-⊢≈ Δ′≈Δ)


--   C⇒F-⊢≈ : A.⊢ Γ ≈ Δ →
--            -----------
--            F.⊢ Γ ≈ Δ
--   C⇒F-⊢≈ []-≈                                        = []-≈
--   C⇒F-⊢≈ (∷-cong Γ≈Δ T≈T′)
--     with T≈T′₁ ← ctxeq-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-≈ T≈T′)
--        with _ , ⊢T , _       ← presup-≈ (C⇒F-≈ T≈T′)
--           | _ , _  , ⊢T′ , _ ← presup-≈ T≈T′₁        = ∷-cong (C⇒F-⊢≈ Γ≈Δ) ⊢T ⊢T′ (C⇒F-≈ T≈T′) T≈T′₁


--   C⇒F-≈ : Γ A.⊢ t ≈ t′ ∶ T →
--           ------------------
--           Γ F.⊢ t ≈ t′ ∶ T
--   C⇒F-≈ (N-[] i ⊢σ)                                 = N-[] i (C⇒F-s ⊢σ)
--   C⇒F-≈ (Se-[] i ⊢σ)                                = Se-[] i (C⇒F-s ⊢σ)
--   C⇒F-≈ (Π-[] ⊢σ ⊢S ⊢T)                             = Π-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
--   C⇒F-≈ (Π-cong S≈S′ T≈T′)
--     with _ , ⊢S , _ ← presup-≈ (C⇒F-≈ S≈S′)         = Π-cong ⊢S (C⇒F-≈ S≈S′) (C⇒F-≈ T≈T′)
--   C⇒F-≈ (v-≈ ⊢Γ T∈Γ)                                = v-≈ (C⇒F-⊢ ⊢Γ) T∈Γ
--   C⇒F-≈ (ze-≈ ⊢Γ)                                   = ze-≈ (C⇒F-⊢ ⊢Γ)
--   C⇒F-≈ (su-cong t≈t′)                              = su-cong (C⇒F-≈ t≈t′)
--   C⇒F-≈ (rec-cong T≈T′ s≈s′ r≈r′ t≈t′)
--     with _ , ⊢T , _ ← presup-≈ (C⇒F-≈ T≈T′)         = rec-cong ⊢T (C⇒F-≈ T≈T′) (C⇒F-≈ s≈s′) (C⇒F-≈ r≈r′) (C⇒F-≈ t≈t′)
--   C⇒F-≈ (Λ-cong t≈t′)
--     with ⊢∷ ⊢Γ ⊢S , _ ← presup-≈ (C⇒F-≈ t≈t′)       = Λ-cong ⊢S (C⇒F-≈ t≈t′)
--   C⇒F-≈ ($-cong t≈t′ r≈r′)
--     with _ , _ , _ , _ , ⊢Π ← presup-≈ (C⇒F-≈ t≈t′) = $-cong (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-≈ t≈t′) (C⇒F-≈ r≈r′)
--   C⇒F-≈ ([]-cong t≈t′ σ≈σ′)                         = []-cong (C⇒F-≈ t≈t′) (C⇒F-s-≈ σ≈σ′)
--   C⇒F-≈ (ze-[] ⊢σ)                                  = ze-[] (C⇒F-s ⊢σ)
--   C⇒F-≈ (su-[] ⊢σ ⊢t)                               = su-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)                     = rec-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-≈ (Λ-[] ⊢σ ⊢t)                                = Λ-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ ($-[] ⊢σ ⊢t ⊢s)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = $-[] (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
--   C⇒F-≈ (rec-β-ze ⊢T ⊢s ⊢r)                         = rec-β-ze (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r)
--   C⇒F-≈ (rec-β-su ⊢T ⊢s ⊢r ⊢t)                      = rec-β-su (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-≈ (Λ-β ⊢t ⊢s)
--     with ⊢∷ ⊢Γ ⊢S , _ , ⊢T ← presup-tm (C⇒F-tm ⊢t)  = Λ-β (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
--   C⇒F-≈ (Λ-η ⊢t)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = Λ-η (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([I] ⊢t)                                    = [I] (C⇒F-tm ⊢t)
--   C⇒F-≈ ([wk] ⊢SΓ T∈Γ)                              = [wk] (C⇒F-⊢ ⊢SΓ) T∈Γ
--   C⇒F-≈ ([∘] ⊢δ ⊢σ ⊢t)                              = [∘] (C⇒F-s ⊢δ) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)                         = [,]-v-ze (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([,]-v-su ⊢σ ⊢S ⊢t T∈Δ)                     = [,]-v-su (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t) T∈Δ
--   C⇒F-≈ (≈-cumu t≈t′)                               = ≈-cumu (C⇒F-≈ t≈t′)
--   C⇒F-≈ (≈-conv t≈t′ S≈T)                           = ≈-conv (C⇒F-≈ t≈t′) (C⇒F-≈ S≈T)
--   C⇒F-≈ (≈-sym t≈t′)                                = ≈-sym (C⇒F-≈ t≈t′)
--   C⇒F-≈ (≈-trans t≈t′ t′≈t″)                        = ≈-trans (C⇒F-≈ t≈t′) (C⇒F-≈ t′≈t″)


--   C⇒F-s-≈ : Γ A.⊢s σ ≈ σ′ ∶ Δ →
--             ------------------
--             Γ F.⊢s σ ≈ σ′ ∶ Δ
--   C⇒F-s-≈ (I-≈ ⊢Γ)                = I-≈ (C⇒F-⊢ ⊢Γ)
--   C⇒F-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (C⇒F-⊢ ⊢TΓ)
--   C⇒F-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ δ≈δ′)
--   C⇒F-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-tm ⊢T) (C⇒F-≈ t≈t′)
--   C⇒F-s-≈ (I-∘ ⊢σ)                = I-∘ (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (∘-I ⊢σ)                = ∘-I (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (C⇒F-s ⊢σ) (C⇒F-s ⊢σ′) (C⇒F-s ⊢σ″)
--   C⇒F-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t) (C⇒F-s ⊢δ)
--   C⇒F-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
--   C⇒F-s-≈ (,-ext ⊢σ)              = ,-ext (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (C⇒F-s-≈ σ≈σ′)
--   C⇒F-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ σ′≈σ″)
--   C⇒F-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (C⇒F-s-≈ σ≈σ′) (C⇒F-⊢≈ Δ′≈Δ)
