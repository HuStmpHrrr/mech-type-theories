{-# OPTIONS --without-K --safe #-}

-- If ⊢ Γ ≈ Δ and Γ ⊢ 𝒥 for any judgment 𝒥, then Δ ⊢ 𝒥
module NonCumulative.Statics.Unascribed.Anno.CtxEquiv where

open import Lib

open import NonCumulative.Statics.Unascribed.Anno
open import NonCumulative.Statics.Unascribed.Anno.Refl
open import NonCumulative.Statics.Unascribed.Anno.Misc
open import NonCumulative.Statics.Unascribed.Anno.Properties.Contexts


eq-se : ∀ {i j k k′} →
        Γ ⊢ T ∶[ k ] Se i →
        Γ ⊢ T ∶[ k′ ] Se j →
        i ≡ j
eq-se (N-wf x) ⊢T′ = {!!}
eq-se (Se-wf i x) ⊢T′ = {!!}
eq-se (Liftt-wf n ⊢T) ⊢T′ = {!!}
eq-se (Π-wf ⊢T ⊢T₁ x) ⊢T′ = {!!}
eq-se (L-E n ⊢T ⊢T₁) ⊢T′ = {!!}
eq-se (conv ⊢T x) ⊢T′ = {!!}

-- -- unique-tm : ∀ {i j} →
-- --             Γ ⊢ t ∶[ i ] T →
-- --             Γ ⊢ t ∶[ j ] T′ →
-- --             i ≡ j × Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i
-- -- unique-tm (N-wf ⊢Γ) (N-wf _) = refl , ≈-refl (Se-wf 0 ⊢Γ)
-- -- unique-tm (Se-wf i ⊢Γ) (Se-wf .i _) = refl , ≈-refl (Se-wf (suc i) ⊢Γ)
-- -- unique-tm (Liftt-wf n ⊢t) (Liftt-wf .n ⊢t′)
-- --   with unique-tm ⊢t ⊢t′
-- -- ...  | refl , _ = refl , ≈-refl (Se-wf _ {!!})
-- -- unique-tm (Π-wf ⊢S ⊢T refl) (Π-wf ⊢S′ ⊢T′ refl)
-- --   with unique-tm ⊢S ⊢S′ | unique-tm ⊢T ⊢T′
-- -- ...  | refl , _ | refl , _ = refl , ≈-refl (Se-wf _ {!!})
-- -- unique-tm (vlookup ⊢Γ T∈Γ) (vlookup ⊢Γ′ T∈Γ′) = {!!}
-- -- unique-tm (ze-I ⊢Γ) (ze-I _) = refl , ≈-refl (N-wf ⊢Γ)
-- -- unique-tm (su-I ⊢t) (su-I ⊢t′) = unique-tm ⊢t ⊢t′
-- -- unique-tm (N-E ⊢t ⊢t₁ ⊢t₂ ⊢t₃) (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!!}
-- -- unique-tm (Λ-I ⊢S ⊢t refl) (Λ-I ⊢S′ ⊢t′ refl) = {!!}
-- -- --   with unique-tm ⊢S ⊢S′ | unique-tm ⊢t ⊢t′
-- -- -- ...  | refl , _ | refl , _ = {!!}
-- -- unique-tm (Λ-E ⊢t ⊢t₁ ⊢t₂ ⊢t₃ x) (Λ-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃ x₁) = {!!}
-- -- unique-tm (L-I n ⊢t) (L-I .n ⊢t′) = {!!}
-- -- unique-tm (L-E n ⊢t ⊢t₁) (L-E n₁ ⊢t′ ⊢t′₁) = {!!}
-- -- unique-tm (t[σ] ⊢t ⊢σ) (t[σ] ⊢t′ _) = {!!}
-- -- unique-tm (conv ⊢t S≈) ⊢t′
-- --   with unique-tm ⊢t ⊢t′
-- -- ...  | refl , S≈T′ = refl , ≈-trans (≈-sym S≈) S≈T′
-- -- unique-tm ⊢t (conv ⊢t′ S≈)
-- --   with unique-tm ⊢t ⊢t′
-- -- ...  | refl , T≈S = refl , ≈-trans T≈S S≈

-- mutual
--   ctxeq-tm : ∀ {i} →
--              ⊢ Γ ≈ Δ →
--              Γ ⊢ t ∶[ i ] T →
--              -----------
--              Δ ⊢ t ∶[ i ] T
--   ctxeq-tm Γ≈Δ (N-wf _)             = N-wf (proj₂ (presup-⊢≈ Γ≈Δ))
--   ctxeq-tm Γ≈Δ (Se-wf i _)          = Se-wf i (proj₂ (presup-⊢≈ Γ≈Δ))
--   ctxeq-tm Γ≈Δ (Π-wf ⊢S ⊢T eq)      = Π-wf (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢T) eq
--   ctxeq-tm Γ≈Δ (vlookup ⊢Γ T∈Γ)     = {!!}
--   ctxeq-tm Γ≈Δ (ze-I _)             = ze-I (proj₂ (presup-⊢≈ Γ≈Δ))
--   ctxeq-tm Γ≈Δ (su-I ⊢t)            = su-I (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-tm Γ≈Δ (N-E ⊢T ⊢s ⊢r ⊢t)
--     with presup-⊢≈ Γ≈Δ
--   ...  | ⊢Γ , ⊢Δ                    = N-E (ctxeq-tm NΓ≈NΔ ⊢T)
--                                           (ctxeq-tm Γ≈Δ ⊢s)
--                                           (ctxeq-tm (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) ⊢r)
--                                           (ctxeq-tm Γ≈Δ ⊢t)
--     where NΓ≈NΔ                     = ∷-cong Γ≈Δ (N-wf ⊢Γ) (N-wf ⊢Δ) (≈-refl (N-wf ⊢Γ)) (≈-refl (N-wf ⊢Δ))
--   ctxeq-tm Γ≈Δ (Λ-I ⊢S ⊢t eq)       = Λ-I (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢t) eq
--   ctxeq-tm Γ≈Δ (Λ-E ⊢S ⊢T ⊢t ⊢s eq) = Λ-E ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm Γ≈Δ ⊢t) (ctxeq-tm Γ≈Δ ⊢s) eq
 --     where ⊢S′                       = ctxeq-tm Γ≈Δ ⊢S
--   ctxeq-tm Γ≈Δ (t[σ] ⊢t ⊢σ)         = t[σ] ⊢t (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-tm Γ≈Δ (conv ⊢t T≈T′)       = conv (ctxeq-tm Γ≈Δ ⊢t) (ctxeq-≈ Γ≈Δ T≈T′)
--   ctxeq-tm Γ≈Δ (Liftt-wf n ⊢T)      = Liftt-wf n (ctxeq-tm Γ≈Δ ⊢T)
--   ctxeq-tm Γ≈Δ (L-I n ⊢t)           = L-I n (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-tm Γ≈Δ (L-E n ⊢T ⊢t)        = L-E n (ctxeq-tm Γ≈Δ ⊢T) (ctxeq-tm Γ≈Δ ⊢t)

--   ctxeq-≈ : ∀ {i} →
--             ⊢ Γ ≈ Δ →
--             Γ ⊢ t ≈ t′ ∶[ i ] T →
--             -----------------
--             Δ ⊢ t ≈ t′ ∶[ i ] T
--   ctxeq-≈ Γ≈Δ (N-[] ⊢σ)              = N-[] (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-≈ Γ≈Δ (Se-[] i ⊢σ)             = Se-[] i (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-≈ Γ≈Δ (Π-[] ⊢σ ⊢S ⊢T eq)          = Π-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢S ⊢T eq
--   ctxeq-≈ Γ≈Δ (Π-cong ⊢S S≈S′ T≈T′ eq)    = {!!} -- Π-cong (ctxeq-≈ Γ≈Δ S≈S′) (ctxeq-≈ (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) T≈T′) eq
--   ctxeq-≈ Γ≈Δ (v-≈ ⊢Γ T∈Γ) = {!!}
--   ctxeq-≈ Γ≈Δ (ze-≈ _)                 = ze-≈ (proj₂ (presup-⊢≈ Γ≈Δ))
--   ctxeq-≈ Γ≈Δ (su-cong t≈t′)           = su-cong (ctxeq-≈ Γ≈Δ t≈t′)
--   ctxeq-≈ Γ≈Δ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′)
--     with presup-⊢≈ Γ≈Δ
--   ...  | ⊢Γ , ⊢Δ                       = rec-cong (ctxeq-tm NΓ≈NΔ ⊢T)
--                                                   (ctxeq-≈ NΓ≈NΔ T≈T′)
--                                                   (ctxeq-≈ Γ≈Δ s≈s′)
--                                                   (ctxeq-≈ (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) r≈r′)
--                                                   (ctxeq-≈ Γ≈Δ t≈t′)
--     where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf ⊢Γ) (N-wf ⊢Δ) (≈-refl (N-wf ⊢Γ)) (≈-refl (N-wf ⊢Δ))
--   ctxeq-≈ Γ≈Δ (Λ-cong ⊢S t≈t′ eq)         = Λ-cong (ctxeq-tm Γ≈Δ ⊢S) (ctxeq-≈ (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) t≈t′) eq
--   ctxeq-≈ Γ≈Δ ($-cong ⊢S ⊢T t≈t′ s≈s′ eq) = $-cong ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ s≈s′) eq
--     where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
--   ctxeq-≈ Γ≈Δ ([]-cong t≈t′ σ≈σ′)      = []-cong t≈t′ (ctxeq-s-≈ Γ≈Δ σ≈σ′)
--   ctxeq-≈ Γ≈Δ (ze-[] ⊢σ)               = ze-[] (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-≈ Γ≈Δ (su-[] ⊢σ ⊢t)            = su-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢t
--   ctxeq-≈ Γ≈Δ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)  = rec-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢T ⊢s ⊢r ⊢t
--   ctxeq-≈ Γ≈Δ (Λ-[] ⊢σ ⊢S ⊢t eq)             = Λ-[] (ctxeq-s Γ≈Δ ⊢σ) ⊢S ⊢t eq
--   ctxeq-≈ Γ≈Δ ($-[] ⊢S ⊢T ⊢σ ⊢t ⊢s eq)    = $-[] ⊢S ⊢T (ctxeq-s Γ≈Δ ⊢σ) ⊢t ⊢s eq
--   ctxeq-≈ Γ≈Δ (rec-β-ze ⊢T ⊢s ⊢r)
--     with presup-⊢≈ Γ≈Δ
--   ...  | ⊢Γ , ⊢Δ                       = rec-β-ze (ctxeq-tm NΓ≈NΔ ⊢T)
--                                                   (ctxeq-tm Γ≈Δ ⊢s)
--                                                   (ctxeq-tm (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T))) ⊢r)
--     where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf ⊢Γ) (N-wf ⊢Δ) (≈-refl (N-wf ⊢Γ)) (≈-refl (N-wf ⊢Δ))
--   ctxeq-≈ Γ≈Δ (rec-β-su ⊢T ⊢s ⊢r ⊢t)
--     with presup-⊢≈ Γ≈Δ
--   ...  | ⊢Γ , ⊢Δ                       = rec-β-su (ctxeq-tm NΓ≈NΔ ⊢T)
 --                                                   (ctxeq-tm Γ≈Δ ⊢s)
--                                                   (ctxeq-tm {!!} ⊢r) -- (∷-cong NΓ≈NΔ ⊢T (ctxeq-tm NΓ≈NΔ ⊢T) (≈-refl ⊢T) (≈-refl (ctxeq-tm NΓ≈NΔ ⊢T)))
--                                                   (ctxeq-tm Γ≈Δ ⊢t)
--     where NΓ≈NΔ                        = ∷-cong Γ≈Δ (N-wf ⊢Γ) (N-wf ⊢Δ) (≈-refl (N-wf ⊢Γ)) (≈-refl (N-wf ⊢Δ))
--   ctxeq-≈ Γ≈Δ (Λ-β ⊢S ⊢T ⊢t ⊢s eq)        = Λ-β ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm (∷-cong Γ≈Δ ⊢S (ctxeq-tm Γ≈Δ ⊢S) (≈-refl ⊢S) (≈-refl (ctxeq-tm Γ≈Δ ⊢S))) ⊢t) (ctxeq-tm Γ≈Δ ⊢s) eq
--     where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
--   ctxeq-≈ Γ≈Δ (Λ-η ⊢S ⊢T ⊢t eq)           = Λ-η ⊢S′ (ctxeq-tm (∷-cong Γ≈Δ ⊢S ⊢S′ (≈-refl ⊢S) (≈-refl ⊢S′)) ⊢T) (ctxeq-tm Γ≈Δ ⊢t) eq
--     where ⊢S′                          = ctxeq-tm Γ≈Δ ⊢S
--   ctxeq-≈ Γ≈Δ ([I] ⊢t)                 = [I] (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-≈ (∷-cong Γ≈Δ _ ⊢T′ _ _) ([wk] ⊢Γ ⊢S T∈Γ) = {!!}
--   ctxeq-≈ Γ≈Δ ([∘] ⊢δ ⊢σ ⊢t)           = [∘] (ctxeq-s Γ≈Δ ⊢δ) ⊢σ ⊢t
--   ctxeq-≈ Γ≈Δ ([,]-v-ze ⊢σ ⊢S ⊢t)      = [,]-v-ze (ctxeq-s Γ≈Δ ⊢σ) ⊢S (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-≈ Γ≈Δ ([,]-v-su ⊢Δ ⊢σ ⊢S ⊢s T∈Γ′) = [,]-v-su ⊢Δ (ctxeq-s Γ≈Δ ⊢σ) ⊢S (ctxeq-tm Γ≈Δ ⊢s) T∈Γ′
--   ctxeq-≈ Γ≈Δ (≈-conv t≈t′ T≈T′)       = ≈-conv (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ T≈T′)
--   ctxeq-≈ Γ≈Δ (≈-sym t≈t′)             = ≈-sym (ctxeq-≈ Γ≈Δ t≈t′)
--   ctxeq-≈ Γ≈Δ (≈-trans t≈t′ t′≈t″)     = ≈-trans (ctxeq-≈ Γ≈Δ t≈t′) (ctxeq-≈ Γ≈Δ t′≈t″)


--   ctxeq-s : ⊢ Γ ≈ Δ →
--             Γ ⊢s σ ∶ Γ′ →
--             -----------
--             Δ ⊢s σ ∶ Γ′
--   ctxeq-s Γ≈Δ (s-I _)                        = s-conv (s-I (proj₂ (presup-⊢≈ Γ≈Δ))) (⊢≈-sym Γ≈Δ)
--   ctxeq-s ⊢≈@(∷-cong Γ≈Δ _ _ _ _) (s-wk ⊢TΓ) = s-conv (s-wk (proj₂ (presup-⊢≈ ⊢≈))) (⊢≈-sym Γ≈Δ)
--   ctxeq-s Γ≈Δ (s-∘ ⊢σ ⊢δ)                    = s-∘ (ctxeq-s Γ≈Δ ⊢σ) ⊢δ
--   ctxeq-s Γ≈Δ (s-, ⊢σ ⊢T ⊢t)                 = s-, (ctxeq-s Γ≈Δ ⊢σ) ⊢T (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-s Γ≈Δ (s-conv ⊢σ Γ″≈Γ′)              = s-conv (ctxeq-s Γ≈Δ ⊢σ) Γ″≈Γ′


--   ctxeq-s-≈ : ⊢ Γ ≈ Δ →
--               Γ ⊢s σ ≈ σ′ ∶ Γ′ →
--               ------------------
--               Δ ⊢s σ ≈ σ′ ∶ Γ′
--   ctxeq-s-≈ Γ≈Δ (I-≈ _)                          = s-≈-conv (I-≈ (proj₂ (presup-⊢≈ Γ≈Δ))) (⊢≈-sym Γ≈Δ)
--   ctxeq-s-≈ ⊢≈@(∷-cong Γ≈Δ _ ⊢T′ _ _) (wk-≈ ⊢TΓ) = s-≈-conv (wk-≈ (proj₂ (presup-⊢≈ ⊢≈))) ((⊢≈-sym Γ≈Δ))
--   ctxeq-s-≈ Γ≈Δ (∘-cong σ≈σ′ δ≈δ′)               = ∘-cong (ctxeq-s-≈ Γ≈Δ σ≈σ′) δ≈δ′
--   ctxeq-s-≈ Γ≈Δ (,-cong σ≈σ′ ⊢T t≈t′)            = ,-cong (ctxeq-s-≈ Γ≈Δ σ≈σ′) ⊢T (ctxeq-≈ Γ≈Δ t≈t′)
--   ctxeq-s-≈ Γ≈Δ (I-∘ ⊢σ)                         = I-∘ (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-s-≈ Γ≈Δ (∘-I ⊢σ)                         = ∘-I (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-s-≈ Γ≈Δ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)             = ∘-assoc ⊢σ ⊢σ′ (ctxeq-s Γ≈Δ ⊢σ″)
--   ctxeq-s-≈ Γ≈Δ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)                = ,-∘ ⊢σ ⊢T ⊢t (ctxeq-s Γ≈Δ ⊢δ)
--   ctxeq-s-≈ Γ≈Δ (p-, ⊢σ ⊢T ⊢t)                   = p-, (ctxeq-s Γ≈Δ ⊢σ) ⊢T (ctxeq-tm Γ≈Δ ⊢t)
--   ctxeq-s-≈ Γ≈Δ (,-ext ⊢σ)                       = ,-ext (ctxeq-s Γ≈Δ ⊢σ)
--   ctxeq-s-≈ Γ≈Δ (s-≈-sym σ≈σ′)                   = s-≈-sym (ctxeq-s-≈ Γ≈Δ σ≈σ′)
--   ctxeq-s-≈ Γ≈Δ (s-≈-trans σ≈σ′ σ′≈σ″)           = s-≈-trans (ctxeq-s-≈ Γ≈Δ σ≈σ′) (ctxeq-s-≈ Γ≈Δ σ′≈σ″)
--   ctxeq-s-≈ Γ≈Δ (s-≈-conv σ≈σ′ Γ″≈Γ′)            = s-≈-conv (ctxeq-s-≈ Γ≈Δ σ≈σ′) Γ″≈Γ′
