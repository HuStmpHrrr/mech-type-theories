{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Unique where

open import Lib
open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.PER
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties.Contexts

mutual
  unique-typ : ∀ {i j} →
    Γ ⊢ t ∶[ i ] T →
    Γ ⊢ t ∶[ j ] T′ →
    i ≡ j × Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i
  unique-typ (N-wf ⊢Γ) (N-wf _)                    = refl , ≈-refl (Se-wf 0 ⊢Γ)
  unique-typ (conv ⊢t S≈T) ⊢t′
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , ≈-trans (≈-sym S≈T) T≈T′
  unique-typ ⊢t (conv ⊢t′ S≈T′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈S                                = refl , ≈-trans T≈S S≈T′
  unique-typ (Se-wf i ⊢Γ) (Se-wf .i _)             = refl , ≈-refl (Se-wf (suc i) ⊢Γ)
  unique-typ (Liftt-wf n ⊢T) (Liftt-wf .n ⊢T′)     = refl , ≈-refl (Se-wf (n + _) (proj₁ (presup-tm ⊢T)))
  unique-typ (Π-wf {k = k} ⊢S ⊢T refl) (Π-wf ⊢S′ ⊢T′ refl) = refl , ≈-refl (Se-wf k (proj₁ (presup-tm ⊢S)))
  unique-typ (vlookup ⊢Γ T∈Γ) (vlookup _ T′∈Γ)
    with same-lookup T∈Γ T′∈Γ
  ...  | refl , refl                               = refl , ≈-refl (∈⇒ty-wf ⊢Γ T∈Γ)
  unique-typ (ze-I ⊢Γ) (ze-I _)                    = refl , ≈-refl (N-wf ⊢Γ)
  unique-typ (su-I ⊢t) (su-I ⊢t′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , T≈T′
  unique-typ (N-E ⊢T _ _ ⊢t) (N-E _ _ _ _)
    with presup-tm ⊢T
  ...  | ⊢∷ ⊢Γ _ , _                               = refl , ≈-refl (t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t))
  unique-typ (Λ-I ⊢S ⊢t refl) (Λ-I _ ⊢t′ refl)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , Π-cong ⊢S (≈-refl ⊢S) T≈T′ refl
  unique-typ (Λ-E ⊢S ⊢T ⊢t ⊢s refl) (Λ-E ⊢S′ ⊢T′ ⊢t′ ⊢s′ refl)
    with unique-typ ⊢t ⊢t′
  ...  | eq , Π≈                                   = {!!} -- TODO: problem! seem to require semantic proof for this
  unique-typ (L-I n ⊢t) (L-I .n ⊢t′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , Liftt-cong n T≈T′
  unique-typ (L-E n ⊢T ⊢t) (L-E n′ ⊢T′ ⊢t′)
    with unique-typ ⊢t ⊢t′
  ...  | eq , Li≈ = {!!} -- TODO: same problem as application. need injectivity
  unique-typ (t[σ] ⊢t ⊢σ) (t[σ] ⊢t′ ⊢σ′)
    with unique-typ ⊢t (ctxeq-tm (unique-ctx ⊢σ′ ⊢σ) ⊢t′)
  ...  | refl , T≈T′                               = refl , []-cong-Se′ T≈T′ ⊢σ

  unique-ctx : Γ ⊢s σ ∶ Δ → Γ ⊢s σ ∶ Δ′ → ⊢ Δ ≈ Δ′
  unique-ctx (s-I ⊢Γ) (s-I _)              = ≈-Ctx-refl ⊢Γ
  unique-ctx (s-conv ⊢σ Δ′≈Δ) ⊢σ′          = ⊢≈-trans (⊢≈-sym Δ′≈Δ) (unique-ctx ⊢σ ⊢σ′)
  unique-ctx ⊢σ (s-conv ⊢σ′ Δ≈Δ′)          = ⊢≈-trans (unique-ctx ⊢σ ⊢σ′) Δ≈Δ′
  unique-ctx (s-wk (⊢∷ ⊢Γ _)) (s-wk _)     = ≈-Ctx-refl ⊢Γ
  unique-ctx (s-∘ ⊢σ ⊢τ) (s-∘ ⊢σ′ ⊢τ′)     = unique-ctx ⊢τ (ctxeq-s (⊢≈-sym (unique-ctx ⊢σ ⊢σ′)) ⊢τ′)
  unique-ctx (s-, ⊢σ ⊢T _) (s-, ⊢σ′ ⊢T′ _) = ∷-cong (unique-ctx ⊢σ ⊢σ′) ⊢T ⊢T′ (≈-refl ⊢T) (≈-refl ⊢T′)
