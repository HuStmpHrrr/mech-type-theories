{-# OPTIONS --without-K --safe #-}

module MLTT.Soundness.Weakening where

open import Lib

open import Data.List.Properties as Lₚ

open import MLTT.Statics
open import MLTT.Statics.Properties

infix 4 _⊢w_∶_

data _⊢w_∶_ : Ctx → Subst → Ctx → Set where
  r-I : Γ ⊢s σ ≈ I ∶ Δ →
        ----------------
        Γ ⊢w σ ∶ Δ
  r-p : Γ ⊢w τ ∶ T ∷ Δ →
        Γ ⊢s σ ≈ p τ ∶ Δ →
        -------------------
        Γ ⊢w σ ∶ Δ


-- A weakening is a well-formed substitution.
⊢w⇒⊢s : Γ ⊢w σ ∶ Δ → Γ ⊢s σ ∶ Δ
⊢w⇒⊢s (r-I ⊢σ)   = proj₁ (proj₂ (presup-s-≈ ⊢σ))
⊢w⇒⊢s (r-p _ ⊢σ) = proj₁ (proj₂ (presup-s-≈ ⊢σ))

-- A weakening's equivalent substitution is also a weakening.
s≈-resp-⊢w : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢w σ′ ∶ Δ → Γ ⊢w σ ∶ Δ
s≈-resp-⊢w σ≈σ′ (r-I σ′≈)    = r-I (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢w σ≈σ′ (r-p ⊢δ σ′≈) = r-p ⊢δ (s-≈-trans σ≈σ′ σ′≈)

-- A weakenings respects context stack equivalence.
⊢w-resp-⊢≈ˡ : Γ ⊢w σ ∶ Δ →
             ⊢ Γ ≈ Γ′ →
             --------------
             Γ′ ⊢w σ ∶ Δ
⊢w-resp-⊢≈ˡ (r-I σ≈I) Γ≈Γ′    = r-I (ctxeq-s-≈ Γ≈Γ′ σ≈I)
⊢w-resp-⊢≈ˡ (r-p ⊢τ ≈pτ) Γ≈Γ′ = r-p (⊢w-resp-⊢≈ˡ ⊢τ Γ≈Γ′) (ctxeq-s-≈ Γ≈Γ′ ≈pτ)

⊢w-resp-⊢≈ʳ : Γ ⊢w σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢w σ ∶ Δ′
⊢w-resp-⊢≈ʳ (r-I σ≈) Δ≈Δ′                       = r-I (s-≈-conv σ≈ Δ≈Δ′)
⊢w-resp-⊢≈ʳ (r-p ⊢τ ≈pτ) Δ≈Δ′
  with presup-s (⊢w⇒⊢s ⊢τ)
... | _ , ⊢∷ ⊢Δ ⊢T                              = r-p (⊢w-resp-⊢≈ʳ ⊢τ (∷-cong Δ≈Δ′ (≈-refl ⊢T))) (s-≈-conv ≈pτ Δ≈Δ′)

----------------------------------------
-- Weakenings form a category.

-- Weakenings are closed under composition.
⊢w-∘ : Γ′ ⊢w σ′ ∶ Γ″ →
       Γ ⊢w σ ∶ Γ′ →
       -----------------
       Γ ⊢w σ′ ∘ σ ∶ Γ″
⊢w-∘ (r-I σ′≈I) ⊢σ
  with presup-s-≈ σ′≈I
...  | _ , _ , ⊢I , ⊢Γ″            = ⊢w-resp-⊢≈ʳ (s≈-resp-⊢w (s-≈-trans (∘-cong (s-≈-refl (⊢w⇒⊢s ⊢σ)) σ′≈I) (s-≈-conv (I-∘ (⊢w⇒⊢s ⊢σ)) Γ′≈Γ″))
                                                             (⊢w-resp-⊢≈ʳ ⊢σ Γ′≈Γ″))
                                                 (⊢≈-refl ⊢Γ″)
  where Γ′≈Γ″ = ⊢I-inv ⊢I
⊢w-∘ (r-p ⊢τ ≈pτ) ⊢σ               = r-p (⊢w-∘ ⊢τ ⊢σ)
                                         (s-≈-trans (∘-cong (s-≈-refl (⊢w⇒⊢s ⊢σ)) ≈pτ)
                                                    (∘-assoc (s-wk (proj₂ (presup-s (⊢w⇒⊢s ⊢τ)))) (⊢w⇒⊢s ⊢τ) (⊢w⇒⊢s ⊢σ)))

-- Identity is restricted.
⊢wI : ⊢ Γ → Γ ⊢w I ∶ Γ
⊢wI ⊢Γ = r-I (I-≈ ⊢Γ)

⊢wwk : ⊢ T ∷ Γ → T ∷ Γ ⊢w wk ∶ Γ
⊢wwk ⊢TΓ = r-p (⊢wI ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ)))
