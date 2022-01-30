{-# OPTIONS --without-K --safe #-}

module Idem.Restricted where

open import Lib

open import Idem.Statics
open import Idem.StaticProps

infix 4 _﹔_⊢r_∶_﹔_

data _﹔_⊢r_∶_﹔_ : Ctx → Ctx → Subst → Ctx → Ctx → Set where
  r-I   : Δ ﹔ Γ ⊢s σ ≈ I ∶ Δ′ ﹔ Γ′ →
          --------------------------
          Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′
  r-p   : Δ ﹔ Γ ⊢r δ ∶ Δ′ ﹔ T ∷ Γ′ →
          Δ ﹔ Γ ⊢s σ ≈ p δ ∶ Δ′ ﹔ Γ′ →
          -------------------------
          Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′
  r-hat : ∀ Γ₁ {Γ₂} →
          Δ ﹔ Γ ⊢r δ ∶ Δ′ ﹔ Γ′ →
          Γ ++ Δ ≡ Γ₁ ++ Γ₂ →
          Γ₂ ﹔ Γ₁ ⊢s σ ≈ hat δ ∶ Γ′ ++ Δ′ ﹔ [] →
          ----------------------------------------
          Γ₂ ﹔ Γ₁ ⊢r σ ∶ Γ′ ++ Δ′ ﹔ []

⊢r⇒⊢s : Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′
⊢r⇒⊢s (r-I ⊢σ)         = proj₁ (presup-s ⊢σ)
⊢r⇒⊢s (r-p _ ⊢σ)       = proj₁ (presup-s ⊢σ)
⊢r⇒⊢s (r-hat _ _ _ ⊢σ) = proj₁ (presup-s ⊢σ)

s≈-resp-⊢r : Δ ﹔ Γ ⊢s σ ≈ σ′ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢r σ′ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′
s≈-resp-⊢r σ≈σ′ (r-I σ′≈)            = r-I (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-p ⊢δ σ′≈)         = r-p ⊢δ (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-hat Γ₁ ⊢δ eq σ′≈) = r-hat Γ₁ ⊢δ eq (s-≈-trans σ≈σ′ σ′≈)

⊢r-til : Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′ → [] ﹔ Γ ++ Δ ⊢r til σ ∶ [] ﹔ Γ′ ++ Δ′
⊢r-til (r-I σ≈)            = r-I {!!}
⊢r-til (r-p ⊢δ σ≈)         = {!!}
⊢r-til (r-hat Γ₁ ⊢δ eq σ≈) = {!!}

-- ⊢r-Tr : ∀ n → Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′ → n < len Δ′ ﹔ Γ′ → ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Δ′ ﹔ Γ′ ≡ Φ₁ ++⁺ Φ₂ × Δ ﹔ Γ ≡ Φ₃ ++⁺ Φ₄ × len Φ₁ ≡ n × len Φ₃ ≡ L σ n × Φ₄ ⊢r Tr σ n ∶ Φ₂
-- ⊢r-Tr {Δ ﹔ Γ} {σ} n (r-I σ≈I) n<
--   with chop Δ ﹔ Γ n<
-- ...  | Φ₁ , Φ₂ , refl , refl
--      with Tr-resp-≈′ Φ₁ σ≈I
-- ...     | Φ₃ , Φ₄ , eq , eql , Trσ≈
--         rewrite Tr-I (len Φ₁)         = Φ₁ , Φ₂ , Φ₁ , Φ₂
--                                       , refl , refl , refl , sym (trans (L-resp-≈ n σ≈I) (L-I _))
--                                       , helper (++⁺-cancelˡ′ Φ₁ Φ₃ eq (sym (trans eql (trans (L-resp-≈ n σ≈I) (L-I (len Φ₁))))))
--   where helper : Φ₂ ≡ Φ₄ →  Φ₂ ⊢r S-Tr σ n ∶ Φ₂
--         helper refl = r-I Trσ≈
-- ⊢r-Tr zero (r-p ⊢δ σ≈p) n<            = [] , _ , [] , _ , refl , refl , refl , refl , r-p ⊢δ σ≈p
-- ⊢r-Tr {_} {σ} (suc n) (r-p ⊢δ σ≈p) n<
--   with ⊢r-Tr (suc n) ⊢δ n<
-- ...  | (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
--      , refl , eq′ , refl , eql′ , Trδ
--      with Tr-resp-≈′ (Γ ∷ Φ₁) σ≈p
-- ...     | Φ₅ , Φ₆ , eq″ , eql″ , Trσ≈ = Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
--                                       , refl , eq′ , refl , trans eql′ (sym eqL)
--                                       , helper (++⁺-cancelˡ′ Φ₃ Φ₅ (trans (sym eq′) eq″) (sym (trans eql″ (trans eqL (sym eql′)))))
--   where eqL = L-resp-≈ (suc n) σ≈p
--         helper : Φ₄ ≡ Φ₆ → Φ₄ ⊢r Tr σ (suc (len Φ₁)) ∶ Φ₂
--         helper refl = s≈-resp-⊢r Trσ≈ Trδ
-- ⊢r-Tr zero (r-； Γs ⊢δ σ≈； eq) n<     = [] , _ , [] , _ , refl , refl , refl , refl , r-； Γs ⊢δ σ≈； eq
-- ⊢r-Tr {_} {σ} (suc n) (r-； Γs ⊢δ σ≈； refl) (s≤s n<)
--   with ⊢r-Tr n ⊢δ n<
-- ...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
--      , refl , refl , refl , eql′ , Trδ
--      with Tr-resp-≈′ ([] ∷ Φ₁) σ≈；
-- ...     | Φ₅ , Φ₆ , eq″ , eql″ , Trσ≈ = [] ∷ Φ₁ , Φ₂ , Γs ++ Φ₃ , Φ₄
--                                       , refl , sym (++-++⁺ Γs)
--                                       , refl , trans (length-++ Γs) (trans (cong (len Γs +_) eql′) (sym eqL))
--                                       , helper (++⁺-cancelˡ′ (Γs ++ Φ₃) Φ₅
--                                                             (trans (++-++⁺ Γs) eq″)
--                                                             (sym (trans eql″
--                                                                  (trans eqL
--                                                                  (trans (cong (_ +_) (sym eql′))
--                                                                         (sym (length-++ Γs)))))))
--   where eqL = L-resp-≈ (suc n) σ≈；
--         helper : Φ₄ ≡ Φ₆ → Φ₄ ⊢r S-Tr σ (suc n) ∶ Φ₂
--         helper refl = s≈-resp-⊢r Trσ≈ Trδ

-- ⊢r-Tr′ : ∀ Γs → Δ ﹔ Γ ⊢r σ ∶ Γs ++⁺ Δ′ ﹔ Γ′ → ∃₂ λ Φ₁ Φ₂ → Δ ﹔ Γ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ L σ (len Γs) × Φ₂ ⊢r Tr σ (len Γs) ∶ Δ′ ﹔ Γ′
-- ⊢r-Tr′ Γs ⊢σ
--   with ⊢r-Tr (len Γs) ⊢σ (length-<-++⁺ Γs)
-- ...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
--      , eq , eq′ , eql , eql′ , Trδ
--      rewrite ++⁺-cancelˡ′ Γs Φ₁ eq (sym eql) = Φ₃ , Φ₄ , eq′ , eql′ , Trδ

-- ⊢r-comp : Δ′ ﹔ Γ′ ⊢r σ′ ∶ Δ ﹔ Γ″ → Δ ﹔ Γ ⊢r σ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢r σ′ ∘ σ ∶ Δ ﹔ Γ″
-- ⊢r-comp (r-I σ′≈I) ⊢σ              = s≈-resp-⊢r (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈I) (I-∘ (⊢r⇒⊢s ⊢σ))) ⊢σ
-- ⊢r-comp (r-p ⊢δ σ′≈p) ⊢σ           = r-p (⊢r-comp ⊢δ ⊢σ)
--                                    (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈p)
--                                               (p-∘ (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ)))
-- ⊢r-comp (r-； Γs ⊢δ σ′≈； refl) ⊢σ
--   with ⊢r-Tr′ Γs ⊢σ
-- ...  | Δs , Δ ﹔ Γ″ , refl , eql , ⊢Trσ = r-； Δs (⊢r-comp ⊢δ ⊢Trσ)
--                                          (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈；)
--                                                     (subst (λ n → Δs ++⁺ Δ ﹔ Γ″ ⊢s _ ≈ _ ； n ∶ _)
--                                                            (sym eql)
--                                                            (；-∘ Γs (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) refl)))
--                                          refl
