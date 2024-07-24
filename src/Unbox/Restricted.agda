{-# OPTIONS --without-K --safe #-}

module Unbox.Restricted where

open import Lib

open import Data.List.Properties as Lₚ

open import Unbox.Statics
open import Unbox.StaticProps

infix 4 _⊢r_∶_

data _⊢r_∶_ : Ctxs → Substs → Ctxs → Set where
  r-I : Ψ ⊢s σ ≈ I ∶ Ψ →
        ----------------
        Ψ ⊢r σ ∶ Ψ
  r-p : Ψ ⊢r δ ∶ (T ∷ Γ) ∷ Γs →
        Ψ ⊢s σ ≈ p ∘ δ ∶ Γ ∷ Γs →
        -------------------------
        Ψ ⊢r σ ∶ Γ ∷ Γs
  r-； : ∀ {n} Γs →
        Ψ ⊢r δ ∶ Ψ′ →
        Γs ++⁺ Ψ ⊢s σ ≈ δ ； n ∶ [] ∷⁺ Ψ′ →
        len Γs ≡ n →
        -----------------------------------
        Γs ++⁺ Ψ ⊢r σ ∶ [] ∷⁺ Ψ′

⊢r⇒⊢s : Ψ ⊢r σ ∶ Ψ′ → Ψ ⊢s σ ∶ Ψ′
⊢r⇒⊢s (r-I ⊢σ)        = proj₁ (presup-s ⊢σ)
⊢r⇒⊢s (r-p _ ⊢σ)      = proj₁ (presup-s ⊢σ)
⊢r⇒⊢s (r-； _ _ ⊢σ _) = proj₁ (presup-s ⊢σ)

s≈-resp-⊢r : Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → Ψ ⊢r σ′ ∶ Ψ′ → Ψ ⊢r σ ∶ Ψ′
s≈-resp-⊢r σ≈σ′ (r-I σ′≈)           = r-I (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-p ⊢δ σ′≈)        = r-p ⊢δ (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-； Γs ⊢δ σ′≈ eq) = r-； Γs ⊢δ (s-≈-trans σ≈σ′ σ′≈) eq

⊢r-Tr : ∀ n → Ψ ⊢r σ ∶ Ψ′ → n < len Ψ′ → ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × Ψ ≡ Φ₃ ++⁺ Φ₄ × len Φ₁ ≡ n × len Φ₃ ≡ O σ n × Φ₄ ⊢r Tr σ n ∶ Φ₂
⊢r-Tr {Ψ} {σ} n (r-I σ≈I) n<
  with chop Ψ n<
...  | Φ₁ , Φ₂ , refl , refl
     with Tr-resp-≈′ Φ₁ σ≈I
...     | Φ₃ , Φ₄ , eq , eql , Trσ≈
        rewrite Tr-I (len Φ₁)         = Φ₁ , Φ₂ , Φ₁ , Φ₂
                                      , refl , refl , refl , sym (trans (O-resp-≈ n σ≈I) (O-I _))
                                      , helper (++⁺-cancelˡ′ Φ₁ Φ₃ eq (sym (trans eql (trans (O-resp-≈ n σ≈I) (O-I (len Φ₁))))))
  where helper : Φ₂ ≡ Φ₄ →  Φ₂ ⊢r S-Tr σ n ∶ Φ₂
        helper refl = r-I Trσ≈
⊢r-Tr zero (r-p ⊢δ σ≈p) n<            = [] , _ , [] , _ , refl , refl , refl , refl , r-p ⊢δ σ≈p
⊢r-Tr {_} {σ} (suc n) (r-p ⊢δ σ≈p) n<
  with ⊢r-Tr (suc n) ⊢δ n<
...  | (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
     , refl , eq′ , refl , eql′ , Trδ
     with Tr-resp-≈′ (Γ ∷ Φ₁) σ≈p
...     | Φ₅ , Φ₆ , eq″ , eql″ , Trσ≈ = Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
                                      , refl , eq′ , refl , trans eql′ (sym eqL)
                                      , helper (++⁺-cancelˡ′ Φ₃ Φ₅ (trans (sym eq′) eq″) (sym (trans eql″ (trans eqL (sym eql′)))))
  where eqL = O-resp-≈ (suc n) σ≈p
        helper : Φ₄ ≡ Φ₆ → Φ₄ ⊢r Tr σ (suc (len Φ₁)) ∶ Φ₂
        helper refl = s≈-resp-⊢r Trσ≈ (s≈-resp-⊢r (I-∘ (⊢r⇒⊢s Trδ)) Trδ)
⊢r-Tr zero (r-； Γs ⊢δ σ≈； eq) n<     = [] , _ , [] , _ , refl , refl , refl , refl , r-； Γs ⊢δ σ≈； eq
⊢r-Tr {_} {σ} (suc n) (r-； Γs ⊢δ σ≈； refl) (s≤s n<)
  with ⊢r-Tr n ⊢δ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
     , refl , refl , refl , eql′ , Trδ
     with Tr-resp-≈′ ([] ∷ Φ₁) σ≈；
...     | Φ₅ , Φ₆ , eq″ , eql″ , Trσ≈ = [] ∷ Φ₁ , Φ₂ , Γs ++ Φ₃ , Φ₄
                                      , refl , sym (++-++⁺ Γs)
                                      , refl , trans (length-++ Γs) (trans (cong (len Γs +_) eql′) (sym eqL))
                                      , helper (++⁺-cancelˡ′ (Γs ++ Φ₃) Φ₅
                                                            (trans (++-++⁺ Γs) eq″)
                                                            (sym (trans eql″
                                                                 (trans eqL
                                                                 (trans (cong (_ +_) (sym eql′))
                                                                        (sym (length-++ Γs)))))))
  where eqL = O-resp-≈ (suc n) σ≈；
        helper : Φ₄ ≡ Φ₆ → Φ₄ ⊢r S-Tr σ (suc n) ∶ Φ₂
        helper refl = s≈-resp-⊢r Trσ≈ Trδ

⊢r-Tr′ : ∀ Γs → Ψ ⊢r σ ∶ Γs ++⁺ Ψ′ → ∃₂ λ Φ₁ Φ₂ → Ψ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ O σ (len Γs) × Φ₂ ⊢r Tr σ (len Γs) ∶ Ψ′
⊢r-Tr′ Γs ⊢σ
  with ⊢r-Tr (len Γs) ⊢σ (length-<-++⁺ Γs)
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
     , eq , eq′ , eql , eql′ , Trδ
     rewrite ++⁺-cancelˡ′ Γs Φ₁ eq (sym eql) = Φ₃ , Φ₄ , eq′ , eql′ , Trδ

⊢r-comp : Ψ′ ⊢r σ′ ∶ Ψ″ → Ψ ⊢r σ ∶ Ψ′ → Ψ ⊢r σ′ ∘ σ ∶ Ψ″
⊢r-comp (r-I σ′≈I) ⊢σ              = s≈-resp-⊢r (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈I) (I-∘ (⊢r⇒⊢s ⊢σ))) ⊢σ
⊢r-comp (r-p ⊢δ σ′≈p) ⊢σ           = r-p (⊢r-comp ⊢δ ⊢σ)
                                   (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈p)
                                              (∘-assoc (⊢r⇒⊢s ⊢σ) (⊢r⇒⊢s ⊢δ) S-p))
⊢r-comp (r-； Γs ⊢δ σ′≈； refl) ⊢σ
  with ⊢r-Tr′ Γs ⊢σ
...  | Δs , Ψ″ , refl , eql , ⊢Trσ = r-； Δs (⊢r-comp ⊢δ ⊢Trσ)
                                         (s-≈-trans (∘-cong (s≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈；)
                                                    (subst (λ n → Δs ++⁺ Ψ″ ⊢s _ ≈ _ ； n ∶ _)
                                                           (sym eql)
                                                           (；-∘ Γs (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) refl)))
                                         refl
