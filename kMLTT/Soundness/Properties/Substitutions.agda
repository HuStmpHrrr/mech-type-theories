{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- prove that the gluing model is cumulative
module kMLTT.Soundness.Properties.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.List.Properties as Lₚ

open import kMLTT.Statics.Properties as Sta
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext
open import kMLTT.Semantics.Properties.Domain fext as Sem
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Mt fext

⊢s®-resp-O : ∀ n →
             (⊢Δ : ⊢ Δ) →
             Γ ⊢s σ ∶ ⊢Δ ® ρ →
             n < len Δ →
             --------------------
             O σ n ≡ O ρ n
⊢s®-resp-O {_} {_} {_} {_} 0       ⊢Δ        σ∼ρ n<Δ       = refl
⊢s®-resp-O {_} {_} {_} {ρ} (suc n) ⊢[]       σ∼ρ (s≤s ())
⊢s®-resp-O {_} {_} {σ} {ρ} (suc n) (⊢κ ⊢Δ)   σ∼ρ (s≤s n<Δ) = trans (Sta.O-+ σ 1 _) (cong₂ _+_ O≡ (trans (O-resp-≈ n ≈σ∥) (⊢s®-resp-O n ⊢Δ step n<Δ)))
  where
    open Gluκ σ∼ρ
⊢s®-resp-O {_} {_} {σ} {_} (suc n) (⊢∺ ⊢Δ x) σ∼ρ n<Δ       = trans (O-resp-≈ (suc n) ≈pσ) (⊢s®-resp-O (suc n) ⊢Δ step n<Δ)
  where
    open Glu∺ σ∼ρ


⊢s®-resp-≈ : (⊢Δ : ⊢ Δ) →
             Γ ⊢s σ ∶ ⊢Δ ® ρ →
             Γ ⊢s σ ≈ σ′ ∶ Δ →
             -------------------
             Γ ⊢s σ′ ∶ ⊢Δ ® ρ
⊢s®-resp-≈                      ⊢[]     σ∼ρ σ≈σ′ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
⊢s®-resp-≈ {_} {Γ} {_} {ρ} {σ′} (⊢κ ⊢Δ) σ∼ρ σ≈σ′ = helper
  where
    module gluκ = Gluκ σ∼ρ
    open gluκ

    helper : Γ ⊢s σ′ ∶ ⊢κ ⊢Δ ® ρ
    helper = record
             { gluκ
             ; ⊢σ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
             ; ≈σ∥ = s-≈-trans (s-≈-sym (∥-resp-≈″ Ψs⁻ L.[ [] ] (subst (_⊢s _ ≈ _ ∶ _) Γ≡ σ≈σ′) len≡)) ≈σ∥
             ; O≡ = trans (sym (O-resp-≈ 1 σ≈σ′)) O≡
             ; len≡ = trans len≡ (O-resp-≈ 1 σ≈σ′)
             }
⊢s®-resp-≈ {_} {Γ} {_} {ρ} {σ′} ⊢TΔ@(⊢∺ ⊢Δ ⊢T) σ∼ρ σ≈σ′ = helper
  where
    module glu∺ = Glu∺ σ∼ρ
    open glu∺

    σ′≈σ = s-≈-sym σ≈σ′
    ⊢σ′ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))

    helper : Γ ⊢s σ′ ∶ ⊢∺ ⊢Δ ⊢T ® ρ
    helper = record
             { glu∺
             ; ⊢σ = ⊢σ′
             ; ≈pσ = s-≈-trans (p-cong (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))) σ′≈σ) ≈pσ
             ; ≈v0σ = ≈-trans (≈-conv ([]-cong (≈-refl (vlookup ⊢TΔ here)) σ′≈σ) (≈-trans (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ′) ([]-cong-Se″ ⊢T (∘-cong σ′≈σ (wk-≈ ⊢TΔ)))) ([]-cong-Se″ ⊢T ≈pσ))) ≈v0σ
             }

∥-⊢s® : ∀ n →
        (⊢Δ : ⊢ Δ) →
        Γ ⊢s σ ∶ ⊢Δ ® ρ →
        n < len Δ →
        -----------------------------------------------
        ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
           Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
         × len Ψs ≡ O σ n × len Ψs′ ≡ n
         × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ n ∶ ⊢Δ′ ® ρ ∥ n
∥-⊢s®                 0       ⊢Δ         σ∼ρ n<Δ       = [] , []
                                                       , _ , _
                                                       , refl , refl
                                                       , refl , refl
                                                       , ⊢Δ , σ∼ρ
∥-⊢s®                 (suc n) ⊢[]        σ∼ρ (s≤s ())
∥-⊢s® {Δ} {Γ} {σ} {ρ} (suc n) (⊢κ ⊢Δ)    σ∼ρ (s≤s n<Δ) = helper
  where
    open Gluκ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊢Δ′ ® ρ ∥ suc n
    helper
      with ∥-⊢s® n ⊢Δ step n<Δ
    ...  | Ψs , Ψs′ , _ , _ , refl , refl , Ψs≡Oσ∥ , refl , ⊢Δ′ , σ∥∼ρ∥
          rewrite Sta.∥-+ σ 1 (len Ψs′)   = Ψs⁻ ++ Ψs , _ ∷ Ψs′
                                          , _ , _
                                          , trans Γ≡ (sym (++-++⁺ Ψs⁻)) , refl
                                          , trans (length-++ Ψs⁻) (trans (cong₂ _+_
                                                                                len≡
                                                                                (trans Ψs≡Oσ∥ (sym (O-resp-≈ (len Ψs′) ≈σ∥))))
                                                                         (sym (Sta.O-+ σ 1 _))) , refl
                                          , ⊢Δ′ , ⊢s®-resp-≈ ⊢Δ′ σ∥∼ρ∥ (∥-resp-≈″ Ψs Ψs′ (s-≈-sym ≈σ∥) Ψs≡Oσ∥)
∥-⊢s® {Δ} {Γ} {σ} {ρ} (suc n) (⊢∺ ⊢Δ ⊢T) σ∼ρ n<Δ     = helper
  where
    open Glu∺ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊢ Δ′) λ ⊢Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊢Δ′ ® ρ ∥ suc n
    helper
      with ∥-⊢s® (suc n) ⊢Δ step n<Δ
    ...  | Ψs , Ψ′ ∷ Ψs′ , _ , _ , refl , refl , Ψs≡Opσ , refl , ⊢Δ′ , pσ∼drop[ρ]
        rewrite O-resp-≈ (suc (len Ψs′)) ≈pσ = Ψs , (_ ∷ Ψ′) ∷ Ψs′
                                             , _ , _
                                             , refl , refl
                                             , Ψs≡Opσ , refl
                                             , ⊢Δ′ , ⊢s®-resp-≈ ⊢Δ′ pσ∼drop[ρ] (s-≈-trans (∥-resp-≈″ Ψs (Ψ′ ∷ Ψs′) (s-≈-sym ≈pσ) Ψs≡Opσ) (I-∘ (∥-⊢s″ Ψs ((_ ∷ Ψ′) ∷ Ψs′) ⊢σ (trans Ψs≡Opσ (sym (O-resp-≈ (suc (len Ψs′)) ≈pσ))))))

∥-⊢s®′ : ∀ Ψs →
        (⊢ΨsΔ : ⊢ Ψs ++⁺ Δ) →
        Γ ⊢s σ ∶ ⊢ΨsΔ ® ρ →
        -----------------------------------------------
        ∃₂ λ Ψs′ Γ′ →
           Γ ≡ Ψs′ ++⁺ Γ′
         × len Ψs′ ≡ O σ (len Ψs)
         × Σ (⊢ Δ) λ ⊢Δ → Γ′ ⊢s σ ∥ (len Ψs) ∶ ⊢Δ ® ρ ∥ (len Ψs)
∥-⊢s®′ Ψs ⊢ΨsΔ σ∼ρ
  with ∥-⊢s® (len Ψs) ⊢ΨsΔ σ∼ρ (length-<-++⁺ Ψs)
... | Ψs′ , Ψs₁ , _ , _ , Γ≡Ψs′Γ′ , ΨsΔ≡Ψs₁Δ₁ , Ψs′≡Oσ , Ψs≡Ψs₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΔ≡Ψs₁Δ₁ (sym Ψs≡Ψs₁) = Ψs′ , _ , Γ≡Ψs′Γ′ , Ψs′≡Oσ , ⊢Δ₁ , σ∥≈

∥-⊢s®″ : ∀ Ψs Ψs′ →
        (⊢Ψs′Δ : ⊢ Ψs′ ++⁺ Δ) →
        Ψs ++⁺ Γ ⊢s σ ∶ ⊢Ψs′Δ ® ρ →
        len Ψs ≡ O σ (len Ψs′) →
        -----------------------------------------------
        Σ (⊢ Δ) λ ⊢Δ → Γ ⊢s σ ∥ (len Ψs′) ∶ ⊢Δ ® ρ ∥ (len Ψs′)
∥-⊢s®″ Ψs Ψs′ ⊢Ψs′Δ σ∼ρ Ψs≡Oσ
  with ∥-⊢s®′ Ψs′ ⊢Ψs′Δ σ∼ρ
... | Ψs₁ , _ , ΨsΓ≡Ψs₁Γ₁ , Ψs≡Oσ₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΓ≡Ψs₁Γ₁ (trans Ψs≡Oσ (sym Ψs≡Oσ₁)) = ⊢Δ₁ , σ∥≈
