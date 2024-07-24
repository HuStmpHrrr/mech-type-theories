{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Properties of the gluing model for substitutions
module Mint.Soundness.Properties.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ
open import Data.List.Properties as Lₚ

open import Mint.Statics.Properties as Sta
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Properties.Evaluation fext
open import Mint.Semantics.Properties.PER fext
open import Mint.Semantics.Readback
open import Mint.Completeness.LogRel
open import Mint.Completeness.Fundamental fext
open import Mint.Soundness.Cumulativity fext
open import Mint.Soundness.LogRel
open import Mint.Soundness.Properties.LogRel fext
open import Mint.Soundness.Properties.Mt fext
open import Mint.Soundness.Realizability fext

-- If a substitution is related to an environment, then the substitution is well-formed.
s®⇒⊢s : (⊩Δ : ⊩ Δ) →
        Γ ⊢s σ ∶ ⊩Δ ® ρ →
        -----------------
        Γ ⊢s σ ∶ Δ
s®⇒⊢s ⊩[]         σ∼ρ = σ∼ρ
s®⇒⊢s (⊩κ ⊩Δ)     σ∼ρ = Gluκ.⊢σ σ∼ρ
s®⇒⊢s (⊩∺ ⊩Δ _ _) σ∼ρ = Glu∺.⊢σ σ∼ρ

-- If an environment is related to a substitution, then this environment is in the PER model.
s®⇒⟦⟧ρ′ : (⊩Δ : ⊩ Δ)
          (⊨Δ : ⊨ Δ) →
          Γ ⊢s σ ∶ ⊩Δ ® ρ →
          --------------------
          ρ ∈′ ⟦ ⊨Δ ⟧ρ
s®⇒⟦⟧ρ′ ⊩[] []-≈ σ∼ρ                     = tt
s®⇒⟦⟧ρ′ (⊩κ ⊩Δ) (κ-cong ⊨Δ) σ∼ρ          = s®⇒⟦⟧ρ′ ⊩Δ ⊨Δ step , refl
  where open Gluκ σ∼ρ
s®⇒⟦⟧ρ′ (⊩∺ ⊩Δ _ gT) (∺-cong ⊨Δ rel) σ∼ρ = dropρ∈ , El-transp T∈𝕌 T≈T′ (®El⇒∈El T∈𝕌 t∼ρ0) (⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′)
  where open Glu∺ σ∼ρ
        dropρ∈ = s®⇒⟦⟧ρ′ ⊩Δ ⊨Δ step
        open RelTyp (rel dropρ∈) renaming (↘⟦T⟧ to ↘⟦T⟧′)

s®⇒⟦⟧ρ : (⊩Δ : ⊩ Δ) →
         Γ ⊢s σ ∶ ⊩Δ ® ρ →
         --------------------------
         Σ (⊨ Δ) λ ⊨Δ → ρ ∈′ ⟦ ⊨Δ ⟧ρ
s®⇒⟦⟧ρ ⊩Δ σ∼ρ = fundamental-⊢Γ (⊩⇒⊢ ⊩Δ) , s®⇒⟦⟧ρ′ ⊩Δ _ σ∼ρ


-- The gluing model respects substitution equivalence.
s®-resp-s≈ : (⊩Δ : ⊩ Δ) →
             Γ ⊢s σ ∶ ⊩Δ ® ρ →
             Γ ⊢s σ ≈ σ′ ∶ Δ →
             -------------------
             Γ ⊢s σ′ ∶ ⊩Δ ® ρ
s®-resp-s≈                      ⊩[]     σ∼ρ σ≈σ′ = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
s®-resp-s≈ {_} {Γ} {_} {ρ} {σ′} (⊩κ ⊩Δ) σ∼ρ σ≈σ′ = helper
  where
    open module gluκ = Gluκ σ∼ρ

    helper : Γ ⊢s σ′ ∶ ⊩κ ⊩Δ ® ρ
    helper = record
             { gluκ
             ; ⊢σ   = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))
             ; ≈σ∥  = s-≈-trans (s-≈-sym (∥-resp-≈″ Ψs⁻ L.[ [] ] (subst (_⊢s _ ≈ _ ∶ _) Γ≡ σ≈σ′) len≡)) ≈σ∥
             ; O≡   = trans (sym (O-resp-≈ 1 σ≈σ′)) O≡
             ; len≡ = trans len≡ (O-resp-≈ 1 σ≈σ′)
             }
s®-resp-s≈ {_} {Γ} {_} {ρ} {σ′} ⊩TΔ@(⊩∺ ⊩Δ ⊢T _) σ∼ρ σ≈σ′ = helper
  where
    open module glu∺ = Glu∺ σ∼ρ

    ⊢TΔ  = ⊩⇒⊢ ⊩TΔ
    σ′≈σ = s-≈-sym σ≈σ′
    ⊢σ′  = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))

    helper : Γ ⊢s σ′ ∶ ⊩TΔ ® ρ
    helper = record
             { glu∺
             ; ⊢σ   = ⊢σ′
             ; ≈pσ  = s-≈-trans (p-cong (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))) σ′≈σ) ≈pσ
             ; ≈v0σ = ≈-trans (≈-conv ([]-cong (≈-refl (vlookup ⊢TΔ here)) σ′≈σ) (≈-trans (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ′) ([]-cong-Se″ ⊢T (∘-cong σ′≈σ (wk-≈ ⊢TΔ)))) ([]-cong-Se″ ⊢T ≈pσ))) ≈v0σ
             }


-- The gluing model respects context stack equivalence.
s®-resp-≈′ : (⊩Δ : ⊩ Δ)
             (⊩Δ′ : ⊩ Δ′) →
             Γ ⊢s σ ∶ ⊩Δ ® ρ →
             ⊢ Δ ≈ Δ′ →
             -------------------
             Γ ⊢s σ ∶ ⊩Δ′ ® ρ
s®-resp-≈′ ⊩[] ⊩[] σ∼ρ []-≈                   = σ∼ρ
s®-resp-≈′ (⊩κ ⊩Δ) (⊩κ ⊩Δ′) σ∼ρ (κ-cong Δ≈Δ′) = record
  { gluκ
  ; ⊢σ   = s-conv ⊢σ (κ-cong Δ≈Δ′)
  ; ≈σ∥  = s-≈-conv ≈σ∥ Δ≈Δ′
  ; step = s®-resp-≈′ ⊩Δ ⊩Δ′ step Δ≈Δ′
  }
  where open module gluκ = Gluκ σ∼ρ
s®-resp-≈′ (⊩∺ {i = i} ⊩Δ ⊢T gT) (⊩∺ {i = j} ⊩Δ′ ⊢T′ gT′) σ∼ρ (∺-cong {T′ = T′} {i = k} Δ≈Δ′ T≈T′)
  with s®-resp-≈′ ⊩Δ ⊩Δ′ (Glu∺.step σ∼ρ) Δ≈Δ′
     | s®⇒⟦⟧ρ ⊩Δ (Glu∺.step σ∼ρ)
     | fundamental-t≈t′ T≈T′
...  | σ∼ρ′
     | ⊨Δ , dropρ∈
     | ⊨Δ₁ , _ , Trel₁
     with Trel₁ (⊨-irrel ⊨Δ ⊨Δ₁ dropρ∈)
        | gT′ σ∼ρ′
...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n _ }
        , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
        | record { ⟦T⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T′⟧ ; T∈𝕌 = T′∈𝕌 ; T∼⟦T⟧ = T′∼⟦T′⟧ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ i<n
              | ⟦⟧-det ↘⟦T⟧₁ (Glu∺.↘⟦T⟧ σ∼ρ)
              | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧ = record
  { ⊢σ   = s-conv ⊢σ (∺-cong Δ≈Δ′ T≈T′)
  ; pσ   = pσ
  ; v0σ  = v0σ
  ; ⟦T⟧  = ⟦T′⟧
  ; ≈pσ  = s-≈-conv ≈pσ Δ≈Δ′
  ; ≈v0σ = ≈-conv ≈v0σ ([]-cong-Se′ T≈T′ ⊢pσ)
  ; ↘⟦T⟧ = ↘⟦T′⟧
  ; T∈𝕌  = T′∈𝕌
  ; t∼ρ0 = ®El-master T∈𝕌 T′∈𝕌 T≈T′₁ T′∼⟦T′⟧ t∼ρ0 ([]-cong-Se′ T≈T′ ⊢pσ)
  ; step = σ∼ρ′
  }
  where
    open module glu∺ = Glu∺ σ∼ρ

    ⊢pσ : _ ⊢s pσ ∶ _
    ⊢pσ = proj₁ (proj₂ (proj₂ (presup-s-≈ ≈pσ)))


-- The witnesses of ⊩ is irrelevant.
s®-irrel : (⊩Δ ⊩Δ′ : ⊩ Δ) →
           Γ ⊢s σ ∶ ⊩Δ ® ρ →
           ------------------
           Γ ⊢s σ ∶ ⊩Δ′ ® ρ
s®-irrel ⊩Δ ⊩Δ′ σ∼ρ = s®-resp-≈′ ⊩Δ ⊩Δ′ σ∼ρ (⊢≈-refl (⊩⇒⊢ ⊩Δ))


-- ⊩ respects context stack equivalence.
⊩-resp-≈ : ⊩ Γ →
           ⊢ Γ ≈ Δ →
           ----------
           ⊩ Δ
⊩-resp-≈ ⊩[] []-≈                       = ⊩[]
⊩-resp-≈ (⊩κ ⊩Γ) (κ-cong Γ≈Δ)           = ⊩κ (⊩-resp-≈ ⊩Γ Γ≈Δ)
⊩-resp-≈ (⊩∺ {i = i} ⊩Γ _ gT) (∺-cong {T′ = T′} {j} Γ≈Δ T≈T′)
  with presup-≈ T≈T′
...  | _ , _ , ⊢T′ , _ = ⊩∺ ⊩Δ (lift-⊢-Se-max′ (ctxeq-tm Γ≈Δ ⊢T′)) helper
  where ⊩Δ    = ⊩-resp-≈ ⊩Γ Γ≈Δ
        lvl   = max i j
        i<lvl = m≤m⊔n i j
        j<lvl = m≤n⊔m i j
        helper : Δ′ ⊢s σ ∶ ⊩Δ ® ρ → GluTyp (max i j) Δ′ T′ σ ρ
        helper σ∼ρ
          with s®-resp-≈′ ⊩Δ ⊩Γ σ∼ρ (⊢≈-sym Γ≈Δ)
             | fundamental-t≈t′ T≈T′
        ...  | σ∼ρ′
             | ⊨Γ , _ , Trel
             with s®⇒⟦⟧ρ ⊩Γ σ∼ρ′
        ...     | ⊨Γ₁ , ρ∈
                with Trel (⊨-irrel ⊨Γ₁ ⊨Γ ρ∈)
                   | gT σ∼ρ′
        ...        | record { ⟦T⟧ = .(U j) ; ↘⟦T⟧ = ⟦Se⟧ .j ; T≈T′ = U j<n _ }
                   , record { ⟦t′⟧ = ⟦T′⟧ ; ↘⟦t⟧ = ↘⟦T⟧′ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′₁ }
                   | record { ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
                   rewrite 𝕌-wellfounded-≡-𝕌 _ j<n
                         | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
          { ⟦T⟧   = ⟦T′⟧
          ; ↘⟦T⟧  = ↘⟦T′⟧
          ; T∈𝕌   = T′∈𝕌
          ; T∼⟦T⟧ = ®-transport T∈𝕌′ T′∈𝕌 (𝕌-cumu j<lvl T≈T′₁)
                                (®-resp-≈ T∈𝕌′ (®-cumu T∈𝕌 T∼⟦T⟧ i<lvl)
                                ([]-cong-Se′ (lift-⊢≈-Se-max′ T≈T′) ⊢σ))
          }
          where T′∈𝕌 : ⟦T′⟧ ∈′ 𝕌 lvl
                T′∈𝕌 = 𝕌-cumu j<lvl (𝕌-refl (𝕌-sym T≈T′₁))
                T∈𝕌′ = 𝕌-cumu i<lvl T∈𝕌
                ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ′

-- The gluing model respects context stack equivalence (in the codomain).
s®-resp-≈ : (⊩Δ : ⊩ Δ) →
            Γ ⊢s σ ∶ ⊩Δ ® ρ →
            ⊢ Δ ≈ Δ′ →
            -------------------------------
            Σ (⊩ Δ′) λ ⊩Δ′ → Γ ⊢s σ ∶ ⊩Δ′ ® ρ
s®-resp-≈ ⊩Δ σ∼ρ Δ≈Δ′ = ⊩Δ′ , s®-resp-≈′ ⊩Δ ⊩Δ′ σ∼ρ Δ≈Δ′
  where ⊩Δ′ = ⊩-resp-≈ ⊩Δ Δ≈Δ′

-- Related substitutions and environments have equal truncation offsets.
s®-resp-O : ∀ n →
            (⊩Δ : ⊩ Δ) →
            Γ ⊢s σ ∶ ⊩Δ ® ρ →
            n < len Δ →
            --------------------
            O σ n ≡ O ρ n
s®-resp-O {_} {_} {_} {_} 0       ⊩Δ        σ∼ρ n<Δ       = refl
s®-resp-O {_} {_} {_} {ρ} (suc n) ⊩[]       σ∼ρ (s≤s ())
s®-resp-O {_} {_} {σ} {ρ} (suc n) (⊩κ ⊩Δ)   σ∼ρ (s≤s n<Δ) = trans (Sta.O-+ σ 1 _) (cong₂ _+_ O≡ (trans (O-resp-≈ n ≈σ∥) (s®-resp-O n ⊩Δ step n<Δ)))
  where
    open Gluκ σ∼ρ
s®-resp-O {_} {_} {σ} {_} (suc n) (⊩∺ ⊩Δ _ _) σ∼ρ n<Δ     = trans (O-resp-≈ (suc n) ≈pσ) (s®-resp-O (suc n) ⊩Δ step n<Δ)
  where
    open Glu∺ σ∼ρ


-- Truncations of related substitutions and environments remain related.
∥-s® : ∀ n →
       (⊩Δ : ⊩ Δ) →
       Γ ⊢s σ ∶ ⊩Δ ® ρ →
       n < len Δ →
       -----------------------------------------------
       ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
          Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
        × len Ψs ≡ O σ n × len Ψs′ ≡ n
        × Σ (⊩ Δ′) λ ⊩Δ′ → Γ′ ⊢s σ ∥ n ∶ ⊩Δ′ ® ρ ∥ n
∥-s®                 0       ⊩Δ         σ∼ρ n<Δ       = [] , []
                                                       , _ , _
                                                       , refl , refl
                                                       , refl , refl
                                                       , ⊩Δ , σ∼ρ
∥-s® {Δ} {Γ} {σ} {ρ} (suc n) (⊩κ ⊩Δ)    σ∼ρ (s≤s n<Δ) = helper
  where
    open Gluκ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊩ Δ′) λ ⊩Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊩Δ′ ® ρ ∥ suc n
    helper
      with ∥-s® n ⊩Δ step n<Δ
    ...  | Ψs , Ψs′ , _ , _ , refl , refl , Ψs≡Oσ∥ , refl , ⊩Δ′ , σ∥∼ρ∥
          rewrite Sta.∥-+ σ 1 (len Ψs′)   = Ψs⁻ ++ Ψs , _ ∷ Ψs′
                                          , _ , _
                                          , trans Γ≡ (sym (++-++⁺ Ψs⁻)) , refl
                                          , trans (length-++ Ψs⁻) (trans (cong₂ _+_
                                                                                len≡
                                                                                (trans Ψs≡Oσ∥ (sym (O-resp-≈ (len Ψs′) ≈σ∥))))
                                                                         (sym (Sta.O-+ σ 1 _))) , refl
                                          , ⊩Δ′ , s®-resp-s≈ ⊩Δ′ σ∥∼ρ∥ (∥-resp-≈″ Ψs Ψs′ (s-≈-sym ≈σ∥) Ψs≡Oσ∥)
∥-s® {Δ} {Γ} {σ} {ρ} (suc n) (⊩∺ ⊩Δ ⊢T _) σ∼ρ n<Δ     = helper
  where
    open Glu∺ σ∼ρ

    helper : ∃₂ λ Ψs Ψs′ →
             ∃₂ λ Γ′ Δ′ →
                  Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′
                × len Ψs ≡ O σ (suc n) × len Ψs′ ≡ suc n
                × Σ (⊩ Δ′) λ ⊩Δ′ → Γ′ ⊢s σ ∥ suc n ∶ ⊩Δ′ ® ρ ∥ suc n
    helper
      with ∥-s® (suc n) ⊩Δ step n<Δ
    ...  | Ψs , Ψ′ ∷ Ψs′ , _ , _ , refl , refl , Ψs≡Opσ , refl , ⊩Δ′ , pσ∼drop[ρ]
        rewrite O-resp-≈ (suc (len Ψs′)) ≈pσ = Ψs , (_ ∷ Ψ′) ∷ Ψs′
                                             , _ , _
                                             , refl , refl
                                             , Ψs≡Opσ , refl
                                             , ⊩Δ′ , s®-resp-s≈ ⊩Δ′ pσ∼drop[ρ] (s-≈-trans (∥-resp-≈″ Ψs (Ψ′ ∷ Ψs′) (s-≈-sym ≈pσ) Ψs≡Opσ) (I-∘ (∥-⊢s″ Ψs ((_ ∷ Ψ′) ∷ Ψs′) ⊢σ (trans Ψs≡Opσ (sym (O-resp-≈ (suc (len Ψs′)) ≈pσ))))))

∥-s®′ : ∀ Ψs →
        (⊩ΨsΔ : ⊩ Ψs ++⁺ Δ) →
        Γ ⊢s σ ∶ ⊩ΨsΔ ® ρ →
        -----------------------------------------------
        ∃₂ λ Ψs′ Γ′ →
           Γ ≡ Ψs′ ++⁺ Γ′
         × len Ψs′ ≡ O σ (len Ψs)
         × Σ (⊩ Δ) λ ⊩Δ → Γ′ ⊢s σ ∥ (len Ψs) ∶ ⊩Δ ® ρ ∥ (len Ψs)
∥-s®′ Ψs ⊩ΨsΔ σ∼ρ
  with ∥-s® (len Ψs) ⊩ΨsΔ σ∼ρ (length-<-++⁺ Ψs)
... | Ψs′ , Ψs₁ , _ , _ , Γ≡Ψs′Γ′ , ΨsΔ≡Ψs₁Δ₁ , Ψs′≡Oσ , Ψs≡Ψs₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΔ≡Ψs₁Δ₁ (sym Ψs≡Ψs₁) = Ψs′ , _ , Γ≡Ψs′Γ′ , Ψs′≡Oσ , ⊢Δ₁ , σ∥≈

∥-s®″ : ∀ Ψs Ψs′ →
        (⊩Ψs′Δ : ⊩ Ψs′ ++⁺ Δ) →
        Ψs ++⁺ Γ ⊢s σ ∶ ⊩Ψs′Δ ® ρ →
        len Ψs ≡ O σ (len Ψs′) →
        -----------------------------------------------
        Σ (⊩ Δ) λ ⊩Δ → Γ ⊢s σ ∥ (len Ψs′) ∶ ⊩Δ ® ρ ∥ (len Ψs′)
∥-s®″ Ψs Ψs′ ⊩Ψs′Δ σ∼ρ Ψs≡Oσ
  with ∥-s®′ Ψs′ ⊩Ψs′Δ σ∼ρ
... | Ψs₁ , _ , ΨsΓ≡Ψs₁Γ₁ , Ψs≡Oσ₁ , ⊢Δ₁ , σ∥≈
    rewrite ++⁺-cancelˡ′ Ψs Ψs₁ ΨsΓ≡Ψs₁Γ₁ (trans Ψs≡Oσ (sym Ψs≡Oσ₁)) = ⊢Δ₁ , σ∥≈


⊩-∥ : ∀ Ψs →
      ⊩ Ψs ++⁺ Γ →
      ------------
      ⊩ Γ
⊩-∥ [] ⊩ΨsΓ                       = ⊩ΨsΓ
⊩-∥ (.[] ∷ Ψs) (⊩κ ⊩ΨsΓ)          = ⊩-∥ Ψs ⊩ΨsΓ
⊩-∥ ((_ ∷ Ψ) ∷ Ψs) (⊩∺ ⊩ΨsΓ ⊢T _) = ⊩-∥ (Ψ ∷ Ψs) ⊩ΨsΓ


-- Monotonicity of the gluing model
s®-mon : (⊩Δ : ⊩ Δ) →
         Γ′ ⊢r τ ∶ Γ →
         Γ ⊢s σ ∶ ⊩Δ ® ρ →
         ------------------
         Γ′ ⊢s σ ∘ τ ∶ ⊩Δ ® ρ [ mt τ ]
s®-mon ⊩[] ⊢τ σ∼ρ             = s-∘ (⊢r⇒⊢s ⊢τ) σ∼ρ
s®-mon {_} {Γ′} {τ} {Γ} {σ} {ρ} (⊩κ ⊩Δ) ⊢τ σ∼ρ
  with chop Γ′ (O-<-len (O σ 1) (⊢r⇒⊢s ⊢τ) (O-<-len 1 (Gluκ.⊢σ σ∼ρ) (s≤s (s≤s z≤n))))
...  | Ψs′ , Γ′₁ , refl , eql = record
  { ⊢σ   = s-∘ ⊢τ′ ⊢σ
  ; Ψs⁻  = Ψs′
  ; Γ∥   = Γ′₁
  ; σ∥   = σ∥ ∘ τ ∥ O σ 1
  ; Γ≡   = refl
  ; ≈σ∥  = ∘-cong (s-≈-refl ⊢τ∥′) ≈σ∥
  ; O≡   = trans (cong (O τ) O≡) (O-resp-mt τ (proj₁ (ρ 0)))
  ; len≡ = eql
  ; step = helper
  }
  where open Gluκ σ∼ρ
        ⊢τ′  = ⊢r⇒⊢s ⊢τ
        ⊢τ∥-helper : Ψs′ ++⁺ Γ′₁ ⊢r τ ∶ Γ → Γ′₁ ⊢r τ ∥ O σ 1 ∶ Γ∥
        ⊢τ∥-helper ⊢τ
          rewrite sym len≡
                | Γ≡ = ⊢r-∥″ Ψs′ Ψs⁻ ⊢τ eql
        ⊢τ∥  = ⊢τ∥-helper ⊢τ
        ⊢τ∥′ = ⊢r⇒⊢s ⊢τ∥

        helper : Γ′₁ ⊢s σ∥ ∘ τ ∥ O σ 1 ∶ ⊩Δ ® ((ρ [ mt τ ]) ∥ 1)
        helper
          with s®-mon ⊩Δ ⊢τ∥ step
        ...  | rel
             rewrite ρ-∥-[] ρ (mt τ) 1
                   | sym (s®-resp-O 1 (⊩κ ⊩Δ) σ∼ρ ((s≤s (s≤s z≤n))))
                   | mt-∥ τ (O σ 1) = rel

s®-mon {_} {Γ′} {τ} {Γ} {σ} {ρ} (⊩∺ {_} {T} ⊩Δ ⊢T _) ⊢τ σ∼ρ = record
  { ⊢σ   = ⊢στ
  ; pσ   = pσ ∘ τ
  ; v0σ  = v0σ [ τ ]
  ; ⟦T⟧  = ⟦T⟧ [ mt τ ]
  ; ≈pσ  = ≈pστ
  ; ≈v0σ = ≈-trans (≈-conv ([∘] ⊢τ′ ⊢σ (vlookup ⊢TΔ here))
                           (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢στ)
                                    ([]-cong-Se″ ⊢T ≈pστ)))
                   (≈-conv ([]-cong ≈v0σ (s-≈-refl ⊢τ′))
                           ([∘]-Se ⊢T ⊢pσ ⊢τ′))
  ; ↘⟦T⟧ = subst (⟦ T ⟧_↘ ⟦T⟧ [ mt τ ]) (drop-mon ρ (mt τ)) (⟦⟧-mon (mt τ) ↘⟦T⟧)
  ; T∈𝕌  = Tτ∈𝕌
  ; t∼ρ0 = ®El-resp-T≈ Tτ∈𝕌 (®El-mon T∈𝕌 Tτ∈𝕌 t∼ρ0 ⊢τ) ([∘]-Se ⊢T ⊢pσ ⊢τ′)
  ; step = helper
  }
  where open Glu∺ σ∼ρ
        ⊢Δ   = ⊩⇒⊢ ⊩Δ
        ⊢TΔ  = ⊢∺ ⊢Δ ⊢T
        ⊢τ′  = ⊢r⇒⊢s ⊢τ
        ⊢στ  = s-∘ ⊢τ′ ⊢σ
        ≈pστ = s-≈-trans (p-∘ ⊢σ ⊢τ′) (∘-cong (s-≈-refl ⊢τ′) ≈pσ)
        ⊢pσ  = proj₁ (proj₂ (proj₂ (presup-s-≈ ≈pσ)))
        Tτ∈𝕌 = 𝕌-mon (mt τ) T∈𝕌

        helper : Γ′ ⊢s pσ ∘ τ ∶ ⊩Δ ® drop (mtran-Envs ρ (mt τ))
        helper
          rewrite sym (drop-mon ρ (mt τ)) = s®-mon ⊩Δ ⊢τ step


-- We can cons the gluing model of terms on top of one of substitutions.
s®-cons-type : ⊩ T ∺ Γ → Set
s®-cons-type ⊩TΓ@(⊩∺ {_} {T} {i} ⊩Γ _ rel) =
  ∀ {Δ σ ρ t a}
  (σ∼ρ : Δ ⊢s σ ∶ ⊩Γ ® ρ) →
  let open GluTyp (rel σ∼ρ) in
  Δ ⊢ t ∶ T [ σ ] ®[ i ] a ∈El T∈𝕌 →
  Δ ⊢s σ , t ∶ ⊩TΓ ® ρ ↦ a

s®-cons : (⊩TΓ : ⊩ T ∺ Γ) → s®-cons-type ⊩TΓ
s®-cons ⊩TΓ@(⊩∺ {_} {T} {i} ⊩Γ ⊢T rel) {_} {σ} {_} {t} σ∼ρ t∼a
  with s®⇒⊢s ⊩Γ σ∼ρ | rel σ∼ρ
... | ⊢σ | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
     with presup-s ⊢σ
...     | ⊢Δ , _  = record
  { ⊢σ   = s-, ⊢σ ⊢T ⊢t
  ; pσ   = σ
  ; v0σ  = t
  ; ⟦T⟧  = ⟦T⟧
  ; ≈pσ  = p-, ⊢σ ⊢T ⊢t
  ; ≈v0σ = [,]-v-ze ⊢σ ⊢T ⊢t
  ; ↘⟦T⟧ = subst (⟦ _ ⟧_↘ _) drop≡ ↘⟦T⟧
  ; T∈𝕌  = T∈𝕌
  ; t∼ρ0 = t∼a
  ; step = subst (_ ⊢s _ ∶ ⊩Γ ®_) drop≡ σ∼ρ
  }
  where ⊢t    = ®El⇒tm T∈𝕌 t∼a
        drop≡ = sym (drop-↦ _ _)


-- The identity substitution is related to initial environment.
InitEnvs⇒s®I : (⊩Δ : ⊩ Δ) →
               InitEnvs Δ ρ →
               Δ ⊢s I ∶ ⊩Δ ® ρ
InitEnvs⇒s®I ⊩[] base = s-I ⊢[]
InitEnvs⇒s®I (⊩κ ⊩Δ) (s-κ ↘ρ)
  with InitEnvs⇒s®I ⊩Δ ↘ρ
...  | I∼ρ∥ = record
               { ⊢σ = s-I (⊢κ ⊢Δ)
               ; Ψs⁻ = L.[ [] ]
               ; σ∥ = I
               ; Γ≡ = refl
               ; ≈σ∥ = I-≈ ⊢Δ
               ; O≡ = refl
               ; len≡ = refl
               ; step = I∼ρ∥
               }
  where ⊢Δ = ⊩⇒⊢ ⊩Δ
InitEnvs⇒s®I {Δ@((T ∷ Ψ) ∷ Ψs)} (⊩∺ ⊩Δ ⊢T gT) (s-∺ {ρ = ρ} ↘ρ ↘A)
  with InitEnvs⇒s®I ⊩Δ ↘ρ | ⊩⇒⊢ ⊩Δ
...  | I∼ρ | ⊢Δ
    with s®⇒⟦⟧ρ ⊩Δ I∼ρ | fundamental-⊢t ⊢T
...    | ⊨Δ , ρ∥∈ | ⊨Δ₁ , j , Trel₁
      with Trel₁ (⊨-irrel ⊨Δ ⊨Δ₁ ρ∥∈)
         | gT I∼ρ
...      | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<j _ }
         , record { ⟦t⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
         | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ i<j
              | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧
              | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
              | ⟦⟧-det ↘⟦T⟧ ↘A = record
                            { ⊢σ = s-I ⊢TΔ
                            ; ≈pσ = ∘-I (s-wk ⊢TΔ)
                            ; ≈v0σ = [I] (vlookup ⊢TΔ here)
                            ; ↘⟦T⟧ = subst (⟦ _ ⟧_↘ _) (sym (drop-↦ _ _)) ↘A
                            ; T∈𝕌 = T≈T′
                            ; t∼ρ0 = v0®x T≈T′ (®-one-sided T∈𝕌 T≈T′ (®-resp-≈ T∈𝕌 T∼⟦T⟧ ([I] ⊢T)))
                            ; step = helper _
                            }
  where ⊢TΔ = ⊢∺ ⊢Δ ⊢T
        helper : ∀ a → Δ ⊢s wk ∶ ⊩Δ ® drop (ρ ↦ a)
        helper a
          with s®-mon ⊩Δ (⊢rwk ⊢TΔ) I∼ρ
        ...  | wk∼ρ
             rewrite drop-↦ ρ a
                   | ρ-ap-vone ρ = s®-resp-s≈ ⊩Δ wk∼ρ (I-∘ (s-wk ⊢TΔ))


-- We can grow the gluing model.
s®； : ∀ {n} Ψs →
      ⊢ Ψs ++⁺ Γ →
      (⊩Δ : ⊩ Δ) →
      Γ ⊢s σ ∶ ⊩Δ ® ρ →
      len Ψs ≡ n →
      --------------------------------
      Ψs ++⁺ Γ ⊢s σ ； n ∶ (⊩κ ⊩Δ) ® ext ρ n
s®； Ψs ⊢ΨsΓ ⊩Δ σ∼ρ eq = record
                     { ⊢σ = s-； Ψs (s®⇒⊢s ⊩Δ σ∼ρ) ⊢ΨsΓ eq
                     ; Ψs⁻ = Ψs
                     ; Γ≡ = refl
                     ; ≈σ∥ = s-≈-refl (s®⇒⊢s ⊩Δ σ∼ρ)
                     ; O≡ = +-identityʳ _
                     ; len≡ = trans eq (sym (+-identityʳ _))
                     ; step = σ∼ρ
                     }
