{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Properties of the gluing model for substitutions
module NonCumulative.Soundness.Properties.Substitutions (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ
open import Data.List.Properties as Lₚ

open import NonCumulative.Statics.Ascribed.Properties.Subst
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties as Sta
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Semantics.Readback
open import NonCumulative.Completeness.LogRel
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Realizability fext

-- If a substitution is related to an environment, then the substitution is well-formed.
s®⇒⊢s : (⊩Δ : ⊩ Δ) →
        Γ ⊢s σ ∶ ⊩Δ ® ρ →
        -----------------
        Γ ⊢s σ ∶ Δ
s®⇒⊢s ⊩[]         σ∼ρ = σ∼ρ
s®⇒⊢s (⊩∷ ⊩Δ _ _) σ∼ρ = Glu∷.⊢σ σ∼ρ

-- If an environment is related to a substitution, then this environment is in the PER model.
s®⇒⟦⟧ρ′ : (⊩Δ : ⊩ Δ)
          (⊨Δ : ⊨ Δ) →
          Γ ⊢s σ ∶ ⊩Δ ® ρ →
          --------------------
          ρ ∈′ ⟦ ⊨Δ ⟧ρ
s®⇒⟦⟧ρ′ ⊩[] []-≈ σ∼ρ                     = tt
s®⇒⟦⟧ρ′ (⊩∷ ⊩Δ _ gT) (∷-cong ⊨Δ rel _) σ∼ρ = dropρ∈ , El-transp T∈𝕌 T≈T′ (®El⇒∈El T∈𝕌 t∼ρ0) (⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′)
  where open Glu∷ σ∼ρ
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
s®-resp-s≈ {_} {Γ} {_} {ρ} {σ′} ⊩TΔ@(⊩∷ ⊩Δ ⊢T _) σ∼ρ σ≈σ′ = helper
  where
    open module glu∷ = Glu∷ σ∼ρ

    ⊢TΔ  = ⊩⇒⊢ ⊩TΔ
    σ′≈σ = s-≈-sym σ≈σ′
    ⊢σ′  = proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))

    helper : Γ ⊢s σ′ ∶ ⊩TΔ ® ρ
    helper = record
             { glu∷
             ; ⊢σ   = ⊢σ′
             ; ≈pσ  = s-≈-trans (p-cong (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈σ′)))) σ′≈σ) ≈pσ
             ; ≈v0σ = ≈-trans (≈-conv ([]-cong (≈-refl (vlookup ⊢TΔ here)) σ′≈σ)
                              (≈-trans (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ′)
                                       ([]-cong-Se‴ ⊢T (∘-cong σ′≈σ (wk-≈ ⊢TΔ))))
                                       ([]-cong-Se‴ ⊢T ≈pσ))) ≈v0σ
             }

-- The gluing model respects context stack equivalence.
s®-resp-≈′ : (⊩Δ : ⊩ Δ)
             (⊩Δ′ : ⊩ Δ′) →
             Γ ⊢s σ ∶ ⊩Δ ® ρ →
             ⊢ Δ ≈ Δ′ →
             -------------------
             Γ ⊢s σ ∶ ⊩Δ′ ® ρ
s®-resp-≈′ ⊩[] ⊩[] σ® []-≈ = σ®
s®-resp-≈′ (⊩∷ ⊩Δ _ gluT) (⊩∷ ⊩Δ′ _ gluT′) σ® (∷-cong Δ≈Δ′ ⊢T ⊢T′ T≈T′ T≈′T′)
  with s®-resp-≈′ ⊩Δ ⊩Δ′ (Glu∷.step σ®) Δ≈Δ′
     | s®⇒⟦⟧ρ ⊩Δ (Glu∷.step σ®)
     | fundamental-t≈t′ T≈T′
... | σ∼ρ′
    | ⊨Δ , dropρ∈
    | ⊨Δ₁ , Trel₁
  with Trel₁ (⊨-irrel ⊨Δ ⊨Δ₁ dropρ∈)
     | gluT′ σ∼ρ′
...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
        , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
        | record { ⟦T⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T′⟧ ; T∈𝕌 = T′∈𝕌 ; T∼⟦T⟧ = T′∼⟦T′⟧ }
  rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
        | ⟦⟧-det ↘⟦T⟧₁ (Glu∷.↘⟦T⟧ σ®)
        | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧ = record
        { ⊢σ = s-conv ⊢σ (∷-cong Δ≈Δ′ ⊢T ⊢T′ T≈T′ T≈′T′)
        ; pσ = pσ
        ; v0σ = v0σ
        ; ⟦T⟧ = ⟦T′⟧
        ; ≈pσ = s-≈-conv ≈pσ Δ≈Δ′
        ; ≈v0σ = ≈-conv ≈v0σ ([]-cong-Se′ T≈T′ ⊢pσ)
        ; ↘⟦T⟧ = ↘⟦T′⟧
        ; T∈𝕌 = T′∈𝕌
        ; t∼ρ0 = ®El-transport T∈𝕌 T′∈𝕌 T≈T′₁ (®El-resp-T≈ T∈𝕌 t∼ρ0 ([]-cong-Se′ T≈T′ ⊢pσ))
        ; step = σ∼ρ′
        }
        where
          open module glu∷ = Glu∷ σ®

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
⊩-resp-≈ ⊩[] []-≈ = ⊩[]
⊩-resp-≈ (⊩∷ {i = i} ⊩Γ _ gluT) (∷-cong {T′ = T′} Γ≈Δ ⊢T ⊢T′ T≈T′ T≈′T′) = ⊩∷ ⊩Δ ⊢T′ helper
  where ⊩Δ    = ⊩-resp-≈ ⊩Γ Γ≈Δ
        helper : Δ′ ⊢s σ ∶ ⊩Δ ® ρ → GluTyp i Δ′ T′ σ ρ
        helper σ∼ρ
          with s®-resp-≈′ ⊩Δ ⊩Γ σ∼ρ (⊢≈-sym Γ≈Δ)
             | fundamental-t≈t′ T≈T′
        ... | σ∼ρ′
            | ⊨Γ , Trel
           with s®⇒⟦⟧ρ ⊩Γ σ∼ρ′
        ...     | ⊨Γ₁ , ρ∈
            with Trel (⊨-irrel ⊨Γ₁ ⊨Γ ρ∈)
               | gluT σ∼ρ′
        ...    | record { ⟦T⟧ = .(U i) ; ↘⟦T⟧ = ⟦Se⟧ .i ; T≈T′ = U eq _ }
               , record { ⟦t′⟧ = ⟦T′⟧ ; ↘⟦t⟧ = ↘⟦T⟧′ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′₁ }
               | record { ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
            rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
                   | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                   { ⟦T⟧ = ⟦T′⟧
                   ; ↘⟦T⟧ = ↘⟦T′⟧
                   ; T∈𝕌 = T′∈𝕌
                   ; T∼⟦T⟧ = ®-transport T∈𝕌 T′∈𝕌 T≈T′₁ (®-resp-≈ T∈𝕌 T∼⟦T⟧ ([]-cong-Se′ T≈T′ ⊢σ))
                   }
            where ⊢σ   = s®⇒⊢s ⊩Γ σ∼ρ′
                  T′∈𝕌 = 𝕌-refl (𝕌-sym T≈T′₁)

-- The gluing model respects context stack equivalence (in the codomain).
s®-resp-≈ : (⊩Δ : ⊩ Δ) →
            Γ ⊢s σ ∶ ⊩Δ ® ρ →
            ⊢ Δ ≈ Δ′ →
            -------------------------------
            Σ (⊩ Δ′) λ ⊩Δ′ → Γ ⊢s σ ∶ ⊩Δ′ ® ρ
s®-resp-≈ ⊩Δ σ∼ρ Δ≈Δ′ = ⊩Δ′ , s®-resp-≈′ ⊩Δ ⊩Δ′ σ∼ρ Δ≈Δ′
  where ⊩Δ′ = ⊩-resp-≈ ⊩Δ Δ≈Δ′

s®-mon : (⊩Δ : ⊩ Δ) →
         Γ′ ⊢w τ ∶ Γ →
         Γ ⊢s σ ∶ ⊩Δ ® ρ →
         ------------------
         Γ′ ⊢s σ ∘ τ ∶ ⊩Δ ® ρ
s®-mon ⊩[] ⊢τ σ® = s-∘ (⊢w⇒⊢s ⊢τ) σ®
s®-mon {_} {Γ′} {τ} {Γ} {σ} {ρ} (⊩∷ {_} {T} ⊩Δ ⊢T _) ⊢τ σ® = record
  { ⊢σ = ⊢στ
  ; pσ = pσ ∘ τ
  ; v0σ = v0σ [ τ ]
  ; ⟦T⟧ = ⟦T⟧
  ; ≈pσ = ≈pστ
  ; ≈v0σ = ≈-trans (≈-conv ([∘] ⊢τ′ ⊢σ (vlookup ⊢TΔ here))
                           (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢στ)
                                    ([]-cong-Se‴ ⊢T ≈pστ)))
                   (≈-conv ([]-cong ≈v0σ (s-≈-refl ⊢τ′))
                           ([∘]-Se ⊢T ⊢pσ ⊢τ′))
  ; ↘⟦T⟧ = ↘⟦T⟧
  ; T∈𝕌 = Tτ∈𝕌
  ; t∼ρ0 = ®El-resp-T≈ Tτ∈𝕌 (®El-mon T∈𝕌 Tτ∈𝕌 t∼ρ0 ⊢τ) ([∘]-Se ⊢T ⊢pσ ⊢τ′)
  ; step = s®-mon ⊩Δ ⊢τ step
  }
  where open Glu∷ σ®
        ⊢Δ   = ⊩⇒⊢ ⊩Δ
        ⊢TΔ  = ⊢∷ ⊢Δ ⊢T
        ⊢τ′  = ⊢w⇒⊢s ⊢τ
        ⊢στ  = s-∘ ⊢τ′ ⊢σ
        ≈pστ = s-≈-trans (p-∘ ⊢σ ⊢τ′) (∘-cong (s-≈-refl ⊢τ′) ≈pσ)
        ⊢pσ  = proj₁ (proj₂ (proj₂ (presup-s-≈ ≈pσ)))
        Tτ∈𝕌 = T∈𝕌

-- We can cons the gluing model of terms on top of one of substitutions.
s®-cons-type : ∀ {i} → ⊩ (T ↙ i) ∷ Γ → Set
s®-cons-type ⊩TΓ@(⊩∷ {_} {T} {i} ⊩Γ _ rel) =
  ∀ {Δ σ ρ t a}
  (σ∼ρ : Δ ⊢s σ ∶ ⊩Γ ® ρ) →
  let open GluTyp (rel σ∼ρ) in
  Δ ⊢ t ∶ T [ σ ] ®[ i ] a ∈El T∈𝕌 →
  Δ ⊢s σ , t ∶ (T ↙ i) ∶ ⊩TΓ ® ρ ↦ a

s®-cons : ∀ {i} → (⊩TΓ : ⊩ (T ↙ i) ∷ Γ) → s®-cons-type ⊩TΓ
s®-cons ⊩TΓ@(⊩∷ {_} {T} {i} ⊩Γ ⊢T rel) {_} {σ} {_} {t} σ∼ρ t∼a
  with s®⇒⊢s ⊩Γ σ∼ρ | rel σ∼ρ
... | ⊢σ | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
     with presup-s ⊢σ
...     | ⊢Δ , _  =  record
  { ⊢σ = s-, ⊢σ ⊢T ⊢t
  ; pσ = σ
  ; v0σ = t
  ; ⟦T⟧ = ⟦T⟧
  ; ≈pσ = p-, ⊢σ ⊢T ⊢t
  ; ≈v0σ = [,]-v-ze ⊢σ ⊢T ⊢t
  ; ↘⟦T⟧ = ↘⟦T⟧
  ; T∈𝕌 = T∈𝕌
  ; t∼ρ0 = t∼a
  ; step = σ∼ρ
  }
  where ⊢t = ®El⇒tm T∈𝕌 t∼a

-- The identity substitution is related to initial environment.
InitEnvs⇒s®I : (⊩Δ : ⊩ Δ) →
               InitEnvs Δ ρ →
               Δ ⊢s I ∶ ⊩Δ ® ρ
InitEnvs⇒s®I ⊩[] base = s-I ⊢[]
InitEnvs⇒s®I {TΔ@(T ∷ Δ)} (⊩∷ ⊩Δ ⊢T gluT) (s-∷ {ρ = ρ} {A = A} ↘ρ ↘A)
  with InitEnvs⇒s®I ⊩Δ ↘ρ | ⊩⇒⊢ ⊩Δ
...  | I∼ρ | ⊢Δ
    with s®⇒⟦⟧ρ ⊩Δ I∼ρ | fundamental-⊢t ⊢T
...    | ⊨Δ , ρ∥∈ | ⊨Δ₁ , Trel₁
      with Trel₁ (⊨-irrel ⊨Δ ⊨Δ₁ ρ∥∈)
         | gluT I∼ρ
...      | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
         , record { ⟦t⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
         | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
         rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
               | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧
               | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
               | ⟦⟧-det ↘⟦T⟧ ↘A = record
                { ⊢σ = s-I ⊢TΔ
                ; pσ = _
                ; v0σ = _
                ; ⟦T⟧ = _
                ; ≈pσ = ∘-I (s-wk ⊢TΔ)
                ; ≈v0σ = [I] (vlookup ⊢TΔ here)
                ; ↘⟦T⟧ = ↘A
                ; T∈𝕌 = T≈T′
                ; t∼ρ0 = v0®x T≈T′ (®-one-sided T∈𝕌 T≈T′ (®-resp-≈ T∈𝕌 T∼⟦T⟧ ([I] ⊢T)))
                ; step = helper
                }
    where ⊢TΔ = ⊢∷ ⊢Δ ⊢T
          helper : TΔ ⊢s wk ∶ ⊩Δ ® ρ
          helper
            with s®-mon ⊩Δ (⊢wwk ⊢TΔ) I∼ρ
          ...  | wk∼ρ = s®-resp-s≈ ⊩Δ wk∼ρ (I-∘ (s-wk ⊢TΔ))