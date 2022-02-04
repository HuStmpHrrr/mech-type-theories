{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Box (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties as Sta
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext

□-wf′ : ∀ {i} →
        [] ∷⁺ Γ ⊩ T ∶ Se i →
        --------------------
        Γ ⊩ □ T ∶ Se i
□-wf′ {Γ} {T} {i} ⊩T
  with ⊩T
... | record { ⊩Γ = ⊩κ ⊩Γ ; lvl = lvl ; krip = Tkrip } = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    ⊢T = ⊩⇒⊢-tm ⊩T
    ⊢Γ = ⊩⇒⊢ ⊩Γ
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           --------------------
           GluExp _ Δ (□ T) (Se i) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ = helper
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

        σ；1∼extρ : Gluκ ([] ∷⁺ Δ) (σ ； 1) Γ (ext ρ 1) (_⊢s_∶ ⊩Γ ®_)
        σ；1∼extρ = record
                        { ⊢σ = s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl
                        ; Ψs⁻ = L.[ [] ]
                        ; Γ≡ = refl
                        ; ≈σ∥ = s-≈-refl ⊢σ
                        ; O≡ = refl
                        ; len≡ = refl
                        ; step = σ∼ρ
                        }

        helper : GluExp _ Δ (□ T) (Se i) σ ρ
        helper
          with Tkrip σ；1∼extρ
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = T∼⟦T⟧ }
            with T∼⟦T⟧
        ...    | record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = Trel } = record
                      { ↘⟦T⟧ = ⟦Se⟧ _
                      ; ↘⟦t⟧ = ⟦□⟧ ↘⟦T⟧
                      ; T∈𝕌 = U′ i<lvl
                      ; t∼⟦t⟧ = record
                            { t∶T = t[σ] (□-wf ⊢T) ⊢σ
                            ; T≈ = lift-⊢≈-Se (Se-[] _ ⊢σ) i<lvl
                            ; A∈𝕌 = □ λ κ → 𝕌-mon κ A∈𝕌
                            ; rel = rel
                            }
                      }
          where
            rel : Glu-wellfounded lvl i<lvl Δ (sub (□ T) σ) (□ (λ κ → 𝕌-mon κ A∈𝕌))
            rel
              rewrite Glu-wellfounded-≡ i<lvl = record
                                                { T≈ = □-[] ⊢σ ⊢T
                                                ; krip = λ {_} {δ} Ψs ⊢δ → ®-mon A∈𝕌 (𝕌-mon (ins (mt δ) (len Ψs)) A∈𝕌) Trel (r-； Ψs ⊢δ (s-≈-refl (s-； Ψs (⊢r⇒⊢s ⊢δ) {!!} refl)) refl)
                                                }
