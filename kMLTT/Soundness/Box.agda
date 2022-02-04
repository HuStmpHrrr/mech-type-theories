{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Box (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext

σ；1∼extρ : (⊩Γ : ⊩ Γ) → Δ ⊢s σ ∶ ⊩Γ ® ρ → [] ∷⁺ Δ ⊢s σ ； 1 ∶ ⊩κ ⊩Γ ® (ext ρ 1)
σ；1∼extρ ⊩Γ σ∼ρ = record
                { ⊢σ = s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl
                ; Ψs⁻ = L.[ [] ]
                ; Γ≡ = refl
                ; ≈σ∥ = s-≈-refl ⊢σ
                ; O≡ = refl
                ; len≡ = refl
                ; step = σ∼ρ
                }
  where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

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
    krip {Δ} {σ} {ρ} σ∼ρ
      with Tkrip (σ；1∼extρ ⊩Γ σ∼ρ)
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
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ

        rel : Glu-wellfounded lvl i<lvl Δ (sub (□ T) σ) (□ (λ κ → 𝕌-mon κ A∈𝕌))
        rel
          rewrite Glu-wellfounded-≡ i<lvl = record
                                            { T≈ = □-[] ⊢σ ⊢T
                                            ; krip = λ {_} {δ} Ψs ⊢ΨsΔ ⊢δ → ®-mon A∈𝕌 (𝕌-mon (ins (mt δ) (len Ψs)) A∈𝕌) Trel (r-； Ψs ⊢δ (s-≈-refl (s-； Ψs (⊢r⇒⊢s ⊢δ) ⊢ΨsΔ refl)) refl)
                                            }

□-I′ : [] ∷⁺ Γ ⊩ t ∶ T →
       -----------------
       Γ ⊩ box t ∶ □ T
□-I′ {_} {t} {T} ⊩t
  with ⊩t
... | record { ⊩Γ = ⊩κ ⊩Γ ; lvl = lvl ; krip = tkrip }
    with ⊩⇒⊢-tm ⊩t
...    | ⊢t
      with presup-tm ⊢t
...      | _ , n , ⊢T = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    lvl′ = max lvl n
    lvl≤lvl′ = m≤m⊔n lvl n
    n≤lvl′ = m≤m⊔n lvl n

    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           --------------------
           GluExp _ Δ (box t) (□ T) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with tkrip (σ；1∼extρ ⊩Γ σ∼ρ)
    ...  | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                            { ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧
                            ; ↘⟦t⟧ = ⟦box⟧ ↘⟦t⟧
                            ; T∈𝕌 = □ λ κ → 𝕌-mon κ (𝕌-cumu lvl≤lvl′ T∈𝕌)
                            ; t∼⟦t⟧ = record
                                      { t∶T = t[σ] (□-I ⊢t) ⊢σ
                                      ; a∈El = λ m κ → record
                                                       { ↘ua = box↘ _
                                                       ; ↘ub = box↘ _
                                                       ; ua≈ub = subst (λ a → a ≈ a ∈ El _ (𝕌-mon (ins κ m) (𝕌-cumu lvl≤lvl′ T∈𝕌))) (sym (D-ins-ins ⟦t⟧ κ m)) {!El-mon!}
                                                       }
                                      ; T≈ = □-[] ⊢σ (lift-⊢-Se-max′ ⊢T)
                                      ; krip = λ {_} {δ} Ψs ⊢ΨsΔ ⊢δ → record { ↘ua = box↘ _ ; rel = {!!} }
                                      }
                            }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
