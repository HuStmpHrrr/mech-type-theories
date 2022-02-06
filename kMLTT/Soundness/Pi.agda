{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Pi (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Consequences fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext


Π-wf′ : ∀ {i} →
        Γ ⊩ S ∶ Se i →
        S ∺ Γ ⊩ T ∶ Se i →
        --------------------
        Γ ⊩ Π S T ∶ Se i
Π-wf′ {_} {S} {T} {i} ⊩S ⊩T
  with ⊩S | ⊩⇒⊢-tm ⊩S | ⊩T | ⊩⇒⊢-tm ⊩T
...  | record { ⊩Γ = ⊩Γ ; lvl = lvl ; krip = Skrip }
     | ⊢S
     | record { ⊩Γ = (⊩∺ ⊩Γ₁ ⊢S₁ gS) ; lvl = lvl₁ ; krip = Tkrip₁ }
     | ⊢T = record { ⊩Γ = ⊩Γ ; lvl = {!!} ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp (max lvl lvl₁) Δ (Π S T) (Se i) σ ρ
    krip σ∼ρ
      with Skrip σ∼ρ -- | gS (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ)
    ...  | record { ⟦t⟧ = ⟦S⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = S∼⟦S⟧ }
        --  | record { ⟦T⟧ = ⟦S⟧₁ ; ↘⟦T⟧ = ↘⟦S⟧₁ ; T∈𝕌 = S∈𝕌₁ ; T∼⟦T⟧ = S∼⟦S⟧₁ }
        -- rewrite Glu-wellfounded-≡ i<lvl
        --       | ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧
          with S∼⟦S⟧
    ...      | record { t∶T = t∶S ; T≈ = S≈ ; A∈𝕌 = S∈𝕌 ; rel = S∼⟦S⟧ } = record
                { ↘⟦T⟧ = ⟦Se⟧ _
                ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧
                ; T∈𝕌 = U′ (<-transˡ i<lvl (m≤m⊔n _ _))
                ; t∼⟦t⟧ = record
                          { t∶T = t[σ] (Π-wf ⊢S ⊢T) ⊢σ
                          ; T≈ = lift-⊢≈-Se (Se-[] _ ⊢σ) (<-transˡ i<lvl (m≤m⊔n _ _))
                          ; A∈𝕌 = Π (λ κ → 𝕌-mon κ S∈𝕌) ΠRTT
                          ; rel = rel
                          }
                }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ

        ΠRTT : {a a′ : D} (κ : UMoT) →
               a ≈ a′ ∈ El i (𝕌-mon κ S∈𝕌) →
               ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 i)
        ΠRTT κ a≈a′ = record
                        { ⟦T⟧ = {!!}
                        ; ⟦T′⟧ = {!!}
                        ; ↘⟦T⟧ = {!!}
                        ; ↘⟦T′⟧ = {!!}
                        ; T≈T′ = {!!}
                        }
          where
            x = Tkrip₁ (s®-cons (⊩∺ ⊩Γ₁ ⊢S₁ gS) (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ) {!!})

        rel : Glu-wellfounded (max lvl lvl₁) (<-transˡ i<lvl (m≤m⊔n lvl lvl₁)) Δ (sub (Π S T) σ) (Π (λ κ → 𝕌-mon κ S∈𝕌) ΠRTT)
        rel = {!!}

Λ-I′ : ∀ {i} →
       Γ ⊩ S ∶ Se i →
       S ∺ Γ ⊩ t ∶ T →
       ------------------
       Γ ⊩ Λ t ∶ Π S T
Λ-I′ ⊩S ⊩t = {!!}

Λ-E′ : ∀ {i} →
       Γ ⊩ T ∶ Se i →
       Γ ⊩ r ∶ Π S T →
       Γ ⊩ s ∶ S →
       ---------------------
       Γ ⊩ r $ s ∶ T [| s ]
Λ-E′ ⊩T ⊩r ⊩s = {!!}
