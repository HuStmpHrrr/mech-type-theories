{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the soundness theorem
--
-- If a term is well-typed, then it is equivalent to its βη normal form.
module NonCumulative.Ascribed.Soundness(fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib

open import NonCumulative.Ascribed.Statics.Properties
open import NonCumulative.Ascribed.Semantics.Readback
open import NonCumulative.Ascribed.Semantics.Properties.PER fext
open import NonCumulative.Ascribed.Completeness.Fundamental fext
open import NonCumulative.Ascribed.Soundness.LogRel
open import NonCumulative.Ascribed.Soundness.Properties.Substitutions fext
open import NonCumulative.Ascribed.Soundness.Realizability fext
open import NonCumulative.Ascribed.Soundness.Fundamental fext


soundness : ∀ {i} →
            Γ ⊢ t ∶[ i ] T →
            ∃ λ w → NbE Γ t i T w × Γ ⊢ t ≈ Nf⇒Exp w ∶[ i ] T
soundness {Γ} {t} {T} {i} ⊢t
  with record { ⊩Γ = ⊩Γ ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with ρ , _ , ρinit , _ ← InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ ⊩Γ))
     with record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } ← krip (InitEnvs⇒s®I ⊩Γ ρinit)
        with record { a∈⊤ = a∈⊤ ; krip = krip } ← ®El⇒®↑El T∈𝕌 t∼⟦t⟧
           with w , ↘w , _ ← a∈⊤ (len Γ)
              | eq ← krip (⊢wI (⊩⇒⊢ ⊩Γ)) = w , nbe , [I]-≈ˡ ([I]-≈ˡ eq)
  where nbe : NbE Γ t i T w
        nbe = record
          { envs = ρ
          ; init = ρinit
          ; nbe  = record
            { ⟦t⟧  = ⟦t⟧
            ; ⟦T⟧  = ⟦T⟧
            ; ↘⟦t⟧ = ↘⟦t⟧
            ; ↘⟦T⟧ = ↘⟦T⟧
            ; ↓⟦t⟧ = ↘w
            }
          }