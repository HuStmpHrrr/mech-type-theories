{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the soundness theorem
--
-- If a term is well-typed, then it is equivalent to its βη normal form.
module Cumulative.Soundness (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib

open import Cumulative.Statics.Properties
open import Cumulative.Semantics.Readback
open import Cumulative.Semantics.Properties.PER fext
open import Cumulative.Completeness.Fundamental fext
open import Cumulative.Soundness.LogRel
open import Cumulative.Soundness.Properties.Substitutions fext
open import Cumulative.Soundness.Realizability fext
open import Cumulative.Soundness.Fundamental fext


soundness : Γ ⊢ t ∶ T →
            ∃ λ w → NbE Γ t T w × Γ ⊢ t ≈ Nf⇒Exp w ∶ T
soundness {Γ} {t} {T} ⊢t
  with record { ⊩Γ = ⊩Γ ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with ρ , _ , ρinit , _ ← InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ ⊩Γ))
     with record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } ← krip (InitEnvs⇒s®I ⊩Γ ρinit)
        with record { a∈⊤ = a∈⊤ ; krip = krip } ← ®El⇒®↑El T∈𝕌 t∼⟦t⟧
           with w , ↘w , _ ← a∈⊤ (len Γ)
              | eq ← krip (⊢wI (⊩⇒⊢ ⊩Γ)) = w , nbe , [I]-≈ˡ ([I]-≈ˡ eq)
  where nbe : NbE Γ t T w
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
