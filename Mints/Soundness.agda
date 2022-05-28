{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the soundness theorem
--
-- If a term is well-typed, then it is equivalent to its βη normal form.
module Mints.Soundness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import Mints.Statics.Properties
open import Mints.Semantics.Readback
open import Mints.Semantics.Properties.Domain fext
open import Mints.Semantics.Properties.PER fext
open import Mints.Completeness.Fundamental fext
open import Mints.Soundness.LogRel
open import Mints.Soundness.Properties.Substitutions fext
open import Mints.Soundness.Realizability fext
open import Mints.Soundness.Fundamental fext


soundness : Γ ⊢ t ∶ T →
            ∃ λ w → NbE Γ t T w × Γ ⊢ t ≈ Nf⇒Exp w ∶ T
soundness {Γ} {t} {T} ⊢t
  with record { ⊩Γ = ⊩Γ ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with ρ , _ , ρinit , _ ← InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ ⊩Γ))
     with record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } ← krip (InitEnvs⇒s®I ⊩Γ ρinit)
        with record { a∈⊤ = a∈⊤ ; krip = krip } ← ®El⇒®↑El T∈𝕌 t∼⟦t⟧
           with w , ↘w , _ ← a∈⊤ (map len Γ) vone
              | eq ← krip (⊢rI (⊩⇒⊢ ⊩Γ))
             rewrite D-ap-vone ⟦t⟧
                   | D-ap-vone ⟦T⟧ = w , nbe , [I]-≈ˡ ([I]-≈ˡ eq)
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
