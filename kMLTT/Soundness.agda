{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the soundness theorem
--
-- If a term is well-typed, then it is equivalent to its βη normal form.
module kMLTT.Soundness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.Substitutions fext
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Fundamental fext


soundness : Γ ⊢ t ∶ T →
            ∃ λ w → NbE Γ t T w × Γ ⊢ t ≈ Nf⇒Exp w ∶ T
soundness {Γ} {t} {T} ⊢t
  with fundamental-⊢t⇒⊩t ⊢t
... | record { ⊩Γ = ⊩Γ ; krip = krip }
    with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ ⊩Γ))
...  | ρ , _ , ρinit , _
     with krip (InitEnvs⇒s®I ⊩Γ ρinit)
...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
        with ®El⇒®↑El T∈𝕌 t∼⟦t⟧
...        | record { t∶T = t∶T ; T∼A = T∼A ; a∈⊤ = a∈⊤ ; krip = krip }
           with a∈⊤ (map len Γ) vone | krip (⊢rI (⊩⇒⊢ ⊩Γ))
...           | w , ↘w , _ | eq
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
