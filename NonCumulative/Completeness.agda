{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the completeness theorem
--
-- If two terms are equivalent, then they have equal βη normal form.
module NonCumulative.Completeness (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Semantics.Domain
open import NonCumulative.Semantics.Evaluation
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Realizability fext
open import NonCumulative.Statics.Ascribed.Full

completeness : ∀ {i} →
               Γ ⊢ t ≈ t′ ∶[ i ] T →
               ∃ λ w → NbE Γ t i T w × NbE Γ t′ i T w
completeness {Γ} t≈t′
  with ⊨Γ , t≈t′ ← fundamental-t≈t′ t≈t′
    with _ , _ , ↘ρ , ↘ρ′ , ρ≈ρ′ ← InitEnvs-related ⊨Γ
      with t≈t′ ρ≈ρ′
...      | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         with _ , ↓⟦t⟧ , ↓⟦t′⟧ ← El⊆Top T≈T′ t≈t′ (len Γ)
         = _
         , record
           { init = ↘ρ
           ; nbe = record
                   { ↘⟦t⟧ = ↘⟦t⟧
                   ; ↘⟦T⟧ = ↘⟦T⟧
                   ; ↓⟦t⟧ = ↓⟦t⟧
                   }
           }
         , record
           { init = ↘ρ′
           ; nbe = record
                   { ↘⟦t⟧ = ↘⟦t′⟧
                   ; ↘⟦T⟧ = ↘⟦T′⟧
                   ; ↓⟦t⟧ = ↓⟦t′⟧
                   }
           }
