{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the completeness theorem
--
-- If two terms are equivalent, then they have equal βη normal form.
module MLTT.Completeness (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import MLTT.Completeness.Fundamental fext
open import MLTT.Semantics.Domain
open import MLTT.Semantics.Evaluation
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Realizability fext
open import MLTT.Statics

completeness : Γ ⊢ t ≈ t′ ∶ T →
               ∃ λ w → NbE Γ t T w × NbE Γ t′ T w
completeness {Γ} t≈t′
  with ⊨Γ , _ , t≈t′ ← fundamental-t≈t′ t≈t′
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
