{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the completeness theorem
--
-- If two terms are equivalent, then they have equal βη normal form.
module Mints.Completeness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Mints.Completeness.Fundamental fext
open import Mints.Semantics.Domain
open import Mints.Semantics.Evaluation
open import Mints.Semantics.Properties.Domain fext
open import Mints.Semantics.Properties.Evaluation fext
open import Mints.Semantics.Properties.PER fext
open import Mints.Semantics.Readback
open import Mints.Semantics.Realizability fext
open import Mints.Statics

completeness : Γ ⊢ t ≈ t′ ∶ T →
               ∃ λ w → NbE Γ t T w × NbE Γ t′ T w
completeness {Γ} t≈t′
  with ⊨Γ , _ , t≈t′ ← fundamental-t≈t′ t≈t′
    with _ , _ , ↘ρ , ↘ρ′ , ρ≈ρ′ ← InitEnvs-related ⊨Γ
      with t≈t′ ρ≈ρ′
...      | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         with _ , ↓⟦t⟧ , ↓⟦t′⟧ ← realizability-Rf T≈T′ t≈t′ (map len Γ) vone
           rewrite Df-ap-vone (↓ ⟦T⟧ ⟦t⟧)
                 | Df-ap-vone (↓ ⟦T′⟧ ⟦t′⟧) = _
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
