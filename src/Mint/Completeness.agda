{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the completeness theorem
--
-- If two terms are equivalent, then they have equal βη normal form.
module Mint.Completeness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Mint.Completeness.Fundamental fext
open import Mint.Semantics.Domain
open import Mint.Semantics.Evaluation
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Properties.Evaluation fext
open import Mint.Semantics.Properties.PER fext
open import Mint.Semantics.Readback
open import Mint.Semantics.Realizability fext
open import Mint.Statics

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
