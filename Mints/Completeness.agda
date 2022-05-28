{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the completeness theorem
--
-- If two terms are equivalent, then they have equal βη normal form.
module Apini.Completeness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Apini.Completeness.Fundamental fext
open import Apini.Semantics.Domain
open import Apini.Semantics.Evaluation
open import Apini.Semantics.Properties.Domain fext
open import Apini.Semantics.Properties.Evaluation fext
open import Apini.Semantics.Properties.PER fext
open import Apini.Semantics.Readback
open import Apini.Semantics.Realizability fext
open import Apini.Statics

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
