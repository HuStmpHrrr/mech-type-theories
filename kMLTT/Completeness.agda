{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext
open import kMLTT.Statics

completeness : Γ ⊢ t ≈ t′ ∶ T →
               ∃ λ w → NbE Γ t T w × NbE Γ t′ T w
completeness {Γ} t≈t′
  with fundamental-t≈t′ t≈t′
...  | ⊨Γ , _ , t≈t′
    with InitEnvs-related ⊨Γ
...    | _ , _ , ↘ρ , ↘ρ′ , ρ≈ρ′
      with t≈t′ ρ≈ρ′
...      | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         with realizability-Rf T≈T′ t≈t′ (map len Γ) vone
...         | _ , ↓⟦t⟧ , ↓⟦t′⟧
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
