{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Fundamental fext

soundness : Γ ⊢ t ∶ T →
            ∃ λ w → NbE Γ t T w × Γ ⊢ t ≈ Nf⇒Exp w ∶ T
soundness ⊢t
  with fundamental-⊢t⇒⊩t ⊢t
...  | x = ?
