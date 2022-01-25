{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.Mt (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.NoFunExt.Mt public


mt-∥ : ∀ σ n → mt (σ ∥ n) ≡ mt σ ∥ n
mt-∥ I n
  rewrite I-∥ n               = sym (vone-∥ n)
mt-∥ (σ ∘ δ) n
  rewrite ∘-∥ n σ δ
        | ø-∥ (mt σ) (mt δ) n
        | mt-∥ σ n
        | O-resp-mt σ n
        | mt-∥ δ (O (mt σ) n) = refl
mt-∥ σ zero                   = refl
mt-∥ wk (suc n)               = refl
mt-∥ (σ , _) (suc n)          = mt-∥ σ (suc n)
mt-∥ (σ ； m) (suc n)         = mt-∥ σ n
