{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

-- Properties of mt
module Mints.Soundness.Properties.Mt (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Mints.Statics.Properties
open import Mints.Semantics.Properties.Domain fext
open import Mints.Soundness.LogRel
open import Mints.Soundness.Properties.NoFunExt.Mt public


-- mt commutes with truncation.
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
