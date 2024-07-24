{-# OPTIONS --without-K --safe #-}

-- Properties of mt that do not rely on functional extensionality
module Mint.Soundness.Properties.NoFunExt.Mt where

open import Lib

open import Mint.Statics.Properties
open import Mint.Semantics.Properties.NoFunExt.Domain
open import Mint.Soundness.LogRel

-- O respects mt, i.e. truncation offsets of a substitution and its mt are the same.
O-resp-mt : ∀ σ n → O σ n ≡ O (mt σ) n
O-resp-mt I n
  rewrite O-I n            = sym (O-vone n)
O-resp-mt (σ ∘ δ) n
  rewrite O-∘ n σ δ
        | O-ø (mt σ) (mt δ) n
        | O-resp-mt σ n    = O-resp-mt δ (O (mt σ) n)
O-resp-mt σ zero           = refl
O-resp-mt wk (suc n)
  rewrite O-vone n         = refl
O-resp-mt (σ , _) (suc n)  = O-resp-mt σ (suc n)
O-resp-mt (σ ； m) (suc n) = cong (m +_) (O-resp-mt σ n)
