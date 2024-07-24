{- A module to avoid circular dependency -}
{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module Mint.Semantics.Properties.PER.Core (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties as ℕₚ

open import Lib
open import Mint.Semantics.Domain
open import Mint.Semantics.Readback
open import Mint.Semantics.PER

Bot-l : ∀ z → l z ≈ l z ∈ Bot
Bot-l z ns κ = v (head ns ∸ z ∸ 1) , Rl ns z , Rl ns z

-- two important helpers which essentially erase some technical details
𝕌-wellfounded-≡ : ∀ {j i i′} (j<i : j < i) (j<i′ : j < i′) → 𝕌-wellfounded i j<i ≡ 𝕌-wellfounded i′ j<i′
𝕌-wellfounded-≡ (s≤s j≤i) (s≤s j≤i′) = cong (PERDef.𝕌 _)
                                            (implicit-extensionality fext
                                              λ {j′} → fext λ j′<j → 𝕌-wellfounded-≡ (≤-trans j′<j j≤i) (≤-trans j′<j j≤i′))


𝕌-wellfounded-≡-𝕌 : ∀ i {j} (j<i : j < i) → 𝕌-wellfounded i j<i ≡ 𝕌 j
𝕌-wellfounded-≡-𝕌 (suc i) {j} (s≤s j≤i) = cong (PERDef.𝕌 _)
                                               (implicit-extensionality fext
                                                 λ {j′} → fext (λ j<j′ → 𝕌-wellfounded-≡ (≤-trans j<j′ j≤i) j<j′))
