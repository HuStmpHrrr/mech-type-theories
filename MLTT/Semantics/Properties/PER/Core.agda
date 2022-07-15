{- A module to avoid circular dependency -}
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module MLTT.Semantics.Properties.PER.Core (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties as ℕₚ

open import Lib
open import MLTT.Semantics.Domain
open import MLTT.Semantics.Readback
open import MLTT.Semantics.PER

Bot-l : ∀ z → l z ≈ l z ∈ Bot
Bot-l z n = v (n ∸ z ∸ 1) , Rl n z , Rl n z

-- two important helpers which essentially erase some technical details
𝕌-wellfounded-≡ : ∀ {j i i′} (j<i : j < i) (j<i′ : j < i′) → 𝕌-wellfounded i j<i ≡ 𝕌-wellfounded i′ j<i′
𝕌-wellfounded-≡ (s≤s j≤i) (s≤s j≤i′) = cong (PERDef.𝕌 _)
                                            (implicit-extensionality fext
                                              (λ {j′} → fext λ j′<j → 𝕌-wellfounded-≡ (≤-trans j′<j j≤i) (≤-trans j′<j j≤i′)))


𝕌-wellfounded-≡-𝕌 : ∀ i {j} (j<i : j < i) → 𝕌-wellfounded i j<i ≡ 𝕌 j
𝕌-wellfounded-≡-𝕌 (suc i) {j} (s≤s j≤i) = cong (PERDef.𝕌 _)
                                               (implicit-extensionality fext
                                                 λ {j′} → fext (λ j<j′ → 𝕌-wellfounded-≡ (≤-trans j<j′ j≤i) j<j′))
