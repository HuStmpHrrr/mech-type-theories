{- A module to avoid circular dependency -}
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Semantics.Properties.PER.Core (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties as ℕₚ

open import Lib
open import NonCumulative.Semantics.Domain
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.PER

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

𝕌-wf-simpl : ∀ i → (λ {j} → 𝕌-wellfounded i {j}) ≡ λ {j} _ → 𝕌 j
𝕌-wf-simpl i = implicit-extensionality fext (λ {j} → fext (𝕌-wellfounded-≡-𝕌 i))

𝕌-wf-gen : ∀ {i′} i (f : ∀ {j} → j < i → j < i′) → (λ {j} j<i → 𝕌-wellfounded _ (f j<i)) ≡ λ {j} → 𝕌-wellfounded i {j}
𝕌-wf-gen i f = implicit-extensionality fext λ {j} → fext λ j<i → 𝕌-wellfounded-≡ (f j<i) j<i

-- Maybe is easier to use
𝕌-≡-gen : ∀ {i′} i (f : ∀ {j} → j < i → j < i′) → PERDef.𝕌 i (λ j<i → 𝕌-wellfounded _ (f j<i)) ≡ 𝕌 i
𝕌-≡-gen {i′} i f
  rewrite 𝕌-wf-simpl i′
        | 𝕌-wf-simpl i = refl

𝕌-≡ : ∀ i → PERDef.𝕌 i (λ {j} _ → 𝕌 j) ≡ 𝕌 i
𝕌-≡ i
  rewrite 𝕌-wf-simpl i = refl
