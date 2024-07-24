{-# OPTIONS --without-K --safe #-}

-- Properties of domain-level operations that do not rely on functional extensionality
module Mint.Semantics.Properties.NoFunExt.Domain where

open import Data.Nat.Properties as Nₚ

open import Lib
open import Mint.Statics.Syntax
open import Mint.Semantics.Domain

O-add-ρ : ∀ n m (ρ : Envs) → O ρ (n + m) ≡ O ρ n + O (ρ ∥ n) m
O-add-ρ zero m ρ    = refl
O-add-ρ (suc n) m ρ = trans (cong (proj₁ (ρ 0) +_) (O-add-ρ n m (ρ ∥ 1)))
                            (sym (+-assoc (proj₁ (ρ 0)) (O (ρ ∥ 1) n) (O (ρ ∥ suc n) m)))

O-vone : ∀ n → O vone n ≡ n
O-vone zero    = refl
O-vone (suc n) = cong suc (O-vone n)

O-+ : ∀ (κ : UMoT) n m → O κ (n + m) ≡ O κ n + O (κ ∥ n) m
O-+ κ zero m              = refl
O-+ κ (suc n) m
  rewrite O-+ (κ ∥ 1) n m = sym (+-assoc (κ 0) (O (κ ∥ 1) n) (O (κ ∥ suc n) m))

O-ø : ∀ κ κ′ n → O (κ ø κ′) n ≡ O κ′ (O κ n)
O-ø κ κ′ zero                        = refl
O-ø κ κ′ (suc n)
  rewrite O-ø (κ ∥ 1) (κ′ ∥ κ 0) n
        | O-+ κ′ (κ 0) (O (κ ∥ 1) n) = refl


O-drop : ∀ n ρ → O (drop ρ) n ≡ O ρ n
O-drop zero ρ    = refl
O-drop (suc n) ρ = refl

O-↦ : ∀ n ρ a → O (ρ ↦ a) n ≡ O ρ n
O-↦ zero ρ a    = refl
O-↦ (suc n) ρ a = refl

O-ρ-+ : ∀ (ρ : Envs) n m → O ρ (n + m) ≡ O ρ n + O (ρ ∥ n) m
O-ρ-+ ρ zero m = refl
O-ρ-+ ρ (suc n) m = trans (cong (proj₁ (ρ 0) +_) (O-ρ-+ (ρ ∥ 1) n m))
                          (sym (+-assoc (proj₁ (ρ 0)) (O (ρ ∥ 1) n) (O (ρ ∥ suc n) m)))
