{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.Properties.NoFunExt.Domain where

open import Data.Nat.Properties as Nₚ

open import Lib
open import kMLTT.Statics.Syntax
open import kMLTT.Semantics.Domain

L-add-ρ : ∀ n m (ρ : Envs) → L ρ (n + m) ≡ L ρ n + L (ρ ∥ n) m
L-add-ρ zero m ρ    = refl
L-add-ρ (suc n) m ρ = trans (cong (proj₁ (ρ 0) +_) (L-add-ρ n m (ρ ∥ 1)))
                            (sym (+-assoc (proj₁ (ρ 0)) (L (ρ ∥ 1) n) (L (ρ ∥ suc n) m)))

L-vone : ∀ n → L vone n ≡ n
L-vone zero    = refl
L-vone (suc n) = cong suc (L-vone n)

L-+ : ∀ (κ : UMoT) n m → L κ (n + m) ≡ L κ n + L (κ ∥ n) m
L-+ κ zero m              = refl
L-+ κ (suc n) m
  rewrite L-+ (κ ∥ 1) n m = sym (+-assoc (κ 0) (L (κ ∥ 1) n) (L (κ ∥ suc n) m))

L-ø : ∀ κ κ′ n → L (κ ø κ′) n ≡ L κ′ (L κ n)
L-ø κ κ′ zero                        = refl
L-ø κ κ′ (suc n)
  rewrite L-ø (κ ∥ 1) (κ′ ∥ κ 0) n
        | L-+ κ′ (κ 0) (L (κ ∥ 1) n) = refl


L-drop : ∀ n ρ → L (drop ρ) n ≡ L ρ n
L-drop zero ρ    = refl
L-drop (suc n) ρ = refl

L-↦ : ∀ n ρ a → L (ρ ↦ a) n ≡ L ρ n
L-↦ zero ρ a    = refl
L-↦ (suc n) ρ a = refl

L-ρ-+ : ∀ (ρ : Envs) n m → L ρ (n + m) ≡ L ρ n + L (ρ ∥ n) m
L-ρ-+ ρ zero m = refl
L-ρ-+ ρ (suc n) m = trans (cong (proj₁ (ρ 0) +_) (L-ρ-+ (ρ ∥ 1) n m))
                          (sym (+-assoc (proj₁ (ρ 0)) (L (ρ ∥ 1) n) (L (ρ ∥ suc n) m)))
