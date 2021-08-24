{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.GluingProps (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as Nₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Gluing
open import Unbox.StaticProps
open import Unbox.SemanticProps fext

L-resp-mt : ∀ σ n → L σ n ≡ L (mt σ) n
L-resp-mt I n
  rewrite L-I n            = sym (L-vone n)
L-resp-mt (σ ∘ δ) n
  rewrite L-∘ n σ δ
        | L-ø (mt σ) (mt δ) n
        | L-resp-mt σ n    = L-resp-mt δ (L (mt σ) n)
L-resp-mt σ zero           = refl
L-resp-mt (p σ) (suc n)    = L-resp-mt σ (suc n)
L-resp-mt (σ , _) (suc n)  = L-resp-mt σ (suc n)
L-resp-mt (σ ； m) (suc n) = cong (m +_) (L-resp-mt σ n)

Tr-mt : ∀ σ n → mt (Tr σ n) ≡ Tr (mt σ) n
Tr-mt I n
  rewrite Tr-I n               = sym (Tr-vone n)
Tr-mt (σ ∘ δ) n
  rewrite Tr-∘ n σ δ
        | Tr-ø (mt σ) (mt δ) n
        | Tr-mt σ n
        | L-resp-mt σ n
        | Tr-mt δ (L (mt σ) n) = refl
Tr-mt σ zero                   = refl
Tr-mt (p σ) (suc n)            = Tr-mt σ (suc n)
Tr-mt (σ , _) (suc n)          = Tr-mt σ (suc n)
Tr-mt (σ ； m) (suc n)         = Tr-mt σ n

mt-resp-≈ : Ψ ⊢s σ ≈ δ ∶ Ψ′ → mt σ ≡ mt δ
mt-resp-≈ I-≈                               = refl
mt-resp-≈ (p-cong σ≈δ)                      = mt-resp-≈ σ≈δ
mt-resp-≈ (,-cong σ≈δ _)                    = mt-resp-≈ σ≈δ
mt-resp-≈ (；-cong Γs σ≈δ refl)             = cong (λ κ → ins κ (len Γs)) (mt-resp-≈ σ≈δ)
mt-resp-≈ (∘-cong σ≈δ σ′≈δ′)
  rewrite mt-resp-≈ σ≈δ
        | mt-resp-≈ σ′≈δ′                   = refl
mt-resp-≈ (∘-I _)                           = ø-vone _
mt-resp-≈ (I-∘ _)                           = vone-ø _
mt-resp-≈ {_} {σ ∘ σ′ ∘ σ″} (∘-assoc _ _ _) = ø-assoc (mt σ) (mt σ′) (mt σ″)
mt-resp-≈ (,-∘ _ _ _)                       = refl
mt-resp-≈ (p-∘ _ _)                         = refl
mt-resp-≈ {_} {σ ； _ ∘ δ} (；-∘ Γs _ _ refl)
  rewrite L-resp-mt δ (len Γs)
        | Tr-mt δ (len Γs)                  = ins-ø (len Γs) (mt σ) (mt δ)
mt-resp-≈ (p-, _ _)                         = refl
mt-resp-≈ (,-ext _)                         = refl
mt-resp-≈ {_} {σ} (；-ext _)
  rewrite L-resp-mt σ 1
        | +-identityʳ (mt σ 0)
        | Tr-mt σ 1                         = fext λ { zero    → refl
                                         ; (suc n) → refl }
mt-resp-≈ (s-≈-sym σ≈δ)                     = sym (mt-resp-≈ σ≈δ)
mt-resp-≈ (s-≈-trans σ≈σ′ σ′≈δ)             = trans (mt-resp-≈ σ≈σ′) (mt-resp-≈ σ′≈δ)
