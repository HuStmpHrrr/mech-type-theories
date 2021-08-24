{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.GluingProps (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Data.List.Properties as Lₚ

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
