{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Properties (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

import NonCumulative.Statics.Ascribed.Full as A
open import NonCumulative.Consequences fext
open import NonCumulative.Statics.Unascribed.Full
open import NonCumulative.Statics.Equivalence.Transfer
open import NonCumulative.Statics.Equivalence.Soundness fext
open import NonCumulative.Statics.Equivalence.Completeness

u-consistency : ∀ {j} → [] ⊢ t ∶ Π (Se j) (v 0) → ⊥
u-consistency ⊢t′
  with i , Γ , t , .(A.Π (_ A.↙ _) (_ A.↙ _)) , ↝[] , t↝ , ↝Π ↝Se ↝v , ⊢t , _ ← fundamental-⊢t⇒⫢t ⊢t′ 
  = consistency-gen ⊢t