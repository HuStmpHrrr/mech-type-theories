{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Properties (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

import NonCumulative.Consequences fext as A
open import NonCumulative.Statics.Unascribed.Full
open import NonCumulative.Statics.Equivalence.Transfer
open import NonCumulative.Statics.Equivalence.Soundness fext
open import NonCumulative.Statics.Equivalence.Completeness

consistency : ∀ {j} → [] ⊢ t ∶ Π (Se j) (v 0) → ⊥
consistency ⊢t′
  with i , Γ , t , ._ , ↝[] , t↝ , ↝Π ↝Se ↝v , ⊢t , _ ← fundamental-⊢t⇒⫢t ⊢t′ 
  = A.consistency-gen ⊢t