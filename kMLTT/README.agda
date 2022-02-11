{-# OPTIONS --without-K #-}

module kMLTT.README where

open import Axiom.Extensionality.Propositional


postulate
  fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′


open import kMLTT.Statics

open import kMLTT.Completeness fext

open import kMLTT.Soundness fext

open import kMLTT.Consequences fext
