{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.LogRel where

open import Lib
open import Data.Nat

open import kMLTT.Semantics.Domain public
open import kMLTT.Semantics.PER public

infix 4 _⊢_®_

_⊢_®_ : ∀ {i} → Ctxs → Typ → A ≈ A ∈ 𝕌 i → Set
Γ ⊢ T ® ne C≈C′  = {!!}
Γ ⊢ T ® N        = {!!}
Γ ⊢ T ® U i<j eq = {!!}
Γ ⊢ T ® □ A≈A    = {!!}
Γ ⊢ T ® Π iA RT  = {!!}
