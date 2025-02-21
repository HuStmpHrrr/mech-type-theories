{-# OPTIONS --without-K --safe #-}

module NonCumulative.Unascribed.Semantics.Transfer where

open import Lib

open import NonCumulative.Ascribed.Statics.Syntax as A
open import NonCumulative.Ascribed.Semantics.Domain as A
open import NonCumulative.Unascribed.Statics.Syntax as U
open import NonCumulative.Unascribed.Statics.Transfer as U
open import NonCumulative.Unascribed.Statics.Syntax as U
open import NonCumulative.Unascribed.Semantics.Domain as U

mutual
    ⌊_⌋ᵈᶠ : A.Df → U.Df
    ⌊ ↓ i A a ⌋ᵈᶠ = ↓ ⌊ A ⌋ᵈ ⌊ a ⌋ᵈ

    ⌊_⌋ᵈ : A.D → U.D
    ⌊ N ⌋ᵈ = N 
    ⌊ Π _ a (T ↙ i) ρ ⌋ᵈ = Π ⌊ a ⌋ᵈ ⌊ T ⌋ λ n → ⌊ ρ n ⌋ᵈ
    ⌊ U i ⌋ᵈ = U i 
    ⌊ Li i j a ⌋ᵈ = Li i ⌊ a ⌋ᵈ
    ⌊ ze ⌋ᵈ = ze
    ⌊ su a ⌋ᵈ = su ⌊ a ⌋ᵈ
    ⌊ Λ t ρ ⌋ᵈ = Λ ⌊ t ⌋ (λ n → ⌊ ρ n ⌋ᵈ)
    ⌊ li i a ⌋ᵈ = li i ⌊ a ⌋ᵈ
    ⌊ ↑ i A e ⌋ᵈ = ↑ ⌊ A ⌋ᵈ ⌊ e ⌋ᵈⁿ

    ⌊_⌋ᵈⁿ : A.Dn → U.Dn
    ⌊ l x ⌋ᵈⁿ = l x   
    ⌊ rec (T ↙ i) a t ρ e ⌋ᵈⁿ = rec ⌊ T ⌋ ⌊ a ⌋ᵈ ⌊ t ⌋ (λ n → ⌊ ρ n ⌋ᵈ) ⌊ e ⌋ᵈⁿ
    ⌊ e $ d ⌋ᵈⁿ = ⌊ e ⌋ᵈⁿ $ ⌊ d ⌋ᵈᶠ
    ⌊ unli e ⌋ᵈⁿ = unli ⌊ e ⌋ᵈⁿ