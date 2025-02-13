{-# OPTIONS --without-K --safe #-}

-- Some miscellaneous properties
module NonCumulative.Statics.InterAscribed.Misc where

open import Lib
open import Data.Nat
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Lₚ

open import NonCumulative.Statics.InterAscribed.Full

t[σ]-Se : ∀ {i} → ⊢ Γ → ⊢ Δ → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶[ 1 + i ] Se i
t[σ]-Se ⊢Γ ⊢Δ ⊢T ⊢σ = conv ⊢Γ (t[σ] ⊢Δ ⊢T ⊢σ) {!   !} ({!   !})

[]-cong-Se : ∀ {i} → ⊢ Γ → ⊢ Δ → Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se ⊢Γ ⊢Δ T≈T′ ⊢σ σ≈σ′ = ≈-conv ⊢Γ ([]-cong ⊢Δ T≈T′ σ≈σ′) (Se-[] _ ⊢σ)

conv-N-[] : ⊢ Γ → Γ ⊢ t ∶[ 0 ] N [ σ ] → Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶[ 0 ] N
conv-N-[] ⊢Γ ⊢t ⊢σ = conv ⊢Γ ⊢t {!   !} (N-[] ⊢σ)