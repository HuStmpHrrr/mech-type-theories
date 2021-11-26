{-# OPTIONS --without-K --safe #-}

module kMLTT.Completeness.Universe where


-- Se-[]      : ∀ i →
--              Γ ⊨s σ ∶ Δ →
--              ----------------------------------
--              Γ ⊨ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
-- ≈-cumu     : ∀ {i} →
--              Γ ⊨ T ≈ T′ ∶ Se i →
--              -----------------------
--              Γ ⊨ T ≈ T′ ∶ Se (1 + i)
