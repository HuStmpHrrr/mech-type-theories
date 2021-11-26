{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Terms (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext


⊨-lookup-gen : ∀ {x}
               (Γ≈Δ : ⊨ Γ ≈ Δ) →
               x ∶ T ∈! Γ →
               x ∶ T′ ∈! Δ →
               ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ →
               --------------------------------------------------------
               Σ (RelTyp T ρ T′ ρ′) λ rel → RelExp (v x) ρ (v x) ρ′ (El∞ (RelTyp.T≈T′ rel))
⊨-lookup-gen {T = sub T _} {sub T′ _} {ρ} {ρ′} (∷-cong Γ≈Δ rel) here here (ρ≈ρ′ , ρ0≈ρ′0)
  = record
      { ⟦T⟧   = ⟦T⟧
      ; ⟦T′⟧  = ⟦T′⟧
      ; ↘⟦T⟧  = ⟦[]⟧ {!⟦wk⟧!} ↘⟦T⟧
      ; ↘⟦T′⟧ = ⟦[]⟧ {!!} ↘⟦T′⟧
      ; T≈T′  = T≈T′
      ; nat   = λ κ → ⟦[]⟧ {!!} (subst (⟦ T ⟧_↘ ⟦T⟧ [ κ ]) (drop-mon ρ κ) (nat κ))
      ; nat′  = λ κ → ⟦[]⟧ {!!} (subst (⟦ T′ ⟧_↘ ⟦T′⟧ [ κ ]) (drop-mon ρ′ κ) (nat′ κ))
      }
  , record
      { ⟦t⟧   = _
      ; ⟦t′⟧  = _
      ; ↘⟦t⟧  = ⟦v⟧ 0
      ; ↘⟦t′⟧ = ⟦v⟧ 0
      ; t≈t′  = ρ0≈ρ′0
      ; nat   = λ κ → ⟦v⟧ 0
      ; nat′  = λ κ → ⟦v⟧ 0
      }
  where open RelTyp (rel ρ≈ρ′)
⊨-lookup-gen {T = sub T _} {sub T′ _} {ρ} {ρ′} (∷-cong Γ≈Δ rel) (there T∈Γ) (there T′∈Δ) (ρ≈ρ′ , _)
  with ⊨-lookup-gen Γ≈Δ T∈Γ T′∈Δ ρ≈ρ′
...  | rt , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
  = record
                   { ⟦T⟧   = ⟦T⟧
                   ; ⟦T′⟧  = ⟦T′⟧
                   ; ↘⟦T⟧  = ⟦[]⟧ {!!} ↘⟦T⟧
                   ; ↘⟦T′⟧ = ⟦[]⟧ {!!} ↘⟦T′⟧
                   ; T≈T′  = T≈T′
                   ; nat   = λ κ → ⟦[]⟧ {!!} (subst (⟦ T ⟧_↘ ⟦T⟧ [ κ ]) (drop-mon ρ κ) (rt.nat κ))
                   ; nat′  = λ κ → ⟦[]⟧ {!!} (subst (⟦ T′ ⟧_↘ ⟦T′⟧ [ κ ]) (drop-mon ρ′ κ) (rt.nat′ κ))
                   }
               , record
                   { ⟦t⟧   = _
                   ; ⟦t′⟧  = _
                   ; ↘⟦t⟧  = ⟦v⟧ _
                   ; ↘⟦t′⟧ = ⟦v⟧ _
                   ; t≈t′  = t≈t′
                   ; nat   = λ κ → ⟦v⟧ _
                   ; nat′  = λ κ → ⟦v⟧ _
                   }
  where module rt = RelTyp rt
        open rt hiding (nat; nat′)


⊨-lookup : ∀ {x}
           (⊨Γ : ⊨ Γ) →
           x ∶ T ∈! Γ →
           ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
           --------------------------------------------------------
           Σ (RelTyp T ρ T ρ′) λ rel → RelExp (v x) ρ (v x) ρ′ (El∞ (RelTyp.T≈T′ rel))
⊨-lookup ⊨Γ T∈Γ = ⊨-lookup-gen ⊨Γ T∈Γ T∈Γ


v-≈′ : ∀ {x} →
       ⊨ Γ →
       x ∶ T ∈! Γ →
       -----------------
       Γ ⊨ v x ≈ v x ∶ T
v-≈′ ⊨Γ T∈Γ = ⊨Γ , ⊨-lookup ⊨Γ T∈Γ


-- []-cong    : Δ ⊨ t ≈ t′ ∶ T →
--              Γ ⊨s σ ≈ σ′ ∶ Δ →
--              ---------------------------------
--              Γ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶ T [ σ ]
-- [I]        : Γ ⊨ t ∶ T →
--              --------------------
--              Γ ⊨ t [ I ] ≈ t ∶ T
-- [p]        : ∀ {x} →
--              Δ ⊨s σ ∶ S ∺ Γ →
--              x ∶ T ∈! Γ →
--              ---------------------------------------------
--              Δ ⊨ v x [ p σ ] ≈ v (suc x) [ σ ] ∶ T [ p σ ]
-- [∘]        : Γ ⊨s τ ∶ Γ′ →
--              Γ′ ⊨s σ ∶ Γ″ →
--              Γ″ ⊨ t ∶ T →
--              ---------------------------------------------
--              Γ ⊨ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T [ σ ∘ τ ]
-- [,]-v-ze   : ∀ {i} →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ S ∶ Se i →
--              Γ ⊨ s ∶ S [ σ ] →
--              --------------------------------
--              Γ ⊨ v 0 [ σ , s ] ≈ s ∶ S [ σ ]
-- [,]-v-su   : ∀ {i x} →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ S ∶ Se i →
--              Γ ⊨ s ∶ S [ σ ] →
--              x ∶ T ∈! Δ →
--              ---------------------------------------------
--              Γ ⊨ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]
-- ≈-conv     : ∀ {i} →
--              Γ ⊨ s ≈ t ∶ S →
--              Γ ⊨ S ≈ T ∶ Se i →
--              --------------------
--              Γ ⊨ s ≈ t ∶ T
-- ≈-sym      : Γ ⊨ t ≈ t′ ∶ T →
--              ----------------
--              Γ ⊨ t′ ≈ t ∶ T
-- ≈-trans    : Γ ⊨ t ≈ t′ ∶ T →
--              Γ ⊨ t′ ≈ t″ ∶ T →
--              ------ ------------
--              Γ ⊨ t ≈ t″ ∶ T
