{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module STLCSubst.Semantics.Substitutions(fext : Extensionality 0ℓ 0ℓ) where

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Lib

open import STLCSubst.Statics
open import STLCSubst.Statics.Properties
open import STLCSubst.Semantics.Definitions
open import STLCSubst.Semantics.PER


Intp-Intpw : ⟦ t ⟧[ conv ϕ ] ρ ≈⟦ t′ ⟧[ conv ϕ′ ] ρ′ ∈ T → ϕ ≗ ϕ′ → ⟦ t ⟧ ρ ≈⟦ t′ ⟧ ρ′ ∈[ ϕ ]w T
Intp-Intpw {t} {ϕ} {ρ} {t′} {ϕ′} {ρ′} r eq = record
  { ↘⟦s⟧  = subst (⟦_⟧ _ ↘ _) (conv-equiv _ _) r.↘⟦s⟧
  ; ↘⟦s⟧′ = subst (⟦ _ ⟧_↘ _) ⟦σ⟧-eq  r.↘⟦s⟧′
  ; ↘⟦t⟧  = subst (⟦_⟧ _ ↘ _) (trans (conv-equiv t′ ϕ′) (sym (wk-transp _ eq))) r.↘⟦t⟧
  ; ↘⟦t⟧′ = subst (⟦ _ ⟧_↘ _) ⟦τ⟧-eq r.↘⟦t⟧′
  ; s≈s′  = r.s≈s′
  ; s≈t   = r.s≈t
  ; t≈t′  = r.t≈t′
  }
  where module r = Intp r
        ⟦σ⟧-eq : r.⟦σ⟧ ≡ ⟦ ϕ ⟧w ρ
        ⟦σ⟧-eq = fext (⟦⟧s-conv ϕ r.↘⟦σ⟧)
        ⟦τ⟧-eq : r.⟦τ⟧ ≡ ⟦ ϕ ⟧w ρ′
        ⟦τ⟧-eq = fext λ x → trans (⟦⟧s-conv _ r.↘⟦τ⟧ x) (sym (cong ρ′ (eq x)))

⊨id : Γ ⊨s id ≈ id ∶ Γ
⊨id {_} {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → ⟦v⟧ (ϕ x)
  ; ↘⟦σ⟧′ = ⟦v⟧
  ; ↘⟦τ⟧  = λ x → ⟦v⟧ (ϕ x)
  ; ↘⟦τ⟧′ = ⟦v⟧
  ; σ≈σ′  = λ {_} {T} T∈Γ → ⟦⟧≈refl T (ρ≈ρ′ (⊢ϕ T∈Γ))
  ; σ≈τ   = λ T∈Γ → ρ≈ρ′ (⊢ϕ T∈Γ)
  ; τ≈τ′  = λ {_} {T} T∈Γ → ⟦⟧≈refl′ T (ρ≈ρ′ (⊢ϕ T∈Γ))
  }

Wk-sem : Γ ⊢w ψ ∶ Δ → Γ ⊨s conv ψ ∶ Δ
Wk-sem {_} {ψ} ⊢ψ {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦σ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; ↘⟦τ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦τ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; σ≈σ′  = λ {_} {T} T∈Δ → ⟦⟧≈refl T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  ; σ≈τ   = λ T∈Δ → ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ))
  ; τ≈τ′  = λ {_} {T} T∈Δ → ⟦⟧≈refl′ T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  }

⊨wk-subst : Δ ⊨s σ ≈ σ′ ∶ Δ′ → Γ ⊢w ψ ∶ Δ → Γ ⊨s σ [ ψ ] ≈ σ′ [ ψ ] ∶ Δ′
⊨wk-subst {_} {σ} {σ′} {_} {_} {ψ} σ≈σ′ ⊢ψ {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → subst (⟦_⟧ _ ↘ _) (sym (wk-app-comb (σ x) ψ ϕ)) (eq-app.↘⟦σ⟧ x)
  ; ↘⟦σ⟧′ = eq-app′.↘⟦σ⟧
  ; ↘⟦τ⟧  = λ x → subst (⟦_⟧ _ ↘ _) (sym (wk-app-comb (σ′ x) ψ ϕ)) (eq-app.↘⟦τ⟧ x)
  ; ↘⟦τ⟧′ = eq-app′.↘⟦τ⟧
  ; σ≈σ′  = λ {_} {T} T∈Δ′ → ⟦⟧-trans T (eq-app.σ≈σ′ T∈Δ′) (⟦⟧-sym T (⟦⟧-transpʳ eq-app′.σ≈σ′ (⟦⟧s-det eq-app′.↘⟦σ⟧′ eq-app.↘⟦σ⟧′) T∈Δ′))
  ; σ≈τ   = eq-app.σ≈τ
  ; τ≈τ′  = λ {_} {T} T∈Δ′ → ⟦⟧-trans T (eq-app.τ≈τ′ T∈Δ′) (⟦⟧-sym T (⟦⟧-transpʳ eq-app′.τ≈τ′ (⟦⟧s-det eq-app′.↘⟦τ⟧′ eq-app.↘⟦τ⟧′) T∈Δ′))
  }
  where eq-app = σ≈σ′ (⊢wk-∙ ⊢ϕ ⊢ψ) ρ≈ρ′
        module eq-app = Intps eq-app
        eq-app′ = σ≈σ′ ⊢ψ (Wk-transp-ctx ⊢ϕ ρ≈ρ′)
        module eq-app′ = Intps eq-app′


-- ⊨ext : Γ ⊨s σ ≈ σ′ ∶ Δ → Γ ⊨ t ≈ t′ ∶ T → Γ ⊨s σ ↦ t ≈ σ′ ↦ t′ ∶ T ∷ Δ
-- ⊨ext {_} {_} {ϕ} σ≈σ′ t≈t′ ⊢ϕ ρ≈ρ′ = record
--   { ↘⟦σ⟧  = ↘⟦σ⟧
--   ; ↘⟦σ⟧′ = {!!}
--   ; ↘⟦τ⟧  = {!!}
--   ; ↘⟦τ⟧′ = {!!}
--   ; σ≈σ′  = {!!}
--   ; σ≈τ   = {!!}
--   ; τ≈τ′  = {!!}
--   }
--   where ↘⟦σ⟧ : _
--         ↘⟦σ⟧ zero = {!!}
--         ↘⟦σ⟧ (suc n) = {!!}
