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
  ; σ≈σ′  = λ {_} {T} T∈Γ → ⟦⟧-refl T (ρ≈ρ′ (⊢ϕ T∈Γ))
  ; σ≈τ   = λ T∈Γ → ρ≈ρ′ (⊢ϕ T∈Γ)
  ; τ≈τ′  = λ {_} {T} T∈Γ → ⟦⟧-refl′ T (ρ≈ρ′ (⊢ϕ T∈Γ))
  }

Wk-sem : Γ ⊢w ψ ∶ Δ → Γ ⊨s conv ψ ∶ Δ
Wk-sem {_} {ψ} ⊢ψ {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦σ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; ↘⟦τ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦τ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; σ≈σ′  = λ {_} {T} T∈Δ → ⟦⟧-refl T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  ; σ≈τ   = λ T∈Δ → ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ))
  ; τ≈τ′  = λ {_} {T} T∈Δ → ⟦⟧-refl′ T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  }

⊨wk-subst : Δ ⊨s σ ≈ σ′ ∶ Δ′ → Γ ⊢w ψ ∶ Δ → Γ ⊨s σ [ ψ ] ≈ σ′ [ ψ ] ∶ Δ′
⊨wk-subst {_} {σ} {σ′} {_} {_} {ψ} σ≈σ′ ⊢ψ {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → subst (⟦_⟧ _ ↘ _) (sym (wk-app-comb (σ x) ψ ϕ)) (eq-app.↘⟦σ⟧ x)
  ; ↘⟦σ⟧′ = eq-app′.↘⟦σ⟧
  ; ↘⟦τ⟧  = λ x → subst (⟦_⟧ _ ↘ _) (sym (wk-app-comb (σ′ x) ψ ϕ)) (eq-app.↘⟦τ⟧ x)
  ; ↘⟦τ⟧′ = eq-app′.↘⟦τ⟧
  ; σ≈σ′  = ⟦⟧-transs eq-app.σ≈σ′ (⟦⟧-transpˡ (⟦⟧-syms eq-app′.σ≈σ′) (⟦⟧s-det eq-app′.↘⟦σ⟧′ eq-app.↘⟦σ⟧′))
  ; σ≈τ   = eq-app.σ≈τ
  ; τ≈τ′  = ⟦⟧-transs eq-app.τ≈τ′ (⟦⟧-transpˡ (⟦⟧-syms eq-app′.τ≈τ′) (⟦⟧s-det eq-app′.↘⟦τ⟧′ eq-app.↘⟦τ⟧′))
  }
  where eq-app = σ≈σ′ (⊢wk-∙ ⊢ϕ ⊢ψ) ρ≈ρ′
        module eq-app  = Intps eq-app
        eq-app′ = σ≈σ′ ⊢ψ (⟦⟧-wk ⊢ϕ ρ≈ρ′)
        module eq-app′ = Intps eq-app′

⊨⇑ : ∀ S → S ∷ Γ ⊨s conv ⇑ ∶ Γ
⊨⇑ S = ⊨wk-subst ⊨id ⊢⇑

⊨ext : Γ ⊨s σ ≈ σ′ ∶ Δ → Γ ⊨ t ≈ t′ ∶ T → Γ ⊨s σ ↦ t ≈ σ′ ↦ t′ ∶ T ∷ Δ
⊨ext {_} {σ} {σ′} {_} {t} {t′} {T} σ≈σ′ t≈t′ {_} {ϕ} {ρ} {ρ′} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = ↘⟦σ⟧
  ; ↘⟦σ⟧′ = ↘⟦σ⟧′
  ; ↘⟦τ⟧  = ↘⟦τ⟧
  ; ↘⟦τ⟧′ = ↘⟦τ⟧′
  ; σ≈σ′  = equiv
  ; σ≈τ   = σ≈τ
  ; τ≈τ′  = τ≈τ′
  }
  where module app = Intps (σ≈σ′ ⊢ϕ ρ≈ρ′)
        module tm  = Intpw (Intp-Intpw (t≈t′ (Wk-sem ⊢ϕ) ρ≈ρ′) λ _ → refl)

        ⟦σ⟧ : Env
        ⟦σ⟧ zero     = tm.⟦s⟧
        ⟦σ⟧ (suc x)  = app.⟦σ⟧ x
        ↘⟦σ⟧ : ⟦ σ ↦ t [ ϕ ] ⟧s ρ ↘ ⟦σ⟧
        ↘⟦σ⟧ zero    = tm.↘⟦s⟧
        ↘⟦σ⟧ (suc x) = app.↘⟦σ⟧ x

        ⟦σ⟧′ : Env
        ⟦σ⟧′ zero     = tm.⟦s⟧′
        ⟦σ⟧′ (suc x)  = app.⟦σ⟧′ x
        ↘⟦σ⟧′ : ⟦ σ ↦ t ⟧s ⟦ ϕ ⟧w ρ ↘ ⟦σ⟧′
        ↘⟦σ⟧′ zero    = tm.↘⟦s⟧′
        ↘⟦σ⟧′ (suc x) = app.↘⟦σ⟧′ x

        ⟦τ⟧ : Env
        ⟦τ⟧ zero     = tm.⟦t⟧
        ⟦τ⟧ (suc x)  = app.⟦τ⟧ x
        ↘⟦τ⟧ : ⟦ σ′ ↦ t′ [ ϕ ] ⟧s ρ′ ↘ ⟦τ⟧
        ↘⟦τ⟧ zero    = tm.↘⟦t⟧
        ↘⟦τ⟧ (suc x) = app.↘⟦τ⟧ x

        ⟦τ⟧′ : Env
        ⟦τ⟧′ zero     = tm.⟦t⟧′
        ⟦τ⟧′ (suc x)  = app.⟦τ⟧′ x
        ↘⟦τ⟧′ : ⟦ σ′ ↦ t′ ⟧s ⟦ ϕ ⟧w ρ′ ↘ ⟦τ⟧′
        ↘⟦τ⟧′ zero    = tm.↘⟦t⟧′
        ↘⟦τ⟧′ (suc x) = app.↘⟦τ⟧′ x

        equiv : ⟦σ⟧ ≈ ⟦σ⟧′ ∈ ⟦ T ∷ _ ⟧
        equiv here        = tm.s≈s′
        equiv (there S∈Δ) = app.σ≈σ′ S∈Δ
        σ≈τ : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ T ∷ _ ⟧
        σ≈τ here          = tm.s≈t
        σ≈τ (there S∈Δ)   = app.σ≈τ S∈Δ
        τ≈τ′ : ⟦τ⟧ ≈ ⟦τ⟧′ ∈ ⟦ T ∷ _ ⟧
        τ≈τ′ here         = tm.t≈t′
        τ≈τ′ (there S∈Δ)  = app.τ≈τ′ S∈Δ


⊨s-sym : Γ′ ⊨s σ ≈ σ′ ∶ Γ → Γ′ ⊨s σ′ ≈ σ ∶ Γ
⊨s-sym σ≈σ′ ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = app.↘⟦τ⟧
  ; ↘⟦σ⟧′ = app.↘⟦τ⟧′
  ; ↘⟦τ⟧  = app.↘⟦σ⟧
  ; ↘⟦τ⟧′ = app.↘⟦σ⟧′
  ; σ≈σ′  = app.τ≈τ′
  ; σ≈τ   = ⟦⟧-syms app.σ≈τ
  ; τ≈τ′  = app.σ≈σ′
  }
  where module app = Intps (σ≈σ′ ⊢ϕ (⟦⟧-syms ρ≈ρ′))

⊨s-trans : Γ′ ⊨s σ ≈ σ′ ∶ Γ → Γ′ ⊨s σ′ ≈ σ″ ∶ Γ → Γ′ ⊨s σ ≈ σ″ ∶ Γ
⊨s-trans σ≈σ′ σ′≈σ″ ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = app.↘⟦σ⟧
  ; ↘⟦σ⟧′ = app.↘⟦σ⟧′
  ; ↘⟦τ⟧  = app′.↘⟦τ⟧
  ; ↘⟦τ⟧′ = app′.↘⟦τ⟧′
  ; σ≈σ′  = app.σ≈σ′
  ; σ≈τ   = ⟦⟧-transs app.σ≈τ (⟦⟧-transpˡ app′.σ≈τ eq) -- ⟦⟧-transs app.σ≈τ {!!} --  app′.σ≈τ
  ; τ≈τ′  = app′.τ≈τ′
  }
  where module app  = Intps (σ≈σ′ ⊢ϕ (⟦⟧-refls ρ≈ρ′))
        module app′ = Intps (σ′≈σ″ ⊢ϕ ρ≈ρ′)
        eq = ⟦⟧s-det app′.↘⟦σ⟧ app.↘⟦τ⟧


⊨s-refl : Γ′ ⊨s σ ≈ σ′ ∶ Γ → Γ′ ⊨s σ ∶ Γ
⊨s-refl σ≈σ′ = ⊨s-trans σ≈σ′ (⊨s-sym σ≈σ′)

⊨s-transpˡ : Γ′ ⊨s σ ≈ σ′ ∶ Γ → σ ≗ σ″ → Γ′ ⊨s σ″ ≈ σ′ ∶ Γ
⊨s-transpˡ σ≈σ′ eq ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = ⟦⟧s-transp _ (wk-app-cong _ eq) app.↘⟦σ⟧
  ; ↘⟦σ⟧′ = ⟦⟧s-transp _ eq app.↘⟦σ⟧′
  ; ↘⟦τ⟧  = app.↘⟦τ⟧
  ; ↘⟦τ⟧′ = app.↘⟦τ⟧′
  ; σ≈σ′  = app.σ≈σ′
  ; σ≈τ   = app.σ≈τ
  ; τ≈τ′  = app.τ≈τ′
  }
  where module app = Intps (σ≈σ′ ⊢ϕ ρ≈ρ′)

⊨s-transpʳ : Γ′ ⊨s σ ≈ σ′ ∶ Γ → σ′ ≗ σ″ → Γ′ ⊨s σ ≈ σ″ ∶ Γ
⊨s-transpʳ σ≈σ′ eq = ⊨s-sym (⊨s-transpˡ (⊨s-sym σ≈σ′) eq)


record IntpsId σ ρ τ ρ′ Γ : Set where
  field
    {⟦σ⟧}  : Env
    {⟦τ⟧}  : Env
    ↘⟦σ⟧   : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    σ≈τ    : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ Γ ⟧

⊨s-inst-id : Γ′ ⊨s σ ≈ σ′ ∶ Γ → ρ ≈ ρ′ ∈ ⟦ Γ′ ⟧ → IntpsId σ ρ σ′ ρ′ Γ
⊨s-inst-id {_} {σ} {σ′} σ≈σ′ ρ≈ρ′ = record
  { ↘⟦σ⟧ = ⟦⟧s-transp _ eq app.↘⟦σ⟧
  ; ↘⟦τ⟧ = ⟦⟧s-transp _ eq′ app.↘⟦τ⟧
  ; σ≈τ  = app.σ≈τ
  }
  where module app = Intps (σ≈σ′ ⊢w-id ρ≈ρ′)
        eq : σ [ id ] ≗ σ
        eq  = subst-wk-id σ
        eq′ : σ′ [ id ] ≗ σ′
        eq′ = subst-wk-id σ′
