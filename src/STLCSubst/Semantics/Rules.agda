{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module STLCSubst.Semantics.Rules(fext : Extensionality 0ℓ 0ℓ) where

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Lib

open import STLCSubst.Statics
open import STLCSubst.Statics.Properties
open import STLCSubst.Semantics.Definitions
open import STLCSubst.Semantics.PER
open import STLCSubst.Semantics.Substitutions fext

record IntpId s ρ u ρ′ T : Set where
  field
    {⟦s⟧} : D
    {⟦t⟧} : D
    ↘⟦s⟧  : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ↘⟦t⟧  : ⟦ u ⟧ ρ′ ↘ ⟦t⟧
    s≈t   : ⟦s⟧ ≈ ⟦t⟧ ∈ ⟦ T ⟧T


⊨-inst-id : Γ ⊨ t ≈ t′ ∶ T → ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → IntpId t ρ t′ ρ′ T
⊨-inst-id {_} {t} {t′} t≈t′ ρ≈ρ′ = record
  { ↘⟦s⟧ = subst (⟦_⟧ _ ↘ _) (subst-app-id t) t.↘⟦s⟧
  ; ↘⟦t⟧ = subst (⟦_⟧ _ ↘ _) (subst-app-id t′) t.↘⟦t⟧
  ; s≈t  = t.s≈t
  }
  where module t = Intp (t≈t′ ⊨id ρ≈ρ′)


≈-sym′ : Γ ⊨ t ≈ t′ ∶ T →
         -------------------
         Γ ⊨ t′ ≈ t ∶ T
≈-sym′ {T = T} t≈t′ σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = t.↘⟦t⟧
  ; ↘⟦σ⟧  = t.↘⟦τ⟧
  ; ↘⟦s⟧′ = t.↘⟦t⟧′
  ; ↘⟦t⟧  = t.↘⟦s⟧
  ; ↘⟦τ⟧  = t.↘⟦σ⟧
  ; ↘⟦t⟧′ = t.↘⟦s⟧′
  ; s≈s′  = t.t≈t′
  ; s≈t   = ⟦⟧-sym T t.s≈t
  ; t≈t′  = t.s≈s′
  }
  where module t = Intp (t≈t′ (⊨s-sym σ≈σ′) (⟦⟧-syms ρ≈ρ′))


≈-trans′ : Γ ⊨ t ≈ t′ ∶ T →
           Γ ⊨ t′ ≈ t″ ∶ T →
           -------------------
           Γ ⊨ t ≈ t″ ∶ T
≈-trans′ {T = T} t≈t′ t′≈t″ σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = t.↘⟦s⟧
  ; ↘⟦σ⟧  = t.↘⟦σ⟧
  ; ↘⟦s⟧′ = t.↘⟦s⟧′
  ; ↘⟦t⟧  = t′.↘⟦t⟧
  ; ↘⟦τ⟧  = t′.↘⟦τ⟧
  ; ↘⟦t⟧′ = t′.↘⟦t⟧′
  ; s≈s′  = t.s≈s′
  ; s≈t   = ⟦⟧-trans T t.s≈t (subst (_≈ _ ∈ ⟦ T ⟧T) (⟦⟧-det t′.↘⟦s⟧ t.↘⟦t⟧) t′.s≈t)
  ; t≈t′  = t′.t≈t′
  }
  where module t = Intp (t≈t′ (⊨s-refl σ≈σ′) (⟦⟧-refls ρ≈ρ′))
        module t′ = Intp (t′≈t″ σ≈σ′ ρ≈ρ′)


≈⇒⊨ : Γ ⊨ t ≈ t′ ∶ T →
      ------------------
      Γ ⊨ t ∶ T
≈⇒⊨ t≈t′ = ≈-trans′ t≈t′ (≈-sym′ t≈t′)


⊨ext-subst : Γ ⊨s σ ≈ σ′ ∶ Δ → Δ ⊨ t ≈ t′ ∶ T → Γ ⊨s σ ↦ (t [ σ ]) ≈ σ′ ↦ (t′ [ σ′ ]) ∶ T ∷ Δ
⊨ext-subst {_} {σ} {σ′} {_} {t} {t′} {T} σ≈σ′ t≈t′ {_} {ϕ} {ρ} {ρ′} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = ↘⟦σ⟧
  ; ↘⟦σ⟧′ = ↘⟦σ⟧′
  ; ↘⟦τ⟧  = ↘⟦τ⟧
  ; ↘⟦τ⟧′ = ↘⟦τ⟧′
  ; σ≈σ′  = equiv
  ; σ≈τ   = σ≈τ
  ; τ≈τ′  = τ≈τ′
  }
  where σ≈σ′[ϕ] : _ ⊨s σ [ ϕ ] ≈ σ′ [ ϕ ] ∶ _
        σ≈σ′[ϕ]     = ⊨wk-subst σ≈σ′ ⊢ϕ
        ρ≈ρ′[ϕ] : ⟦ ϕ ⟧w ρ ≈ ⟦ ϕ ⟧w ρ′ ∈ ⟦ _ ⟧
        ρ≈ρ′[ϕ]     = ⟦⟧-wk ⊢ϕ ρ≈ρ′
        module σ    = Intps (σ≈σ′ ⊢ϕ ρ≈ρ′)
        module t    = Intp (t≈t′ σ≈σ′[ϕ] ρ≈ρ′)
        module t[ϕ] = Intp (t≈t′ σ≈σ′ ρ≈ρ′[ϕ])
        module t[σ] = IntpId (⊨-inst-id (≈⇒⊨ t≈t′) σ.σ≈σ′)

        eq    : (σ ↦ (t [ σ ])) [ ϕ ] ≗ σ [ ϕ ] ↦ (t [ σ [ ϕ ] ])
        eq            = subst (λ x → (σ ↦ (t [ σ ])) [ ϕ ] ≗ σ [ ϕ ] ↦ x) (wk-app-subst t σ ϕ) (ext-wk σ (t [ σ ]) ϕ)
        ⟦σ⟧   : Env
        ⟦σ⟧ zero      = t.⟦s⟧
        ⟦σ⟧ (suc x)   = σ.⟦σ⟧ x
        ↘⟦σ⟧  : ⟦ (σ ↦ (t [ σ ])) [ ϕ ] ⟧s ρ ↘ ⟦σ⟧
        ↘⟦σ⟧          = ⟦⟧s-transp _ (≗.sym eq) λ { zero → t.↘⟦s⟧ ; (suc x) → σ.↘⟦σ⟧ x }
        ⟦σ⟧′  : Env
        ⟦σ⟧′ zero     = t[ϕ].⟦s⟧
        ⟦σ⟧′ (suc x)  = σ.⟦σ⟧′ x
        ↘⟦σ⟧′ : ⟦ σ ↦ (t [ σ ]) ⟧s ⟦ ϕ ⟧w ρ ↘ ⟦σ⟧′
        ↘⟦σ⟧′ zero    = t[ϕ].↘⟦s⟧
        ↘⟦σ⟧′ (suc x) = σ.↘⟦σ⟧′ x
        eqs   : t.⟦σ⟧ ≗ σ.⟦σ⟧
        eqs           = ⟦⟧s-det t.↘⟦σ⟧ σ.↘⟦σ⟧

        eq′   : (σ′ ↦ (t′ [ σ′ ])) [ ϕ ] ≗ σ′ [ ϕ ] ↦ (t′ [ σ′ [ ϕ ] ])
        eq′           = subst (λ x → (σ′ ↦ (t′ [ σ′ ])) [ ϕ ] ≗ σ′ [ ϕ ] ↦ x) (wk-app-subst t′ σ′ ϕ) (ext-wk σ′ (t′ [ σ′ ]) ϕ)
        ⟦τ⟧   : Env
        ⟦τ⟧ zero      = t.⟦t⟧
        ⟦τ⟧ (suc x)   = σ.⟦τ⟧ x
        ↘⟦τ⟧  : ⟦ (σ′ ↦ (t′ [ σ′ ])) [ ϕ ] ⟧s ρ′ ↘ ⟦τ⟧
        ↘⟦τ⟧          = ⟦⟧s-transp _ (≗.sym eq′) λ { zero → t.↘⟦t⟧ ; (suc x) → σ.↘⟦τ⟧ x }
        ⟦τ⟧′  : Env
        ⟦τ⟧′ zero     = t[ϕ].⟦t⟧
        ⟦τ⟧′ (suc x)  = σ.⟦τ⟧′ x
        ↘⟦τ⟧′ : ⟦ σ′ ↦ (t′ [ σ′ ]) ⟧s ⟦ ϕ ⟧w ρ′ ↘ ⟦τ⟧′
        ↘⟦τ⟧′ zero    = t[ϕ].↘⟦t⟧
        ↘⟦τ⟧′ (suc x) = σ.↘⟦τ⟧′ x

        eq₁ : t[σ].⟦s⟧ ≡ t.⟦s⟧′
        eq₁ = ⟦⟧-det t[σ].↘⟦s⟧ (subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext eqs) t.↘⟦s⟧′)
        eq₂ : t[ϕ].⟦σ⟧ ≗ σ.⟦σ⟧′
        eq₂ = ⟦⟧s-det t[ϕ].↘⟦σ⟧ σ.↘⟦σ⟧′
        eq₃ : t[ϕ].⟦s⟧′ ≡ t[σ].⟦t⟧
        eq₃ = ⟦⟧-det (subst (⟦ _ ⟧_↘ t[ϕ].⟦s⟧′) (fext eq₂) t[ϕ].↘⟦s⟧′) t[σ].↘⟦t⟧

        equiv : ⟦σ⟧ ≈ ⟦σ⟧′ ∈ ⟦ _ ⟧
        equiv here        = ⟦⟧-trans T t.s≈s′ (⟦⟧-trans T (subst (_≈ t[σ].⟦t⟧ ∈ ⟦ T ⟧T) eq₁ t[σ].s≈t) (subst (_≈ t[ϕ].⟦s⟧ ∈ ⟦ T ⟧T) eq₃ (⟦⟧-sym T t[ϕ].s≈s′)))
        equiv (there S∈Δ) = σ.σ≈σ′ S∈Δ

        σ≈τ : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ _ ⟧
        σ≈τ here          = t.s≈t
        σ≈τ (there S∈Δ)   = σ.σ≈τ S∈Δ

        σ′≈τ′ : ⟦σ⟧′ ≈ ⟦τ⟧′ ∈ ⟦ _ ⟧
        σ′≈τ′ here        = t[ϕ].s≈t
        σ′≈τ′ (there S∈Δ) = (⟦⟧-transs (⟦⟧-syms σ.σ≈σ′) (⟦⟧-transs σ.σ≈τ σ.τ≈τ′)) S∈Δ

        τ≈τ′ = ⟦⟧-transs (⟦⟧-syms σ≈τ) (⟦⟧-transs equiv σ′≈τ′)


v-≈′ : ∀ {x} →
       x ∶ T ∈ Γ →
       ---------------
       Γ ⊨ v x ≈ v x ∶ T
v-≈′ {_} {_} {x} T∈Γ {_} σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = app.↘⟦σ⟧ x
  ; ↘⟦σ⟧  = app.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦v⟧ x
  ; ↘⟦t⟧  = app.↘⟦τ⟧ x
  ; ↘⟦τ⟧  = app.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦v⟧ x
  ; s≈s′  = ⟦⟧-refls app.σ≈τ T∈Γ
  ; s≈t   = app.σ≈τ T∈Γ
  ; t≈t′  = ⟦⟧-refls′ app.σ≈τ T∈Γ
  }
  where module app = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)

⊨s-q-alt : ∀ T →
           Γ ⊨s σ ≈ σ′ ∶ Δ →
           T ∷ Γ ⊨s q-alt σ ≈ q-alt σ′ ∶ T ∷ Δ
⊨s-q-alt T σ≈σ′ = ⊨ext (⊨wk-subst σ≈σ′ ⊢⇑) (v-≈′ here)

⊨s-q : ∀ T →
       Γ ⊨s σ ≈ σ′ ∶ Δ →
       T ∷ Γ ⊨s q σ ≈ q σ′ ∶ T ∷ Δ
⊨s-q {_} {σ} {σ′} T σ≈σ′ = ⊨s-transpˡ (⊨s-transpʳ (⊨s-q-alt T σ≈σ′) λ x → sym (subst-q-equiv σ′ x)) λ x → sym (subst-q-equiv σ x)

ze-≈′ : Γ ⊨ ze ≈ ze ∶ N
ze-≈′ σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = ⟦ze⟧
  ; ↘⟦σ⟧  = app.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦ze⟧
  ; ↘⟦t⟧  = ⟦ze⟧
  ; ↘⟦τ⟧  = app.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦ze⟧
  ; s≈s′  = ze-≈
  ; s≈t   = ze-≈
  ; t≈t′  = ze-≈
  }
  where module app = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)


su-cong′ : Γ ⊨ t ≈ t′ ∶ N →
          ---------------------
          Γ ⊨ su t ≈ su t′ ∶ N
su-cong′ t≈t′ σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = ⟦su⟧ t.↘⟦s⟧
  ; ↘⟦σ⟧  = t.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦su⟧ t.↘⟦s⟧′
  ; ↘⟦t⟧  = ⟦su⟧ t.↘⟦t⟧
  ; ↘⟦τ⟧  = t.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦su⟧ t.↘⟦t⟧′
  ; s≈s′  = su-≈ t.s≈s′
  ; s≈t   = su-≈ t.s≈t
  ; t≈t′  = su-≈ t.t≈t′
  }
  where module t = Intp (t≈t′ σ≈σ′ ρ≈ρ′)


q-subst-equiv : ∀ {ρ‴} S → Γ ⊨s σ ≈ σ′ ∶ Δ → ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → a ≈ a′ ∈ ⟦ S ⟧T → ⟦ q σ ⟧s ρ ↦ a ↘ ρ″ → ⟦ σ ⟧s ρ ↘ ρ‴ → ρ″ ≈ ρ‴ ↦ a ∈ ⟦ S ∷ Δ ⟧
q-subst-equiv {ρ″ = ρ″} S σ≈σ′ ρ≈ρ′ a≈a′ ↘ρ″ ↘ρ‴ here
  with ρ″ 0 | ↘ρ″ 0
...  | _ | ⟦v⟧ _ = ⟦⟧-refl S a≈a′
q-subst-equiv {ρ″ = ρ″} {ρ‴} S σ≈σ′ ρ≈ρ′ a≈a′ ↘ρ″ ↘ρ‴ {suc x} {T} (there T∈Δ)
  = subst₂ ⟦ T ⟧T eq eq′ (app.σ≈σ′ T∈Δ)
  where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
        ext         = ctx-ext ρ≈ρ′ a≈a′
        module app = Intps (σ≈σ′ ⊢⇑ ext)
        eq : app.⟦σ⟧ x ≡ ρ″ (ℕ.suc x)
        eq = ⟦⟧-det (app.↘⟦σ⟧ x) (↘ρ″ (ℕ.suc x))
        eq′ : app.⟦σ⟧′ x ≡ ρ‴ x
        eq′ = ⟦⟧-det (app.↘⟦σ⟧′ x) (↘ρ‴ x)

Λ-cong′ : S ∷ Γ ⊨ t ≈ t′ ∶ T →
          ----------------------
          Γ ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
Λ-cong′ {S} {Γ} {t} {t′} {T} t≈t′ {_} {σ} {σ′} {ρ} {ρ′} σ≈σ′ ρ≈ρ′ = record
   { ↘⟦s⟧  = ⟦Λ⟧ _
   ; ↘⟦σ⟧  = app.↘⟦σ⟧
   ; ↘⟦s⟧′ = ⟦Λ⟧ t
   ; ↘⟦t⟧  = ⟦Λ⟧ _
   ; ↘⟦τ⟧  = app.↘⟦τ⟧
   ; ↘⟦t⟧′ = ⟦Λ⟧ t′
   ; s≈s′  = s≈s′
   ; s≈t   = s≈t
   ; t≈t′  = ⟦⟧-trans (S ⟶ T) (⟦⟧-sym (S ⟶ T) s≈t) (⟦⟧-trans (S ⟶ T) s≈s′ s′≈t′)
   }
  where module app = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        s≈s′ : Λ (t [ q σ ]) ρ ≈ Λ t app.⟦σ⟧ ∈ ⟦ S ⟧T ⇒ ⟦ T ⟧T
        s≈s′ {a} {a′} a≈a′ = t.⟦s⟧ - t′.⟦s⟧ - Λ∙ t.↘⟦s⟧ - Λ∙ t′.↘⟦s⟧ - ⟦⟧-trans T t.s≈s′ (subst (_≈ t′.⟦s⟧ ∈ ⟦ T ⟧T) lem₆ (⟦⟧-sym T t′.s≈t))
          where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext              = ctx-ext ρ≈ρ′ a≈a′
                module t         = Intp (t≈t′ (⊨s-q S σ≈σ′) ext)
                module app′      = Intps (σ≈σ′ ⊢⇑ ext)
                lem : ⟦ q-alt σ ⟧s ρ ↦ a ↘ t.⟦σ⟧
                lem              = ⟦⟧s-transp _ (subst-q-equiv σ) t.↘⟦σ⟧
                lem₁ : t.⟦σ⟧ ≗ app′.⟦σ⟧ ↦ a
                lem₁             = ⟦⟧s-det lem (λ { zero → ⟦v⟧ 0 ; (suc x) → app′.↘⟦σ⟧ x })
                lem₂ : app′.⟦σ⟧′ ≗ app.⟦σ⟧
                lem₂             = ⟦⟧s-det app′.↘⟦σ⟧′ app.↘⟦σ⟧
                lem₃ : app′.⟦σ⟧ ↦ a ≈ app.⟦σ⟧ ↦ a′ ∈ ⟦ S ∷ Γ ⟧
                lem₃             =  ctx-ext (⟦⟧-transpʳ app′.σ≈σ′ lem₂) a≈a′
                lem₄ : app.⟦σ⟧ ↦ a′ ≈ app′.⟦σ⟧ ↦ a ∈ ⟦ S ∷ Γ ⟧
                lem₄             = ⟦⟧-syms lem₃
                module t′        = IntpId (⊨-inst-id (≈⇒⊨ t≈t′) lem₄)
                lem₅ : ⟦ t ⟧ app′.⟦σ⟧ ↦ a ↘ t.⟦s⟧′
                lem₅             = subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext lem₁) t.↘⟦s⟧′
                lem₆ : t′.⟦t⟧ ≡ t.⟦s⟧′
                lem₆             = ⟦⟧-det t′.↘⟦t⟧ lem₅

        s≈t : Λ (t [ q σ ]) ρ ≈ Λ (t′ [ q σ′ ]) ρ′ ∈ ⟦ S ⟧T ⇒ ⟦ T ⟧T
        s≈t a≈a′ = t.⟦s⟧ - t.⟦t⟧ - (Λ∙ t.↘⟦s⟧) - Λ∙ t.↘⟦t⟧ - t.s≈t
          where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext = ctx-ext ρ≈ρ′ a≈a′
                module t = Intp (t≈t′ (⊨s-q S σ≈σ′) ext)

        s′≈t′ : Λ t app.⟦σ⟧ ≈ Λ t′ app.⟦τ⟧ ∈ ⟦ S ⟧T ⇒ ⟦ T ⟧T
        s′≈t′ a≈a′ = t.⟦s⟧ - t.⟦t⟧ - (Λ∙ t.↘⟦s⟧) - Λ∙ t.↘⟦t⟧ - t.s≈t
          where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext = ctx-ext app.σ≈τ a≈a′
                module t = IntpId (⊨-inst-id t≈t′ ext)


$-cong′ : Γ ⊨ t ≈ t′ ∶ S ⟶ T →
          Γ ⊨ s ≈ s′ ∶ S →
          ------------------------
          Γ ⊨ t $ s ≈ t′ $ s′ ∶ T
$-cong′ {T = T} t≈t′ s≈s′ σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = ⟦$⟧ t.↘⟦s⟧ s.↘⟦s⟧ ap.↘fa
  ; ↘⟦σ⟧  = app.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦$⟧ (subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext eq₁) t.↘⟦s⟧′) (subst (⟦ _ ⟧_↘ s.⟦s⟧′) (fext eq₂) s.↘⟦s⟧′) ap.↘fa′
  ; ↘⟦t⟧  = ⟦$⟧ t.↘⟦t⟧ s.↘⟦t⟧ ap′.↘fa
  ; ↘⟦τ⟧  = app.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦$⟧ (subst (⟦ _ ⟧_↘ t.⟦t⟧′) (fext eq₃) t.↘⟦t⟧′) (subst (⟦ _ ⟧_↘ s.⟦t⟧′) (fext eq₄) s.↘⟦t⟧′) ap′.↘fa′
  ; s≈s′  = ap.fa≈fa′
  ; s≈t   = subst₂ ⟦ T ⟧T (ap-det ap″.↘fa ap.↘fa) (ap-det ap″.↘fa′ ap′.↘fa) ap″.fa≈fa′
  ; t≈t′  = ap′.fa≈fa′
  }
  where module app = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        module t = Intp (t≈t′ σ≈σ′ ρ≈ρ′)
        module s = Intp (s≈s′ σ≈σ′ ρ≈ρ′)
        eq₁ : t.⟦σ⟧ ≗ app.⟦σ⟧
        eq₁ = ⟦⟧s-det t.↘⟦σ⟧ app.↘⟦σ⟧
        eq₂ : s.⟦σ⟧ ≗ app.⟦σ⟧
        eq₂ = ⟦⟧s-det s.↘⟦σ⟧ app.↘⟦σ⟧
        eq₃ : t.⟦τ⟧ ≗ app.⟦τ⟧
        eq₃ = ⟦⟧s-det t.↘⟦τ⟧ app.↘⟦τ⟧
        eq₄ : s.⟦τ⟧ ≗ app.⟦τ⟧
        eq₄ = ⟦⟧s-det s.↘⟦τ⟧ app.↘⟦τ⟧
        module ap  = FAppIn (t.s≈s′ s.s≈s′)
        module ap′ = FAppIn (t.t≈t′ s.t≈t′)
        module ap″ = FAppIn (t.s≈t s.s≈t)


Λ-β′ : S ∷ Γ ⊨ t ∶ T →
       Γ ⊨ s ∶ S →
       ------------------------------
       Γ ⊨ Λ t $ s ≈ t [ id ↦ s ] ∶ T
Λ-β′ {S} {Γ} {t} {T} {s} ⊨t ⊨s {_} {σ} {σ′} {ρ} {ρ′} σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = ⟦$⟧ (⟦Λ⟧ (t [ q σ ])) s.↘⟦s⟧ (Λ∙ t.↘⟦s⟧)
  ; ↘⟦σ⟧  = s.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦$⟧ (⟦Λ⟧ t) s.↘⟦s⟧′ (Λ∙ t′.↘⟦s⟧)
  ; ↘⟦t⟧  = ↘⟦t⟧
  ; ↘⟦τ⟧  = s.↘⟦τ⟧
  ; ↘⟦t⟧′ = t-ext′.↘⟦t⟧
  ; s≈s′  = s≈s′
  ; s≈t   = s≈t
  ; t≈t′  = t≈t′
  }
  where module σ      = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        module s      = Intp (⊨s σ≈σ′ ρ≈ρ′)
        ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
        ext           = ctx-ext (⟦⟧-refls ρ≈ρ′) s.s≈s′
        module t      = Intp (⊨t (⊨s-q S (⊨s-refl σ≈σ′)) ext)
        σ-eq : σ.⟦σ⟧ ≗ s.⟦σ⟧
        σ-eq          = ⟦⟧s-det σ.↘⟦σ⟧ s.↘⟦σ⟧
        τ-eq : σ.⟦τ⟧ ≗ s.⟦τ⟧
        τ-eq          = ⟦⟧s-det σ.↘⟦τ⟧ s.↘⟦τ⟧
        σ≈τ : s.⟦σ⟧ ≈ s.⟦τ⟧ ∈ ⟦ Γ ⟧
        σ≈τ           = ⟦⟧-transpˡ (⟦⟧-transpʳ σ.σ≈τ τ-eq) σ-eq
        module t′     = IntpId (⊨-inst-id ⊨t (ctx-ext σ≈τ (⟦⟧-sym S s.s≈s′)))
        σs            = ⊨ext-subst σ≈σ′ ⊨s
        module σs     = IntpsId (⊨s-inst-id σs ρ≈ρ′)
        module t-ext  = Intp (⊨t σs ρ≈ρ′)
        ids           = ⊨ext ⊨id ⊨s
        module ids    = IntpsId (⊨s-inst-id ids σ≈τ)
        module t-ext′ = Intp (⊨t ids σ≈τ)

        ↘⟦t⟧ : ⟦ t [ id ↦ s ] [ σ′ ] ⟧ ρ′ ↘ t-ext.⟦t⟧
        ↘⟦t⟧  = subst (⟦_⟧ ρ′ ↘ t-ext.⟦t⟧) (trans (subst-transp t (≗.sym (ext-comp id σ′ s))) (sym (subst-app-comb t (id ↦ s) σ′))) t-ext.↘⟦t⟧

        eq₁ : t.⟦τ⟧ ≈ s.⟦σ⟧ ↦ s.⟦s⟧′ ∈ ⟦ S ∷ _ ⟧
        eq₁ = q-subst-equiv S σ≈σ′ ρ≈ρ′ (⟦⟧-sym S s.s≈s′) t.↘⟦τ⟧ s.↘⟦σ⟧
        eq₂ : t.⟦t⟧′ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        eq₂ = subst₂ ⟦ T ⟧T (⟦⟧-det tt.↘⟦s⟧ t.↘⟦t⟧′) (⟦⟧-det tt.↘⟦t⟧ t′.↘⟦s⟧) tt.s≈t
          where module tt = IntpId (⊨-inst-id ⊨t eq₁)
        eq₃ : t-ext.⟦τ⟧ ≗ σs.⟦τ⟧
        eq₃ = ⟦⟧s-det t-ext.↘⟦τ⟧ σs.↘⟦τ⟧
        ⟦σ′s⟧↘ : ⟦ σ′ ↦ (s [ σ′ ]) ⟧s ρ′ ↘ σ.⟦τ⟧ ↦ s.⟦t⟧
        ⟦σ′s⟧↘ = ⟦⟧s-ext σ.↘⟦τ⟧ s.↘⟦t⟧
        eq₄ : t-ext.⟦τ⟧ ≗ s.⟦τ⟧ ↦ s.⟦t⟧
        eq₄ = ≗.trans eq₃ (≗.trans (⟦⟧s-det σs.↘⟦τ⟧ ⟦σ′s⟧↘) (ext-cong τ-eq refl))
        eq₅ : t-ext.⟦t⟧′ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        eq₅ = subst₂ ⟦ T ⟧T (⟦⟧-det tt.↘⟦s⟧ t-ext.↘⟦t⟧′) (⟦⟧-det tt.↘⟦t⟧ t′.↘⟦s⟧) tt.s≈t
          where ext′ = ⟦⟧-transpˡ (ctx-ext (⟦⟧-syms σ≈τ) s.t≈s′) (≗.sym eq₄)
                module tt = IntpId (⊨-inst-id ⊨t ext′)
        eq₆ : t-ext′.⟦τ⟧ ≗ s.⟦τ⟧ ↦ s.⟦t⟧′
        eq₆ = ⟦⟧s-det t-ext′.↘⟦τ⟧ (⟦⟧s-ext ⟦⟧s-id s.↘⟦t⟧′)
        eq₇ : t-ext′.⟦t⟧′ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        eq₇ = subst₂ ⟦ T ⟧T (⟦⟧-det tt.↘⟦s⟧ t-ext′.↘⟦t⟧′) (⟦⟧-det tt.↘⟦t⟧ t′.↘⟦s⟧) tt.s≈t
          where ext′ = ⟦⟧-transpˡ (ctx-ext (⟦⟧-syms σ≈τ) (⟦⟧-sym S s.s′≈t′)) (≗.sym eq₆)
                module tt = IntpId (⊨-inst-id ⊨t ext′)

        s≈s′ : t.⟦s⟧ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        s≈s′  = ⟦⟧-trans T t.s≈t (⟦⟧-trans T t.t≈t′ eq₂)
        t≈s′ : t-ext.⟦t⟧ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        t≈s′  = ⟦⟧-trans T t-ext.t≈t′ eq₅
        t′≈s′ : t-ext′.⟦t⟧ ≈ t′.⟦s⟧ ∈ ⟦ T ⟧T
        t′≈s′ = ⟦⟧-trans T t-ext′.t≈t′ eq₇
        s≈t : t.⟦s⟧ ≈ t-ext.⟦t⟧ ∈ ⟦ T ⟧T
        s≈t   = ⟦⟧-trans T s≈s′ (⟦⟧-sym T t≈s′)
        t≈t′ : t-ext.⟦t⟧ ≈ t-ext′.⟦t⟧ ∈ ⟦ T ⟧T
        t≈t′  = ⟦⟧-trans T t≈s′ (⟦⟧-sym T t′≈s′)

Λ-η′ : Γ ⊨ t ∶ S ⟶ T →
       ----------------------------------
       Γ ⊨ t ≈ Λ ((t [ ⇑ ]) $ v 0) ∶ S ⟶ T
Λ-η′ {_} {t} {S} {T} ⊨t {_} {σ} {σ′} {ρ} {ρ′} σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = t.↘⟦s⟧
  ; ↘⟦σ⟧  = t.↘⟦σ⟧
  ; ↘⟦s⟧′ = t.↘⟦s⟧′
  ; ↘⟦t⟧  = ⟦Λ⟧ _
  ; ↘⟦τ⟧  = σ.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦Λ⟧ _
  ; s≈s′  = t.s≈s′
  ; s≈t   = ⟦⟧-trans (S ⟶ T) t.s≈s′ s′≈t
  ; t≈t′  = ⟦⟧-trans (S ⟶ T) (⟦⟧-sym (S ⟶ T) s′≈t) s′≈t′
  }
  where module σ = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        module t = Intp (⊨t σ≈σ′ ρ≈ρ′)

        s′≈t : t.⟦s⟧′ ≈ Λ ((t [ ⇑ ] [ q σ′ ]) $ v 0) ρ′ ∈ ⟦ S ⟧T ⇒ ⟦ T ⟧T
        s′≈t {a} {a′} a≈a′ = ap′.fa - ap.fa′
                           - ap′.↘fa
                           - Λ∙ (subst (λ x → ⟦ x $ v 0 ⟧ _ ↘ ap.fa′) (sym (exp-wk-q t σ′)) ↘fa′)
                           - ⟦⟧-trans T ap′.fa≈fa′ (⟦⟧-trans T (subst (_≈ ap″.fa ∈ ⟦ T ⟧T) eq₅ (⟦⟧-sym T ap″.fa≈fa′)) (subst (_≈ ap.fa′ ∈ ⟦ T ⟧T) eq₆ ap.fa≈fa′))
          where σ[⇑] = ⊨wk-subst (⊨s-refl (⊨s-sym σ≈σ′)) ⊢⇑
                ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext = ⟦⟧-refls′ (ctx-ext ρ≈ρ′ a≈a′)
                module σ′ = Intps (σ≈σ′ ⊢⇑ ext)
                module t′ = Intp (⊨t σ[⇑] ext)
                module ap = FAppIn (⟦⟧-sym (S ⟶ T) t′.t≈t′ (⟦⟧-refl′ S a≈a′))
                ↘fa′ : ⟦ (t [ σ′ [ ⇑ ] ]) $ v 0 ⟧ ρ′ ↦ a′ ↘ ap.fa′
                ↘fa′ = ⟦$⟧ t′.↘⟦t⟧ (⟦v⟧ 0) ap.↘fa′
                eq₁ : t′.⟦τ⟧ ≗ σ′.⟦τ⟧
                eq₁ = ⟦⟧s-det t′.↘⟦τ⟧ σ′.↘⟦τ⟧
                eq₂ : t.⟦τ⟧ ≗ σ′.⟦τ⟧′
                eq₂ = ⟦⟧s-det t.↘⟦τ⟧ σ′.↘⟦τ⟧′
                module t″ = IntpId (⊨-inst-id ⊨t (⟦⟧-transpˡ (⟦⟧-transpʳ σ′.τ≈τ′ (≗.sym eq₂)) (≗.sym eq₁)))
                eq₃ : t′.⟦t⟧′ ≡ t″.⟦s⟧
                eq₃ = ⟦⟧-det t′.↘⟦t⟧′ t″.↘⟦s⟧
                eq₄ : t.⟦t⟧′ ≡ t″.⟦t⟧
                eq₄ = ⟦⟧-det t.↘⟦t⟧′ t″.↘⟦t⟧
                module ap′ = FAppIn (t.s′≈t′ a≈a′)
                equiv : t′.⟦t⟧′ ≈ t.⟦t⟧′ ∈ ⟦ S ⟶ T ⟧T
                equiv = subst₂ ⟦ S ⟶ T ⟧T (sym eq₃) (sym eq₄) t″.s≈t
                module ap″ = FAppIn (equiv (⟦⟧-refl′ S a≈a′))
                eq₅ : ap″.fa′ ≡ ap′.fa′
                eq₅ = ap-det ap″.↘fa′ ap′.↘fa′
                eq₆ : ap.fa ≡ ap″.fa
                eq₆ = ap-det ap.↘fa ap″.↘fa

        s′≈t′ : t.⟦s⟧′ ≈ Λ ((t [ ⇑ ]) $ v 0) σ.⟦τ⟧ ∈ ⟦ S ⟧T ⇒ ⟦ T ⟧T
        s′≈t′ {a} {a′} a≈a′ = {!!} - {!!}
                            - {!!}
                            - Λ∙ (⟦$⟧ {!!} (⟦v⟧ 0) {!!})
                            - {!!}
