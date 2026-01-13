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

record Equiv Γ : Set where
  field
    {t₁} : Exp
    {t₂} : Exp
    {TT} : Typ
    equiv : Γ ⊨ t₁ ≈ t₂ ∶ TT

⊨ext-subst-gen : Γ ⊨s σ ≈ σ′ ∶ Δ →
                 (equivs : List (Equiv Δ)) →
                 Γ ⊨s subst-exts σ (L.map (λ e → Equiv.t₁ e [ σ ]) equivs) ≈ subst-exts σ′ (L.map (λ e → Equiv.t₂ e [ σ′ ]) equivs) ∶ L.map Equiv.TT equivs ++ Δ
⊨ext-subst-gen {_} {σ} {σ′} {_} σ≈σ′ [] ⊢ϕ ρ≈ρ′ = σ≈σ′ ⊢ϕ ρ≈ρ′
⊨ext-subst-gen {_} {σ} {σ′} {_} σ≈σ′ (record { t₁ = t₁ ; t₂ = t₂ ; TT = TT ; equiv = t≈t′ } ∷ equivs) {_} {ϕ} {ρ} {ρ′} ⊢ϕ ρ≈ρ′
  with ⊨ext-subst-gen σ≈σ′ equivs ⊢ϕ ρ≈ρ′
...  | prev = record
  { ↘⟦σ⟧  = ↘⟦σ⟧
  ; ↘⟦σ⟧′ = ↘⟦σ⟧′
  ; ↘⟦τ⟧  = ↘⟦τ⟧
  ; ↘⟦τ⟧′ = ↘⟦τ⟧′
  ; σ≈σ′  = equiv
  ; σ≈τ   = σ≈τ
  ; τ≈τ′  = τ≈τ′
  }
  where module prev = Intps prev
        σ≈σ′[ϕ] : _ ⊨s σ [ ϕ ] ≈ σ′ [ ϕ ] ∶ _
        σ≈σ′[ϕ]     = ⊨wk-subst σ≈σ′ ⊢ϕ
        ρ≈ρ′[ϕ] : ⟦ ϕ ⟧w ρ ≈ ⟦ ϕ ⟧w ρ′ ∈ ⟦ _ ⟧
        ρ≈ρ′[ϕ]     = ⟦⟧-wk ⊢ϕ ρ≈ρ′
        module σ    = Intps (σ≈σ′ ⊢ϕ ρ≈ρ′)
        module t    = Intp (t≈t′ σ≈σ′[ϕ] ρ≈ρ′)
        module t[ϕ] = Intp (t≈t′ σ≈σ′ ρ≈ρ′[ϕ])
        module t[σ] = IntpId (⊨-inst-id (≈⇒⊨ t≈t′) σ.σ≈σ′)

        τ₁ = subst-exts σ (L.map (λ e → Equiv.t₁ e [ σ ]) equivs)
        τ₂ = subst-exts σ′ (L.map (λ e → Equiv.t₂ e [ σ′ ]) equivs)

        eq    : (τ₁ ↦ (t₁ [ σ ])) [ ϕ ] ≗ τ₁ [ ϕ ] ↦ (t₁ [ σ [ ϕ ] ])
        eq            = subst (λ x → (τ₁ ↦ (t₁ [ σ ])) [ ϕ ] ≗ τ₁ [ ϕ ] ↦ x) (wk-app-subst t₁ σ ϕ) (ext-wk τ₁ (t₁ [ σ ]) ϕ)
        ⟦σ⟧   : Env
        ⟦σ⟧ zero      = t.⟦s⟧
        ⟦σ⟧ (suc x)   = prev.⟦σ⟧ x
        ↘⟦σ⟧  : ⟦ (τ₁ ↦ (t₁ [ σ ])) [ ϕ ] ⟧s ρ ↘ ⟦σ⟧
        ↘⟦σ⟧          = ⟦⟧s-transp _ (≗.sym eq) λ { zero → t.↘⟦s⟧ ; (suc x) → prev.↘⟦σ⟧ x }
        ⟦σ⟧′  : Env
        ⟦σ⟧′ zero     = t[ϕ].⟦s⟧
        ⟦σ⟧′ (suc x)  = prev.⟦σ⟧′ x
        ↘⟦σ⟧′ : ⟦ τ₁ ↦ (t₁ [ σ ]) ⟧s ⟦ ϕ ⟧w ρ ↘ ⟦σ⟧′
        ↘⟦σ⟧′ zero    = t[ϕ].↘⟦s⟧
        ↘⟦σ⟧′ (suc x) = prev.↘⟦σ⟧′ x
        eqs   : t.⟦σ⟧ ≗ σ.⟦σ⟧
        eqs           = ⟦⟧s-det t.↘⟦σ⟧ σ.↘⟦σ⟧

        eq′   : (τ₂ ↦ (t₂ [ σ′ ])) [ ϕ ] ≗ τ₂ [ ϕ ] ↦ (t₂ [ σ′ [ ϕ ] ])
        eq′           = subst (λ x → (τ₂ ↦ (t₂ [ σ′ ])) [ ϕ ] ≗ τ₂ [ ϕ ] ↦ x) (wk-app-subst t₂ σ′ ϕ) (ext-wk τ₂ (t₂ [ σ′ ]) ϕ)
        ⟦τ⟧   : Env
        ⟦τ⟧ zero      = t.⟦t⟧
        ⟦τ⟧ (suc x)   = prev.⟦τ⟧ x
        ↘⟦τ⟧  : ⟦ (τ₂ ↦ (t₂ [ σ′ ])) [ ϕ ] ⟧s ρ′ ↘ ⟦τ⟧
        ↘⟦τ⟧          = ⟦⟧s-transp _ (≗.sym eq′) λ { zero → t.↘⟦t⟧ ; (suc x) → prev.↘⟦τ⟧ x }
        ⟦τ⟧′  : Env
        ⟦τ⟧′ zero     = t[ϕ].⟦t⟧
        ⟦τ⟧′ (suc x)  = prev.⟦τ⟧′ x
        ↘⟦τ⟧′ : ⟦ τ₂ ↦ (t₂ [ σ′ ]) ⟧s ⟦ ϕ ⟧w ρ′ ↘ ⟦τ⟧′
        ↘⟦τ⟧′ zero    = t[ϕ].↘⟦t⟧
        ↘⟦τ⟧′ (suc x) = prev.↘⟦τ⟧′ x

        eq₁ : t[σ].⟦s⟧ ≡ t.⟦s⟧′
        eq₁ = ⟦⟧-det t[σ].↘⟦s⟧ (subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext eqs) t.↘⟦s⟧′)
        eq₂ : t[ϕ].⟦σ⟧ ≗ σ.⟦σ⟧′
        eq₂ = ⟦⟧s-det t[ϕ].↘⟦σ⟧ σ.↘⟦σ⟧′
        eq₃ : t[ϕ].⟦s⟧′ ≡ t[σ].⟦t⟧
        eq₃ = ⟦⟧-det (subst (⟦ _ ⟧_↘ t[ϕ].⟦s⟧′) (fext eq₂) t[ϕ].↘⟦s⟧′) t[σ].↘⟦t⟧

        equiv : ⟦σ⟧ ≈ ⟦σ⟧′ ∈ ⟦ _ ⟧
        equiv here        = ⟦⟧-trans TT
                                     t.s≈s′
                           (⟦⟧-trans TT
                                     (subst (_≈ t[σ].⟦t⟧ ∈ ⟦ TT ⟧T) eq₁ t[σ].s≈t)
                                     (subst (_≈ t[ϕ].⟦s⟧ ∈ ⟦ TT ⟧T) eq₃ (⟦⟧-sym TT t[ϕ].s≈s′)))
        equiv (there S∈Δ) = prev.σ≈σ′ S∈Δ

        σ≈τ : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ _ ⟧
        σ≈τ here          = t.s≈t
        σ≈τ (there S∈Δ)   = prev.σ≈τ S∈Δ

        σ′≈τ′ : ⟦σ⟧′ ≈ ⟦τ⟧′ ∈ ⟦ _ ⟧
        σ′≈τ′ here        = t[ϕ].s≈t
        σ′≈τ′ (there S∈Δ) = (⟦⟧-transs (⟦⟧-syms prev.σ≈σ′) (⟦⟧-transs prev.σ≈τ prev.τ≈τ′)) S∈Δ

        τ≈τ′ = ⟦⟧-transs (⟦⟧-syms σ≈τ) (⟦⟧-transs equiv σ′≈τ′)

⊨ext-subst : Γ ⊨s σ ≈ σ′ ∶ Δ → Δ ⊨ t ≈ t′ ∶ T → Γ ⊨s σ ↦ (t [ σ ]) ≈ σ′ ↦ (t′ [ σ′ ]) ∶ T ∷ Δ
⊨ext-subst σ≈σ′ t≈t′ = ⊨ext-subst-gen σ≈σ′ (record { equiv = t≈t′ } ∷ [])

⊨ext-subst₂ : Γ ⊨s σ ≈ σ′ ∶ Δ →
              Δ ⊨ t ≈ t′ ∶ T →
              Δ ⊨ s ≈ s′ ∶ S →
              Γ ⊨s σ ↦ (t [ σ ]) ↦ (s [ σ ]) ≈ σ′ ↦ (t′ [ σ′ ]) ↦ (s′ [ σ′ ]) ∶ S ∷ T ∷ Δ
⊨ext-subst₂ σ≈σ′ t≈t′ s≈s′ = ⊨ext-subst-gen σ≈σ′ (record { equiv = s≈s′ } ∷ record { equiv = t≈t′ } ∷ [])


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

q-subst-equiv′ : ∀ {ρ‴} S → Γ ⊨s σ ≈ σ′ ∶ Δ → ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ⟦ σ ⟧s ρ ↘ ρ‴ → a ≈ a′ ∈ ⟦ S ⟧T → ∃ λ ρ″ → ⟦ q σ ⟧s ρ ↦ a ↘ ρ″ × ρ″ ≈ ρ‴ ↦ a ∈ ⟦ S ∷ Δ ⟧
q-subst-equiv′ S σ≈σ′ ρ≈ρ′ ↘ρ‴ a≈a′ = -, qσ.↘⟦σ⟧ , q-subst-equiv S σ≈σ′ ρ≈ρ′ a≈a′ qσ.↘⟦σ⟧ ↘ρ‴
  where qσ  = ⊨s-q S σ≈σ′
        ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
        ext = ctx-ext ρ≈ρ′ a≈a′
        module qσ = IntpsId (⊨s-inst-id qσ ext)


qq-subst-equiv′ : ∀ {ρ‴} S T →
                  Γ ⊨s σ ≈ σ′ ∶ Δ →
                  ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ⟦ σ ⟧s ρ ↘ ρ‴ → a ≈ a′ ∈ ⟦ S ⟧T → b ≈ b′ ∈ ⟦ T ⟧T →
                  ∃ λ ρ″ → ⟦ q (q σ) ⟧s ρ ↦ a ↦ b ↘ ρ″ × ρ″ ≈ ρ‴ ↦ a ↦ b ∈ ⟦ T ∷ S ∷ Δ ⟧
qq-subst-equiv′ S T σ≈σ′ ρ≈ρ′ ↘ρ‴ a≈a′ b≈b′
  with q-subst-equiv′ S σ≈σ′ ρ≈ρ′ ↘ρ‴ a≈a′
...  | _ , ↘ρ₁ , ρ₁≈
     with q-subst-equiv′ T (⊨s-q S σ≈σ′) (ctx-ext ρ≈ρ′ a≈a′) ↘ρ₁ b≈b′
...     | _ , ↘ρ₂ , ρ₂≈ = -, ↘ρ₂ , ⟦⟧-transs ρ₂≈ (ctx-ext ρ₁≈ (⟦⟧-refl T b≈b′))


qq-subst-equiv : ∀ {ρ‴} S T →
                 Γ ⊨s σ ≈ σ′ ∶ Δ →
                 ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ⟦ σ ⟧s ρ ↘ ρ‴ → a ≈ a′ ∈ ⟦ S ⟧T → b ≈ b′ ∈ ⟦ T ⟧T →
                 ⟦ q (q σ) ⟧s ρ ↦ a ↦ b ↘ ρ″ →
                 ρ″ ≈ ρ‴ ↦ a ↦ b ∈ ⟦ T ∷ S ∷ Δ ⟧
qq-subst-equiv S T σ≈σ′ ρ≈ρ′ ↘ρ‴ a≈a′ b≈b′ ↘ρ″
  with qq-subst-equiv′ S T σ≈σ′ ρ≈ρ′ ↘ρ‴ a≈a′ b≈b′
...  | _ , ↘ρ₁ , ρ₁≈ = ⟦⟧-transpˡ ρ₁≈ eq
  where eq = ⟦⟧s-det ↘ρ₁ ↘ρ″

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
        ↘⟦t⟧  = subst (⟦_⟧ ρ′ ↘ t-ext.⟦t⟧) (sym (subst-ext-app₁ t s v σ′)) t-ext.↘⟦t⟧

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
        s′≈t′ {a} {a′} a≈a′ = ap.fa - ap′.fa′
                            - subst (_∙ _ ↘ ap.fa) eq₃ ap.↘fa
                            - Λ∙ (⟦$⟧ ⟦t⇑⟧ (⟦v⟧ 0) ap′.↘fa′)
                            - ⟦⟧-trans T ap.fa≈fa′ (subst (_≈ ap′.fa′ ∈ ⟦ T ⟧T) eq₅ ap′.fa≈fa′)
          where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext        = ⟦⟧-refls′ (ctx-ext σ.σ≈τ a≈a′)
                module t′  = Intp (⊨t (⊨⇑ S) ext)
                ⟦t⇑⟧ : ⟦ t [ ⇑ ] ⟧ σ.⟦τ⟧ ↦ a′ ↘ t′.⟦s⟧
                ⟦t⇑⟧       = subst (⟦_⟧ _ ↘ t′.⟦s⟧) (conv-equiv t ⇑) t′.↘⟦s⟧
                eq₁ : t′.⟦σ⟧ ≗ σ.⟦τ⟧
                eq₁        = ⟦⟧s-conv ⇑ t′.↘⟦σ⟧
                eq₂ : t.⟦σ⟧ ≗ σ.⟦σ⟧
                eq₂        = ⟦⟧s-det t.↘⟦σ⟧ σ.↘⟦σ⟧
                module t″  = IntpId (⊨-inst-id ⊨t (⟦⟧-transpˡ ((⟦⟧-transpʳ σ.σ≈τ (≗.sym eq₁))) (≗.sym eq₂)))
                eq₃ : t″.⟦s⟧ ≡ t.⟦s⟧′
                eq₃        = ⟦⟧-det t″.↘⟦s⟧  t.↘⟦s⟧′
                module ap  = FAppIn (t″.s≈t a≈a′)
                module ap′ = FAppIn (⟦⟧-sym (S ⟶ T) t′.s≈s′ (⟦⟧-refl′ S a≈a′))
                eq₄ : t′.⟦s⟧′ ≡ t″.⟦t⟧
                eq₄        = ⟦⟧-det t′.↘⟦s⟧′ t″.↘⟦t⟧
                eq₅ : ap′.fa ≡ ap.fa′
                eq₅ = ap-det (subst (_∙ _ ↘ ap′.fa) eq₄ ap′.↘fa) ap.↘fa′


rec-helper : a ≈ a′ ∈ ⟦ T ⟧T →
             T ∷ N ∷ Γ ⊨ r ∶ T →
             Γ′ ⊨s σ ≈ σ′ ∶ Γ →
             ρ ≈ ρ′ ∈ ⟦ Γ′ ⟧ →
             ⟦ σ ⟧s ρ ↘ ρ″ →
             ρ″ ≈ ρ″ ∈ ⟦ Γ ⟧ →
             b ≈ b′ ∈N →
             ∃₂ λ z z′ → rec T , a , r [ q (q σ) ] , ρ , b ↘ z × rec T , a′ , r , ρ″ , b′ ↘ z′ × z ≈ z′ ∈ ⟦ T ⟧T
rec-helper a≈a′ r≈r′ σ≈σ′ ρ≈ρ′ ↘ρ″ ρ″≈ ze-≈ = -, -, rze , rze , a≈a′
rec-helper {_} {_} {T} {_} {Γ′ = Γ′} {σ} {σ′} {ρ} {ρ′} a≈a′ r≈r′ σ≈σ′ ρ≈ρ′ ↘ρ″ ρ″≈ (su-≈ {b} {b′} b≈b′)
  with rec-helper a≈a′ r≈r′ σ≈σ′ ρ≈ρ′ ↘ρ″ ρ″≈ b≈b′
...  | z , z′ , ↘z , ↘z′ , z≈z′ = -, -, rsu ↘z r.↘⟦s⟧ , rsu ↘z′ r′.↘⟦t⟧ , ⟦⟧-trans T r.s≈s′ (subst (λ x → ⟦ T ⟧T x r′.⟦t⟧) (⟦⟧-det r′.↘⟦s⟧ r.↘⟦s⟧′) r′.s≈t)
  where qqσ = ⊨s-q T (⊨s-q N (⊨s-refl σ≈σ′))
        ext : ρ ↦ b ↦ z ≈ ρ′ ↦ b′ ↦ z′ ∈ ⟦ T ∷ N ∷ Γ′ ⟧
        ext = ctx-ext (ctx-ext ρ≈ρ′ b≈b′) z≈z′
        module r = Intp ((≈⇒⊨ r≈r′) qqσ ext)
        eq₁ = qq-subst-equiv N T σ≈σ′ ρ≈ρ′ ↘ρ″ b≈b′ z≈z′ r.↘⟦σ⟧
        eq₂ = ⟦⟧-transs eq₁ (ctx-ext (ctx-ext ρ″≈ b≈b′) z≈z′)
        module r′ = IntpId (⊨-inst-id r≈r′ eq₂)
rec-helper {a} {a′} {T} {Γ} {r} {Γ′} {σ} {σ′} {ρ} {ρ′} {ρ″} a≈a′ r≈r′ σ≈σ′ ρ≈ρ′ ↘ρ″ ρ″≈ (↑N {e} {e′} e≈e′) = -, -, rec , rec , Bot⇒⟦⟧ T helper
  where helper : rec T (↓ T a) (r [ q (q σ) ]) ρ e ≈ rec T (↓ T a′) r ρ″ e′ ∈ Bot
        helper n
          with  ⟦⟧⇒Top T a≈a′ n | e≈e′ n
        ...  | _ , a↘ , a′↘ | _ , e↘ , e′↘ =
          let _ , rs↘ , r′t↘ = ⟦⟧⇒Top T eq₃ (ℕ.suc (ℕ.suc n))
          in -, Rr n a↘ r.↘⟦s⟧ rs↘ e↘ , Rr n a′↘ r′.↘⟦t⟧ r′t↘ e′↘
          where qqσ = ⊨s-q T (⊨s-q N (⊨s-refl σ≈σ′))
                ext : ρ ↦ l′ N n ↦ l′ T (1 + n) ≈ ρ′ ↦ l′ N n ↦ l′ T (1 + n) ∈ ⟦ T ∷ N ∷ Γ′ ⟧
                ext = ctx-ext (ctx-ext ρ≈ρ′ (Bot⇒⟦⟧ N (l∈Bot n))) (Bot⇒⟦⟧ T (l∈Bot (1 + n)))
                module r = Intp ((≈⇒⊨ r≈r′) qqσ ext)
                eq₁ = qq-subst-equiv N T σ≈σ′ ρ≈ρ′ ↘ρ″ (Bot⇒⟦⟧ N (l∈Bot n)) (Bot⇒⟦⟧ T (l∈Bot (1 + n))) r.↘⟦σ⟧
                module r′ = IntpId (⊨-inst-id r≈r′ eq₁)
                eq₂ = ⟦⟧-det r′.↘⟦s⟧ r.↘⟦s⟧′
                eq₃ = ⟦⟧-trans T r.s≈s′ (subst (λ x → ⟦ T ⟧T x r′.⟦t⟧) eq₂ r′.s≈t)

rec-helper′ : a ≈ a′ ∈ ⟦ T ⟧T →
              T ∷ N ∷ Γ ⊨ r ≈ r′ ∶ T →
              ρ ≈ ρ′ ∈ ⟦ Γ ⟧ →
              b ≈ b′ ∈N →
              ∃₂ λ z z′ → rec T , a , r , ρ , b ↘ z × rec T , a′ , r′ , ρ′ , b′ ↘ z′ × z ≈ z′ ∈ ⟦ T ⟧T
rec-helper′ a≈a′ r≈r′ ρ≈ρ′ ze-≈                  = -, -, rze , rze , a≈a′
rec-helper′ a≈a′ r≈r′ ρ≈ρ′ (su-≈ b≈b′)
  with rec-helper′ a≈a′ r≈r′ ρ≈ρ′ b≈b′
...  | z , z′ , ↘z , ↘z′ , z≈z′                  = ⟦s⟧ , ⟦t⟧ , rsu ↘z ↘⟦s⟧ , rsu ↘z′ ↘⟦t⟧ , s≈t
  where open IntpId (⊨-inst-id r≈r′ (ctx-ext (ctx-ext ρ≈ρ′ b≈b′) z≈z′))
rec-helper′ {_} {_} {T} a≈a′ r≈r′ ρ≈ρ′ (↑N e≈e′) = -, -, rec , rec , Bot⇒⟦⟧ T λ n →
  let w  , ↘w  , ↘w′ = ⟦⟧⇒Top T a≈a′ n
      ext : _ ↦ l′ N n ↦ l′ T (1 + n) ≈ _ ↦ l′ N n ↦ l′ T (1 + n) ∈ ⟦ T ∷ N ∷ _ ⟧
      ext = ctx-ext (ctx-ext ρ≈ρ′ (Bot⇒⟦⟧ N (l∈Bot n))) (Bot⇒⟦⟧ T (l∈Bot (1 + n)))
      r = ⊨-inst-id r≈r′ ext
      module r = IntpId r
      w′ , ↘w″ , ↘w‴ = ⟦⟧⇒Top T r.s≈t (2 + n)
      u  , ↘u  , ↘u′ = e≈e′ n
  in rec T w w′ u , Rr n ↘w r.↘⟦s⟧ ↘w″ ↘u , Rr n ↘w′ r.↘⟦t⟧ ↘w‴ ↘u′

rec-cong′ : Γ ⊨ s ≈ s′ ∶ T →
            T ∷ N ∷ Γ ⊨ r ≈ r′ ∶ T →
            Γ ⊨ t ≈ t′ ∶ N →
            -------------------------------------
            Γ ⊨ rec T s r t ≈ rec T s′ r′ t′ ∶ T
rec-cong′ {_} {_} {_} {T} s≈s′ r≈r′ t≈t′ σ≈σ′ ρ≈ρ′ =
  let _ , _ , ↘z , ↘z′ , z≈z′ = rec-helper s.s≈s′ (≈⇒⊨ r≈r′) σ≈σ′ ρ≈ρ′ σ.↘⟦σ⟧ (⟦⟧-refls σ.σ≈τ) t.s≈s′
      _ , _ , ↘z₁ , ↘z₂ , z₁≈ = rec-helper s.t≈t′ (≈⇒⊨ (≈-sym′ r≈r′)) (⊨s-sym σ≈σ′) (⟦⟧-syms ρ≈ρ′) σ.↘⟦τ⟧ (⟦⟧-refls′ σ.σ≈τ) t.t≈t′
      _ , _ , ↘z₃ , ↘z₄ , z₃≈ = rec-helper′ s.s′≈t′ r≈r′ σ.σ≈τ t.s′≈t′
      eq₅ = rec-det ↘z₃ ↘z′
      eq₆ = rec-det ↘z₄ ↘z₂
  in record
  { ↘⟦s⟧  = ⟦rec⟧ s.↘⟦s⟧ t.↘⟦s⟧ ↘z
  ; ↘⟦σ⟧  = σ.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦rec⟧ (subst (⟦ _ ⟧_↘ s.⟦s⟧′) (fext eq₁) s.↘⟦s⟧′) (subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext eq₂) t.↘⟦s⟧′) ↘z′
  ; ↘⟦t⟧  = ⟦rec⟧ s.↘⟦t⟧ t.↘⟦t⟧ ↘z₁
  ; ↘⟦τ⟧  = σ.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦rec⟧ (subst (⟦ _ ⟧_↘ s.⟦t⟧′) (fext eq₃) s.↘⟦t⟧′) (subst (⟦ _ ⟧_↘ t.⟦t⟧′) (fext eq₄) t.↘⟦t⟧′) ↘z₂
  ; s≈s′  = z≈z′
  ; s≈t   = ⟦⟧-trans T z≈z′
            (⟦⟧-trans T (subst₂ ⟦ T ⟧T eq₅ eq₆ z₃≈)
              (⟦⟧-sym T z₁≈))
  ; t≈t′  = z₁≈
  }
  where module s = Intp (s≈s′ σ≈σ′ ρ≈ρ′)
        module t = Intp (t≈t′ σ≈σ′ ρ≈ρ′)
        module σ = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        eq₁ = ⟦⟧s-det s.↘⟦σ⟧ σ.↘⟦σ⟧
        eq₂ = ⟦⟧s-det t.↘⟦σ⟧ σ.↘⟦σ⟧
        eq₃ = ⟦⟧s-det s.↘⟦τ⟧ σ.↘⟦τ⟧
        eq₄ = ⟦⟧s-det t.↘⟦τ⟧ σ.↘⟦τ⟧

rec-β-ze′ : Γ ⊨ s ∶ T →
            T ∷ N ∷ Γ ⊨ r ∶ T →
            -----------------------------
            Γ ⊨ rec T s r ze     ≈ s ∶ T
rec-β-ze′ ⊨s ⊨r σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = ⟦rec⟧ s.↘⟦s⟧ ⟦ze⟧ rze
  ; ↘⟦σ⟧  = s.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦rec⟧ s.↘⟦s⟧′ ⟦ze⟧ rze
  ; ↘⟦t⟧  = s.↘⟦t⟧
  ; ↘⟦τ⟧  = s.↘⟦τ⟧
  ; ↘⟦t⟧′ = s.↘⟦t⟧′
  ; s≈s′  = s.s≈s′
  ; s≈t   = s.s≈t
  ; t≈t′  = s.t≈t′
  }
  where module s = Intp (⊨s σ≈σ′ ρ≈ρ′)


rec-β-su′ : Γ ⊨ s ∶ T →
            T ∷ N ∷ Γ ⊨ r ∶ T →
            Γ ⊨ t ∶ N →
            --------------------------------------------------
            Γ ⊨ rec T s r (su t) ≈ r [ id ↦ t ↦ rec T s r t ] ∶ T
rec-β-su′ {Γ} {s} {T} {r} {t} ⊨s ⊨r ⊨t {_} {σ} {σ′} {ρ} {ρ′} σ≈σ′ ρ≈ρ′ =
  record
  { ↘⟦s⟧  = ⟦rec⟧ s.↘⟦s⟧ (⟦su⟧ t.↘⟦s⟧) (rsu ↘z r.↘⟦s⟧)
  ; ↘⟦σ⟧  = σ.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦rec⟧ (subst (⟦ _ ⟧_↘ s.⟦s⟧′) (fext eq₁) s.↘⟦s⟧′) (⟦su⟧ (subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext eq₂) t.↘⟦s⟧′)) (rsu ↘z′ r′.↘⟦t⟧)
  ; ↘⟦t⟧  = ↘⟦t⟧
  ; ↘⟦τ⟧  = σ.↘⟦τ⟧
  ; ↘⟦t⟧′ = r-idtr.↘⟦t⟧
  ; s≈s′  = s≈s′
  ; s≈t   = ⟦⟧-trans T s≈s′ (⟦⟧-trans T s′≈t₁ (⟦⟧-sym T r-σtr.t≈t′))
  ; t≈t′  = t≈t′
  }
  where module s = Intp (⊨s σ≈σ′ ρ≈ρ′)
        module t = Intp (⊨t σ≈σ′ ρ≈ρ′)
        module σ = IntpsId (⊨s-inst-id σ≈σ′ ρ≈ρ′)
        rc = rec-cong′ ⊨s ⊨r ⊨t
        module rc = Intp (rc σ≈σ′ ρ≈ρ′)
        eq₁ = ⟦⟧s-det s.↘⟦σ⟧ σ.↘⟦σ⟧
        eq₂ = ⟦⟧s-det t.↘⟦σ⟧ σ.↘⟦σ⟧

        tup = rec-helper s.s≈s′ ⊨r σ≈σ′ ρ≈ρ′ σ.↘⟦σ⟧ (⟦⟧-refls σ.σ≈τ) t.s≈s′
        z = proj₁ tup
        z′ = proj₁ (proj₂ tup)
        ↘z = proj₁ (proj₂ (proj₂ tup))
        ↘z′ = proj₁ (proj₂ (proj₂ (proj₂ tup)))
        z≈z′ = proj₂ (proj₂ (proj₂ (proj₂ tup)))

        qqσ = ⊨s-q T (⊨s-q N (⊨s-refl σ≈σ′))
        ext : ρ ↦ _ ↦ _ ≈ ρ′ ↦ _ ↦ _ ∈ ⟦ T ∷ N ∷ _ ⟧
        ext = ctx-ext (ctx-ext ρ≈ρ′ t.s≈s′) z≈z′
        module r = Intp (⊨r qqσ ext)
        eq₃ = qq-subst-equiv N T σ≈σ′ ρ≈ρ′ σ.↘⟦σ⟧ t.s≈s′ z≈z′ r.↘⟦σ⟧
        eq₄ = ⟦⟧-transs eq₃ (ctx-ext (ctx-ext (⟦⟧-refls σ.σ≈τ) t.s≈s′) z≈z′)
        module r′ = IntpId (⊨-inst-id ⊨r eq₄)
        s≈s′ = ⟦⟧-trans T r.s≈s′ (subst (λ x → ⟦ T ⟧T x r′.⟦t⟧) (⟦⟧-det r′.↘⟦s⟧ r.↘⟦s⟧′) r′.s≈t)

        σtr = ⊨ext-subst₂ σ≈σ′ ⊨t rc
        module σtr   = IntpsId (⊨s-inst-id σtr ρ≈ρ′)
        module r-σtr = Intp (⊨r σtr ρ≈ρ′)
        idtr = ⊨ext (⊨ext ⊨id ⊨t) rc
        σ≈τ : σ.⟦σ⟧ ≈ σ.⟦τ⟧ ∈ ⟦ Γ ⟧
        σ≈τ = σ.σ≈τ
        module idtr = IntpsId (⊨s-inst-id idtr σ≈τ)
        module r-idtr = Intp (⊨r idtr σ≈τ)

        ↘⟦t⟧ : ⟦ r [ id ↦ t ↦ rec T s r t ] [ σ′ ] ⟧ ρ′ ↘ r-σtr.⟦t⟧
        ↘⟦t⟧ = subst (⟦_⟧ ρ′ ↘ r-σtr.⟦t⟧)
                     (sym (subst-ext-app₂ r t (rec T s r t) v σ′))
                     r-σtr.↘⟦t⟧

        ⟦σtr⟧↘ : ⟦ σ′ ↦ (t [ σ′ ]) ↦ (rec T s r t [ σ′ ]) ⟧s ρ′ ↘ σ.⟦τ⟧ ↦ t.⟦t⟧ ↦ rc.⟦t⟧
        ⟦σtr⟧↘ = ⟦⟧s-ext (⟦⟧s-ext σ.↘⟦τ⟧ t.↘⟦t⟧) rc.↘⟦t⟧
        eq₅ : r-σtr.⟦τ⟧ ≗ σ.⟦τ⟧ ↦ t.⟦t⟧ ↦ rc.⟦t⟧
        eq₅ = ⟦⟧s-det r-σtr.↘⟦τ⟧ ⟦σtr⟧↘
        eq₆ = ⟦⟧s-det t.↘⟦τ⟧ σ.↘⟦τ⟧
        eq₇ = ⟦⟧s-det rc.↘⟦τ⟧ σ.↘⟦τ⟧
        ⟦idtr⟧↘ : ⟦ id ↦ t ↦ rec T s r t ⟧s σ.⟦τ⟧ ↘ σ.⟦τ⟧ ↦ t.⟦t⟧′ ↦ rc.⟦t⟧′
        ⟦idtr⟧↘ = ⟦⟧s-ext (⟦⟧s-ext ⟦⟧s-id (subst (⟦ t ⟧_↘ t.⟦t⟧′) (fext eq₆) t.↘⟦t⟧′)) (subst (⟦ _ ⟧_↘ rc.⟦t⟧′) (fext eq₇) rc.↘⟦t⟧′)
        eq₈ : r-idtr.⟦τ⟧ ≗ σ.⟦τ⟧ ↦ t.⟦t⟧′ ↦ rc.⟦t⟧′
        eq₈ = ⟦⟧s-det r-idtr.↘⟦τ⟧ ⟦idtr⟧↘

        ev : ⟦ r ⟧ σ.⟦τ⟧ ↦ t.⟦t⟧ ↦ rc.⟦t⟧ ↘ r-σtr.⟦t⟧′
        ev = subst (⟦ _ ⟧_↘ r-σtr.⟦t⟧′) (fext eq₅) r-σtr.↘⟦t⟧′

        t≈t′ : r-σtr.⟦t⟧ ≈ r-idtr.⟦t⟧ ∈ ⟦ T ⟧T
        t≈t′ = ⟦⟧-trans T r-σtr.t≈t′
               (⟦⟧-trans T (subst₂ ⟦ T ⟧T (⟦⟧-det rr.↘⟦s⟧ ev) (⟦⟧-det rr.↘⟦t⟧ ev′) rr.s≈t)
                           (⟦⟧-sym T r-idtr.t≈t′))
          where ev′ : ⟦ r ⟧ σ.⟦τ⟧ ↦ t.⟦t⟧′ ↦ rc.⟦t⟧′ ↘ r-idtr.⟦t⟧′
                ev′ = subst (⟦ _ ⟧_↘ r-idtr.⟦t⟧′) (fext eq₈) r-idtr.↘⟦t⟧′
                equiv : σ.⟦τ⟧ ↦ t.⟦t⟧ ↦ rc.⟦t⟧ ≈ σ.⟦τ⟧ ↦ t.⟦t⟧′ ↦ rc.⟦t⟧′ ∈ ⟦ T ∷ N ∷ Γ ⟧
                equiv = ctx-ext (ctx-ext (⟦⟧-refls′ σ.σ≈τ) t.t≈t′) rc.t≈t′
                module rr = IntpId (⊨-inst-id ⊨r equiv)

        eq₉ : rc.⟦s⟧′ ≡ z′
        eq₉
          with rc.↘⟦s⟧′
        ...  | ⟦rec⟧ s↘ t↘ r↘
             rewrite ⟦⟧-det s↘ (subst (⟦ s ⟧_↘ s.⟦s⟧′) (fext eq₁) s.↘⟦s⟧′)
                   | ⟦⟧-det t↘ (subst (⟦ t ⟧_↘ t.⟦s⟧′) (fext eq₂) t.↘⟦s⟧′) = rec-det r↘ ↘z′

        s′≈t₁ : r′.⟦t⟧ ≈ r-σtr.⟦t⟧′ ∈ ⟦ T ⟧T
        s′≈t₁ = subst₂ ⟦ T ⟧T (⟦⟧-det rr.↘⟦s⟧ r′.↘⟦t⟧) (⟦⟧-det rr.↘⟦t⟧ ev) rr.s≈t
          where equiv : σ.⟦σ⟧ ↦ t.⟦s⟧′ ↦ z′ ≈ σ.⟦τ⟧ ↦ t.⟦t⟧ ↦ rc.⟦t⟧ ∈ ⟦ T ∷ N ∷ Γ ⟧
                equiv = ctx-ext (ctx-ext σ.σ≈τ (⟦⟧-sym N t.t≈s′)) (⟦⟧-sym T (subst (⟦ T ⟧T _) eq₉ rc.t≈s′))
                module rr = IntpId (⊨-inst-id ⊨r equiv)


Initial-refl : ∀ Γ → InitialEnv Γ ≈ InitialEnv Γ ∈ ⟦ Γ ⟧
Initial-refl (T ∷ Γ)  here        = Bot⇒⟦⟧ T (l∈Bot (L.length Γ))
Initial-refl .(_ ∷ _) (there T∈Γ) = Initial-refl _ T∈Γ

record Completeness′ n s ρ t ρ′ T : Set where
  field
    nf  : Nf
    nbs : Nbe n ρ s T nf
    nbt : Nbe n ρ′ t T nf

Completeness : ℕ → Env → Exp → Exp → Typ → Set
Completeness n ρ s t T = Completeness′ n s ρ t ρ T

⊨-conseq : Γ ⊨ s ≈ t ∶ T → ∀ n → ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → Completeness′ n s ρ t ρ′ T
⊨-conseq {T = T} s≈ n ρ≈ =
  let (w , ↘w , ↘w′) = TTop T s≈t n in
  record
  { nf  = w
  ; nbs = record
    { ⟦t⟧  = ⟦s⟧
    ; ↘⟦t⟧ = ↘⟦s⟧
    ; ↓⟦t⟧ = ↘w
    }
  ; nbt = record
    { ⟦t⟧  = ⟦t⟧
    ; ↘⟦t⟧ = ↘⟦t⟧
    ; ↓⟦t⟧ = ↘w′
    }
  }
  where open IntpId (⊨-inst-id s≈ ρ≈)
        TTop : ∀ T → ⟦ T ⟧T a b → Top (↓ T a) (↓ T b)
        TTop T aTb = ⟦⟧⇒Top T aTb

sem-sound : Γ ⊢ t ∶ T → Γ ⊨ t ∶ T
sem-sound (vlookup T∈Γ) = v-≈′ T∈Γ
sem-sound ze-I          = ze-≈′
sem-sound (su-I t)      = su-cong′ (sem-sound t)
sem-sound (N-E s r t)   = rec-cong′ (sem-sound s) (sem-sound r) (sem-sound t)
sem-sound (Λ-I t)       = Λ-cong′ (sem-sound t)
sem-sound (Λ-E t s)     = $-cong′ (sem-sound t) (sem-sound s)

completeness₀ : Γ ⊢ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) t t T
completeness₀ {Γ} t = ⊨-conseq (sem-sound t) (L.length Γ) (Initial-refl Γ)

nbe-comp : Γ ⊢ t ∶ T → ∃ λ w → Nbe (L.length Γ) (InitialEnv Γ) t T w
nbe-comp t = nf , nbs
  where open Completeness′ (completeness₀ t)

≈sem-sound : Γ ⊢ s ≈ t ∶ T → Γ ⊨ s ≈ t ∶ T
≈sem-sound (v-≈ T∈Γ)                 = v-≈′ T∈Γ
≈sem-sound ze-≈                      = ze-≈′
≈sem-sound (su-cong s≈t)             = su-cong′ (≈sem-sound s≈t)
≈sem-sound (rec-cong s≈s′ r≈r′ t≈t′) = rec-cong′ (≈sem-sound s≈s′) (≈sem-sound r≈r′) (≈sem-sound t≈t′)
≈sem-sound (Λ-cong s≈t)              = Λ-cong′ (≈sem-sound s≈t)
≈sem-sound ($-cong t≈t′ s≈s′)        = $-cong′ (≈sem-sound t≈t′) (≈sem-sound s≈s′)
≈sem-sound (rec-β-ze s r)            = rec-β-ze′ (sem-sound s) (sem-sound r)
≈sem-sound (rec-β-su s r t)          = rec-β-su′ (sem-sound s) (sem-sound r) (sem-sound t)
≈sem-sound (Λ-β t s)                 = Λ-β′ (sem-sound t) (sem-sound s)
≈sem-sound (Λ-η t)                   = Λ-η′ (sem-sound t)
≈sem-sound (≈-sym s≈t)               = ≈-sym′ (≈sem-sound s≈t)
≈sem-sound (≈-trans s≈t t≈t′)        = ≈-trans′ (≈sem-sound s≈t) (≈sem-sound t≈t′)

completeness : Γ ⊢ s ≈ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) s t T
completeness {Γ} s≈t = ⊨-conseq (≈sem-sound s≈t) (L.length Γ) (Initial-refl Γ)
