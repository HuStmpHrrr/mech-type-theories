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

-- -- ze-≈′ : Γ ⊨ ze ≈ ze ∶ N
-- -- ze-≈′ ρ≈ = record
-- --   { ⟦s⟧ = ze
-- --   ; ⟦t⟧ = ze
-- --   ; ↘⟦s⟧ = ⟦ze⟧
-- --   ; ↘⟦t⟧ = ⟦ze⟧
-- --   ; s≈t = ze-≈
-- --   }

-- -- su-cong : Γ ⊨ t ≈ t′ ∶ N →
-- --           ---------------------
-- --           Γ ⊨ su t ≈ su t′ ∶ N
-- -- su-cong t≈t′ ρ≈ = record
-- --   { ⟦s⟧  = su ⟦s⟧
-- --   ; ⟦t⟧  = su ⟦t⟧
-- --   ; ↘⟦s⟧ = ⟦su⟧ ↘⟦s⟧
-- --   ; ↘⟦t⟧ = ⟦su⟧ ↘⟦t⟧
-- --   ; s≈t  = su-≈ s≈t
-- --   }
-- --   where open Intp (t≈t′ ρ≈)


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
        s≈s′ {a} {a′} a≈a′ = t.⟦s⟧ - t′.⟦s⟧ - (Λ∙ t.↘⟦s⟧) - (Λ∙ t′.↘⟦s⟧) - ⟦⟧-trans T t.s≈s′ (subst (_≈ t′.⟦s⟧ ∈ ⟦ T ⟧T) lem₆ (⟦⟧-sym T t′.s≈t))
          where ext : _ ≈ _ ∈ ⟦ S ∷ _ ⟧
                ext = ctx-ext ρ≈ρ′ a≈a′
                module t = Intp (t≈t′ (⊨s-q S σ≈σ′) ext)
                module app′ = Intps (σ≈σ′ ⊢⇑ ext)
                lem : ⟦ q-alt σ ⟧s ρ ↦ a ↘ t.⟦σ⟧
                lem              = ⟦⟧s-transp _ (subst-q-equiv σ) t.↘⟦σ⟧
                lem₁ : t.⟦σ⟧ ≗ app′.⟦σ⟧ ↦ a
                lem₁             = ⟦⟧s-det lem (λ { zero → ⟦v⟧ 0 ; (suc x) → app′.↘⟦σ⟧ x })
                lem₂ : app′.⟦σ⟧′ ≗ app.⟦σ⟧
                lem₂             = ⟦⟧s-det app′.↘⟦σ⟧′ app.↘⟦σ⟧
                lem₃ : app′.⟦σ⟧ ↦ a ≈ app.⟦σ⟧ ↦ a′ ∈ ⟦ S ∷ Γ ⟧
                lem₃ here        = a≈a′
                lem₃ (there T∈Γ) = ⟦⟧-transpʳ app′.σ≈σ′ lem₂ T∈Γ
                lem₄ : app.⟦σ⟧ ↦ a′ ≈ app′.⟦σ⟧ ↦ a ∈ ⟦ S ∷ Γ ⟧
                lem₄ = ⟦⟧-syms lem₃
                module t′ = IntpId (⊨-inst-id (≈⇒⊨ t≈t′) lem₄)
                lem₅ : ⟦ t ⟧ app′.⟦σ⟧ ↦ a ↘ t.⟦s⟧′
                lem₅ = subst (⟦ _ ⟧_↘ t.⟦s⟧′) (fext lem₁) t.↘⟦s⟧′
                lem₆ : t′.⟦t⟧ ≡ t.⟦s⟧′
                lem₆ = ⟦⟧-det t′.↘⟦t⟧ lem₅

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

-- -- Λ-cong {S} {Γ} {t} {t′} {T} t≈t′ {ρ} {ρ′} ρ≈ = record
-- --   { ⟦s⟧  = Λ _ _
-- --   ; ⟦t⟧  = Λ _ _
-- --   ; ↘⟦s⟧ = ⟦Λ⟧ _
-- --   ; ↘⟦t⟧ = ⟦Λ⟧ _
-- --   ; s≈t  = helper
-- --   }
-- --   where helper : (⟦ S ⟧T ⇒ ⟦ T ⟧T) (Λ t ρ) (Λ t′ ρ′)
-- --         helper aSa′ = ⟦s⟧
-- --                     - ⟦t⟧
-- --                     - Λ∙ ↘⟦s⟧
-- --                     - Λ∙ ↘⟦t⟧
-- --                     - s≈t
-- --           where open Intp (t≈t′ (ctx-ext ρ≈ aSa′))

-- -- $-cong : Γ ⊨ r ≈ r′ ∶ S ⟶ T →
-- --          Γ ⊨ s ≈ s′ ∶ S →
-- --          ------------------------
-- --          Γ ⊨ r $ s ≈ r′ $ s′ ∶ T
-- -- $-cong r≈ s≈ ρ≈ = record
-- --   { ⟦s⟧  = rs.fa
-- --   ; ⟦t⟧  = rs.fa′
-- --   ; ↘⟦s⟧ = ⟦$⟧ r.↘⟦s⟧ s.↘⟦s⟧ rs.↘fa
-- --   ; ↘⟦t⟧ = ⟦$⟧ r.↘⟦t⟧ s.↘⟦t⟧ rs.↘fa′
-- --   ; s≈t  = rs.fa≈fa′
-- --   }
-- --   where module r = Intp (r≈ ρ≈)
-- --         module s = Intp (s≈ ρ≈)
-- --         rs = r.s≈t s.s≈t
-- --         module rs = FAppIn rs
