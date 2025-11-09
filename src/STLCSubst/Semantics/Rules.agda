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

-- ≈⇒⊨ : Γ ⊨ t ≈ t′ ∶ T →
--       ------------------
--       Γ ⊨ t ∶ T
-- ≈⇒⊨ t≈ = ≈-trans t≈ (≈-sym t≈)

v-≈′ : ∀ {x} →
       x ∶ T ∈ Γ →
       ---------------
       Γ ⊨ v x ≈ v x ∶ T
v-≈′ {_} {_} {x} T∈Γ {_} {σ} {σ′} σ≈σ′ ρ≈ρ′ = record
  { ↘⟦s⟧  = subst (⟦_⟧ _ ↘ _) (eq x) (app.↘⟦σ⟧ x)
  ; ↘⟦σ⟧  = ⟦⟧s-transp _ eq app.↘⟦σ⟧
  ; ↘⟦s⟧′ = ⟦v⟧ x
  ; ↘⟦t⟧  = subst (⟦_⟧ _ ↘ _) (eq′ x) (app.↘⟦τ⟧ x)
  ; ↘⟦τ⟧  = ⟦⟧s-transp _ eq′ app.↘⟦τ⟧
  ; ↘⟦t⟧′ = ⟦v⟧ x
  ; s≈s′  = ⟦⟧-refls app.σ≈σ′ T∈Γ
  ; s≈t   = app.σ≈τ T∈Γ
  ; t≈t′  = ⟦⟧-refls app.τ≈τ′ T∈Γ
  }
  where module app = Intps (σ≈σ′ ⊢w-id ρ≈ρ′)
        eq : σ [ id ] ≗ σ
        eq  = subst-wk-id σ
        eq′ : σ′ [ id ] ≗ σ′
        eq′ = subst-wk-id σ′

-- ze-≈′ : Γ ⊨ ze ≈ ze ∶ N
-- ze-≈′ ρ≈ = record
--   { ⟦s⟧ = ze
--   ; ⟦t⟧ = ze
--   ; ↘⟦s⟧ = ⟦ze⟧
--   ; ↘⟦t⟧ = ⟦ze⟧
--   ; s≈t = ze-≈
--   }

-- su-cong : Γ ⊨ t ≈ t′ ∶ N →
--           ---------------------
--           Γ ⊨ su t ≈ su t′ ∶ N
-- su-cong t≈ ρ≈ = record
--   { ⟦s⟧  = su ⟦s⟧
--   ; ⟦t⟧  = su ⟦t⟧
--   ; ↘⟦s⟧ = ⟦su⟧ ↘⟦s⟧
--   ; ↘⟦t⟧ = ⟦su⟧ ↘⟦t⟧
--   ; s≈t  = su-≈ s≈t
--   }
--   where open Intp (t≈ ρ≈)

-- Λ-cong : S ∷ Γ ⊨ t ≈ t′ ∶ T →
--          ----------------------
--          Γ ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
-- Λ-cong {S} {Γ} {t} {t′} {T} t≈ {ρ} {ρ′} ρ≈ = record
--   { ⟦s⟧  = Λ _ _
--   ; ⟦t⟧  = Λ _ _
--   ; ↘⟦s⟧ = ⟦Λ⟧ _
--   ; ↘⟦t⟧ = ⟦Λ⟧ _
--   ; s≈t  = helper
--   }
--   where helper : (⟦ S ⟧T ⇒ ⟦ T ⟧T) (Λ t ρ) (Λ t′ ρ′)
--         helper aSa′ = ⟦s⟧
--                     - ⟦t⟧
--                     - Λ∙ ↘⟦s⟧
--                     - Λ∙ ↘⟦t⟧
--                     - s≈t
--           where open Intp (t≈ (ctx-ext ρ≈ aSa′))

-- $-cong : Γ ⊨ r ≈ r′ ∶ S ⟶ T →
--          Γ ⊨ s ≈ s′ ∶ S →
--          ------------------------
--          Γ ⊨ r $ s ≈ r′ $ s′ ∶ T
-- $-cong r≈ s≈ ρ≈ = record
--   { ⟦s⟧  = rs.fa
--   ; ⟦t⟧  = rs.fa′
--   ; ↘⟦s⟧ = ⟦$⟧ r.↘⟦s⟧ s.↘⟦s⟧ rs.↘fa
--   ; ↘⟦t⟧ = ⟦$⟧ r.↘⟦t⟧ s.↘⟦t⟧ rs.↘fa′
--   ; s≈t  = rs.fa≈fa′
--   }
--   where module r = Intp (r≈ ρ≈)
--         module s = Intp (s≈ ρ≈)
--         rs = r.s≈t s.s≈t
--         module rs = FAppIn rs
