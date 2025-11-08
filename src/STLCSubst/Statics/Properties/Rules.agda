{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Properties.Rules where

open import Relation.Binary using (PartialSetoid)
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib
open import STLCSubst.Statics.Definitions
open import STLCSubst.Statics.Rules
open import STLCSubst.Statics.Properties.Ops

⊢wk-q : ∀ T → Γ ⊢w ϕ ∶ Δ → T ∷ Γ ⊢w q ϕ ∶ T ∷ Δ
⊢wk-q T ⊢ϕ here        = here
⊢wk-q T ⊢ϕ (there S∈Δ) = there (⊢ϕ S∈Δ)

⊢⇑ : T ∷ Γ ⊢w ⇑ ∶ Γ
⊢⇑ S∈Γ = there S∈Γ

⊢wk-∙ : Γ ⊢w ϕ ∶ Γ′ → Γ′ ⊢w ψ ∶ Γ″ → Γ ⊢w ψ ∙ ϕ ∶ Γ″
⊢wk-∙ ⊢ϕ ⊢ψ T∈Γ″ = ⊢ϕ (⊢ψ T∈Γ″)

⊢wk-app : Δ ⊢ t ∶ T → Γ ⊢w ϕ ∶ Δ → Γ ⊢ t [ ϕ ] ∶ T
⊢wk-app (vlookup T∈Δ) ⊢ϕ  = vlookup (⊢ϕ T∈Δ)
⊢wk-app ze-I ⊢ϕ           = ze-I
⊢wk-app (su-I ⊢t) ⊢ϕ      = su-I (⊢wk-app ⊢t ⊢ϕ)
⊢wk-app (N-E ⊢s ⊢r ⊢t) ⊢ϕ = N-E (⊢wk-app ⊢s ⊢ϕ) (⊢wk-app ⊢r (⊢wk-q _ (⊢wk-q N ⊢ϕ))) (⊢wk-app ⊢t ⊢ϕ)
⊢wk-app (Λ-I ⊢t) ⊢ϕ       = Λ-I (⊢wk-app ⊢t (⊢wk-q _ ⊢ϕ))
⊢wk-app (Λ-E ⊢t ⊢s) ⊢ϕ   = Λ-E (⊢wk-app ⊢t ⊢ϕ) (⊢wk-app ⊢s ⊢ϕ)

⊢id : Γ ⊢s id ∶ Γ
⊢id = vlookup

⊢wk-subst : Δ ⊢s σ ∶ Δ′ → Γ ⊢w ϕ ∶ Δ → Γ ⊢s σ [ ϕ ] ∶ Δ′
⊢wk-subst ⊢σ ⊢ϕ T∈Δ′ = ⊢wk-app (⊢σ T∈Δ′) ⊢ϕ

⊢ext : Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶ T → Γ ⊢s σ ↦ t ∶ T ∷ Δ
⊢ext ⊢σ ⊢t here        = ⊢t
⊢ext ⊢σ ⊢t (there S∈Δ) = ⊢σ S∈Δ

⊢subst-q : ∀ T → Γ ⊢s σ ∶ Δ → T ∷ Γ ⊢s q σ ∶ T ∷ Δ
⊢subst-q T ⊢σ here        = vlookup here
⊢subst-q T ⊢σ (there S∈Δ) = ⊢wk-app (⊢σ S∈Δ) ⊢⇑

⊢subst-app : Δ ⊢ t ∶ T → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ∶ T
⊢subst-app (vlookup T∈Δ) ⊢σ  = ⊢σ T∈Δ
⊢subst-app ze-I ⊢σ           = ze-I
⊢subst-app (su-I ⊢t) ⊢σ      = su-I (⊢subst-app ⊢t ⊢σ)
⊢subst-app (N-E ⊢s ⊢r ⊢t) ⊢σ = N-E (⊢subst-app ⊢s ⊢σ) (⊢subst-app ⊢r (⊢subst-q _ (⊢subst-q _ ⊢σ))) (⊢subst-app ⊢t ⊢σ)
⊢subst-app (Λ-I ⊢t) ⊢σ       = Λ-I (⊢subst-app ⊢t (⊢subst-q _ ⊢σ))
⊢subst-app (Λ-E ⊢t ⊢s) ⊢σ    = Λ-E (⊢subst-app ⊢t ⊢σ) (⊢subst-app ⊢s ⊢σ)

⊢subst-∙ : Γ ⊢s τ ∶ Γ′ → Γ′ ⊢s σ ∶ Γ″ → Γ ⊢s σ ∙ τ ∶ Γ″
⊢subst-∙ ⊢τ ⊢σ T∈Γ″ = ⊢subst-app (⊢σ T∈Γ″) ⊢τ

⊢subst-sym : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢s σ′ ≈ σ ∶ Δ
⊢subst-sym eq T∈Δ = ≈-sym (eq T∈Δ)

⊢subst-trans : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢s σ′ ≈ σ″ ∶ Δ → Γ ⊢s σ ≈ σ″ ∶ Δ
⊢subst-trans eq eq′ T∈Δ = ≈-trans (eq T∈Δ) (eq′ T∈Δ)

⊢PartialSetoid : Ctx → Typ → PartialSetoid _ _
⊢PartialSetoid Γ T = record
  { Carrier              = Exp
  ; _≈_                  = λ t t′ → Γ ⊢ t ≈ t′ ∶ T
  ; isPartialEquivalence = record
    { sym   = ≈-sym
    ; trans = ≈-trans
    }
  }

module TR {Γ T} = PS (⊢PartialSetoid Γ T)

⊢sPartialSetoid : Ctx → Ctx → PartialSetoid _ _
⊢sPartialSetoid Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = λ t t′ → Γ ⊢s t ≈ t′ ∶ Δ
  ; isPartialEquivalence = record
    { sym   = ⊢subst-sym
    ; trans = ⊢subst-trans
    }
  }

module TRS {Γ Δ} = PS (⊢sPartialSetoid Γ Δ)

≈⇒⊢-gen : Γ ⊢ t ≈ t′ ∶ T →
          ----------------------
          Γ ⊢ t ∶ T × Γ ⊢ t′ ∶ T
≈⇒⊢-gen (v-≈ T∈Γ)           = vlookup T∈Γ , vlookup T∈Γ
≈⇒⊢-gen ze-≈                = ze-I , ze-I
≈⇒⊢-gen (su-cong t≈)        = su-I (≈⇒⊢-gen t≈ .proj₁) , su-I (≈⇒⊢-gen t≈ .proj₂)
≈⇒⊢-gen (rec-cong s≈ r≈ t≈) = N-E (≈⇒⊢-gen s≈ .proj₁) (≈⇒⊢-gen r≈ .proj₁) (≈⇒⊢-gen t≈ .proj₁)
                            , N-E (≈⇒⊢-gen s≈ .proj₂) (≈⇒⊢-gen r≈ .proj₂) (≈⇒⊢-gen t≈ .proj₂)
≈⇒⊢-gen (Λ-cong t≈)         = Λ-I (≈⇒⊢-gen t≈ .proj₁) , Λ-I (≈⇒⊢-gen t≈ .proj₂)
≈⇒⊢-gen ($-cong t≈ s≈)      = Λ-E (≈⇒⊢-gen t≈ .proj₁) (≈⇒⊢-gen s≈ .proj₁)
                            , Λ-E (≈⇒⊢-gen t≈ .proj₂) (≈⇒⊢-gen s≈ .proj₂)
≈⇒⊢-gen (rec-β-ze ⊢s ⊢r)    = N-E ⊢s ⊢r ze-I , ⊢s
≈⇒⊢-gen (rec-β-su ⊢s ⊢r ⊢t) = (N-E ⊢s ⊢r (su-I ⊢t))
                            , ⊢subst-app ⊢r (⊢ext (⊢ext ⊢id ⊢t) (N-E ⊢s ⊢r ⊢t))
≈⇒⊢-gen (Λ-β ⊢t ⊢s)         = Λ-E (Λ-I ⊢t) ⊢s , ⊢subst-app ⊢t (⊢ext ⊢id ⊢s)
≈⇒⊢-gen (Λ-η ⊢t)            = ⊢t , Λ-I (Λ-E (⊢wk-app ⊢t ⊢⇑) (vlookup here))
≈⇒⊢-gen (≈-sym t≈)          = ≈⇒⊢-gen t≈ .proj₂ , ≈⇒⊢-gen t≈ .proj₁
≈⇒⊢-gen (≈-trans t≈ t≈′)    = ≈⇒⊢-gen t≈ .proj₁ , ≈⇒⊢-gen t≈′ .proj₂


≈⇒⊢ : Γ ⊢ t ≈ t′ ∶ T →
      ------------------
      Γ ⊢ t ∶ T
≈⇒⊢ t≈ with ≈⇒⊢-gen t≈
... | t , _ = t

≈⇒⊢′ : Γ ⊢ t ≈ t′ ∶ T →
       ------------------
       Γ ⊢ t′ ∶ T
≈⇒⊢′ t≈ with ≈⇒⊢-gen t≈
... | _ , t = t


≈⇒⊢s-gen : Γ ⊢s σ ≈ σ′ ∶ Δ →
           -------------------------
           Γ ⊢s σ ∶ Δ × Γ ⊢s σ′ ∶ Δ
≈⇒⊢s-gen {Γ} {σ} {σ′} {Δ} σ≈ = (λ T∈Δ → lem T∈Δ .proj₁) , λ T∈Δ → lem T∈Δ .proj₂
  where lem : ∀ {x} → x ∶ T ∈ Δ → Γ ⊢ σ x ∶ T × Γ ⊢ σ′ x ∶ T
        lem T∈Δ = ≈⇒⊢-gen (σ≈ T∈Δ)

ext-∙ : Γ ⊢s σ ∶ Γ′ →
        Γ′ ⊢s σ′ ∶ Γ″ →
        Γ′ ⊢ t ∶ T →
        ----------------------------------------------
        Γ ⊢s (σ′ ↦ t) ∙ σ ≈ (σ′ ∙ σ) ↦ (t [ σ ]) ∶ T ∷ Γ″
ext-∙ ⊢σ ⊢σ′ ⊢t here         = ≈-refl (⊢subst-app ⊢t ⊢σ)
ext-∙ ⊢σ ⊢σ′ ⊢t (there S∈Γ″) = ≈-refl (⊢subst-app (⊢σ′ S∈Γ″) ⊢σ)

≗-⊢s≈ : Γ ⊢s σ ∶ Δ → σ ≗ σ′ → Γ ⊢s σ ≈ σ′ ∶ Δ
≗-⊢s≈ ⊢σ eq {x} T∈Δ
  rewrite sym (eq x) = ⊢subst-refl ⊢σ T∈Δ

⊢s≈-transp : Γ ⊢s σ ≈ σ′ ∶ Δ → σ′ ≗ τ → Γ ⊢s σ ≈ τ ∶ Δ
⊢s≈-transp σ≈ eq
  with ≈⇒⊢s-gen σ≈
...  | _ , ⊢σ′ = ⊢subst-trans σ≈ (≗-⊢s≈ ⊢σ′ eq)


q-∙ : ∀ T →
      Γ ⊢s τ ∶ Γ′ →
      Γ′ ⊢s σ ∶ Γ″ →
      -----------------------------
      T ∷ Γ ⊢s q σ ∙ q τ ≈ q (σ ∙ τ) ∶ T ∷ Γ″
q-∙ {_} {τ} {_} {σ} T ⊢τ ⊢σ = ⊢subst-sym (⊢s≈-transp (⊢subst-refl (⊢subst-q _ (⊢subst-∙ ⊢τ ⊢σ))) (≈.sym {A = Subst} (q-∙-dist σ τ)))
