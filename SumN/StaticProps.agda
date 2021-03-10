{-# OPTIONS --without-K --safe #-}

module SumN.StaticProps where

open import Lib
open import SumN.Statics
open import Relation.Binary using (PartialSetoid)
import Relation.Binary.Reasoning.PartialSetoid as PS

⊢PartialSetoid : Env → Typ → PartialSetoid _ _
⊢PartialSetoid Γ T = record
  { Carrier              = Exp
  ; _≈_                  = λ t t′ → Γ ⊢ t ≈ t′ ∶ T
  ; isPartialEquivalence = record
    { sym   = ≈-sym
    ; trans = ≈-trans
    }
  }

module PS′ {o ℓ} (P : PartialSetoid o ℓ) where
  open PS P public
  module P = PartialSetoid P
  open P

  step-≈-close : ∀ x y → x ≈ y → x IsRelatedTo y
  step-≈-close x y x∼y = relTo x∼y

  infix 4 step-≈-close

  syntax step-≈-close x y x≈y = x ≈!⟨ x≈y ⟩ y ∎

module TR {Γ T} = PS′ (⊢PartialSetoid Γ T)

⊢sPartialSetoid : Env → Env → PartialSetoid _ _
⊢sPartialSetoid Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = λ t t′ → Γ ⊢s t ≈ t′ ∶ Δ
  ; isPartialEquivalence = record
    { sym   = S-≈-sym
    ; trans = S-≈-trans
    }
  }

module TRS {Γ Δ} = PS′ (⊢sPartialSetoid Γ Δ)

mutual

  ≈⇒⊢-gen : Γ ⊢ t ≈ t′ ∶ T →
            ------------------------
            Γ ⊢ t ∶ T × Γ ⊢ t′ ∶ T
  ≈⇒⊢-gen (v-≈ T∈Γ)          = vlookup T∈Γ , vlookup T∈Γ
  ≈⇒⊢-gen ze-≈               = ze-I , ze-I
  ≈⇒⊢-gen (su-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = su-I t , su-I t′
  ≈⇒⊢-gen (pr-cong s≈ r≈)
    with ≈⇒⊢-gen s≈ | ≈⇒⊢-gen r≈
  ...  | s , s′     | r , r′ = X-I s r , X-I s′ r′
  ≈⇒⊢-gen (p₁-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = X-E₁ t , X-E₁ t′
  ≈⇒⊢-gen (p₂-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = X-E₂ t , X-E₂ t′
  ≈⇒⊢-gen (i₁-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = ∪-I₁ t , ∪-I₁ t′
  ≈⇒⊢-gen (i₂-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = ∪-I₂ t , ∪-I₂ t′
  ≈⇒⊢-gen (pm-cong t≈ s≈ r≈)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen s≈ | ≈⇒⊢-gen r≈
  ...  | t , t′
       | s , s′
       | r , r′              = ∪-E t s r , ∪-E t′ s′ r′
  ≈⇒⊢-gen (Λ-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = Λ-I t , Λ-I t′
  ≈⇒⊢-gen ($-cong t≈ s≈)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen s≈
  ...  | t , t′ | s , s′     = Λ-E t s , Λ-E t′ s′
  ≈⇒⊢-gen ([]-cong σ≈ t≈)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢-gen t≈
  ...  | σ , σ′ | t , t′     = t[σ] t σ , t[σ] t′ σ′
  ≈⇒⊢-gen (ze-[] σ)          = t[σ] ze-I σ , ze-I
  ≈⇒⊢-gen (su-[] σ t)        = t[σ] (su-I t) σ , su-I (t[σ] t σ)
  ≈⇒⊢-gen (pr-[] σ s r)      = t[σ] (X-I s r) σ , X-I (t[σ] s σ) (t[σ] r σ)
  ≈⇒⊢-gen (p₁-[] σ t)        = t[σ] (X-E₁ t) σ , X-E₁ (t[σ] t σ)
  ≈⇒⊢-gen (p₂-[] σ t)        = t[σ] (X-E₂ t) σ , X-E₂ (t[σ] t σ)
  ≈⇒⊢-gen (i₁-[] σ t)        = t[σ] (∪-I₁ t) σ , ∪-I₁ (t[σ] t σ)
  ≈⇒⊢-gen (i₂-[] σ t)        = t[σ] (∪-I₂ t) σ , ∪-I₂ (t[σ] t σ)
  ≈⇒⊢-gen (pm-[] σ t s r)    = t[σ] (∪-E t s r) σ , ∪-E (t[σ] t σ) (t[σ] s σ) (t[σ] r σ)
  ≈⇒⊢-gen (Λ-[] σ t)         = t[σ] (Λ-I t) σ , Λ-I (t[σ] t (S-, (S-∘ S-↑ σ) (vlookup here)))
  ≈⇒⊢-gen ($-[] σ r s)       = t[σ] (Λ-E r s) σ , Λ-E (t[σ] r σ) (t[σ] s σ)
  ≈⇒⊢-gen (X-β₁ s r)         = X-E₁ (X-I s r) , s
  ≈⇒⊢-gen (X-β₂ s r)         = X-E₂ (X-I s r) , r
  ≈⇒⊢-gen (X-η t)            = t , X-I (X-E₁ t) (X-E₂ t)
  ≈⇒⊢-gen (∪-β₁ t s r)       = ∪-E (∪-I₁ t) s r , Λ-E s t
  ≈⇒⊢-gen (∪-β₂ t s r)       = ∪-E (∪-I₂ t) s r , Λ-E r t
  ≈⇒⊢-gen (Λ-β t s)          = Λ-E (Λ-I t) s , t[σ] t (S-, S-I s)
  ≈⇒⊢-gen (Λ-η t)            = t , Λ-I (Λ-E (t[σ] t S-↑) (vlookup here))
  ≈⇒⊢-gen ([I] t)            = t[σ] t S-I , t
  ≈⇒⊢-gen (↑-lookup T∈Γ)     = t[σ] (vlookup T∈Γ) S-↑ , vlookup (there T∈Γ)
  ≈⇒⊢-gen ([∘] τ σ t)        = t[σ] t (S-∘ τ σ) , t[σ] (t[σ] t σ) τ
  ≈⇒⊢-gen ([,]-v-ze σ t)     = t[σ] (vlookup here) (S-, σ t) , t
  ≈⇒⊢-gen ([,]-v-su σ s T∈Δ) = t[σ] (vlookup (there T∈Δ)) (S-, σ s) , t[σ] (vlookup T∈Δ) σ
  ≈⇒⊢-gen (≈-sym t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′              = t′ , t
  ≈⇒⊢-gen (≈-trans t≈ t≈′)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen t≈′
  ...  | t , _ | _ , t′      = t , t′

  ≈⇒⊢s-gen : Γ ⊢s σ ≈ σ′ ∶ Δ →
             -------------------------
             Γ ⊢s σ ∶ Δ × Γ ⊢s σ′ ∶ Δ
  ≈⇒⊢s-gen ↑-≈               = S-↑ , S-↑
  ≈⇒⊢s-gen I-≈               = S-I , S-I
  ≈⇒⊢s-gen (∘-cong σ≈ τ≈)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢s-gen τ≈
  ...  | σ , σ′ | τ , τ′     = S-∘ σ τ , S-∘ σ′ τ′
  ≈⇒⊢s-gen (,-cong σ≈ t≈)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢-gen t≈
  ...  | σ , σ′ | t , t′     = S-, σ t , S-, σ′ t′
  ≈⇒⊢s-gen (↑-∘-, σ s)       = S-∘ (S-, σ s) S-↑ , σ
  ≈⇒⊢s-gen (I-∘ σ)           = S-∘ σ S-I , σ
  ≈⇒⊢s-gen (∘-I σ)           = S-∘ S-I σ , σ
  ≈⇒⊢s-gen (∘-assoc σ σ′ σ″) = S-∘ σ″ (S-∘ σ′ σ) , S-∘ (S-∘ σ″ σ′) σ
  ≈⇒⊢s-gen (,-ext σ)         = σ , S-, (S-∘ σ S-↑) (t[σ] (vlookup here) σ)
  ≈⇒⊢s-gen (S-≈-sym σ≈)
    with ≈⇒⊢s-gen σ≈
  ...  | σ , σ′              = σ′ , σ
  ≈⇒⊢s-gen (S-≈-trans σ≈ σ≈′)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢s-gen σ≈′
  ...  | σ , _ | _ , σ′      = σ , σ′

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

q⇒⊢s : ∀ T → Γ ⊢s σ ∶ Δ → T ∷ Γ ⊢s q σ ∶ T ∷ Δ
q⇒⊢s T σ = S-, (S-∘ S-↑ σ) (vlookup here)

,-∘ : Γ ⊢s σ ∶ Γ′ →
      Γ′ ⊢s σ′ ∶ Γ″ →
      Γ′ ⊢ t ∶ T →
      ----------------------------------------------
      Γ ⊢s (σ′ , t) ∘ σ ≈ (σ′ ∘ σ) , t [ σ ] ∶ T ∷ Γ″
,-∘ {_} {σ} {_} {σ′} {_} {t} ⊢σ ⊢σ′ ⊢t = begin
  (σ′ , t) ∘ σ                                  ≈⟨ ,-ext (S-∘ ⊢σ (S-, ⊢σ′ ⊢t)) ⟩
  (↑ ∘ ((σ′ , t) ∘ σ)) , (v 0 [ (σ′ , t) ∘ σ ]) ≈⟨ ,-cong (S-≈-sym (∘-assoc S-↑ (S-, ⊢σ′ ⊢t) ⊢σ))
                                                          ([∘] ⊢σ (S-, ⊢σ′ ⊢t) (vlookup here)) ⟩
  ((↑ ∘ (σ′ , t) ∘ σ) , v 0 [ σ′ , t ] [ σ ])   ≈!⟨ ,-cong (∘-cong (S-≈-refl ⊢σ) (↑-∘-, ⊢σ′ ⊢t))
                                                          ([]-cong (S-≈-refl ⊢σ) ([,]-v-ze ⊢σ′ ⊢t)) ⟩
  (σ′ ∘ σ) , t [ σ ]                            ∎
  where open TRS

q⇒∘ : ∀ T →
      Γ ⊢s τ ∶ Γ′ →
      Γ′ ⊢s σ ∶ Γ″ →
      -----------------------------
      T ∷ Γ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ T ∷ Γ″
q⇒∘ T τ σ = S-≈-trans (,-∘ (q⇒⊢s T τ) (S-∘ S-↑ σ) (vlookup here))
                      (,-cong (S-≈-trans (∘-assoc σ S-↑ (S-, (S-∘ S-↑ τ) (vlookup here)))
                              (S-≈-trans (∘-cong (↑-∘-, (S-∘ S-↑ τ) (vlookup here)) (S-≈-refl σ))
                                         (S-≈-sym (∘-assoc σ τ S-↑))))
                              ([,]-v-ze (S-∘ S-↑ τ) (vlookup here)))