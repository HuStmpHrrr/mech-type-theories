{-# OPTIONS --without-K --safe #-}

module T.StaticProps where

open import Lib
open import T.Statics

open Typing

mutual

  ≈⇒⊢-gen : Γ ⊢ t ≈ t′ ∶ T →
            ------------------------
            Γ ⊢ t ∶ T × Γ ⊢ t′ ∶ T
  ≈⇒⊢-gen (v-≈ T∈Γ)               = vlookup T∈Γ , vlookup T∈Γ
  ≈⇒⊢-gen ze-≈                    = ze-I , ze-I
  ≈⇒⊢-gen (su-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′                   = su-I t , su-I t′
  ≈⇒⊢-gen (rec-cong s≈ r≈ t≈)
    with ≈⇒⊢-gen s≈ | ≈⇒⊢-gen r≈ | ≈⇒⊢-gen t≈
  ...  | s , s′ | r , r′ | t , t′ = N-E s r t , N-E s′ r′ t′
  ≈⇒⊢-gen (Λ-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′                   = Λ-I t , Λ-I t′
  ≈⇒⊢-gen ($-cong t≈ s≈)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen s≈
  ...  | t , t′ | s , s′          = Λ-E t s , Λ-E t′ s′
  ≈⇒⊢-gen ([]-cong σ≈ t≈)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢-gen t≈
  ...  | σ , σ′ | t , t′          = t[σ] t σ , t[σ] t′ σ′
  ≈⇒⊢-gen (ze-[] σ)               = t[σ] ze-I σ , ze-I
  ≈⇒⊢-gen (su-[] σ t)             = t[σ] (su-I t) σ , su-I (t[σ] t σ)
  ≈⇒⊢-gen (Λ-[] σ t)              = t[σ] (Λ-I t) σ , Λ-I (t[σ] t (S-, (S-∘ S-↑ σ) (vlookup here)))
  ≈⇒⊢-gen ($-[] σ r s)            = t[σ] (Λ-E r s) σ , Λ-E (t[σ] r σ) (t[σ] s σ)
  ≈⇒⊢-gen (rec-[] σ s r t)        = t[σ] (N-E s r t) σ , N-E (t[σ] s σ) (t[σ] r σ) (t[σ] t σ)
  ≈⇒⊢-gen (rec-β-ze t r)          = N-E t r ze-I , t
  ≈⇒⊢-gen (rec-β-su s r t)        = N-E s r (su-I t) , Λ-E (Λ-E r t) (N-E s r t)
  ≈⇒⊢-gen (Λ-β t s)               = Λ-E (Λ-I t) s , t[σ] t (S-, S-I s)
  ≈⇒⊢-gen (Λ-η t)                 = t , Λ-I (Λ-E (t[σ] t S-↑) (vlookup here))
  ≈⇒⊢-gen ([I] t)                 = t[σ] t S-I , t
  ≈⇒⊢-gen (↑-lookup T∈Γ)          = t[σ] (vlookup T∈Γ) S-↑ , vlookup (there T∈Γ)
  ≈⇒⊢-gen ([∘] τ σ t)             = t[σ] t (S-∘ τ σ) , t[σ] (t[σ] t σ) τ
  ≈⇒⊢-gen ([,]-v-ze σ t)          = t[σ] (vlookup here) (S-, σ t) , t
  ≈⇒⊢-gen ([,]-v-su σ s T∈Δ)      = t[σ] (vlookup (there T∈Δ)) (S-, σ s) , t[σ] (vlookup T∈Δ) σ
  ≈⇒⊢-gen (≈-sym t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′                   = t′ , t
  ≈⇒⊢-gen (≈-trans t≈ t≈′)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen t≈′
  ...  | t , _ | _ , t′           = t , t′

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
