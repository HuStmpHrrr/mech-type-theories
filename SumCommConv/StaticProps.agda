{-# OPTIONS --without-K --safe #-}

module SumCommConv.StaticProps where

open import Lib
open import SumCommConv.Statics
open import Relation.Binary using (PartialSetoid)
import Relation.Binary.Reasoning.PartialSetoid as PS

⊢PartialSetoid : Ctx → Typ → PartialSetoid _ _
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

⊢sPartialSetoid : Ctx → Ctx → PartialSetoid _ _
⊢sPartialSetoid Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = λ t t′ → Γ ⊢s t ≈ t′ ∶ Δ
  ; isPartialEquivalence = record
    { sym   = S-≈-sym
    ; trans = S-≈-trans
    }
  }

module TRS {Γ Δ} = PS′ (⊢sPartialSetoid Γ Δ)

q⇒⊢s : ∀ T → Γ ⊢s σ ∶ Δ → T ∷ Γ ⊢s q σ ∶ T ∷ Δ
q⇒⊢s T σ = S-, (S-∘ S-↑ σ) (vlookup here)

mutual
  ≈⇒⊢-gen : Γ ⊢ t ≈ t′ ∶ T →
            ------------------------
            Γ ⊢ t ∶ T × Γ ⊢ t′ ∶ T
  ≈⇒⊢-gen (v-≈ T∈Γ)           = vlookup T∈Γ , vlookup T∈Γ
  ≈⇒⊢-gen ze-≈                = ze-I , ze-I
  ≈⇒⊢-gen (su-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = su-I t , su-I t′
  ≈⇒⊢-gen (pr-cong s≈ r≈)
    with ≈⇒⊢-gen s≈ | ≈⇒⊢-gen r≈
  ...  | s , s′     | r , r′  = X-I s r , X-I s′ r′
  ≈⇒⊢-gen (p₁-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = X-E₁ t , X-E₁ t′
  ≈⇒⊢-gen (p₂-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = X-E₂ t , X-E₂ t′
  ≈⇒⊢-gen (i₁-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = ∪-I₁ t , ∪-I₁ t′
  ≈⇒⊢-gen (i₂-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = ∪-I₂ t , ∪-I₂ t′
  ≈⇒⊢-gen (pm-cong t≈ s≈ r≈)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen s≈ | ≈⇒⊢-gen r≈
  ...  | t , t′
       | s , s′
       | r , r′               = ∪-E t s r , ∪-E t′ s′ r′
  ≈⇒⊢-gen (Λ-cong t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = Λ-I t , Λ-I t′
  ≈⇒⊢-gen ($-cong t≈ s≈)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen s≈
  ...  | t , t′ | s , s′      = Λ-E t s , Λ-E t′ s′
  ≈⇒⊢-gen ([]-cong σ≈ t≈)
    with ≈⇒⊢s-gen σ≈ | ≈⇒⊢-gen t≈
  ...  | σ , σ′ | t , t′      = t[σ] t σ , t[σ] t′ σ′
  ≈⇒⊢-gen (ze-[] σ)           = t[σ] ze-I σ , ze-I
  ≈⇒⊢-gen (su-[] σ t)         = t[σ] (su-I t) σ , su-I (t[σ] t σ)
  ≈⇒⊢-gen (pr-[] σ s r)       = t[σ] (X-I s r) σ , X-I (t[σ] s σ) (t[σ] r σ)
  ≈⇒⊢-gen (p₁-[] σ t)         = t[σ] (X-E₁ t) σ , X-E₁ (t[σ] t σ)
  ≈⇒⊢-gen (p₂-[] σ t)         = t[σ] (X-E₂ t) σ , X-E₂ (t[σ] t σ)
  ≈⇒⊢-gen (i₁-[] σ t)         = t[σ] (∪-I₁ t) σ , ∪-I₁ (t[σ] t σ)
  ≈⇒⊢-gen (i₂-[] σ t)         = t[σ] (∪-I₂ t) σ , ∪-I₂ (t[σ] t σ)
  ≈⇒⊢-gen (pm-[] σ t s r)     = t[σ] (∪-E t s r) σ
                              , ∪-E (t[σ] t σ) (t[σ] s (q⇒⊢s _ σ)) (t[σ] r (q⇒⊢s _ σ))
  ≈⇒⊢-gen (Λ-[] σ t)          = t[σ] (Λ-I t) σ , Λ-I (t[σ] t (S-, (S-∘ S-↑ σ) (vlookup here)))
  ≈⇒⊢-gen ($-[] σ r s)        = t[σ] (Λ-E r s) σ , Λ-E (t[σ] r σ) (t[σ] s σ)
  ≈⇒⊢-gen (X-β₁ s r)          = X-E₁ (X-I s r) , s
  ≈⇒⊢-gen (X-β₂ s r)          = X-E₂ (X-I s r) , r
  ≈⇒⊢-gen (X-η t)             = t , X-I (X-E₁ t) (X-E₂ t)
  ≈⇒⊢-gen (∪-β₁ t s r)        = ∪-E (∪-I₁ t) s r , t[σ] s (S-, S-I t)
  ≈⇒⊢-gen (∪-β₂ t s r)        = ∪-E (∪-I₂ t) s r , t[σ] r (S-, S-I t)
  ≈⇒⊢-gen (Λ-β t s)           = Λ-E (Λ-I t) s , t[σ] t (S-, S-I s)
  ≈⇒⊢-gen (Λ-η t)             = t , Λ-I (Λ-E (t[σ] t S-↑) (vlookup here))
  ≈⇒⊢-gen ([I] t)             = t[σ] t S-I , t
  ≈⇒⊢-gen (↑-lookup T∈Γ)      = t[σ] (vlookup T∈Γ) S-↑ , vlookup (there T∈Γ)
  ≈⇒⊢-gen ([∘] τ σ t)         = t[σ] t (S-∘ τ σ) , t[σ] (t[σ] t σ) τ
  ≈⇒⊢-gen ([,]-v-ze σ t)      = t[σ] (vlookup here) (S-, σ t) , t
  ≈⇒⊢-gen ([,]-v-su σ s T∈Δ)  = t[σ] (vlookup (there T∈Δ)) (S-, σ s) , t[σ] (vlookup T∈Δ) σ
  ≈⇒⊢-gen (p₁-pm t s r)       = X-E₁ (∪-E t s r)
                              , ∪-E t (X-E₁ s) (X-E₁ r)
  ≈⇒⊢-gen (p₂-pm t s r)       = X-E₂ (∪-E t s r)
                              , ∪-E t (X-E₂ s) (X-E₂ r)
  ≈⇒⊢-gen (pm-pm t s r s′ r′) = ∪-E (∪-E t s r) s′ r′
                              , ∪-E t (∪-E s (t[σ] s′ (q⇒⊢s _ S-↑)) (t[σ] r′ (q⇒⊢s _ S-↑)))
                                      (∪-E r (t[σ] s′ (q⇒⊢s _ S-↑)) (t[σ] r′ (q⇒⊢s _ S-↑)))
  ≈⇒⊢-gen ($-pm t s r t′)     = Λ-E (∪-E t s r) t′
                              , ∪-E t (Λ-E s (t[σ] t′ S-↑)) (Λ-E r (t[σ] t′ S-↑))
  ≈⇒⊢-gen (≈-sym t≈)
    with ≈⇒⊢-gen t≈
  ...  | t , t′               = t′ , t
  ≈⇒⊢-gen (≈-trans t≈ t≈′)
    with ≈⇒⊢-gen t≈ | ≈⇒⊢-gen t≈′
  ...  | t , _ | _ , t′       = t , t′

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

inv-i₁ : Γ ⊢ i₁ t ∶ S ∪ T → Γ ⊢ t ∶ S
inv-i₁ (∪-I₁ t) = t

inv-i₂ : Γ ⊢ i₂ t ∶ S ∪ T → Γ ⊢ t ∶ T
inv-i₂ (∪-I₂ t) = t

inv-[I] : Γ ⊢ t [ I ] ∶ T → Γ ⊢ t ∶ T
inv-[I] (t[σ] t∶T S-I) = t∶T

inv-t[σ] : Γ ⊢ t [ σ ] ∶ T →
           ∃ λ Δ → Δ ⊢ t ∶ T × Γ ⊢s σ ∶ Δ
inv-t[σ] (t[σ] t σ) = -, t , σ
