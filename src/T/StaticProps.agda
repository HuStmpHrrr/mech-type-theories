{-# OPTIONS --without-K --safe #-}

module T.StaticProps where

open import Lib
open import T.Statics
open import Relation.Binary using (PartialSetoid)
import Relation.Binary.Reasoning.PartialSetoid as PS

open Typing

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
    { sym   = S-≈-sym
    ; trans = S-≈-trans
    }
  }

module TRS {Γ Δ} = PS (⊢sPartialSetoid Γ Δ)

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

≈⇒⊢′ : Γ ⊢ t ≈ t′ ∶ T →
       ------------------
       Γ ⊢ t′ ∶ T
≈⇒⊢′ t≈ with ≈⇒⊢-gen t≈
... | _ , t = t

q⇒⊢s : ∀ T → Γ ⊢s σ ∶ Δ → T ∷ Γ ⊢s q σ ∶ T ∷ Δ
q⇒⊢s T σ = S-, (S-∘ S-↑ σ) (vlookup here)

Weaken⇒Subst⇒⊢s : (σ : Weaken Γ Δ) → Γ ⊢s Weaken⇒Subst σ ∶ Δ
Weaken⇒Subst⇒⊢s I       = S-I
Weaken⇒Subst⇒⊢s (P T σ) = S-∘ S-↑ (Weaken⇒Subst⇒⊢s σ)
Weaken⇒Subst⇒⊢s (Q T σ) = q⇒⊢s T (Weaken⇒Subst⇒⊢s σ)

,-∘ : Γ ⊢s σ ∶ Γ′ →
      Γ′ ⊢s σ′ ∶ Γ″ →
      Γ′ ⊢ t ∶ T →
      ----------------------------------------------
      Γ ⊢s (σ′ , t) ∘ σ ≈ (σ′ ∘ σ) , t [ σ ] ∶ T ∷ Γ″
,-∘ {_} {σ} {_} {σ′} {_} {t} ⊢σ ⊢σ′ ⊢t = begin
  (σ′ , t) ∘ σ                                  ≈⟨ ,-ext (S-∘ ⊢σ (S-, ⊢σ′ ⊢t)) ⟩
  (↑ ∘ ((σ′ , t) ∘ σ)) , (v 0 [ (σ′ , t) ∘ σ ]) ≈⟨ ,-cong (S-≈-sym (∘-assoc S-↑ (S-, ⊢σ′ ⊢t) ⊢σ))
                                                          ([∘] ⊢σ (S-, ⊢σ′ ⊢t) (vlookup here)) ⟩
  ((↑ ∘ (σ′ , t) ∘ σ) , v 0 [ σ′ , t ] [ σ ])   ≈⟨ ,-cong (∘-cong (S-≈-refl ⊢σ) (↑-∘-, ⊢σ′ ⊢t))
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

Weaken⇒Subst∘∘ : (σ : Weaken Γ′ Δ) (δ : Weaken Γ Γ′) → Γ ⊢s Weaken⇒Subst σ ∘ Weaken⇒Subst δ ≈ Weaken⇒Subst (σ ∘∘ δ) ∶ Δ
Weaken⇒Subst∘∘ σ I              = ∘-I (Weaken⇒Subst⇒⊢s σ)
Weaken⇒Subst∘∘ σ (P T δ)        = S-≈-trans (S-≈-sym (∘-assoc (Weaken⇒Subst⇒⊢s σ) (Weaken⇒Subst⇒⊢s δ) S-↑)) (∘-cong ↑-≈ (Weaken⇒Subst∘∘ σ δ))
Weaken⇒Subst∘∘ I (Q T δ)        = I-∘ (q⇒⊢s T (Weaken⇒Subst⇒⊢s δ))
Weaken⇒Subst∘∘ (P .T σ) (Q T δ) = let ⊢σ = Weaken⇒Subst⇒⊢s σ
                                      ⊢δ = Weaken⇒Subst⇒⊢s δ
                                  in
                                  S-≈-trans (∘-assoc ⊢σ S-↑ (q⇒⊢s T ⊢δ))
                                  (S-≈-trans (∘-cong (↑-∘-, (S-∘ S-↑ ⊢δ) (vlookup here)) (S-≈-refl ⊢σ))
                                  (S-≈-trans (S-≈-sym (∘-assoc ⊢σ ⊢δ S-↑))
                                             (∘-cong ↑-≈ (Weaken⇒Subst∘∘ σ δ))))
Weaken⇒Subst∘∘ (Q .T σ) (Q T δ) = S-≈-trans (q⇒∘ T (Weaken⇒Subst⇒⊢s δ) (Weaken⇒Subst⇒⊢s σ))
                                            (,-cong (∘-cong ↑-≈ (Weaken⇒Subst∘∘ σ δ)) (v-≈ here))

pred-syn : Exp → Exp
pred-syn = rec N ze (Λ (Λ (v 1)))

⊢pred-syn : Γ ⊢ t ∶ N →
            -------------------
            Γ ⊢ pred-syn t ∶ N
⊢pred-syn t = N-E ze-I (Λ-I (Λ-I (vlookup (there here)))) t

pred-syn-su : Γ ⊢ t ∶ N →
              ----------------------------
              Γ ⊢ pred-syn (su t) ≈ t ∶ N
pred-syn-su {_} {t} ⊢t =
  let ⊢rc = ⊢pred-syn ⊢t
      ≈rc = ≈-refl ⊢rc
      src = S-, S-I ⊢rc
  in begin
  pred-syn (su t)                          ≈⟨ rec-β-su ze-I (Λ-I (Λ-I (vlookup (there here)))) ⊢t ⟩
  Λ (Λ (v 1)) $ t $ pred-syn t             ≈⟨ $-cong (Λ-β (Λ-I (vlookup (there here))) ⊢t) ≈rc ⟩
  Λ (v 1) [ I , t ] $ pred-syn t           ≈⟨ $-cong (Λ-[] (S-, S-I ⊢t) (vlookup (there here))) ≈rc ⟩
  Λ (v 1 [ q (I , t) ]) $ pred-syn t       ≈⟨ Λ-β (t[σ] (vlookup (there here)) (S-, (S-∘ S-↑ (S-, S-I ⊢t)) (vlookup here)))
                                                  ⊢rc ⟩
  v 1 [ q (I , t) ] [ I , pred-syn t ]     ≈⟨ []-cong (S-≈-refl src)
                                                      ([,]-v-su (S-∘ S-↑ (S-, S-I ⊢t)) (vlookup here) here) ⟩
  v 0 [ (I , t) ∘ ↑ ] [ I , pred-syn t ]   ≈˘⟨ [∘] src (S-∘ S-↑ (S-, S-I ⊢t)) (vlookup here) ⟩
  v 0 [ (I , t) ∘ ↑ ∘ (I , pred-syn t) ]   ≈⟨ []-cong (∘-assoc (S-, S-I ⊢t) S-↑ src) (v-≈ here) ⟩
  v 0 [ (I , t) ∘ (↑ ∘ (I , pred-syn t)) ] ≈⟨ []-cong (∘-cong (↑-∘-, S-I ⊢rc) (S-≈-refl (S-, S-I ⊢t))) (v-≈ here) ⟩
  v 0 [ (I , t) ∘ I ]                      ≈⟨ []-cong (∘-I (S-, S-I ⊢t)) (v-≈ here) ⟩
  v 0 [ I , t ]                            ≈⟨ [,]-v-ze S-I ⊢t ⟩
  t                                        ∎
  where open TR

inv-su-≈ : Γ ⊢ su t ≈ su t′ ∶ N →
           -----------------------
           Γ ⊢ t ≈ t′ ∶ N
inv-su-≈ {_} {t} {t′} su≈ with ≈⇒⊢-gen su≈
... | su-I ⊢t , su-I ⊢t′ = begin
  t                ≈˘⟨ pred-syn-su ⊢t ⟩
  pred-syn (su t)  ≈⟨ rec-cong ze-≈ (Λ-cong (Λ-cong (v-≈ (there here)))) su≈ ⟩
  pred-syn (su t′) ≈⟨ pred-syn-su ⊢t′ ⟩
  t′               ∎
  where open TR
