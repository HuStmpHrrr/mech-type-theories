
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Equiv  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Consequences fext
open import NonCumulative.Statics.Ascribed.Full as A renaming (Ctx to lCtx)
open import NonCumulative.Statics.Unascribed.Full as U
open import NonCumulative.Statics.Unascribed.Transfer

U⇒A-vlookup : ∀ {x} →
  A.Γ [↝] U.Γ′ → 
  x ∶ U.T′ ∈! U.Γ′ →
  ∃₂ λ i T →  (T ↝ U.T′) × (x ∶[ i ] T ∈! A.Γ)
U⇒A-vlookup (↝∷ {Γ′} {Γ} {T′} {T} {i′} Γ↝Γ′ T↝T′) here = _ , _ , (↝sub T↝T′ ↝wk , here) 
U⇒A-vlookup (↝∷ Γ↝Γ′ _) (there x∈Γ') with U⇒A-vlookup Γ↝Γ′ x∈Γ'
... | i , T , T↝T′ , x∈Γ = _ , _ , ↝sub T↝T′ ↝wk , there x∈Γ

mutual
  [↝]-inv-det : ∀ {Γ₁ Γ₂} →
            A.⊢ Γ₁ → 
            A.⊢ Γ₂ →
            Γ₁ [↝] U.Γ′ → 
            Γ₂ [↝] U.Γ′ → 
            Γ₁ ≡ Γ₂
  [↝]-inv-det {[]} ⊢Γ₁ ⊢Γ₂ ↝[] ↝[] = refl
  [↝]-inv-det {T′ ∷ Γ′} (⊢∷ ⊢Γ₁ ⊢T₁) (⊢∷ ⊢Γ₂ ⊢T₂) (↝∷ {Γ₁} {T = T₁} Γ₁[↝]Γ′ T₁↝T′) (↝∷ {Γ₂} {T = T₂} Γ₂[↝]Γ′ T₂↝T′) 
    rewrite [↝]-inv-det ⊢Γ₁ ⊢Γ₂ Γ₁[↝]Γ′ Γ₂[↝]Γ′
    with ↝-inv-det T₁↝T′ T₂↝T′ ⊢T₁ ⊢T₂ 
  ... | refl 
      with unique-typ ⊢T₁ ⊢T₂ 
  ... | refl , _ = refl

  ↝-inv-det : ∀ {t₁ t₂ i₁ i₂ T₁ T₂} →
    t₁ ↝ U.t′ → 
    t₂ ↝ U.t′ → 
    A.Γ ⊢ t₁ ∶[ i₁ ] T₁ → 
    A.Γ ⊢ t₂ ∶[ i₂ ] T₂ →
    t₁ ≡ t₂
  ↝-inv-det {N} ↝N ↝N ⊢t₁ ⊢t₂ = refl
  ↝-inv-det {Π x x₁} (↝Π t1↝t′ t1↝t′₁) (↝Π t₂↝t′ t₂↝t′₁) ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {Liftt x x₁} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {Se i} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {v x} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {ze} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {su t′} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {rec T t′ t′₁ t′₂} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {Λ t′} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {t′ $ t′₁} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {liftt x t′} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {unlift t′} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}
  ↝-inv-det {sub t′ x} t1↝t′ t₂↝t′ ⊢t₁ ⊢t₂ = {!   !}

mutual
  U⇒A-⊢ : U.⊢ U.Γ →
          -------
          ∃ λ Γ → A.⊢ Γ × Γ [↝] U.Γ
  U⇒A-⊢ ⊢[] = _ , ⊢[] , ↝[]
  U⇒A-⊢ (⊢∷ {Γ′} {T′} {i = i′} ⊢Γ′ ⊢T′) with U⇒A-tm ⊢T′ 
  ... | i , Γ , T , .(Se i′) , Γ[↝]Γ′ , T↝T′ , ↝Se , ⊢T = _ , ({!   !} , ↝∷ {i = i′} Γ[↝]Γ′ T↝T′)  
 
  U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
           ∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (T ↝ U.T′) × Γ A.⊢ t ∶[ i ] T
  U⇒A-tm (N-wf ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝N , ↝Se , N-wf ⊢Γ
  U⇒A-tm (Se-wf i ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝Se , ↝Se , Se-wf _ ⊢Γ
  U⇒A-tm (Liftt-wf {Γ′} {T′} {i′} n ⊢T′) with U⇒A-tm ⊢T′ 
  ... | i , Γ , T , _ , Γ↝Γ′ , T↝T′ , ↝Se , ⊢T = _ , _ , _ , _ , Γ↝Γ′ , ↝Liftt T↝T′ , ↝Se , Liftt-wf _ {!   !} -- Γ ⊢ T ∶[ i ] Se i′ → i ≡ 1 + i′
  U⇒A-tm (Π-wf {Γ′} {S′} {T′} ⊢S ⊢T k≡maxij) = {!   !}
  U⇒A-tm (vlookup {x = x} ⊢Γ′ x∈Γ′) with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝Γ′ 
      with U⇒A-vlookup Γ↝Γ′ x∈Γ′
  ...    | i , T , T↝T′ , x∈Γ = _ , _ , _ , _ , Γ↝Γ′ , ↝v , T↝T′ , vlookup ⊢Γ x∈Γ 
  U⇒A-tm (ze-I ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝ze , ↝N , ze-I ⊢Γ 
  U⇒A-tm (su-I {t = t′} ⊢t) with U⇒A-tm ⊢t 
  ... | i , Γ , t , N , Γ↝Γ′ , t↝t′ , ↝N , ⊢t = _ , _ , _ , _ , Γ↝Γ′ , ↝su t↝t′ , ↝N , su-I {!   !} -- Γ ⊢ t ∶[ i ] N → i ≡ 0
  U⇒A-tm (N-E ⊢T′ ⊢s′ ⊢r′ ⊢t′) = {!   !}
  U⇒A-tm (Λ-I {Γ′} {S′} {t′} {T′} {i′} ⊢S′ ⊢t′) 
    with U⇒A-tm ⊢S′ 
       | U⇒A-tm ⊢t′
  ...  | j , Γ , S , _ , Γ↝Γ′ , S↝S′ , ↝Se , ⊢S 
       | i , _ , t , T , (↝∷ {Γ₁} Γ↝′Γ′ S↝′S′) , t↝t′ , T↝T′ , ⊢t 
       with A.presup-tm ⊢S 
          | A.presup-tm ⊢t 
  ...     | ⊢Γ , _
          | ⊢∷ ⊢Γ₁ ⊢S₁  , _
          rewrite [↝]-inv-det ⊢Γ₁ ⊢Γ Γ↝′Γ′ Γ↝Γ′ 
          with ↝-inv-det S↝′S′ S↝S′ ⊢S₁ ⊢S 
  ...        | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝Λ t↝t′ , ↝Π S↝S′ T↝T′ , Λ-I ⊢S₁ ⊢t refl
  U⇒A-tm (Λ-E ⊢S′ ⊢T′ ⊢r′ ⊢s′) = {!   !}
  U⇒A-tm (L-I {Γ'} {t′} {T′} n ⊢t′) with U⇒A-tm ⊢t′  
  ... | i , Γ , t , T , Γ↝Γ′ , t↝t′ , T↝T′ , ⊢t = _ , _ , _ , _ , Γ↝Γ′ , ↝liftt t↝t′ , ↝Liftt T↝T′ , L-I _ ⊢t 
  U⇒A-tm (L-E {Γ'} {T′} {t′} {i′} n ⊢T′ ⊢t′) 
    with U⇒A-tm ⊢T′ 
       | U⇒A-tm ⊢t′
  ...  | i , Γ , T , _ , Γ↝Γ′ , T↝T′ , ↝Se , ⊢T
       | j , Γ₁ , t , _ , Γ↝′Γ′ , t↝t′ , ↝Liftt T↝′T′ , ⊢t 
       with A.presup-tm ⊢T 
          | A.presup-tm ⊢t 
  ...     | ⊢Γ , _
          | ⊢Γ₁ , _
          rewrite [↝]-inv-det ⊢Γ₁ ⊢Γ Γ↝′Γ′ Γ↝Γ′ = {!   !} , {!   !} , {!   !} , {!   !} , Γ↝Γ′ , ↝unlift t↝t′ , {!   !} , L-E {!   !} {!   !} {!   !} 
  U⇒A-tm (t[σ] {Δ′} {t′} {T′} {Γ′} {σ′} ⊢t′ ⊢σ′) = {!   !}
  U⇒A-tm (conv ⊢t′ S′≈T′) = {!   !}
  
-- mutual
--   U⇒A-⊢ : U.⊢ U.Γ →
--           A.Γ [↝] U.Γ → 
--           -------
--           A.⊢ A.Γ
--   U⇒A-⊢ ⊢[] ↝s = ⊢[]
--   U⇒A-⊢ (⊢∷ ⊢Γ ⊢T) (↝∷ {i = i} Γ↝Γ′ ⊢T′) = {!   !}

--   U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
--            A.Γ [↝] U.Γ′ → 
--            A.t ↝ U.t′ →
--           -------------
--            ∃₂ λ i T → (T ↝ U.T′) × A.Γ A.⊢ A.t ∶[ i ] T
--   U⇒A-tm (N-wf ⊢Γ′) Γ[↝]Γ' ↝N = _ , (_ , ↝Se , N-wf (U⇒A-⊢ ⊢Γ′ Γ[↝]Γ')) 
--   U⇒A-tm (Se-wf i ⊢Γ′) Γ[↝]Γ' ↝Se = _ , (_ , ↝Se , Se-wf _ (U⇒A-⊢ ⊢Γ′ Γ[↝]Γ')) 
--   U⇒A-tm (Liftt-wf n ⊢t′) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (Π-wf ⊢t′ ⊢t′₁ x) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (vlookup x x₁) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (ze-I x) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (su-I ⊢t′) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (Λ-I ⊢t′ ⊢t′₁) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (Λ-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (L-I n ⊢t′) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (L-E n ⊢t′) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (t[σ] ⊢t′ x) Γ[↝]Γ' t↝t′ = {!   !}
--   U⇒A-tm (conv ⊢t′ x) Γ[↝]Γ' t↝t′ = {!   !}
-- Stronger connection when T = Se i ?
-- Determinism ?
--   U⇒A-tm : U.Γ′ U.⊢ t ∶ T →
--            A.Γ ↝Γ U.Γ′ → 
--           -------------
--            ∃ λ i → A.Γ A.⊢ t ∶[ i ] T
--   U⇒A-tm (N-wf ⊢Γ) Γ↝Γ′ = _ , N-wf (U⇒A-⊢ ⊢Γ Γ↝Γ′)
--   U⇒A-tm (Se-wf i ⊢Γ) Γ↝Γ′ = _ , Se-wf _ (U⇒A-⊢ ⊢Γ Γ↝Γ′)
--   U⇒A-tm (Liftt-wf n ⊢t) Γ↝Γ′ = {!   !}
--   U⇒A-tm (Π-wf ⊢S ⊢T k≡maxij) Γ↝Γ′ = {!   !} , Π-wf {!   !} {!   !} {!   !}
--   U⇒A-tm (vlookup x x₁) Γ↝Γ′ = {!   !} , (vlookup {!   !} {!   !}) 
--   U⇒A-tm (ze-I ⊢Γ) Γ↝Γ′ = _ , ze-I (U⇒A-⊢ ⊢Γ Γ↝Γ′)
--   U⇒A-tm (su-I ⊢′t) Γ↝Γ′ with U⇒A-tm ⊢′t Γ↝Γ′ 
--   ... | i , ⊢t = _ , (su-I {!   !})
--   U⇒A-tm (N-E ⊢T ⊢s ⊢r ⊢t) Γ↝Γ′ = {!   !}
--   U⇒A-tm (Λ-I ⊢S ⊢t) Γ↝Γ′ = {!   !}
--   U⇒A-tm (Λ-E ⊢S ⊢T ⊢r ⊢s) Γ↝Γ′ = {!   !}
--   U⇒A-tm (L-I n ⊢t) Γ↝Γ′ = {!   !}
--   U⇒A-tm (L-E n ⊢t) Γ↝Γ′ = {!   !}
--   U⇒A-tm (t[σ] ⊢t ⊢σ) Γ↝Γ′ = {!   !}
--   U⇒A-tm (conv ⊢t S≈T) Γ↝Γ′ = {!   !}

-- mutual
--   U⇒A-⊢ : U.⊢ Γ →
--           -------
--           A.⊢ Γ
--   U⇒A-⊢ ⊢[]        = ⊢[]
--   U⇒A-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (U⇒A-⊢ ⊢Γ) {!U⇒A-tm ⊢T!} -- (proj₂ (U⇒A-tm ⊢T))


--   U⇒A-tm : Γ U.⊢ t ∶ T →
--            -------------
--            ∃ λ i → Γ A.⊢ t ∶[ i ] T
--   U⇒A-tm = {!!}

--   U⇒A-s : Γ U.⊢s σ ∶ Δ →
--           --------------
--           Γ A.⊢s σ ∶ Δ
--   U⇒A-s (s-I ⊢Γ)           = s-I (U⇒A-⊢ ⊢Γ)
--   U⇒A-s (s-wk ⊢Γ)          = s-wk (U⇒A-⊢ ⊢Γ)
--   U⇒A-s (s-∘ ⊢σ ⊢δ)        = s-∘ (U⇒A-s ⊢σ) (U⇒A-s ⊢δ)
--   U⇒A-s (s-, ⊢σ ⊢T ⊢t)     = s-, (U⇒A-s ⊢σ) {!!} {!!}
--   U⇒A-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (U⇒A-s ⊢σ) (U⇒A-⊢≈ Δ′≈Δ)


--   U⇒A-⊢≈ : U.⊢ Γ ≈ Δ →
--            -----------
--            A.⊢ Γ ≈ Δ
--   U⇒A-⊢≈ []-≈                    = []-≈
--   U⇒A-⊢≈ (∷-cong Γ≈Δ _ _ T≈T′ _) = {!!}


--   U⇒A-≈ : Γ U.⊢ t ≈ t′ ∶ T →
--           ------------------
--           ∃ λ i → Γ A.⊢ t ≈ t′ ∶[ i ] T
--   U⇒A-≈ = {!!}

--   U⇒A-s-≈ : Γ U.⊢s σ ≈ σ′ ∶ Δ →
--             ------------------
--             Γ A.⊢s σ ≈ σ′ ∶ Δ
--   U⇒A-s-≈ (I-≈ ⊢Γ)                = I-≈ (U⇒A-⊢ ⊢Γ)
--   U⇒A-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (U⇒A-⊢ ⊢TΓ)
--   U⇒A-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (U⇒A-s-≈ σ≈σ′) (U⇒A-s-≈ δ≈δ′)
--   U⇒A-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (U⇒A-s-≈ σ≈σ′) {!!} {!!}
--   U⇒A-s-≈ (I-∘ ⊢σ)                = I-∘ (U⇒A-s ⊢σ)
--   U⇒A-s-≈ (∘-I ⊢σ)                = ∘-I (U⇒A-s ⊢σ)
--   U⇒A-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (U⇒A-s ⊢σ) (U⇒A-s ⊢σ′) (U⇒A-s ⊢σ″)
--   U⇒A-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (U⇒A-s ⊢σ) {!!} {!!} {!!}
--   U⇒A-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (U⇒A-s ⊢σ) {!!} {!!}
--   U⇒A-s-≈ (,-ext ⊢σ)              = ,-ext (U⇒A-s ⊢σ)
--   U⇒A-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (U⇒A-s-≈ σ≈σ′)
--   U⇒A-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (U⇒A-s-≈ σ≈σ′) (U⇒A-s-≈ σ′≈σ″)
--   U⇒A-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (U⇒A-s-≈ σ≈σ′) (U⇒A-⊢≈ Δ′≈Δ)


-- mutual
--   C⇒F-⊢ : A.⊢ Γ →
--           -------
--           U.⊢ Γ
--   C⇒F-⊢ ⊢[]        = ⊢[]
--   C⇒F-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T)


--   C⇒F-tm : Γ A.⊢ t ∶ T →
--            -------------
--            Γ U.⊢ t ∶ T
--   C⇒F-tm (N-wf i ⊢Γ)                              = N-wf i (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (Se-wf i ⊢Γ)                             = Se-wf i (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (Π-wf ⊢S ⊢T)                             = Π-wf (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
--   C⇒F-tm (vlookup ⊢Γ T∈Γ)                         = vlookup (C⇒F-⊢ ⊢Γ) T∈Γ
--   C⇒F-tm (ze-I ⊢Γ)                                = ze-I (C⇒F-⊢ ⊢Γ)
--   C⇒F-tm (su-I ⊢t)                                = su-I (C⇒F-tm ⊢t)
--   C⇒F-tm (N-E ⊢T ⊢s ⊢r ⊢t)                        = N-E (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-tm (Λ-I ⊢t)
--     with ⊢∷ ⊢Γ ⊢S ← proj₁ (presup-tm (C⇒F-tm ⊢t)) = Λ-I ⊢S (C⇒F-tm ⊢t)
--   C⇒F-tm (Λ-E ⊢t ⊢r)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)       = Λ-E (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t) (C⇒F-tm ⊢r)
--   C⇒F-tm (t[σ] ⊢t ⊢σ)                             = t[σ] (C⇒F-tm ⊢t) (C⇒F-s ⊢σ)
--   C⇒F-tm (cumu ⊢t)                                = cumu (C⇒F-tm ⊢t)
--   C⇒F-tm (conv ⊢t T≈T′)                           = conv (C⇒F-tm ⊢t) (C⇒F-≈ T≈T′)


--   C⇒F-s : Γ A.⊢s σ ∶ Δ →
--           --------------
--           Γ U.⊢s σ ∶ Δ
--   C⇒F-s (s-I ⊢Γ)           = s-I (C⇒F-⊢ ⊢Γ)
--   C⇒F-s (s-wk ⊢TΓ)         = s-wk (C⇒F-⊢ ⊢TΓ)
--   C⇒F-s (s-∘ ⊢σ ⊢δ)        = s-∘ (C⇒F-s ⊢σ) (C⇒F-s ⊢δ)
--   C⇒F-s (s-, ⊢σ ⊢T ⊢t)     = s-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
--   C⇒F-s (s-conv ⊢σ Δ′≈Δ)   = s-conv (C⇒F-s ⊢σ) (C⇒F-⊢≈ Δ′≈Δ)


--   C⇒F-⊢≈ : A.⊢ Γ ≈ Δ →
--            -----------
--            U.⊢ Γ ≈ Δ
--   C⇒F-⊢≈ []-≈                                        = []-≈
--   C⇒F-⊢≈ (∷-cong Γ≈Δ T≈T′)
--     with T≈T′₁ ← ctxeq-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-≈ T≈T′)
--        with _ , ⊢T , _       ← presup-≈ (C⇒F-≈ T≈T′)
--           | _ , _  , ⊢T′ , _ ← presup-≈ T≈T′₁        = ∷-cong (C⇒F-⊢≈ Γ≈Δ) ⊢T ⊢T′ (C⇒F-≈ T≈T′) T≈T′₁


--   C⇒F-≈ : Γ A.⊢ t ≈ t′ ∶ T →
--           ------------------
--           Γ U.⊢ t ≈ t′ ∶ T
--   C⇒F-≈ (N-[] i ⊢σ)                                 = N-[] i (C⇒F-s ⊢σ)
--   C⇒F-≈ (Se-[] i ⊢σ)                                = Se-[] i (C⇒F-s ⊢σ)
--   C⇒F-≈ (Π-[] ⊢σ ⊢S ⊢T)                             = Π-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢T)
--   C⇒F-≈ (Π-cong S≈S′ T≈T′)
--     with _ , ⊢S , _ ← presup-≈ (C⇒F-≈ S≈S′)         = Π-cong ⊢S (C⇒F-≈ S≈S′) (C⇒F-≈ T≈T′)
--   C⇒F-≈ (v-≈ ⊢Γ T∈Γ)                                = v-≈ (C⇒F-⊢ ⊢Γ) T∈Γ
--   C⇒F-≈ (ze-≈ ⊢Γ)                                   = ze-≈ (C⇒F-⊢ ⊢Γ)
--   C⇒F-≈ (su-cong t≈t′)                              = su-cong (C⇒F-≈ t≈t′)
--   C⇒F-≈ (rec-cong T≈T′ s≈s′ r≈r′ t≈t′)
--     with _ , ⊢T , _ ← presup-≈ (C⇒F-≈ T≈T′)         = rec-cong ⊢T (C⇒F-≈ T≈T′) (C⇒F-≈ s≈s′) (C⇒F-≈ r≈r′) (C⇒F-≈ t≈t′)
--   C⇒F-≈ (Λ-cong t≈t′)
--     with ⊢∷ ⊢Γ ⊢S , _ ← presup-≈ (C⇒F-≈ t≈t′)       = Λ-cong ⊢S (C⇒F-≈ t≈t′)
--   C⇒F-≈ ($-cong t≈t′ r≈r′)
--     with _ , _ , _ , _ , ⊢Π ← presup-≈ (C⇒F-≈ t≈t′) = $-cong (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-≈ t≈t′) (C⇒F-≈ r≈r′)
--   C⇒F-≈ ([]-cong t≈t′ σ≈σ′)                         = []-cong (C⇒F-≈ t≈t′) (C⇒F-s-≈ σ≈σ′)
--   C⇒F-≈ (ze-[] ⊢σ)                                  = ze-[] (C⇒F-s ⊢σ)
--   C⇒F-≈ (su-[] ⊢σ ⊢t)                               = su-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)                     = rec-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-≈ (Λ-[] ⊢σ ⊢t)                                = Λ-[] (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ ($-[] ⊢σ ⊢t ⊢s)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = $-[] (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
--   C⇒F-≈ (rec-β-ze ⊢T ⊢s ⊢r)                         = rec-β-ze (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r)
--   C⇒F-≈ (rec-β-su ⊢T ⊢s ⊢r ⊢t)                      = rec-β-su (C⇒F-tm ⊢T) (C⇒F-tm ⊢s) (C⇒F-tm ⊢r) (C⇒F-tm ⊢t)
--   C⇒F-≈ (Λ-β ⊢t ⊢s)
--     with ⊢∷ ⊢Γ ⊢S , _ , ⊢T ← presup-tm (C⇒F-tm ⊢t)  = Λ-β (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s)
--   C⇒F-≈ (Λ-η ⊢t)
--     with _ , _ , ⊢Π ← presup-tm (C⇒F-tm ⊢t)         = Λ-η (lift-⊢-Se-max (proj₂ (inv-Π-wf′ ⊢Π))) (lift-⊢-Se-max′ (proj₂ (inv-Π-wf ⊢Π))) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([I] ⊢t)                                    = [I] (C⇒F-tm ⊢t)
--   C⇒F-≈ ([wk] ⊢SΓ T∈Γ)                              = [wk] (C⇒F-⊢ ⊢SΓ) T∈Γ
--   C⇒F-≈ ([∘] ⊢δ ⊢σ ⊢t)                              = [∘] (C⇒F-s ⊢δ) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)                         = [,]-v-ze (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t)
--   C⇒F-≈ ([,]-v-su ⊢σ ⊢S ⊢t T∈Δ)                     = [,]-v-su (C⇒F-s ⊢σ) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t) T∈Δ
--   C⇒F-≈ (≈-cumu t≈t′)                               = ≈-cumu (C⇒F-≈ t≈t′)
--   C⇒F-≈ (≈-conv t≈t′ S≈T)                           = ≈-conv (C⇒F-≈ t≈t′) (C⇒F-≈ S≈T)
--   C⇒F-≈ (≈-sym t≈t′)                                = ≈-sym (C⇒F-≈ t≈t′)
--   C⇒F-≈ (≈-trans t≈t′ t′≈t″)                        = ≈-trans (C⇒F-≈ t≈t′) (C⇒F-≈ t′≈t″)


--   C⇒F-s-≈ : Γ A.⊢s σ ≈ σ′ ∶ Δ →
--             ------------------
--             Γ U.⊢s σ ≈ σ′ ∶ Δ
--   C⇒F-s-≈ (I-≈ ⊢Γ)                = I-≈ (C⇒F-⊢ ⊢Γ)
--   C⇒F-s-≈ (wk-≈ ⊢TΓ)              = wk-≈ (C⇒F-⊢ ⊢TΓ)
--   C⇒F-s-≈ (∘-cong σ≈σ′ δ≈δ′)      = ∘-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ δ≈δ′)
--   C⇒F-s-≈ (,-cong σ≈σ′ ⊢T t≈t′)   = ,-cong (C⇒F-s-≈ σ≈σ′) (C⇒F-tm ⊢T) (C⇒F-≈ t≈t′)
--   C⇒F-s-≈ (I-∘ ⊢σ)                = I-∘ (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (∘-I ⊢σ)                = ∘-I (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)    = ∘-assoc (C⇒F-s ⊢σ) (C⇒F-s ⊢σ′) (C⇒F-s ⊢σ″)
--   C⇒F-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢δ)       = ,-∘ (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t) (C⇒F-s ⊢δ)
--   C⇒F-s-≈ (p-, ⊢σ ⊢T ⊢t)          = p-, (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t)
--   C⇒F-s-≈ (,-ext ⊢σ)              = ,-ext (C⇒F-s ⊢σ)
--   C⇒F-s-≈ (s-≈-sym σ≈σ′)          = s-≈-sym (C⇒F-s-≈ σ≈σ′)
--   C⇒F-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)  = s-≈-trans (C⇒F-s-≈ σ≈σ′) (C⇒F-s-≈ σ′≈σ″)
--   C⇒F-s-≈ (s-≈-conv σ≈σ′ Δ′≈Δ)    = s-≈-conv (C⇒F-s-≈ σ≈σ′) (C⇒F-⊢≈ Δ′≈Δ)
 
-- ↝ relation is functonal (deterministic and total)
mutual
  ↝-det : ∀ {t₁′ t₂′} →
          A.t ↝ t₁′ →
          A.t ↝ t₂′ →
          -------------
          t₁′ ≡ t₂′
  ↝-det {N} ↝N ↝N = refl
  ↝-det {Π .(_ ↙ _) .(_ ↙ _)} (↝Π S↝S₁′ T↝T₁′) (↝Π S↝S₂′ T↝T₂′) = cong₂ Π (↝-det S↝S₁′ S↝S₂′) (↝-det T↝T₁′ T↝T₂′) 
  ↝-det {Liftt n .(_ ↙ _)} (↝Liftt T↝T₁′) (↝Liftt T↝T₂′) = cong₂ Liftt refl (↝-det T↝T₁′ T↝T₂′) 
  ↝-det {Se i} ↝Se ↝Se = refl
  ↝-det {v x} ↝v ↝v = refl
  ↝-det {ze} ↝ze ↝ze = refl
  ↝-det {su t} (↝su t↝t₁′) (↝su t↝t₂′) = cong su (↝-det t↝t₁′ t↝t₂′)
  ↝-det {rec .(_ ↙ _) t t₁ t₂} (↝rec T↝T₁′ r↝r₁′ s↝s₁′ t↝t₁′) (↝rec T↝T₂′ r↝r₂′ s↝s₂′ t↝t₂′) 
    with ↝-det T↝T₂′ T↝T₁′ 
       | ↝-det r↝r₂′ r↝r₁′ 
       | ↝-det s↝s₂′ s↝s₁′ 
       | ↝-det t↝t₂′ t↝t₁′  
  ... | refl | refl | refl | refl = refl
  ↝-det {Λ .(_ ↙ _) t} (↝Λ t↝t₁′) (↝Λ t↝t₂′) = cong Λ (↝-det  t↝t₁′ t↝t₂′)
  ↝-det {t $ s} (↝$ t↝t₁′ s↝s₁′) (↝$ t↝t₂′ s↝s₂′) = cong₂ _$_ (↝-det t↝t₁′ t↝t₂′) (↝-det s↝s₁′ s↝s₂′)
  ↝-det {liftt x t} (↝liftt t↝t₁′) (↝liftt t↝t₂′) = cong₂ liftt refl (↝-det t↝t₁′ t↝t₂′) 
  ↝-det {unlift t} (↝unlift t↝t₁′) (↝unlift t↝t₂′) = cong unlift (↝-det t↝t₁′ t↝t₂′)
  ↝-det {sub t σ} (↝sub t↝t₁′ σ↝σ₁′) (↝sub t↝t₂′ σ↝σ₂′) = cong₂ sub (↝-det t↝t₁′ t↝t₂′) (↝-det-s σ↝σ₁′ σ↝σ₂′)
  
  ↝-det-s : ∀ {σ₁′ σ₂′} →
            _↝s_ A.σ σ₁′ →
            _↝s_ A.σ σ₂′ →
            -------------
            σ₁′ ≡ σ₂′
  ↝-det-s {I} ↝I ↝I = refl
  ↝-det-s {wk} ↝wk ↝wk = refl
  ↝-det-s {σ ∘ τ} (↝∘ σ↝σ₁′ τ↝τ₁′) (↝∘ σ↝σ₂′ τ↝τ₂′) = cong₂ _∘_ (↝-det-s σ↝σ₁′ σ↝σ₂′) (↝-det-s τ↝τ₁′ τ↝τ₂′)
  ↝-det-s {σ , t ∶ T} (↝, σ↝σ₁′ t↝t₁′) (↝, σ↝σ₂′ t↝t₂′) = cong₂ _,_ (↝-det-s σ↝σ₁′ σ↝σ₂′) (↝-det t↝t₁′ t↝t₂′)
    
[↝]-det : ∀ {Γ₁′ Γ₂′} →
          A.Γ [↝] Γ₁′ →
          A.Γ [↝] Γ₂′ →
          -------------
          Γ₁′ ≡ Γ₂′
[↝]-det {[]} ↝[] ↝[] = refl
[↝]-det {.(_ ↙ _) ∷ Γ} (↝∷ Γ↝Γ₁′ T↝T₁′) (↝∷ Γ↝Γ₂ T↝T₂′) = cong₂ _∷_ (↝-det T↝T₁′ T↝T₂′) ([↝]-det Γ↝Γ₁′ Γ↝Γ₂)

mutual
  ↝-total : ∀ t → 
            ∃ λ t′ → t ↝ t′
  ↝-total N = _ , ↝N
  ↝-total (Π x x₁) = {!   !}
  ↝-total (Liftt x x₁) = {!   !}
  ↝-total (Se i) = {!   !}
  ↝-total (v x) = {!   !}
  ↝-total ze = {!   !}
  ↝-total (su t) = {!   !}
  ↝-total (rec T t t₁ t₂) = {!   !}
  ↝-total (Λ S t) = {!   !}
  ↝-total (t $ t₁) = {!   !}
  ↝-total (liftt x t) = {!   !}
  ↝-total (unlift t) = {!   !}
  ↝-total (sub t x) = {!   !}

[↝]-total : ∀ Γ → 
            ∃ λ Γ′ → Γ [↝] Γ′
[↝]-total [] = _ , ↝[]
[↝]-total ((T ↙ i) ∷ Γ) 
  with ↝-total T
     | [↝]-total Γ
...  | T′ , T↝T′ 
     | Γ′ , Γ↝Γ′ = _ , ↝∷ Γ↝Γ′ T↝T′

A⇒U-vlookup : ∀ {x i} →
  x ∶[ i ] A.T ∈! A.Γ → 
  A.Γ [↝] U.Γ′ → 
  A.T ↝ U.T′ →
  x ∶ U.T′ ∈! U.Γ′
A⇒U-vlookup here (↝∷ Γ↝Γ′ T↝T′) (↝sub T↝′T′ ↝wk) with ↝-det T↝T′ T↝′T′
... | refl = here
A⇒U-vlookup (there x∈Γ′) (↝∷ Γ↝Γ′ _) (↝sub T↝T′ ↝wk) = there (A⇒U-vlookup x∈Γ′ Γ↝Γ′ T↝T′) 

mutual
  A⇒U-⊢ : A.⊢ A.Γ →
          A.Γ [↝] U.Γ′ →
          -------
          U.⊢ U.Γ′
  A⇒U-⊢ ⊢[] ↝[] = ⊢[] 
  A⇒U-⊢ (⊢∷ ⊢Γ ⊢T) (↝∷ Γ↝Γ′ T↝T′) = ⊢∷ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se) 

  A⇒U-tm : ∀ {i} → 
           A.Γ A.⊢ A.t ∶[ i ] A.T →
           A.Γ [↝] U.Γ′ →
           A.t ↝ U.t′ →
           A.T ↝ U.T′ →
          -------------
           U.Γ′ U.⊢ U.t′ ∶ U.T′
  A⇒U-tm (N-wf ⊢Γ) Γ↝Γ′ ↝N ↝Se = N-wf (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (Se-wf i ⊢Γ) Γ↝Γ′ ↝Se ↝Se = Se-wf _ (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (Liftt-wf n ⊢T) Γ↝Γ′ (↝Liftt T↝T′) ↝Se = Liftt-wf _ (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se) 
  A⇒U-tm (Π-wf ⊢S ⊢T k≡maxij) Γ↝Γ′ (↝Π S↝S′ T↝T′) ↝Se = Π-wf (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se) k≡maxij 
  A⇒U-tm (vlookup ⊢Γ x∈Γ) Γ↝Γ′ ↝v T↝T′ = vlookup (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-vlookup x∈Γ Γ↝Γ′ T↝T′)
  A⇒U-tm (ze-I ⊢Γ) Γ↝Γ′ ↝ze ↝N = ze-I (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (su-I ⊢t) Γ↝Γ′ (↝su t↝t′) ↝N = su-I (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ ↝N)
  A⇒U-tm (N-E ⊢T ⊢s ⊢r ⊢t) Γ↝Γ′ (↝rec {s′ = r′} {r′ = s′} T↝T′ r↝r′ s↝s′ t↝t′) (↝sub T↝′T′ (↝, ↝I t↝′t′)) 
    with ↝-det t↝′t′ t↝t′ 
       | ↝-det T↝′T′ T↝T′ 
  ... | refl | refl = N-E (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ ↝N) T↝T′ ↝Se) 
                          (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub T↝T′ (↝, ↝I ↝ze)))  
                          (A⇒U-tm ⊢r (↝∷ (↝∷ Γ↝Γ′ ↝N) T↝T′) r↝r′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v))))
                          (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ ↝N) 
  A⇒U-tm (Λ-I {i = j} {j = k} ⊢S ⊢t i≡maxjk) Γ↝Γ′ (↝Λ t↝t′) (↝Π S↝S′ T↝T′) = Λ-I (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)  (A⇒U-tm ⊢t (↝∷ Γ↝Γ′ S↝S′) t↝t′ T↝T′)
  A⇒U-tm (Λ-E {S = S} ⊢S ⊢T ⊢r ⊢s k≡maxij) Γ↝Γ′ (↝$ r↝r′ s↝s′) (↝sub T↝T′ (↝, ↝I s↝′s′)) with ↝-det s↝′s′ s↝s′ 
  ... | refl 
    with ↝-total S 
  ... | S′ , S↝S′ = Λ-E (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se)  (A⇒U-tm ⊢r Γ↝Γ′ r↝r′ (↝Π S↝S′ T↝T′))  (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ S↝S′) 
  A⇒U-tm (L-I n ⊢t) Γ↝Γ′ (↝liftt t↝t′) (↝Liftt T↝T′) = L-I _ (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ T↝T′) 
  A⇒U-tm (L-E n ⊢T ⊢t) Γ↝Γ′ (↝unlift t↝t′) T↝T′ = L-E _ (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se) (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝Liftt T↝T′))
  A⇒U-tm (t[σ] {Δ = Δ} ⊢t ⊢σ) Γ↝Γ′ (↝sub t↝t′ σ↝σ′) (↝sub {t′ = T′} T↝T′ σ↝σ₁′) 
    with ↝-det-s σ↝σ₁′ σ↝σ′ 
       | [↝]-total Δ
  ... | refl 
      | Δ′ , Δ↝Δ′ = t[σ] (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ T↝T′) (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
  A⇒U-tm (conv {S = S} ⊢t S≈T) Γ↝Γ′ t↝t′ T↝T′ with ↝-total S 
  ... | S′ , S↝S′ = conv (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ S↝S′) (A⇒U-≈ S≈T Γ↝Γ′ S↝S′ T↝T′ ↝Se) 

  A⇒U-s : A.Γ A.⊢s A.σ ∶ A.Δ →
          A.Γ [↝] U.Γ′ →
          A.σ ↝s U.σ′ →
          A.Δ [↝] U.Δ′ →
          -------------
          U.Γ′ U.⊢s U.σ′ ∶ U.Δ′ 
  A⇒U-s (s-I ⊢Γ) Γ↝Γ′ ↝I Δ↝Δ′ with [↝]-det Δ↝Δ′ Γ↝Γ′ 
  ... | refl = s-I (A⇒U-⊢ ⊢Γ Γ↝Γ′)  
  A⇒U-s (s-wk (⊢∷ ⊢Γ ⊢t)) (↝∷ Γ↝Γ′ T↝T′) ↝wk Δ↝Δ′ with [↝]-det Δ↝Δ′ Γ↝Γ′
  ... | refl = s-wk (⊢∷ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢t Γ↝Γ′ T↝T′ ↝Se)) 
  A⇒U-s (s-∘ {Γ′ = Σ} ⊢σ ⊢τ) Γ↝Γ′ (↝∘ σ↝σ′ τ↝τ′) Δ↝Δ′ with [↝]-total Σ
  ... | Σ′ , Σ↝Σ′ = s-∘ (A⇒U-s ⊢σ Γ↝Γ′ τ↝τ′ Σ↝Σ′) (A⇒U-s ⊢τ Σ↝Σ′ σ↝σ′ Δ↝Δ′)
  A⇒U-s (s-, ⊢σ ⊢T ⊢t) Γ↝Γ′ (↝, σ↝σ′ t↝t′) (↝∷ Δ↝Δ′ T↝T′) = s-, (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) 
                                                              (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se) 
                                                              (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝sub T↝T′ σ↝σ′))
  A⇒U-s (s-conv ⊢σ x) Γ↝Γ′ σ↝σ′ Δ↝Δ′ = {!   !}

  A⇒U-≈ : ∀ {i} → 
          A.Γ A.⊢ A.t ≈ A.s ∶[ i ] A.T →
          A.Γ [↝] U.Γ′ →
          A.t ↝ U.t′ →
          A.s ↝ U.s′ →
          A.T ↝ U.T′ →
        -------------
          U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′
  A⇒U-≈ (N-[] ⊢σ) Γ↝Γ′ (↝sub ↝N σ↝σ′) ↝N ↝Se = N-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ {!   !})
  A⇒U-≈ (Se-[] i x) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Liftt-[] n x x₁) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Π-[] x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Π-cong x t≈s t≈s₁ x₁) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Liftt-cong n t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (v-≈ x x₁) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (ze-≈ ⊢Γ) Γ↝Γ′ ↝ze ↝ze ↝N = ze-≈ (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-≈ (su-cong t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (rec-cong x t≈s t≈s₁ t≈s₂ t≈s₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Λ-cong ⊢S S≈T t≈s _) Γ↝Γ′ (↝Λ t↝t′) (↝Λ s↝s′) (↝Π S↝S′ T↝T′) = Λ-cong (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) 
                                                                               (A⇒U-≈ t≈s (↝∷ Γ↝Γ′ S↝S′) t↝t′ s↝s′ T↝T′) 
  A⇒U-≈ ($-cong x x₁ t≈s t≈s₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (liftt-cong n t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (unlift-cong n x t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([]-cong t≈s x) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (ze-[] x) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (su-[] x x₁) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (rec-[] x x₁ x₂ x₃ x₄) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Λ-[] x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ($-[] x x₁ x₂ x₃ x₄ x₅) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (liftt-[] n x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (unlift-[] n x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (rec-β-ze x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (rec-β-su x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Λ-β x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (Λ-η x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (L-β n x) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (L-η n x x₁) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([I] x) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([wk] x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([∘] x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([,]-v-ze x x₁ x₂) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ ([,]-v-su x x₁ x₂ x₃) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = {!   !}
  A⇒U-≈ (≈-conv {S = S} t≈s S≈T) Γ↝Γ′ t↝t′ s↝s′ T↝T′ with ↝-total S 
  ... | S′ , S↝S′ = ≈-conv (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ S↝S′)  (A⇒U-≈ S≈T Γ↝Γ′ S↝S′ T↝T′ ↝Se)
  A⇒U-≈ (≈-sym t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = ≈-sym (A⇒U-≈ t≈s Γ↝Γ′ s↝s′ t↝t′ T↝T′)
  A⇒U-≈ (≈-trans {t′ = r} r≈s t≈r) Γ↝Γ′ t↝t′ s↝s′ T↝T′ with ↝-total r 
  ... | r′ , r↝r′ = ≈-trans (A⇒U-≈ r≈s Γ↝Γ′ t↝t′ r↝r′ T↝T′) (A⇒U-≈ t≈r Γ↝Γ′ r↝r′ s↝s′ T↝T′)