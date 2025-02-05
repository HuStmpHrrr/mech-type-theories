
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Equiv  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Statics.Ascribed.CtxEquiv as A
open import NonCumulative.Statics.Ascribed.Properties.Contexts as A
open import NonCumulative.Completeness.Consequences fext
open import NonCumulative.Consequences fext
open import NonCumulative.Statics.Ascribed.Full as A renaming (Ctx to lCtx)
open import NonCumulative.Statics.Ascribed.Simpl
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
  ↝-inv-≈ : ∀ {t₁ t₂ i₁ i₂ T₁ T₂} →
    U.Γ′ U.⊢ U.t′ ∶ U.T′ →
    t₁ ↝ U.t′ → 
    t₂ ↝ U.t′ → 
    A.Γ [↝] U.Γ′ →
    T₁ ↝ U.T′ →
    T₂ ↝ U.T′ →
    A.Γ ⊢ t₁ ∶[ i₁ ] T₁ → 
    A.Γ ⊢ t₂ ∶[ i₂ ] T₂ →
    A.Γ A.⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁
  ↝-inv-≈ = {!   !}

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
  U⇒A-⊢′ : U.⊢ U.Γ′ →
          -------
          ∃ λ Γ → (A.⊢ Γ × Γ [↝] U.Γ′ × (∀ {Γ₁} → Γ₁ [↝] U.Γ′ → A.⊢ Γ₁ → A.⊢ Γ ≈ Γ₁))
  U⇒A-⊢′ ⊢[]       = [] , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }
  U⇒A-⊢′ (⊢∷ ⊢Γ ⊢T)
    with U⇒A-⊢′ ⊢Γ
       | U⇒A-tm′ ⊢T
  ...  | Γ , ⊢Γ , ↝Γ , IHΓ
       | i , Γ′ , T′ , .(Se _) , ↝Γ′ , ↝T , ↝Se , ⊢T , IHT
       with ⊢T:Se-lvl ⊢T
          | presup-tm ⊢T
  ...     | refl
          | ⊢Γ′ , _
          with IHΓ ↝Γ′ ⊢Γ′
  ...        | Γ≈Γ′ = (T′ ↙ _) ∷ Γ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ′) ⊢T) , ↝∷ ↝Γ ↝T , helper
    where helper : ∀ {Γ₁} → Γ₁ [↝] _ → A.⊢ Γ₁ → A.⊢ _ ≈ Γ₁
          helper (↝∷ ↝Γ₁ T₁↝) (⊢∷ ⊢Γ₁ ⊢T₁)
            with IHΓ ↝Γ₁ ⊢Γ₁
               | IHT T₁↝ ⊢T₁
          ...  | Γ≈Γ₁
               | T≈T₁ , refl , _ = ∷-cong-simp Γ≈Γ₁ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈T₁)

  U⇒A-tm′ : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
           ∃₂ λ i Γ → ∃₂ λ t T →
             (Γ [↝] U.Γ′) ×
             (t ↝ U.t′) ×
             (T ↝ U.T′) ×
             Γ A.⊢ t ∶[ i ] T ×
             (∀ {Γ t₁ i₁ T₁} →
                t₁ ↝ U.t′ →
                Γ ⊢ t₁ ∶[ i₁ ] T₁ →
                Γ A.⊢ t ≈ t₁ ∶[ i₁ ] T₁ × i ≡ i₁ × Γ A.⊢ T ≈ T₁ ∶[ 1 + i ] Se i₁)
  U⇒A-tm′ (N-wf ⊢Γ′) = {!   !}
  U⇒A-tm′ (Se-wf i x) = {!   !}
  U⇒A-tm′ (Liftt-wf n ⊢t′) = n , {!   !} 
  U⇒A-tm′ (Π-wf ⊢t′ ⊢t′₁ x) = {!   !}
  U⇒A-tm′ (vlookup x x₁) = {!   !}
  U⇒A-tm′ (ze-I x) = {!   !}
  U⇒A-tm′ (su-I ⊢t′) = {!   !}
  U⇒A-tm′ (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
  U⇒A-tm′ (Λ-I ⊢t′ ⊢t′₁) = {!   !}
  U⇒A-tm′ (Λ-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
  U⇒A-tm′ (L-I n ⊢t′) = {!   !}
  U⇒A-tm′ (L-E n ⊢t′ ⊢t′₁) = {!   !}
  U⇒A-tm′ (t[σ] ⊢t′ x) = {!   !}
  U⇒A-tm′ (conv ⊢t′ x) = {!   !}      

mutual
  U⇒A-⊢ : U.⊢ U.Γ →
          -------
          ∃ λ Γ → A.⊢ Γ × Γ [↝] U.Γ
  U⇒A-⊢ ⊢[] = _ , ⊢[] , ↝[]
  U⇒A-⊢ (⊢∷ {Γ′} {T′} {i = i′} ⊢Γ′ ⊢T′) 
    with U⇒A-tm ⊢T′ 
  ...  | i , Γ , T , .(Se i′) , Γ[↝]Γ′ , T↝T′ , ↝Se , ⊢T 
       with ⊢T:Se-lvl ⊢T
          | presup-tm ⊢T
  ...     | refl
          | ⊢Γ , _ = _ , (⊢∷ ⊢Γ ⊢T , ↝∷ {i = i′} Γ[↝]Γ′ T↝T′)  
 
  U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
           ∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (T ↝ U.T′) × Γ A.⊢ t ∶[ i ] T
  U⇒A-tm (N-wf ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝N , ↝Se , N-wf ⊢Γ
  U⇒A-tm (Se-wf i ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝Se , ↝Se , Se-wf _ ⊢Γ
  U⇒A-tm (Liftt-wf {Γ′} {T′} {i′} n ⊢T′) 
    with U⇒A-tm ⊢T′ 
  ...  | i , Γ , T , _ , Γ↝Γ′ , T↝T′ , ↝Se , ⊢T
       with ⊢T:Se-lvl ⊢T
  ...     | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝Liftt T↝T′ , ↝Se , Liftt-wf _ ⊢T
  U⇒A-tm (Π-wf {Γ′} {S′} {T′} ⊢S′ ⊢T′ k≡maxij) 
    with U⇒A-tm ⊢T′ 
       | U⇒A-tm ⊢S′ 
  ...  | 1+j , .((_ ↙ _) L.∷ _) , T , _ , ↝∷ {T = S} Γ↝Γ′ S↝S′ , T↝T′ , ↝Se , ⊢T 
       | 1+i , Γ₁ , S₁ , _ , Γ↝₁Γ′ , S↝₁S′ , ↝Se , ⊢S   = {!   !} , {!   !} , {!   !} , {!   !} , Γ↝Γ′ , ↝Π S↝₁S′ T↝T′ , ↝Se , Π-wf {!   !} {!   !} {!   !}
  U⇒A-tm (vlookup {x = x} ⊢Γ′ x∈Γ′) with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝Γ′ 
      with U⇒A-vlookup Γ↝Γ′ x∈Γ′
  ...    | i , T , T↝T′ , x∈Γ = _ , _ , _ , _ , Γ↝Γ′ , ↝v , T↝T′ , vlookup ⊢Γ x∈Γ 
  U⇒A-tm (ze-I ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
  ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝ze , ↝N , ze-I ⊢Γ 
  U⇒A-tm (su-I {t = t′} ⊢t) 
    with U⇒A-tm ⊢t 
  ...  | i , Γ , t , N , Γ↝Γ′ , t↝t′ , ↝N , ⊢t 
       with ⊢t∶N-lvl ⊢t 
  ...     | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝su t↝t′ , ↝N , su-I ⊢t
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

  U⇒A-≈ : U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′ →
          ∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ s → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (s ↝ U.s′) × (T ↝ U.T′) × A.Γ A.⊢ t ≈ s ∶[ i ] T
  U⇒A-≈ t≈s = {!   !}       
  
-------- bookmark

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
