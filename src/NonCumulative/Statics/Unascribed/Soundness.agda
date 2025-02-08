
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Soundness  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Statics.Ascribed.CtxEquiv as A
open import NonCumulative.Statics.Ascribed.Refl as A
open import NonCumulative.Statics.Ascribed.Properties.Contexts as A
open import NonCumulative.Statics.Ascribed.Properties as A
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
  U⇒A-⊢ : U.⊢ U.Γ′ →
          -------
          ∃ λ Γ → (A.⊢ Γ × Γ [↝] U.Γ′ × (∀ {Γ₁} → Γ₁ [↝] U.Γ′ → A.⊢ Γ₁ → A.⊢ Γ ≈ Γ₁))
  U⇒A-⊢ ⊢[] = [] , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }
  U⇒A-⊢ (⊢∷ ⊢Γ′ ⊢T′)     
    with U⇒A-⊢ ⊢Γ′
       | U⇒A-tm ⊢T′
  ...  | Γ , ⊢Γ , ↝Γ , IHΓ
       | i , Γ′ , T′ , .(Se _) , ↝Γ′ , ↝T , ↝Se , ⊢T , IHT 
       with ⊢T:Se-lvl ⊢T
          | presup-tm ⊢T
  ...     | refl
          | ⊢Γ′ , _
          with IHΓ ↝Γ′ ⊢Γ′
  ...        | Γ≈Γ′ = (T′ ↙ _) ∷ Γ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ′) ⊢T) , ↝∷ ↝Γ ↝T , helper
    where  helper : ∀ {Γ₁} → Γ₁ [↝] _ → A.⊢ Γ₁ → A.⊢ _ ≈ Γ₁
           helper (↝∷ ↝Γ₁ T₁↝) (⊢∷ ⊢Γ₁ ⊢T₁)
             with IHΓ ↝Γ₁ ⊢Γ₁
           ...  | Γ≈Γ₁ 
            with (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ′) ⊢T₁)
           ... | ⊢T₁′ 
            with IHT T₁↝ ⊢T₁′
           ...  | T≈T₁ 
            with unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
           ... | refl , _ = ∷-cong-simp Γ≈Γ₁ (ctxeq-≈ (⊢≈-sym Γ≈Γ′) T≈T₁)

  U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
          -------------
           ∃₂ λ i Γ → ∃₂ λ t T →
             (Γ [↝] U.Γ′) ×
             (t ↝ U.t′) ×
             (T ↝ U.T′) ×
             Γ A.⊢ t ∶[ i ] T ×
             (∀ {t₁ i₁ T₁} →
                t₁ ↝ U.t′ →
                Γ ⊢ t₁ ∶[ i₁ ] T₁ →
                Γ A.⊢ t ≈ t₁ ∶[ i₁ ] T₁) 
  U⇒A-tm (N-wf ⊢Γ′) 
   with U⇒A-⊢ ⊢Γ′ 
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , _ , Γ↝ , ↝N , ↝Se , N-wf ⊢Γ , λ { ↝N ⊢N → ≈-refl ⊢N }
  U⇒A-tm (Se-wf i ⊢Γ′) 
   with U⇒A-⊢ ⊢Γ′ 
  ...  | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , _ , _ , Γ↝ , ↝Se , ↝Se , Se-wf _ ⊢Γ , λ { ↝Se ⊢Se → ≈-refl ⊢Se }
  U⇒A-tm (Liftt-wf n ⊢T′) 
    with U⇒A-tm ⊢T′
  ... | i , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHT 
    with ⊢T:Se-lvl ⊢T
  ... | refl = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝Liftt t₁↝) ⊢t₁ = {!   !}
  U⇒A-tm (Π-wf ⊢S′ ⊢T′ x) = {!  !}
  U⇒A-tm (vlookup ⊢Γ′ x∈Γ') 
    with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝ , IHΓ
    with U⇒A-vlookup Γ↝ x∈Γ'
  ... | _ , _ , T↝ , x∈Γ = _ , _ , _ , _ , Γ↝ , ↝v , T↝ , vlookup ⊢Γ x∈Γ , λ { ↝v ⊢v → ≈-refl ⊢v }
  U⇒A-tm (ze-I ⊢Γ′) = {!   !}
  U⇒A-tm (su-I {t = t′} ⊢t′) 
    with U⇒A-tm ⊢t′
  ... | _ , Γ , t , .N , Γ↝ , t↝ , ↝N , ⊢t , IHt
    with  ⊢t∶N-lvl ⊢t 
  ... | refl = _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝N , (su-I ⊢t) , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝su t₁↝) ⊢sut₁
            with su-inv ⊢sut₁ 
          ... | refl , T₁≈N , ⊢t₁ = ≈-conv (su-cong (IHt t₁↝ ⊢t₁)) (≈-sym T₁≈N)
  U⇒A-tm (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
  U⇒A-tm (Λ-I {Γ = Γ′} {S = S′} {T = T′} {i = i′} ⊢S′ ⊢t′) 
    with U⇒A-tm ⊢S′ 
       | U⇒A-tm ⊢t′ 
  ... | j , Γ , S , _ , Γ↝Γ′ , S↝S′ , ↝Se , ⊢S , IHS
      | k , _ , t , T , (↝∷ {T = S₁} Γ↝₁Γ′ S↝₁S′) , t↝t′ , T↝T′ , ⊢t , IHt = {!   !} , _ , {!   !} , {!   !} , Γ↝Γ′ , ↝Λ {i = i′} S↝S′ t↝t′ , ↝Π {i = i′} {j = k} S↝S′ T↝T′ , {!   !} , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝Λ {i = i} t₁↝ t₁↝₁) ⊢t₁ 
            with Λ-inv′ ⊢t₁ 
          ... | j₁ , T₁ , T₁≈ , i≡maxj₁ , ⊢t₁′ 
            with presup-tm ⊢t₁′ 
          ... | ⊢∷ ⊢Γ ⊢S₂ , _ 
            with IHS t₁↝ ⊢S₂
          ... | S≈S₂ = ≈-conv (≈-sym {!   !}) (≈-sym T₁≈)
  U⇒A-tm (Λ-E {S = S′} {T = T′} {r = r′} {s = s′} ⊢S′ ⊢T′ ⊢r′ ⊢s′) 
    with U⇒A-tm ⊢S′
  ... | 1+j , Γ , S , _ , Γ↝Γ′ , S↝S′ , ↝Se , ⊢S , IHS 
    with U⇒A-tm ⊢r′
       | U⇒A-tm ⊢s′
  ... | k , Γ₁ , r , _ , Γ↝₁Γ′ , r↝r′ , ↝Π _ T↝T′ , ⊢r , IHr 
      | j , Γ₂ , s , S₁ , Γ↝₂Γ′ , s↝s′ , _ , ⊢s , IHs = {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , ↝$ r↝r′ s↝s′ , ↝sub T↝T′ (↝, ↝I s↝s′) , Λ-E {!   !} {!   !} {!  ⊢r  !} {!   !} {!   !} , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝$ t₁↝ t₁↝₁) ⊢t₁ 
            with $-inv ⊢t₁
          ... | j , k , S , T , ⊢r , ⊢s , i≡maxjk , ≈T[|s] = ≈-conv (≈-sym ($-cong {!   !} {!    !} {!   !} {!   !} i≡maxjk)) (≈-sym ≈T[|s]) 
  U⇒A-tm (L-I n ⊢t′) = {!   !}
  U⇒A-tm (L-E {t = t′} n ⊢T′ ⊢t′) = {!   !}
  U⇒A-tm (t[σ] {Δ = Δ′} {σ = σ′} ⊢t′ ⊢σ′) 
    with U⇒A-tm ⊢t′
       | U⇒A-s-⊢ ⊢σ′ 
  ...  | i , Δ , t , T , Δ↝ , t↝ , T↝ , ⊢t , IHt 
       | Γ , Δ₁ , σ , Γ↝ , Δ↝₁ , σ↝ , ⊢σ , IHσ = {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , ↝sub t↝ σ↝ , ↝sub T↝ σ↝ , t[σ] {!   !} {!   !} , helper
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
          helper (↝sub t₁↝ σ₁↝) ⊢t₁[σ] 
            with t[σ]-inv ⊢t₁[σ] 
          ... | Δ₂ , S , ⊢σ₁ , ⊢t₁ , ≈S[σ₁] = ≈-conv (≈-sym ([]-cong (≈-sym (IHt t₁↝ {!    !})) (s-≈-sym (IHσ σ₁↝ {!   !}) ))) (≈-sym ≈S[σ₁])
  U⇒A-tm (conv {S = S′} ⊢t′ S′≈T′) 
    with U⇒A-tm ⊢t′
       | U⇒A-≈ S′≈T′
  ...  | i , Γ , t , S , Γ↝ , t↝ , S↝ , ⊢t , IHt 
       | 1+i₁ , Γ₁ , S₁ , T , _ , _ , _ , T↝ , ↝Se , T≈S = {!   !} , {!   !} , {!   !} , {!   !} , Γ↝ , t↝ , T↝ , conv ⊢t {!   !} , IHt 

  U⇒A-s-⊢ : U.Γ′ U.⊢s U.σ′ ∶ U.Δ′ →
           ------------------
           ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × (σ ↝s U.σ′) × Γ A.⊢s σ ∶ Δ × 
            (∀ {σ₁ Δ₁} →
                σ₁ ↝s U.σ′ →
                Γ A.⊢s σ₁ ∶ Δ₁ →
                Γ A.⊢s σ ≈ σ₁ ∶ Δ₁)
  U⇒A-s-⊢ (s-I ⊢Γ′)
    with U⇒A-⊢ ⊢Γ′
  ... | Γ , ⊢Γ , Γ↝ , IHΓ = _ , _ , {!   !} , Γ↝ , Γ↝ , ↝I , s-I ⊢Γ ,  λ { ↝I ⊢σ₁ → s-≈-refl ⊢σ₁ }
  U⇒A-s-⊢ (s-wk x) = {!   !}
  U⇒A-s-⊢ (s-∘ ⊢σ′ ⊢σ′₁) = {!   !}
  U⇒A-s-⊢ (s-, {Γ = Γ′} {Δ = Δ′} {T = T′} {t = t′} ⊢σ′ ⊢T′ ⊢t′) 
    with U⇒A-s-⊢ ⊢σ′
       | U⇒A-tm ⊢T′
       | U⇒A-tm ⊢t′
  ... | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ
      | 1+i , Δ₁ , T , _ , Δ₁↝ , T↝ , ↝Se , ⊢T , IHT
      | i , Γ₁ , t , _ , Γ₁↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , IHt = 
        {!   !} , {!   !} , {!   !} , Γ↝ , {!   !} , ↝, {!   !} t↝ , s-, {!   !} {!   !} {!   !} , {!   !}
  U⇒A-s-⊢ (s-conv ⊢σ′ x) = {!   !}

  U⇒A-≈ : U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′ →
          ------------------
          ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] U.Γ′) ×  (t ↝ U.t′) × (s ↝ U.s′) × (T ↝ U.T′) × Γ A.⊢ t ≈ s ∶[ i ] T
  U⇒A-≈ (N-[] ⊢σ′) with U⇒A-s-⊢ ⊢σ′
  ... | Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝N σ↝ , ↝N , ↝Se , N-[] ⊢σ 
  U⇒A-≈ (Se-[] i x) = {!   !}
  U⇒A-≈ (Liftt-[] n x x₁) = {!   !}
  U⇒A-≈ (Π-[] x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Π-cong x t≈s t≈s₁ x₁) = {!   !}
  U⇒A-≈ (Liftt-cong n t≈s) = {!   !}
  U⇒A-≈ (v-≈ x x₁) = {!   !}
  U⇒A-≈ (ze-≈ x) = {!   !}
  U⇒A-≈ (su-cong t≈s) = {!   !}
  U⇒A-≈ (rec-cong x t≈s t≈s₁ t≈s₂ t≈s₃) = {!   !}
  U⇒A-≈ (Λ-cong x t≈s t≈s₁) = {!   !}
  U⇒A-≈ ($-cong x x₁ t≈s t≈s₁) = {!   !}
  U⇒A-≈ (liftt-cong n t≈s) = {!   !}
  U⇒A-≈ (unlift-cong n x t≈s) = {!   !}
  U⇒A-≈ ([]-cong t≈s x) = {!   !}
  U⇒A-≈ (ze-[] x) = {!   !}
  U⇒A-≈ (su-[] x x₁) = {!   !}
  U⇒A-≈ (rec-[] x x₁ x₂ x₃ x₄) = {!   !}
  U⇒A-≈ (Λ-[] x x₁ x₂) = {!   !}
  U⇒A-≈ ($-[] x x₁ x₂ x₃ x₄) = {!   !}
  U⇒A-≈ (liftt-[] n x x₁ x₂) = {!   !}
  U⇒A-≈ (unlift-[] n x x₁ x₂) = {!   !}
  U⇒A-≈ (rec-β-ze x x₁ x₂) = {!   !}
  U⇒A-≈ (rec-β-su x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Λ-β x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (Λ-η x x₁ x₂) = {!   !}
  U⇒A-≈ (L-β n x) = {!   !}
  U⇒A-≈ (L-η n x x₁) = {!   !}
  U⇒A-≈ ([I] x) = {!   !}
  U⇒A-≈ ([wk] x x₁) = {!   !}
  U⇒A-≈ ([∘] x x₁ x₂) = {!   !}
  U⇒A-≈ ([,]-v-ze x x₁ x₂) = {!   !}
  U⇒A-≈ ([,]-v-su x x₁ x₂ x₃) = {!   !}
  U⇒A-≈ (≈-conv t≈s t≈s₁) = {!   !}
  U⇒A-≈ (≈-sym t≈s) = {!   !}
  U⇒A-≈ (≈-trans t≈s t≈s₁) = {!   !}

  U⇒A-s-≈ : U.Γ′ U.⊢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
           ------------------
           ∃₂ λ Γ Δ → ∃₂ λ σ τ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × (σ ↝s U.σ′) × (τ ↝s U.τ′) × Γ A.⊢s σ ≈ τ ∶ Δ
  U⇒A-s-≈ = {!   !}

  U⇒A-⊢≈ : U.⊢ U.Γ′ ≈ U.Δ′ →
          ------------------
           ∃₂ λ Γ Δ → (Γ [↝] U.Γ′) × (Δ [↝] U.Δ′) × A.⊢ Γ ≈ Δ
  U⇒A-⊢≈ = {!   !}

-- mutual
--   U⇒A-⊢′ : U.⊢ U.Γ′ →
--           -------
--           (∃ λ Γ → A.⊢ Γ × Γ [↝] U.Γ′) × (∀ {Γ₁ Γ₂} → Γ₁ [↝] U.Γ′ → Γ₂ [↝] U.Γ′ → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂)
--   U⇒A-⊢′ ⊢[] = (_ , ⊢[] , ↝[]), helper
--     where 
--       helper : ∀ {Γ₁ Γ₂} → Γ₁ [↝] L.[] → Γ₂ [↝] L.[] → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂
--       helper ↝[] ↝[] _ _ = []-≈
--   U⇒A-⊢′ (⊢∷ {Γ′} {T′} {i = i′} ⊢Γ′ ⊢T′) 
--     with U⇒A-tm′ ⊢T′ 
--        | U⇒A-⊢′ ⊢Γ′
--   ... | ( i , Γ , T , .(Se i′) , (Γ[↝]Γ′ , T↝T′ , ↝Se) , ⊢T) , IHT 
--       | _ , IHΓ
--     with ⊢T:Se-lvl ⊢T 
--        | presup-tm ⊢T
--   ...  | refl 
--        | ⊢Γ , _ = (_ , ⊢∷ ⊢Γ ⊢T , ↝∷ {i = i′} Γ[↝]Γ′ T↝T′) , helper 
--     where 
--       helper : ∀ {Γ₁ Γ₂} → Γ₁ [↝] T′ L.∷ Γ′ → Γ₂ [↝] T′ L.∷ Γ′ → A.⊢ Γ₁ → A.⊢ Γ₂ → A.⊢ Γ₁ ≈ Γ₂
--       helper (↝∷ ↝Γ₁ T₁↝) (↝∷ ↝Γ₂ T₂↝) (⊢∷ ⊢Γ₁ ⊢T₁) (⊢∷ ⊢Γ₂ ⊢T₂) 
--         with IHΓ ↝Γ₁ ↝Γ₂ ⊢Γ₁ ⊢Γ₂
--       ... | Γ₁≈Γ₂
--         with ctxeq-tm Γ₁≈Γ₂ ⊢T₁
--       ... | ⊢T₁′
--         with IHT T₁↝ T₂↝ ↝Γ₂ ↝Se ↝Se {!   !} {!   !}
--       ... | b = {!   !}

--   U⇒A-tm′ : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
--           -------------
--            (∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ T → ((Γ [↝] U.Γ′) × (t ↝ U.t′) × (T ↝ U.T′)) × Γ A.⊢ t ∶[ i ] T) × 
--            (∀ {Γ t₁ t₂ i₁ i₂ T₁ T₂} → t₁ ↝ U.t′ → t₂ ↝ U.t′ → Γ [↝] U.Γ′ → 
--             -- cannot have this condition , otherwise cannot be used at 𝟙 
--             T₁ ↝ U.T′ → T₂ ↝ U.T′ → 
--             Γ ⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t₂ ∶[ i₂ ] T₂ → Γ A.⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁)
--   U⇒A-tm′ (N-wf ⊢Γ′) = {!   !} , {!   !} 
--   U⇒A-tm′ (Se-wf i x) = {!   !}
--   U⇒A-tm′ (Liftt-wf n ⊢t′) = n , {!   !} 
--   U⇒A-tm′ (Π-wf ⊢t′ ⊢t′₁ x) = {!   !}
--   U⇒A-tm′ (vlookup x x₁) = {!   !}
--   U⇒A-tm′ (ze-I x) = {!   !}
--   U⇒A-tm′ (su-I ⊢t′) = {!   !}
--   U⇒A-tm′ (N-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
--   U⇒A-tm′ (Λ-I {Γ = Γ′} {S = S′} {t = t′} {T = T′} ⊢S′ ⊢t′) = {!   !} , helper
--     where 
--       helper : ∀ {Γ t₁ t₂ i₁ i₂ T₁ T₂} →
--         t₁ ↝ Λ t′ →
--         t₂ ↝ Λ t′ →
--         Γ [↝] Γ′ →
--         T₁ ↝ Π S′ T′ →
--         T₂ ↝ Π S′ T′ →
--         Γ ⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ t₂ ∶[ i₂ ] T₂ → Γ ⊢ t₁ ≈ t₂ ∶[ i₁ ] T₁
--       helper (↝Λ t₁↝) (↝Λ t₂↝) Γ↝ (↝Π T₁↝ T₁↝₁) (↝Π T₂↝ T₂↝₁) ⊢t₁ ⊢t₂ = {!   !}

--   U⇒A-tm′ (Λ-E ⊢t′ ⊢t′₁ ⊢t′₂ ⊢t′₃) = {!   !}
--   U⇒A-tm′ (L-I n ⊢t′) = {!   !}
--   U⇒A-tm′ (L-E n ⊢t′ ⊢t′₁) = {!   !}
--   U⇒A-tm′ (t[σ] ⊢t′ x) = {!   !}
--   U⇒A-tm′ (conv ⊢t′ x) = {!   !}      

-- mutual
--   U⇒A-⊢ : U.⊢ U.Γ →
--           -------
--           ∃ λ Γ → A.⊢ Γ × Γ [↝] U.Γ
--   U⇒A-⊢ ⊢[] = _ , ⊢[] , ↝[]
--   U⇒A-⊢ (⊢∷ {Γ′} {T′} {i = i′} ⊢Γ′ ⊢T′) 
--     with U⇒A-tm ⊢T′ 
--   ...  | i , Γ , T , .(Se i′) , Γ[↝]Γ′ , T↝T′ , ↝Se , ⊢T 
--        with ⊢T:Se-lvl ⊢T
--           | presup-tm ⊢T
--   ...     | refl
--           | ⊢Γ , _ = _ , (⊢∷ ⊢Γ ⊢T , ↝∷ {i = i′} Γ[↝]Γ′ T↝T′)  
 
--   U⇒A-tm : U.Γ′ U.⊢ U.t′ ∶ U.T′ →
--           -------------
--            ∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (T ↝ U.T′) × Γ A.⊢ t ∶[ i ] T
--   U⇒A-tm (N-wf ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
--   ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝N , ↝Se , N-wf ⊢Γ
--   U⇒A-tm (Se-wf i ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
--   ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝Se , ↝Se , Se-wf _ ⊢Γ
--   U⇒A-tm (Liftt-wf {Γ′} {T′} {i′} n ⊢T′) 
--     with U⇒A-tm ⊢T′ 
--   ...  | i , Γ , T , _ , Γ↝Γ′ , T↝T′ , ↝Se , ⊢T
--        with ⊢T:Se-lvl ⊢T
--   ...     | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝Liftt T↝T′ , ↝Se , Liftt-wf _ ⊢T
--   U⇒A-tm (Π-wf {Γ′} {S′} {T′} ⊢S′ ⊢T′ k≡maxij) 
--     with U⇒A-tm ⊢T′ 
--        | U⇒A-tm ⊢S′ 
--   ...  | 1+j , .((_ ↙ _) L.∷ _) , T , _ , ↝∷ {T = S} Γ↝Γ′ S↝S′ , T↝T′ , ↝Se , ⊢T 
--        | 1+i , Γ₁ , S₁ , _ , Γ↝₁Γ′ , S↝₁S′ , ↝Se , ⊢S   = {!   !} , {!   !} , {!   !} , {!   !} , Γ↝Γ′ , ↝Π S↝₁S′ T↝T′ , ↝Se , Π-wf {!   !} {!   !} {!   !}
--   U⇒A-tm (vlookup {x = x} ⊢Γ′ x∈Γ′) with U⇒A-⊢ ⊢Γ′
--   ... | Γ , ⊢Γ , Γ↝Γ′ 
--       with U⇒A-vlookup Γ↝Γ′ x∈Γ′
--   ...    | i , T , T↝T′ , x∈Γ = _ , _ , _ , _ , Γ↝Γ′ , ↝v , T↝T′ , vlookup ⊢Γ x∈Γ 
--   U⇒A-tm (ze-I ⊢Γ′) with U⇒A-⊢ ⊢Γ′ 
--   ... | Γ , ⊢Γ , Γ↝Γ′ = _ , _ , _ , _ , Γ↝Γ′ , ↝ze , ↝N , ze-I ⊢Γ 
--   U⇒A-tm (su-I {t = t′} ⊢t) 
--     with U⇒A-tm ⊢t 
--   ...  | i , Γ , t , N , Γ↝Γ′ , t↝t′ , ↝N , ⊢t 
--        with ⊢t∶N-lvl ⊢t 
--   ...     | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝su t↝t′ , ↝N , su-I ⊢t
--   U⇒A-tm (N-E ⊢T′ ⊢s′ ⊢r′ ⊢t′) = {!   !}
--   U⇒A-tm (Λ-I {Γ′} {S′} {t′} {T′} {i′} ⊢S′ ⊢t′) 
--     with U⇒A-tm ⊢S′ 
--        | U⇒A-tm ⊢t′
--   ...  | j , Γ , S , _ , Γ↝Γ′ , S↝S′ , ↝Se , ⊢S 
--        | i , _ , t , T , (↝∷ {Γ₁} Γ↝′Γ′ S↝′S′) , t↝t′ , T↝T′ , ⊢t 
--        with A.presup-tm ⊢S 
--           | A.presup-tm ⊢t 
--   ...     | ⊢Γ , _
--           | ⊢∷ ⊢Γ₁ ⊢S₁  , _
--           rewrite [↝]-inv-det ⊢Γ₁ ⊢Γ Γ↝′Γ′ Γ↝Γ′ 
--           with ↝-inv-det S↝′S′ S↝S′ ⊢S₁ ⊢S 
--   ...        | refl = _ , _ , _ , _ , Γ↝Γ′ , ↝Λ t↝t′ , ↝Π S↝S′ T↝T′ , Λ-I ⊢S₁ ⊢t refl
--   U⇒A-tm (Λ-E ⊢S′ ⊢T′ ⊢r′ ⊢s′) = {!   !}
--   U⇒A-tm (L-I {Γ'} {t′} {T′} n ⊢t′) with U⇒A-tm ⊢t′  
--   ... | i , Γ , t , T , Γ↝Γ′ , t↝t′ , T↝T′ , ⊢t = _ , _ , _ , _ , Γ↝Γ′ , ↝liftt t↝t′ , ↝Liftt T↝T′ , L-I _ ⊢t 
--   U⇒A-tm (L-E {Γ'} {T′} {t′} {i′} n ⊢T′ ⊢t′) 
--     with U⇒A-tm ⊢T′ 
--        | U⇒A-tm ⊢t′
--   ...  | i , Γ , T , _ , Γ↝Γ′ , T↝T′ , ↝Se , ⊢T
--        | j , Γ₁ , t , _ , Γ↝′Γ′ , t↝t′ , ↝Liftt T↝′T′ , ⊢t 
--        with A.presup-tm ⊢T 
--           | A.presup-tm ⊢t 
--   ...     | ⊢Γ , _
--           | ⊢Γ₁ , _
--           rewrite [↝]-inv-det ⊢Γ₁ ⊢Γ Γ↝′Γ′ Γ↝Γ′ = {!   !} , {!   !} , {!   !} , {!   !} , Γ↝Γ′ , ↝unlift t↝t′ , {!   !} , L-E {!   !} {!   !} {!   !} 
--   U⇒A-tm (t[σ] {Δ′} {t′} {T′} {Γ′} {σ′} ⊢t′ ⊢σ′) = {!   !}
--   U⇒A-tm (conv ⊢t′ S′≈T′) = {!   !}

--   U⇒A-≈ : U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′ →
--           ∃ λ i → ∃ λ Γ → ∃ λ t → ∃ λ s → ∃ λ T → (Γ [↝] U.Γ′) × (t ↝ U.t′) × (s ↝ U.s′) × (T ↝ U.T′) × A.Γ A.⊢ t ≈ s ∶[ i ] T
--   U⇒A-≈ t≈s = {!   !}       
  
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
  