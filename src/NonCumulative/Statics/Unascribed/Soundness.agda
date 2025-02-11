
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Unascribed.Soundness  (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

open import NonCumulative.Statics.Ascribed.Presup as A
open import NonCumulative.Statics.Ascribed.CtxEquiv as A
open import NonCumulative.Statics.Ascribed.Refl as A
open import NonCumulative.Statics.Ascribed.Misc as A
open import NonCumulative.Statics.Ascribed.Inversion as A
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
 ∃₂ λ i T → (T ↝ U.T′) × (x ∶[ i ] T ∈! A.Γ)
U⇒A-vlookup (↝∷ {Γ′} {Γ} {T′} {T} {i′} Γ↝Γ′ T↝T′) here = _ , _ , (↝sub T↝T′ ↝wk , here) 
U⇒A-vlookup (↝∷ Γ↝Γ′ _) (there x∈Γ') with U⇒A-vlookup Γ↝Γ′ x∈Γ'
... | i , T , T↝T′ , x∈Γ = _ , _ , ↝sub T↝T′ ↝wk , there x∈Γ

unique-lvl : ∀ {i j} →
 A.Γ ⊢ A.t ∶[ i ] A.T →
 A.Γ ⊢ A.t ∶[ j ] A.T′ →
 i ≡ j 
unique-lvl ⊢t ⊢t′ = proj₁ (unique-typ ⊢t ⊢t′)

∷-inv : ∀ {i j} →
 A.⊢ ((A.T ↙ i) ∷ A.Γ) ≈ ((A.S ↙ j) ∷ A.Δ) →
 A.⊢ A.Γ ≈ A.Δ
∷-inv (∷-cong x x₁ x₂ x₃ x₄) = x

∷-inv′ : ∀ {i} →
 A.⊢ ((A.T ↙ i) ∷ A.Γ) ≈ ((A.S ↙ i) ∷ A.Δ) →
 A.⊢ A.Γ ≈ A.Δ
∷-inv′ ⊢s = ∷-inv ⊢s

infix 4 ⫢_ ⫢_≈_ _⫢_∶_ _⫢s_∶_ _⫢_≈_∶_ _⫢s_≈_∶_

⫢_ : U.Ctx → Set
⫢ Γ′ = ∃ λ Γ → (A.⊢ Γ × Γ [↝] Γ′ × (∀ {Γ₁} → Γ₁ [↝] Γ′ → A.⊢ Γ₁ → A.⊢ Γ ≈ Γ₁))

_⫢_∶_ : U.Ctx → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ∶ T′ =  ∃₂ λ i Γ → ∃₂ λ t T → 
                  (Γ [↝] Γ′) ×
                  (t ↝ t′) ×
                  (T ↝ T′) ×
                  Γ A.⊢ t ∶[ i ] T ×
                  (∀ {t₁ i₁ T₁} →
                      t₁ ↝ t′ →
                      Γ ⊢ t₁ ∶[ i₁ ] T₁ →
                      Γ A.⊢ t ≈ t₁ ∶[ i₁ ] T₁)

_⫢s_∶_ : U.Ctx → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ∶ Δ′ = ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × Γ A.⊢s σ ∶ Δ ×
                  (∀ {σ₁ Δ₁} →
                      σ₁ ↝s σ′ →
                      Γ A.⊢s σ₁ ∶ Δ₁ →
                      Γ A.⊢s σ ≈ σ₁ ∶ Δ₁)

⫢_≈_ : U.Ctx → U.Ctx → Set
⫢ Γ′ ≈ Δ′ = ∃₂ λ Γ Δ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × A.⊢ Γ ≈ Δ

_⫢_≈_∶_ : U.Ctx → U.Exp → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ≈ s′ ∶ T′ = ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] Γ′) × (t ↝ t′) × (s ↝ s′) × (T ↝ T′) × Γ A.⊢ t ≈ s ∶[ i ] T

_⫢s_≈_∶_ : U.Ctx → U.Subst → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ≈ τ′ ∶ Δ′ = ∃₂ λ Γ Δ → ∃₂ λ σ τ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × (τ ↝s τ′) × Γ A.⊢s σ ≈ τ ∶ Δ

⫢[] : ⫢ []
⫢[] = _ , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }

⫢[]-≈ : ⫢ [] ≈ []
⫢[]-≈ = _ , _ , ↝[] , ↝[] , []-≈

⫢∷ : ∀ {i} →
      ⫢ U.Γ′ →
      U.Γ′ ⫢ U.T′ ∶ Se i →
      --------------------
      ⫢ U.T′ ∷ U.Γ′
⫢∷ ⫢Γ′ ⫢T′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | i , Γ₁ , T , .(Se _) , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T)) = _ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) , ↝∷ Γ↝ T↝ , helper
    where 
      helper : ∀ { Γᵢ } → Γᵢ [↝] _ → A.⊢ Γᵢ → A.⊢ _ ≈ Γᵢ
      helper (↝∷ {T = Tᵢ} ↝Γᵢ ↝Tᵢ) (⊢∷ ⊢Γᵢ ⊢Tᵢ) 
        with Γ≈Γᵢ ← IHΓ ↝Γᵢ ⊢Γᵢ
        with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γᵢ) Γ≈Γ₁) ⊢Tᵢ) 
        with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ∷-cong-simp Γ≈Γᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈Tᵢ)

⫢∷-cong : ∀ {i} →
          ⫢ U.Γ′ → -- additional premise
          ⫢ U.Δ′ → -- additional premise
          ⫢ U.Γ′ ≈ U.Δ′ →
          U.Γ′ ⫢ U.T′ ∶ Se i →      
          U.Δ′ ⫢ U.S′ ∶ Se i →      
          U.Γ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →      
          U.Δ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →    
          --------------------
          ⫢ U.T′ ∷ U.Γ′ ≈ U.S′ ∷ U.Δ′
⫢∷-cong ⫢Γ′ ⫢Δ′ Γ′≈Δ′ ⫢T′ ⫢S′ Γ⫢T≈S′ Δ⫢T≈S′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
  with Γ₁ , Δ₁ , Γ₁↝ , Δ₁↝ , Γ₁≈Δ₁ ← Γ′≈Δ′
     | _ , Γ₂ , T , _ , Γ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , Γ₃ , T₁ , S₁ , _ , Γ₃↝ , T↝₁ , S↝₁ , ↝Se , T₁≈S₁  ← Γ⫢T≈S′
  with refl ← ⊢T:Se-lvl ⊢T
  with refl ← ⊢T:Se-lvl ⊢S 
  with ⊢Γ₃ , ⊢T₁ , ⊢S₁ , _  ← presup-≈ T₁≈S₁
  with ⊢Γ₁ , ⊢Δ₁ ← presup-⊢≈ Γ₁≈Δ₁
  with refl ← ⊢T:Se-lvl ⊢T₁
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ (proj₁ (presup-tm ⊢T))  
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃  
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-tm ⊢S))
  with Γ≈Δ ← ⊢≈-trans Γ≈Γ₁ (⊢≈-trans Γ₁≈Δ₁ (⊢≈-sym Δ≈Δ₁))
  with T≈T₁ ← IHT T↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃)  Γ≈Γ₂) ⊢T₁)
     | S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) (⊢≈-trans Γ≈Δ Δ≈Δ₂)) ⊢S₁)
  = _ , _ , ↝∷ Γ↝ T↝ , ↝∷ Δ↝ S↝ , ∷-cong-simp Γ≈Δ (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) T≈T₁) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) T₁≈S₁) (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₂) (⊢≈-sym Γ≈Δ)) (≈-sym S≈S₁) )))  

⫢N-wf : ⫢ U.Γ′ →
        U.Γ′ ⫢ N ∶ Se 0
⫢N-wf ⫢Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝N , ↝Se , N-wf ⊢Γ , λ { ↝N ⊢N → ≈-refl ⊢N }

⫢Se-wf : ∀ {i} →
         ⫢ U.Γ′ →
         U.Γ′ ⫢ Se i ∶ Se (1 + i)
⫢Se-wf ⫢Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝Se , ↝Se , Se-wf _ ⊢Γ , λ { ↝Se ⊢Se → ≈-refl ⊢Se }

⫢Liftt-wf : ∀ {i n} →
            U.Γ′ ⫢ U.T′ ∶ Se i →
            U.Γ′ ⫢ Liftt n U.T′ ∶ Se (n + i)
⫢Liftt-wf ⫢T′ 
  with _ , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , helper
    where 
      helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
      helper (↝Liftt t₁↝) ⊢Liftt₁ 
        with Liftt-inv′ ⊢Liftt₁ 
      ... | refl , ⊢Tᵢ , ≈Se 
        with IHT t₁↝ ⊢Tᵢ
      ... | T≈Tᵢ 
        with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
      ... | refl = ≈-conv (Liftt-cong _ T≈Tᵢ) (≈-sym ≈Se)

⫢Π-wf : ∀ {i j k} →
        ⫢ U.Γ′ → 
        U.Γ′ ⫢ U.S′ ∶ Se i →
        (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
        k ≡ max i j →
        --------------------
        U.Γ′ ⫢ Π U.S′ U.T′ ∶ Se k
⫢Π-wf ⫢Γ′ ⫢S′ ⫢T′ k≡maxij
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ↝₁ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , _ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₂ S↝₁) , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
  with ⊢T:Se-lvl ⊢S
     | ⊢T:Se-lvl ⊢T
...  | refl | refl
  with ⊢∷ ⊢Γ₂ ⊢S₂ ← proj₁ (presup-tm ⊢T)
  with IHΓ Γ↝₁ (proj₁ (presup-tm ⊢S))
     | IHΓ Γ↝₂ ⊢Γ₂
...  | Γ≈Γ₁ | Γ≈Γ₂
  with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
  with IHS S↝₁ (ctxeq-tm Γ₁≈Γ₂ ⊢S₂)
...  | S≈S₂
  with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
...  | refl = _ , _ , _ , _ , Γ↝ , ↝Π S↝ T↝ , ↝Se , Π-wf (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (⊢≈-sym S∷Γ≈S₂∷Γ₂) ⊢T) k≡maxij , helper
  where 
    S∷Γ≈S₂∷Γ₂ : A.⊢ (S ↙ _) L.∷ Γ ≈ (S₁ ↙ _) L.∷ _
    S∷Γ≈S₂∷Γ₂ = ∷-cong Γ≈Γ₂ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) ⊢S₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) S≈S₂)

    helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    helper (↝Π S₁↝ T₁↝) ⊢Πt₁
      with Π-inv′ ⊢Πt₁
    ...  | refl , ≈Se , ⊢S₁ , ⊢T₁
      with IHS S₁↝ (ctxeq-tm Γ≈Γ₁ ⊢S₁)
    ...  | S≈S₁
      with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
    ...  | refl
      with S₁≈S₂ ← ≈-trans (≈-sym S≈S₁) S≈S₂
      with IHT T₁↝ (ctxeq-tm (∷-cong Γ≈Γ₂ ⊢S₁ ⊢S₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁≈S₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) S₁≈S₂)) ⊢T₁)
    ...  | T≈T₁
      with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    ...  | refl = ≈-conv (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₁) (ctxeq-≈ (⊢≈-sym S∷Γ≈S₂∷Γ₂) T≈T₁) refl) (≈-sym ≈Se)

⫢vlookup : ∀ {x} →
           ⫢ U.Γ′ →
           x ∶ U.T′ ∈! U.Γ′ →
           ------------
           U.Γ′ ⫢ v x ∶ U.T′
⫢vlookup ⫢Γ′ x∈Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
  with  _ , _ , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , Γ↝ , ↝v , T↝ , vlookup ⊢Γ x∈Γ , λ { ↝v ⊢v → ≈-refl ⊢v }

⫢ze-I : ⫢ U.Γ′ →
      U.Γ′ ⫢ ze ∶ N
⫢ze-I ⫢Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝ze , ↝N , ze-I ⊢Γ , λ { ↝ze ⊢ze → ≈-refl ⊢ze }

⫢su-I : U.Γ′ ⫢ U.t′ ∶ N → 
        U.Γ′ ⫢ su U.t′ ∶ N
⫢su-I ⫢t′ 
  with _ , Γ , t , .N , Γ↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′ 
  with  ⊢t∶N-lvl ⊢t
...  | refl = _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝N , (su-I ⊢t) , helper
  where 
    helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    helper (↝su t₁↝) ⊢sut₁
      with su-inv ⊢sut₁
    ...  | refl , T₁≈N , ⊢t₁ = ≈-conv (su-cong (IHt t₁↝ ⊢t₁)) (≈-sym T₁≈N)

⫢N-E : ∀ {i} →
        ⫢ U.Γ′ →
        (N ∷ U.Γ′) ⫢ U.T′ ∶ Se i →
        U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
        (U.T′ ∷ N ∷ U.Γ′) ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
        U.Γ′ ⫢ U.t′ ∶ N →
        --------------------------
        U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ U.[| U.t′ ∶ N ]
⫢N-E ⫢Γ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , _ , T , _ , (↝∷ Γ₁↝ ↝N) , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | j , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T↝₁ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
     | k , _ , r , _ , (↝∷ {T = T₃} (↝∷ Γ₃↝ ↝N) T↝₃) , r↝ , ↝sub {t = T₂} T↝₂ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
     | _ , Γ₄ , t , _ , Γ₄↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
  with (⊢∷ {Γ = Γ₁} ⊢Γ₁ ⊢N₁) ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ , ⊢T₁[|ze] ← presup-tm ⊢s
     | (⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃) , ⊢T₁[wkwk,ze] ← (presup-tm ⊢r) 
  with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
  with refl ← ⊢T:Se-lvl ⊢T
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ (proj₁ (presup-tm ⊢s))
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
     | Γ≈Γ₄ ← IHΓ Γ₄↝ (proj₁ (presup-tm ⊢t))
  with IHT T↝₃ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₃) )) ⊢T₃)
...  | T≈T₃
  with refl , _ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃))) = _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ t↝ , ↝sub T↝ (↝, ↝I t↝ ↝N) , 
    (N-E ((ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₁))) ⊢T)) ⊢s_ ⊢r_ ⊢t_) , helper 
  where
    ⊢s_ : Γ ⊢ s ∶[ _ ] T A.[| ze ∶ N₀ ]
    ⊢s_
      with t[σ]-inv ⊢T₁[|ze]
    ... | Γ₂∷N , _ , ⊢[|ze] , ⊢T₁ , _
      with ,-inv ⊢[|ze]
    ... | Γ₅ , ⊢I , ⊢ze , N∷Γ₅≈N∷Δ
      with ∷-cong Γ₅≈Δ _ _ T′1≈N _ ← N∷Γ₅≈N∷Δ
      with refl , _ ← ze-inv ⊢ze
      with _ , ∷-cong Γ₂≈Δ _ _ _ _ ← ,-inv′ ⊢[|ze] (s-I ⊢Γ₂)
      with Γ₂≈Γ₅ ← ⊢≈-trans Γ₂≈Δ (⊢≈-sym Γ₅≈Δ)
      with Γ₅≈Γ ← ⊢≈-trans (⊢≈-sym Γ₂≈Γ₅) (⊢≈-sym Γ≈Γ₂) 
      with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
      with T≈T₁ ← IHT T↝₁ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ₂≈Δ) (⊢≈-sym Γ₁≈Γ₂)) (ctxeq-≈ Γ₅≈Δ (≈-sym T′1≈N) )) ⊢T₁) 
      with refl , Sej≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) = 
        ctxeq-tm (⊢≈-sym Γ≈Γ₂) (conv ⊢s ([]-cong-Se (≈-conv (≈-sym T≈T₁) (≈-sym Sej≈)) Γ₂⊢I,ze (s-≈-refl Γ₂⊢I,ze)))
      where Γ₂⊢I,ze = s-, (s-conv (s-I ⊢Γ₂) (⊢≈-sym Γ₁≈Γ₂)) (N-wf ⊢Γ₁) (conv (ze-I ⊢Γ₂) (≈-sym ([I] (N-wf ⊢Γ₂) ))) 

    ⊢r_ : (T ↙ _) L.∷ N₀ L.∷ Γ ⊢ r ∶[ _ ] sub T ((wk ∘ wk) , su (v 1) ∶ N₀)
    ⊢r_
      with t[σ]-inv  ⊢T₁[wkwk,ze]
    ...  | Γ₃∷N∷T , _ , ⊢wkwk,ze , ⊢T₁ , _
      with ,-inv  ⊢wkwk,ze
    ...  | Γ₆ , ⊢wkwk1 , ⊢su , ∷-cong Γ₆≈Δ _ _ N≈T′ _ 
      with ⊢TNΓ₃ ← ⊢wk∘wk-gen (proj₁ (presup-tm ⊢r))
      with Γ₃≈Δ ← ∷-inv′ (proj₂ (,-inv′ ⊢wkwk,ze ⊢TNΓ₃))
      with Γ≈Δ ← ⊢≈-trans Γ≈Γ₃ Γ₃≈Δ
      with Γ≈Γ₆ ← ⊢≈-trans Γ≈Δ (⊢≈-sym Γ₆≈Δ)
      with Γ₁≈Γ₃ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₃
      with su-inv ⊢su
    ...  | refl , _ , _ 
      with T≈T₂ ← IHT T↝₂ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Δ) Γ≈Γ₁) (ctxeq-≈ Γ₆≈Δ (≈-sym N≈T′))) ⊢T₁) 
      with unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
    ...  | refl , Sej≈ = ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl (N-wf ⊢Γ₃))) (ctxeq-≈ (∷-cong-simp Γ₁≈Γ₃ (≈-refl (N-wf ⊢Γ₁))) (≈-sym T≈T₃))) (conv ⊢r ([]-cong-Se (≈-conv (≈-sym T≈T₂) (≈-sym Sej≈)) Γ₃⊢wkwk,su (s-≈-refl Γ₃⊢wkwk,su)))
      where Γ₃⊢wkwk,su = s-, (s-conv ⊢TNΓ₃ (⊢≈-sym Γ₁≈Γ₃)) (N-wf ⊢Γ₁) ⊢su
      
    ⊢t_ : Γ ⊢ t ∶[ _ ] N
    ⊢t_
      with refl ← ⊢t∶N-lvl ⊢t = (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢t)

    helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    helper (↝rec ↝Tᵢ ↝sᵢ ↝rᵢ ↝tᵢ) ⊢rectᵢ 
      with rec-inv ⊢rectᵢ
    ...  | refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , Tᵢ≈
      with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁)  (≈-refl (N-wf ⊢Γ₁) )
         | N∷Γ≈N∷Γ₃ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₃)  (≈-refl (N-wf ⊢Γ₃) )
      with IHT ↝Tᵢ (ctxeq-tm (⊢≈-sym N∷Γ≈N∷Γ₁) ⊢Tᵢ)
    ...  | T≈Tᵢ
      with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
    ...  | refl
      with IHs ↝sᵢ (ctxeq-tm Γ≈Γ₂ ⊢sᵢ)
         | IHr ↝rᵢ (ctxeq-tm (∷-cong-simp (⊢≈-sym N∷Γ≈N∷Γ₃) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-trans (≈-sym T≈Tᵢ ) T≈T₃)) ) ⊢rᵢ)
         | IHt ↝tᵢ (ctxeq-tm Γ≈Γ₄ ⊢tᵢ)
    ...  | s≈sᵢ | r≈rᵢ | t≈tᵢ = ≈-conv (≈-sym (rec-cong ⊢Tᵢ (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈Tᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym s≈sᵢ)) (ctxeq-≈ (∷-cong-simp N∷Γ≈N∷Γ₃ (ctxeq-≈ (⊢≈-trans N∷Γ≈N∷Γ₁ (⊢≈-sym N∷Γ≈N∷Γ₃)) (≈-trans (≈-sym T≈T₃) T≈Tᵢ) )) (≈-sym r≈rᵢ))  (ctxeq-≈ (⊢≈-sym Γ≈Γ₄) (≈-sym t≈tᵢ)) ) ) (≈-sym Tᵢ≈)

⫢Λ-I : ∀ {i} →
       ⫢ U.Γ′ →
       U.Γ′ ⫢ U.S′ ∶ Se i →
       (U.S′ ∷ U.Γ′) ⫢ U.t′ ∶ U.T′ →
       --------------------
       U.Γ′ ⫢ Λ U.S′ U.t′ ∶ Π U.S′ U.T′
⫢Λ-I {i = i} ⫢Γ′ ⫢S′ ⫢t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ↝₁ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | k , _ , t , T , (↝∷ {T = S₁} Γ↝₂ S↝₁) , t↝ , T↝ , ⊢t , IHt ← ⫢t′ 
  with ⊢∷ ⊢Γ₂ ⊢S₂ ← proj₁ (presup-tm ⊢t)
  with Γ≈Γ₁ ← IHΓ Γ↝₁ (proj₁ (presup-tm ⊢S))
     | Γ≈Γ₂ ← IHΓ Γ↝₂ ⊢Γ₂
  with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
  with S≈S₂ ← IHS S↝₁ (ctxeq-tm Γ₁≈Γ₂ ⊢S₂)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
  with refl ← ⊢T:Se-lvl ⊢S = _ , _ , _ , _ , Γ↝ , ↝Λ S↝ t↝ , ↝Π {i = i} {j = k} S↝ T↝ , Λ-I (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) (≈-sym S≈S₂) )) ⊢t) refl , helper
    where 
      helper : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
      helper (↝Λ {i = i} Sᵢ↝ tᵢ↝) ⊢Λtᵢ
        with Λ-inv′ ⊢Λtᵢ
      ... | jᵢ , Tᵢ , Tᵢ≈ , i≡maxjᵢ , ⊢tᵢ
        with presup-tm ⊢tᵢ
      ... | ⊢∷ ⊢Γ ⊢Sᵢ , _
        with IHS Sᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢Sᵢ)
      ... | S≈Sᵢ
        with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ)))
      ... | refl
        with S∷Γ≈S₂∷Γ₂ ← ∷-cong-simp Γ≈Γ₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans (≈-sym S≈Sᵢ) S≈S₂))
        with IHt tᵢ↝ (ctxeq-tm S∷Γ≈S₂∷Γ₂ ⊢tᵢ)
      ... | t≈tᵢ = ≈-conv (≈-sym (Λ-cong ⊢Sᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈Sᵢ)) (ctxeq-≈ (⊢≈-sym S∷Γ≈S₂∷Γ₂) (≈-sym t≈tᵢ)) i≡maxjᵢ)) (≈-sym Tᵢ≈)

⫢s-I : ⫢ U.Γ′ →
       --------------------
       U.Γ′ ⫢s I ∶ U.Γ′
⫢s-I ⫢Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , Γ↝ , Γ↝ , ↝I , s-I ⊢Γ , λ { ↝I ⊢σ₁ → s-≈-refl ⊢σ₁ }

⫢s-wk : ⫢ U.T′ ∷ U.Γ′ →
        --------------------
        U.T′ ∷ U.Γ′ ⫢s wk ∶ U.Γ′
⫢s-wk ⫢T∷Γ′
  with .((_ ↙ _) L.∷ _) , ⊢∷ ⊢Γ ⊢T , ↝∷ Γ↝ T↝ , IHΓ ← ⫢T∷Γ′ = _ , _ , _ , ↝∷ Γ↝ T↝ , Γ↝ , ↝wk , s-wk (⊢∷ ⊢Γ ⊢T) , λ { ↝wk ⊢σ₁ → s-≈-refl ⊢σ₁ }

⫢s-∘ :  ⫢ U.Δ′ → -- new condition
        U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
        U.Δ′ ⫢s U.τ′ ∶ U.Ψ′ →
        --------------------
        U.Γ′ ⫢s U.τ′ ∘ U.σ′ ∶ U.Ψ′
⫢s-∘ ⫢Δ′ ⫢σ′ ⫢τ′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHτ ← ⫢σ′
     | Δ₂ , Ψ , τ , Δ₂↝ , Ψ↝ , τ↝ , ⊢τ , IHσ ← ⫢τ′
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-s ⊢τ))
    = _ , _ , _ , Γ↝ , Ψ↝ , ↝∘ τ↝ σ↝ , s-∘ ⊢σ (ctxeq-s (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢τ) , helper 
  where helper :  (∀ {σᵢ Δᵢ} →  σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
        helper (↝∘ {σ = τᵢ} {τ = σᵢ} τᵢ↝ σᵢ↝) ⊢σᵢ∘τᵢ 
          with ∘-inv ⊢σᵢ∘τᵢ 
        ...  | Ψᵢ , ⊢σᵢ , ⊢τᵢ 
          with σ≈σᵢ ← (IHτ σᵢ↝ ⊢σᵢ) 
          with Δ₁≈Ψᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
          with Δ₂≈Ψᵢ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) (⊢≈-trans Δ≈Δ₁ Δ₁≈Ψᵢ)
          with τ≈τᵢ ← IHσ τᵢ↝ (ctxeq-s (⊢≈-sym Δ₂≈Ψᵢ) ⊢τᵢ) = ∘-cong σ≈σᵢ (ctxeq-s-≈ Δ₂≈Ψᵢ τ≈τᵢ)

⫢s-, : ∀ {i} → 
       ⫢ U.Γ′ →
       ⫢ U.Δ′ →
       U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
       U.Δ′ ⫢ U.T′ ∶ Se i →
       U.Γ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
       -------------------------
       U.Γ′ ⫢s U.σ′ , U.t′ ∶ U.T′ ∶ U.T′ ∷ U.Δ′
⫢s-, ⫢Γ′ ⫢Δ′ ⫢σ′ ⫢T′ ⫢t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | i , Γ₂ , t , _ , Γ₂↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T
  with IHΓ Γ₁↝ (proj₁ (presup-s ⊢σ))
     | IHΓ Γ₂↝ (proj₁ (presup-tm ⊢t))
...  | Γ≈Γ₁ | Γ≈Γ₂
  with IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
     | IHΔ Δ₂↝ (proj₁ (presup-tm ⊢T))
...  | Δ≈Δ₁ | Δ≈Δ₂ = _ , _ , _ , Γ↝ , ↝∷ Δ↝ T↝ , (↝, σ↝ t↝ T↝) , s-, (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) ⊢t_ , helper
  where
    ⊢t_ : Γ ⊢ t ∶[ _ ] sub T σ
    ⊢t_   
      with ⊢T₁[σ] ← proj₂ (presup-tm ⊢t)
      with Δ₃ , S , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ] 
      with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
      with σ≈σ₁ ← IHσ σ↝₁ (ctxeq-s (⊢≈-sym Γ₁≈Γ₂) ⊢σ₁) 
      with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
      with Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) Δ₁≈Δ₃
      with T≈T₁ ← IHT T↝₁ (ctxeq-tm (⊢≈-sym Δ₂≈Δ₃) ⊢T₁) 
      with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) = 
          ctxeq-tm (⊢≈-sym Γ≈Γ₂) (conv ⊢t ([]-cong-Se (ctxeq-≈ Δ₂≈Δ₃ (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se)))  ⊢σ₁ (ctxeq-s-≈ Γ₁≈Γ₂ (s-≈-sym σ≈σ₁))))

    helper :  (∀ {σᵢ Δᵢ} →  σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
    helper (↝, {σ = σᵢ} {t = tᵢ} {T = Tᵢ} σᵢ↝ tᵢ↝ Tᵢ↝) ⊢σᵢ, 
      with ,-inv ⊢σᵢ, 
    ...  | Δᵢ , ⊢σᵢ , ⊢tᵢ , ≈T∷Δᵢ 
      with ⊢Tᵢ[σᵢ] ← proj₂ (presup-tm ⊢tᵢ)
      with S , ⊢Tᵢ , Seᵢ≈S[σᵢ] ← t[σ]-inv′ ⊢Tᵢ[σᵢ] ⊢σᵢ 
      with σ≈σᵢ ← IHσ σᵢ↝ (ctxeq-s Γ≈Γ₁ ⊢σᵢ)
      with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
      with Δ₂≈Δᵢ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) (⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ)
      with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ₂≈Δᵢ) ⊢Tᵢ)
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢tᵢ)
      with refl , Sei≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) 
      with Δᵢ⊢T≈Tᵢ ← ctxeq-≈ Δ₂≈Δᵢ (≈-conv T≈Tᵢ (≈-sym Sei≈)) =  
        s-≈-conv (,-cong (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) σ≈σᵢ) (ctxeq-tm Δ₂≈Δᵢ ⊢T) Δᵢ⊢T≈Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) 
                         (≈-conv t≈tᵢ ([]-cong-Se (≈-sym Δᵢ⊢T≈Tᵢ) (ctxeq-s Γ≈Γ₂ ⊢σᵢ) (ctxeq-s-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂) (s-≈-sym σ≈σᵢ)))
                         ))) 
                 (⊢≈-trans (∷-cong-simp (⊢≈-refl (proj₂ (presup-s ⊢σᵢ))) Δᵢ⊢T≈Tᵢ) ≈T∷Δᵢ)

⫢s-conv : ⫢ U.Δ′ →
          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
          ⫢ U.Δ′ ≈ U.Ψ′ →
          -------------------------
          U.Γ′ ⫢s U.σ′ ∶ U.Ψ′
⫢s-conv ⫢Δ′ ⫢σ′ Δ′≈Ψ′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | Δ₂ , Ψ , Δ₂↝ , Ψ↝ , Δ₂≈Ψ ← Δ′≈Ψ′ 
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-⊢≈ Δ₂≈Ψ))
     = _ , _ , _ , Γ↝ , Ψ↝ , σ↝ , s-conv ⊢σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) (⊢≈-trans Δ≈Δ₂ Δ₂≈Ψ)) , IHσ

⫢N-[] : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
        --------------------
        U.Γ′ ⫢ N U.[ U.σ′ ] ≈ N ∶ Se 0
⫢N-[] ⫢σ′
  with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝N σ↝ , ↝N , ↝Se , N-[] ⊢σ

⫢Se-[] : ∀ {i} →
          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
          --------------------
          U.Γ′ ⫢ Se i U.[ U.σ′ ] ≈ Se i ∶ Se (1 + i)
⫢Se-[] ⫢σ′
  with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝Se σ↝ , ↝Se , ↝Se , Se-[] _ ⊢σ

⫢Liftt-[] : ∀ {i j} →
            ⫢ U.Δ′ →
            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
            U.Δ′ ⫢ U.T′ ∶ Se i →
            --------------------
            U.Γ′ ⫢ Liftt j U.T′ U.[ U.σ′ ] ≈ Liftt j (U.T′ U.[ U.σ′ ]) ∶ Se (j + i)
⫢Liftt-[] ⫢Δ′ ⫢σ′ ⫢T′ 
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-tm ⊢T))
     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Liftt T↝) σ↝ , ↝Liftt (↝sub T↝ σ↝) , ↝Se , Liftt-[] _ ⊢σ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢T)

⫢Π-cong : ∀ {i j k S₁′ S₂′ T₁′ T₂′} →
           ⫢ U.Γ′ → -- new condition
           U.Γ′ ⫢ S₁′ ∶ Se i →
           U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
           S₁′ ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se j →
           k ≡ max i j →
           --------------------
           U.Γ′ ⫢ Π S₁′ T₁′ ≈ Π S₂′ T₂′ ∶ Se k
⫢Π-cong ⫢Γ′ ⫢S₁′ S₁′≈S₂′ T₁′≈T₂′ k≡maxij
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S₁₁ , _ , Γ₁↝ , S₁₁↝ , ↝Se , ⊢S₁ , IHS₁ ← ⫢S₁′
     | _ , Γ₂ , S₁₂ , S₂₁ , _ , Γ₂↝ , S₁₂↝ , S₂₁↝ , ↝Se , S₁₂≈S₂₁ ← S₁′≈S₂′
     | _ , S∷Γ₃ , T₁₁ , T₂₁ , _ , (↝∷ {T = S₁₃} Γ₃↝ S₁₃↝)  , T₁₁↝ , T₂₁↝ , ↝Se , T₁₁≈T₂₁ ← T₁′≈T₂′
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢S₁)
     | ⊢Γ₂ , ⊢S₁₂ , _ ← presup-≈ S₁₂≈S₂₁
     | ⊢∷ ⊢Γ₃ ⊢S₁₃ ← proj₁ (presup-≈ T₁₁≈T₂₁)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
  with refl ← ⊢T:Se-lvl ⊢S₁
     | refl ← ⊢T≈S:Se-lvl S₁₂≈S₂₁
     | refl ← ⊢T≈S:Se-lvl T₁₁≈T₂₁ 
  with Γ₂≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
     | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with S₁≈S₁₂ ← IHS₁ S₁₂↝ (ctxeq-tm Γ₂≈Γ₁ ⊢S₁₂)
     | S₁≈S₁₃ ← IHS₁ S₁₃↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₁₃) 
  with refl ← unique-lvl ⊢S₁ (proj₁ (proj₂ (presup-≈ S₁≈S₁₃))) =
        _ , _ , _ , _ , _ , Γ↝ , ↝Π S₁₁↝ T₁₁↝ , ↝Π S₂₁↝ T₂₁↝ , ↝Se , 
          Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans S₁≈S₁₂ (ctxeq-≈ Γ₂≈Γ₁ S₁₂≈S₂₁))) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁≈S₁₃))) T₁₁≈T₂₁) k≡maxij  

⫢Liftt-cong : ∀ {i j} →
              U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
              --------------------
              U.Γ′ ⫢ Liftt j U.S′ ≈ Liftt j U.T′ ∶ Se (j + i)
⫢Liftt-cong S′≈T′ 
  with _ , Γ , S , T , _ , Γ↝ , S↝ , T↝ , ↝Se , S≈T ← S′≈T′ 
  with refl ← ⊢T≈S:Se-lvl S≈T = _ , _ , _ , _ , _ , Γ↝ , ↝Liftt S↝ , ↝Liftt T↝ , ↝Se , Liftt-cong _ S≈T

⫢v-≈ : ∀ {x} →
       ⫢ U.Γ′ →
       x ∶ U.T′ ∈! U.Γ′ →
       --------------------
       U.Γ′ ⫢ v x ≈ v x ∶ U.T′
⫢v-≈ ⫢Γ′ x∈Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
  with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , _ , Γ↝ , ↝v , ↝v , T↝ , v-≈ ⊢Γ x∈Γ

⫢rec-cong : ∀ {i j s₁′ s₂′ r₁′ r₂′ t₁′ t₂′} →
            ⫢ U.Γ′ → -- extra condition
            N ∷ U.Γ′ ⫢ U.S′ ∶ Se i →
            N ∷ U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se j →
            U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ U.T′ U.[| ze ∶ N ] →
            U.T′ ∷ N ∷ U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
            U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ N →
            --------------------
            U.Γ′ ⫢ rec U.T′ s₁′ r₁′ t₁′ ≈ rec U.S′ s₂′ r₂′ t₂′ ∶ U.T′ U.[| t₁′ ∶ N ]
⫢rec-cong = {!   !}

⫢Λ-cong : ∀ {i S₁′ S₂′ t₁′ t₂′} →
           ⫢ U.Γ′ → -- extra condition
           U.Γ′ ⫢ S₁′ ∶ Se i →
           U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
           (S₁′ ∷ U.Γ′) ⫢ t₁′ ≈ t₂′ ∶ U.T′ →
           --------------------
           U.Γ′ ⫢ Λ S₁′ t₁′ ≈ Λ S₂′ t₂′ ∶ Π S₁′ U.T′
⫢Λ-cong ⫢Γ′ ⫢S₁′ S₁′≈S₂′ ⫢t₁′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S₁₁ , _ , Γ₁↝ , S₁↝ , ↝Se , ⊢S₁₁ , IHS₁ ← ⫢S₁′
     | _ , Γ₂ , S₁₂ , S₂₁ , _ , Γ₂↝ , S₁₂↝ , S₂₁↝ , ↝Se , S₁≈S₂ ← S₁′≈S₂′
     | _ , S∷Γ₃ , t₁ , t₂ , T , ↝∷ {T = S₁₃} Γ₃↝ S₁₃↝ , t₁↝ , t₂↝ , T↝ , t₁≈t₂ ← ⫢t₁′
  with refl ← ⊢T:Se-lvl ⊢S₁₁
     | refl ← ⊢T≈S:Se-lvl S₁≈S₂ 
  with ⊢∷ ⊢Γ₃ ⊢S₁₃ ← proj₁ (presup-≈ t₁≈t₂)
     | ⊢Γ₂ , ⊢S₁₂ , _ ← presup-≈ S₁≈S₂
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢S₁₁))
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
  with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with S₁₁≈S₁₂ ← IHS₁ S₁₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢S₁₂)
     | S₁₁≈S₁₃ ← IHS₁ S₁₃↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₁₃) 
  with refl ← unique-lvl ⊢S₁₁ (proj₁ (proj₂ (presup-≈ S₁₁≈S₁₃)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝Λ S₁↝ t₁↝ , ↝Λ S₂₁↝ t₂↝ , ↝Π S₁↝ T↝ , 
          Λ-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁₁) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁₁≈S₁₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) S₁≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁₁≈S₁₃))) t₁≈t₂) refl

⫢$-cong : ∀ {i j s₁′ s₂′ r₁′ r₂′} →
           ⫢ U.Γ′ → -- extra condition
           U.Γ′ ⫢ U.S′ ∶ Se i →
           (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
           U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ Π U.S′ U.T′ →
           U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ U.S′ →
           --------------------
           U.Γ′ ⫢ r₁′ $ s₁′ ≈ r₂′ $ s₂′ ∶ U.T′ U.[| s₁′ ∶ U.S′ ]
⫢$-cong ⫢Γ′ ⫢S′ ⫢T′ ⫢r₁′≈r₂′ ⫢s₁′≈s₂′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ↝₁ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , S₄∷Γ₂ , T , _ , ↝∷ {T = S₁} {i = i} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₃ , r₁ , r₂ , _ , Γ₃↝ , r₁↝ , r₂↝ , ↝Π S₂↝ T₁↝ , r₁≈r₂ ← ⫢r₁′≈r₂′
     | _ , Γ₄ , s₁ , s₂ , S₃ , Γ₄↝ , s₁↝ , s₂↝ , S₃↝ , s₁≈s₂ ← ⫢s₁′≈s₂′
  with refl ← ⊢T:Se-lvl ⊢S 
     | refl ← ⊢T:Se-lvl ⊢T
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
     | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₃ , _ , _ , ⊢ΠS₂T₁ ← presup-≈ r₁≈r₂
     | ⊢Γ₄ , _ , _ , ⊢S₃ ← presup-≈ s₁≈s₂
  with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
  with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
     | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
  with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
  with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
     | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
     | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) ⊢S₃)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃))) 
  with S₁≈S₂ ← ≈-trans (≈-sym S≈S₁) S≈S₂
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁≈S₂))) ⊢T₁) 
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) =
        _ , _ , _ , _ , _ , Γ↝ , ↝$ r₁↝ s₁↝ , ↝$ r₂↝ s₂↝ , ↝sub T↝ (↝, ↝I s₁↝ S↝) , 
          $-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) 
                 (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁) )) ⊢T) 
                 (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) r₁≈r₂) (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂)) 
                                                       (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ S₁≈S₂)) (≈-sym T≈T₁)) refl)) 
                 (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₄) s₁≈s₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃))) 
                 refl   