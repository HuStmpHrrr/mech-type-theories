
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
           ⫢ U.Γ′ → -- extra condition
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

T[I,ze]-inv : ∀ {i j} →
              A.Γ A.⊢ sub A.T (I , ze ∶ N ↙ j) ∶[ 1 + i ] Se i →
              ∃ λ S → j ≡ 0 × N₀ ∷ A.Γ ⊢ A.T ∶[ 1 + i ] S
T[I,ze]-inv ⊢T[|ze]
  with t[σ]-inv ⊢T[|ze]
... | Δ , S , ⊢[|ze] , ⊢T , ≈Sei 
  with ⊢ze , ≈Δ ← ,-inv′ ⊢[|ze] (s-I (proj₁ (presup-tm ⊢T[|ze]))) 
  with refl , ≈N ← ze-inv ⊢ze = _ , refl , ctxeq-tm (⊢≈-sym ≈Δ) ⊢T

T[wkwk,suv1]-inv : ∀ {i j} →
                   A.lS ∷ A.lT ∷ A.Γ A.⊢ sub A.T ((wk ∘ wk) , su (v 1) ∶ N ↙ j) ∶[ 1 + i ] Se i →
                   ∃ λ S → j ≡ 0 × N₀ ∷ A.Γ ⊢ A.T ∶[ 1 + i ] S
T[wkwk,suv1]-inv ⊢T[wkwk,suv1]
  with t[σ]-inv ⊢T[wkwk,suv1]
... | Δ , S , ⊢[wkwk,suv1] , ⊢T , ≈Sei 
  with ⊢suv1 , ≈Δ ← ,-inv′ ⊢[wkwk,suv1] (⊢wk∘wk-gen (proj₁ (presup-tm ⊢T[wkwk,suv1]))) 
  with refl , _ ← su-inv ⊢suv1 = _ , refl , ctxeq-tm (⊢≈-sym ≈Δ) ⊢T

⫢rec-cong : ∀ {i T₁′ T₂′ s₁′ s₂′ r₁′ r₂′ t₁′ t₂′} →
            ⫢ U.Γ′ → -- extra condition
            N ∷ U.Γ′ ⫢ T₁′ ∶ Se i →
            N ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se i →
            U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ T₁′ U.[| ze ∶ N ] →
            T₁′ ∷ N ∷ U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ T₁′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
            U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ N →
            --------------------
            U.Γ′ ⫢ rec T₁′ s₁′ r₁′ t₁′ ≈ rec T₂′ s₂′ r₂′ t₂′ ∶ T₁′ U.[| t₁′ ∶ N ]
⫢rec-cong ⫢Γ′ ⫢S′ T₁′≈T₂′ s₁′≈s₂′ r₁≈r₂′ t₁≈t₂′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , N∷Γ₁ , T₁₁ , _ , (↝∷ Γ₁↝ ↝N) , T₁₁↝ , ↝Se , ⊢T₁₁ , IHT₁ ← ⫢S′
     | _ , N∷Γ₂ , T₁₂ , T₂₁ , _ , (↝∷ Γ₂↝ ↝N) , T₁₂↝ , T₂₁↝ , ↝Se , T₁₂≈T₂₁ ← T₁′≈T₂′ 
     | _ , Γ₃ , s₁ , s₂ , _ , Γ₃↝ , s₁↝ , s₂↝ , ↝sub {t = T₁₃} T₁₃↝ (↝, ↝I ↝ze ↝N) , s₁≈s₂ ← s₁′≈s₂′ 
     | _ , T₁∷N∷Γ₄ , r₁ , r₂ , _ , ↝∷ {T = T₁₅} (↝∷ Γ₄↝ ↝N) T₁₅↝ , r₁↝ , r₂↝ , ↝sub {t = T₁₄} T₁₄↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , r₁≈r₂ ← r₁≈r₂′
     | _ , Γ₅ , t₁ , t₂ , N , Γ₅↝ , t₁↝ , t₂↝ , ↝N , t₁≈t₂ ← t₁≈t₂′ 
  with refl ← ⊢T:Se-lvl ⊢T₁₁  
     | refl ← ⊢T≈S:Se-lvl T₁₂≈T₂₁
  with _ , refl , ⊢T₁₃ ← T[I,ze]-inv (proj₂ (proj₂ (proj₂ (presup-≈ s₁≈s₂))))
     | _ , refl , ⊢T₁₄ ← T[wkwk,suv1]-inv (proj₂ (proj₂ (proj₂ (presup-≈ r₁≈r₂))))
  with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T₁₁)
     | ⊢∷ ⊢Γ₂ ⊢N₂ ← proj₁ (presup-≈ T₁₂≈T₂₁)
     | ⊢Γ₃ ← proj₁ (presup-≈ s₁≈s₂)
     | ⊢∷ (⊢∷ ⊢Γ₄ ⊢N₃) ⊢T₁₅ ← proj₁ (presup-≈ r₁≈r₂)
     | ⊢Γ₅ ← proj₁ (presup-≈ t₁≈t₂)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
     | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
     | Γ≈Γ₅ ← IHΓ Γ₅↝ ⊢Γ₅
  with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₃)
     | refl ← ⊢t≈s∶N-lvl t₁≈t₂
  with T₁₁≈T₁₂ ← IHT₁ T₁₂↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl ⊢N₂)) (proj₁ (proj₂ (presup-≈ T₁₂≈T₂₁))))
     | T₁₁≈T₁₃ ← IHT₁ T₁₃↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₃))) ⊢T₁₃)
     | T₁₁≈T₁₄ ← IHT₁ T₁₄↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) (≈-refl ⊢N₃)) ⊢T₁₄)
     | T₁₁≈T₁₅ ← IHT₁ T₁₅↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) (≈-refl ⊢N₃)) ⊢T₁₅)
  with refl , ≈Se ← unique-typ ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₃)))
     | refl , ≈Se₁ ← unique-typ ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₄)))
     | refl ← unique-lvl ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₅)))
  with N∷Γ₁≈N∷Γ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
     = _ , _ , _ , _ , _ , Γ↝ , ↝rec T₁₁↝ s₁↝ r₁↝ t₁↝ , ↝rec T₂₁↝ s₂↝ r₂↝ t₂↝ , ↝sub T₁₁↝ (↝, ↝I t₁↝ ↝N) , 
      rec-cong (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) ⊢T₁₁) 
               (≈-trans (ctxeq-≈ N∷Γ₁≈N∷Γ T₁₁≈T₁₂) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) T₁₂≈T₂₁)) 
               (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) s₁≈s₂) ([]-cong-Se (≈-conv (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T₁₁≈T₁₃)) (ctxeq-≈ N∷Γ₁≈N∷Γ  (≈-sym ≈Se))) (⊢I,ze ⊢Γ) (s-≈-refl (⊢I,ze ⊢Γ)))) 
               (≈-conv (ctxeq-≈ (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₄) (≈-refl ⊢N₃)) (ctxeq-≈ (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₄) (≈-refl ⊢N₁)) (≈-sym T₁₁≈T₁₅))) r₁≈r₂) 
                       ([]-cong-Se (≈-conv (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T₁₁≈T₁₄)) (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T₁₁))) (s-≈-refl (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T₁₁))) ))) 
               (ctxeq-≈ (⊢≈-sym Γ≈Γ₅) t₁≈t₂)

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

⫢liftt-cong : ∀ {j} →
              U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′ →
              --------------------
              U.Γ′ ⫢ liftt j U.s′ ≈ liftt j U.t′ ∶ Liftt j U.T′
⫢liftt-cong s′≈t′ 
  with _ , Γ , s , t , T , Γ↝ , s↝ , t↝ , ↝T , s≈t ← s′≈t′ = _ , _ , _ , _ , _ , Γ↝ , ↝liftt s↝ , ↝liftt t↝ , ↝Liftt ↝T , liftt-cong _ s≈t

⫢unliftt-cong : ∀ {i j} →
                ⫢ U.Γ′ → -- extra condition
                U.Γ′ ⫢ U.T′ ∶ Se i → 
                U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ Liftt j U.T′ →
                --------------------
                U.Γ′ ⫢ unlift U.s′ ≈ unlift U.t′ ∶ U.T′
⫢unliftt-cong ⫢Γ′ ⫢T′ ⫢s′≈t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₂ , s , t , _ , Γ₂↝ , s↝ , t↝ , ↝Liftt {T = T₁} ↝T₁ , s≈t ← ⫢s′≈t′ 
  with refl ← ⊢T:Se-lvl ⊢T 
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ , _ , _ , ⊢LifttT₁ ← presup-≈ s≈t
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
  with refl , ⊢T₁ ← Liftt-inv ⊢LifttT₁ 
  with T≈T₁ ← IHT ↝T₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢T₁) 
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝unlift s↝ , ↝unlift t↝ , ↝T₁ , unlift-cong _ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢T₁) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t)

⫢[]-cong : ⫢ U.Δ′ → -- extra condition
           U.Δ′ ⫢ U.t′ ≈ U.s′ ∶ U.T′ →
           U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
           --------------------
           U.Γ′ ⫢ U.t′ U.[ U.σ′ ] ≈ U.s′ U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ]
⫢[]-cong ⫢Δ′ t′≈s′ σ′≈τ′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | _ , Δ₁ , t , s , T , Δ₁↝ , t↝ , s↝ , ↝T , t≈s ← t′≈s′
     | Γ , Δ₂ , σ , τ , Γ↝ , Δ₂↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′ 
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₁ (presup-≈ t≈s)) 
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈τ))))
     = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub s↝ τ↝ , ↝sub ↝T σ↝ , []-cong (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) t≈s) σ≈τ
  
⫢ze-[] :  U.Γ′ ⫢s U.σ′ ∶ U.Δ′ → 
          --------------------
          U.Γ′ ⫢ ze U.[ U.σ′ ] ≈ ze ∶ N
⫢ze-[] ⫢σ′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝ze σ↝ , ↝ze , ↝N , ze-[] ⊢σ

⫢su-[] : ⫢ U.Δ′ → -- extra condition
         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.t′ ∶ N →
         --------------------
         U.Γ′ ⫢ su U.t′ U.[ U.σ′ ] ≈ su (U.t′ U.[ U.σ′ ]) ∶ N
⫢su-[] ⫢Δ′ ⫢σ′ ⫢t′ 
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , t , _ , Δ₂↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
  with refl ← ⊢t∶N-lvl ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
     | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-tm ⊢t))
      = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝su t↝) σ↝ , ↝su (↝sub t↝ σ↝) , ↝N , (su-[] (s-conv ⊢σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂)) ⊢t) 

⫢rec-[] : ∀ {i} →
          ⫢ U.Δ′ → -- extra condition
          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
          N ∷ U.Δ′ ⫢ U.T′ ∶ Se i →
          U.Δ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
          U.T′ ∷ N ∷ U.Δ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
          U.Δ′ ⫢ U.t′ ∶ N →
          --------------------
          U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ U.[ U.σ′ ] ≈ rec (U.T′ U.[ U.q N U.σ′ ]) (U.s′ U.[ U.σ′ ]) (U.r′ U.[ U.q U.T′ ( U.q N U.σ′ ) ]) (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.t′ U.[ U.σ′ ] ∶ N ]
⫢rec-[] ⫢Δ′ ⫢σ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′ 
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , _ , T , _ , ↝∷ {Γ = Δ₂} Δ₂↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | i , Δ₃ , s , _ , Δ₃↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
     | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Δ₄} Δ₄↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
     | _ , Δ₅ , t , _ , Δ₅↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′ 
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢∷ ⊢Δ₂ ⊢N₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Δ₃ ← proj₁ (presup-tm ⊢s)
     | ⊢∷ (⊢∷ ⊢Δ₄ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
     | ⊢Δ₅ ← proj₁ (presup-tm ⊢t)
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
     | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
     | Δ≈Δ₅ ← IHΔ Δ₅↝ ⊢Δ₅
  with Δ₂≈Δ₄ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₄
  with refl ← ⊢T:Se-lvl ⊢T
     | refl ← ⊢t∶N-lvl ⊢t
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
  with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
     | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) (≈-refl (N-wf ⊢Δ₃))) ⊢T₁)
     | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ₂≈Δ₄) (≈-refl ⊢N₂)) ⊢T₂)
     | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ₂≈Δ₄) (≈-refl ⊢N₂)) ⊢T₃)
  with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
     | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
     | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
     = _ , _ , _ , _ , _ , Γ↝ , 
      ↝sub (↝rec T↝ s↝ r↝ t↝) σ↝ , ↝rec (↝sub T↝ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N)) (↝sub s↝ σ↝) (↝sub r↝ (↝, (↝∘ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N) ↝wk) ↝v T↝)) (↝sub t↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub t↝ σ↝) ↝N) , 
        rec-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁))
               (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ⊢T) 
               (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym T≈T₁)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym ≈Se))) (⊢I,ze ⊢Δ)))
               (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Δ≈Δ₄) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp Δ₂≈Δ₄ (≈-refl ⊢N₁)) (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ≈Se₁)) ) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Δ (N-wf  ⊢Δ)) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ⊢T)))))
               (ctxeq-tm (⊢≈-sym Δ≈Δ₅) ⊢t)

⫢Λ-[] : ∀ {i} →
         ⫢ U.Δ′ → -- extra condition
         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.S′ ∶ Se i →
         U.S′ ∷ U.Δ′ ⫢ U.t′ ∶ U.T′ →
         --------------------
         U.Γ′ ⫢ Λ U.S′ U.t′ U.[ U.σ′ ] ≈ Λ (U.S′ U.[ U.σ′ ]) (U.t′ U.[ U.q U.S′ U.σ′ ]) ∶ Π U.S′ U.T′ U.[ U.σ′ ]
⫢Λ-[] ⫢Δ′ ⫢σ′ ⫢S′ ⫢t′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , _ , t , T , ↝∷ {Γ = Δ₃} {T = S₁} Δ₃↝ S₁↝ , t↝ , ↝T , ⊢t , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢S 
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
     | ⊢∷ ⊢Δ₃ ⊢S₁ ← proj₁ (presup-tm ⊢t)
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢S₁)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Λ S↝ t↝) σ↝ , ↝Λ (↝sub S↝ σ↝) (↝sub t↝ (↝, (↝∘ σ↝ ↝wk) ↝v S↝)) , ↝sub (↝Π S↝ ↝T) σ↝ , Λ-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₃) (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₃) (≈-sym S≈S₁))) ⊢t) refl 

⫢$-[] : ∀ {i j} →
         ⫢ U.Δ′ → -- extra condition
         U.Δ′ ⫢ U.S′ ∶ Se i →
         U.S′ ∷ U.Δ′ ⫢ U.T′ ∶ Se j →
         U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
         U.Δ′ ⫢ U.r′ ∶ Π U.S′ U.T′ →
         U.Δ′ ⫢ U.s′ ∶ U.S′ →
         --------------------
         U.Γ′ ⫢ (U.r′ $ U.s′) U.[ U.σ′ ] ≈ (U.r′ U.[ U.σ′ ]) $ (U.s′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.s′ U.[ U.σ′ ] ∶ U.S′ ]
⫢$-[] ⫢Δ′ ⫢S′ ⫢T′ ⫢σ′ ⫢r′ ⫢s′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | _ , Δ₁ , S , _ , Δ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , _ , T , _ , ↝∷ {Γ = Δ₂} {T = S₁} Δ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | Γ , Δ₃ , σ , Γ↝ , Δ₃↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₄ , r , _ , Δ₄↝ , r↝ , ↝Π S₂↝ T₁↝ , ⊢r , IHr ← ⫢r′
     | _ , Δ₅ , s , S₃ , Δ₅↝ , s↝ , S₃↝ , ⊢s , IHs ← ⫢s′
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₁ (presup-tm ⊢S)
      | ⊢∷ ⊢Δ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
      | ⊢Δ₃ ← proj₂ (presup-s ⊢σ)
      | ⊢Δ₄ , ⊢ΠS₂T₁ ← presup-tm ⊢r
      | ⊢Δ₅ , ⊢S₃ ← presup-tm ⊢s
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
     | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
     | Δ≈Δ₅ ← IHΔ Δ₅↝ ⊢Δ₅
  with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
     | Δ₄≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₂
  with refl , Se≈ , ⊢S₂ , ⊢T₁ ← Π-inv′ ⊢ΠS₂T₁
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm  (⊢≈-sym Δ₁≈Δ₂) ⊢S₁)
     | S≈S₂ ← IHS S₂↝ (ctxeq-tm  (⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₁) ⊢S₂)
     | S≈S₃ ← IHS S₃↝ (ctxeq-tm  (⊢≈-trans (⊢≈-sym Δ≈Δ₅) Δ≈Δ₁) ⊢S₃)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm  (∷-cong-simp Δ₄≈Δ₂ (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₄) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝$ r↝ s↝) σ↝ , ↝$ (↝sub r↝ σ↝) (↝sub s↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub s↝ σ↝) S↝) , 
      $-[] (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ₁≈Δ₂ (≈-sym S≈S₁))) ⊢T) 
           (s-conv ⊢σ (⊢≈-sym Δ≈Δ₃)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₄) ⊢r) (Π-cong (ctxeq-tm (⊢≈-sym Δ≈Δ₄) ⊢S₂) (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-trans (ctxeq-≈ Δ₁≈Δ₂ (≈-sym S≈S₁)) (ctxeq-≈ Δ₁≈Δ₂ S≈S₂))) (≈-sym T≈T₁)) refl)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₅) ⊢s) (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) (≈-sym S≈S₃))) refl

⫢liftt-[] : ∀ {i j} →
            ⫢ U.Δ′ → -- extra condition
            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
            U.Δ′ ⫢ U.T′ ∶ Se i →
            U.Δ′ ⫢ U.t′ ∶ U.T′ →
            ------------------------
            U.Γ′ ⫢ liftt j U.t′ U.[ U.σ′ ] ≈ liftt j (U.t′ U.[ U.σ′ ]) ∶ Liftt j U.T′ U.[ U.σ′ ]
⫢liftt-[] ⫢Δ′ ⫢σ′ ⫢T′ ⫢t′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Δ₃ , t , T₁ , Δ₃↝ , t↝ , T₁↝ , ⊢t , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
     | ⊢Δ₃ , ⊢T₁ ← presup-tm ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝liftt t↝) σ↝ , ↝liftt (↝sub t↝ σ↝) , ↝sub (↝Liftt T↝) σ↝ , liftt-[] _ (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢t) (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-sym T≈T₁)))

⫢unlift-[] : ∀ {i j} →
             ⫢ U.Δ′ → -- extra condition
             U.Δ′ ⫢ U.T′ ∶ Se i →
             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
             U.Δ′ ⫢ U.t′ ∶ Liftt j U.T′ →
             ---------------------------------
             U.Γ′ ⫢ unlift U.t′ U.[ U.σ′ ] ≈ unlift (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ ]
⫢unlift-[] ⫢Δ′ ⫢T′ ⫢σ′ ⫢t′
  with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Δ₃ , t , _ , Δ₃↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T
  with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
     | ⊢Δ₃ , ⊢LiftT₁ ← presup-tm ⊢t
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
  with refl , ⊢T₁ , _ ← Liftt-inv′ ⊢LiftT₁
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢T₁) 
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝unlift t↝) σ↝ , ↝unlift (↝sub t↝ σ↝) , ↝sub T↝ σ↝ , unlift-[] _ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢t) (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-sym T≈T₁))))
      
⫢rec-β-ze : ∀ {i} →
            ⫢ U.Γ′ → -- extra condition
            N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
            U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
            U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
            --------------------
            U.Γ′ ⫢ rec U.T′ U.s′ U.r′ ze ≈ U.s′ ∶ U.T′ U.[| ze ∶ N ]
⫢rec-β-ze ⫢Γ′ ⫢T′ ⫢s′ ⫢r′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
     | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₃} Γ₃↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′ 
  with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ ← proj₁ (presup-tm ⊢s)
     | ⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
  with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with refl ← ⊢T:Se-lvl ⊢T
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂) 
  with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
  with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
     | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₂) )) ⊢T₁)
     | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₂)
     | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₃)
  with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
     | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
     | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
     = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ ↝ze , s↝ , ↝sub T↝ (↝, ↝I ↝ze ↝N) , rec-β-ze (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₁)) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym ≈Se))) (⊢I,ze ⊢Γ) )) (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym  Γ₃≈Γ₁) (≈-refl ⊢N₁)) (≈-sym T≈T₃) )) ⊢r) 
        ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ N∷Γ≈N∷Γ₁ ≈Se₁)) ) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf  ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T)))))

⫢rec-β-su : ∀ {i} →
            ⫢ U.Γ′ → -- extra condition
            N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
            U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
            U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
            U.Γ′ ⫢ U.t′ ∶ N →
            --------------------------------
            U.Γ′ ⫢ rec U.T′ U.s′ U.r′ (su U.t′) ≈ U.r′ U.[ (I , U.t′ ∶ N ) , rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ ] ∶ U.T′ U.[| su U.t′ ∶ N ]
⫢rec-β-su ⫢Γ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
     | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₃} Γ₃↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
     | _ , Γ₄ , t , _ , Γ₄↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
  with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ ← proj₁ (presup-tm ⊢s)
     | ⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
     | ⊢Γ₄ ← proj₁ (presup-tm ⊢t)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
     | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
  with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
  with refl ← ⊢T:Se-lvl ⊢T
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
     | refl ← ⊢t∶N-lvl ⊢t
  with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
     | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₂) )) ⊢T₁)
     | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₂)
     | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₃)
  with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
     | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
     | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ (↝su t↝) , ↝sub r↝ (↝, (↝, ↝I t↝ ↝N) (↝rec T↝ s↝ r↝ t↝) T↝) , ↝sub T↝ (↝, ↝I (↝su t↝) ↝N) , 
      rec-β-su (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₁)) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym ≈Se))) (⊢I,ze ⊢Γ))) 
        (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym  Γ₃≈Γ₁) (≈-refl ⊢N₁)) (≈-sym T≈T₃) )) ⊢r) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ N∷Γ≈N∷Γ₁ ≈Se₁)) ) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf  ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T))))) (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢t)

⫢Λ-β : ∀ {i j} →
        ⫢ U.Γ′ → -- extra condition
        U.Γ′ ⫢ U.S′ ∶ Se i →
        U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
        U.S′ ∷ U.Γ′ ⫢ U.t′ ∶ U.T′ →
        U.Γ′ ⫢ U.s′ ∶ U.S′ →
        --------------------
        U.Γ′ ⫢ (Λ U.S′ U.t′) $ U.s′ ≈ U.t′ U.[| U.s′ ∶ U.S′ ] ∶ U.T′ U.[| U.s′ ∶ U.S′ ]
⫢Λ-β ⫢Γ′ ⫢S′ ⫢T′ ⫢t′ ⫢s′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | j , _ , t , T₁ , ↝∷ {Γ = Γ₃} {T = S₂} Γ₃↝ S₂↝  , t↝ , T₁↝ , ⊢t , IHt ← ⫢t′
     | i , Γ₄ , s , S₃ , Γ₄↝ , s↝ , S₃↝ , ⊢s , IHs ← ⫢s′
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
     | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
     | ⊢∷ ⊢Γ₃ ⊢S₂ , ⊢T₁ ← presup-tm ⊢t
     | ⊢Γ₄ , ⊢S₃ ← presup-tm ⊢s
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
     | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
  with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
     | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
     | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
     | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) ⊢S₃)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃))) 
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝$ (↝Λ S↝ t↝) s↝ , ↝sub t↝ (↝, ↝I s↝ S↝) , ↝sub T↝ (↝, ↝I s↝ S↝) , 
      Λ-β (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) 
          (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T) 
          (conv (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S≈S₂) ))  ⊢t) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁) )) (≈-sym T≈T₁) )) 
          (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢s) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃) ))

⫢Λ-η : ∀ {i j} →
        ⫢ U.Γ′ → -- extra condition
        U.Γ′ ⫢ U.S′ ∶ Se i →
        U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
        U.Γ′ ⫢ U.t′ ∶ Π U.S′ U.T′ →
        --------------------
        U.Γ′ ⫢ U.t′ ≈ Λ U.S′ (U.t′ U.[ wk ] $ v 0) ∶ Π U.S′ U.T′
⫢Λ-η ⫢Γ′ ⫢S′ ⫢T′ ⫢t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₃ , t , _ , Γ₃↝ , t↝ , ↝Π S₂↝ T₁↝ , ⊢t , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
     | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₃ , ⊢ΠS₂T₁ ← presup-tm ⊢t
  with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁ 
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂ 
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃ 
  with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
     | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
     | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂) 
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁)) ) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝Λ S↝ (↝$ (↝sub t↝ ↝wk) ↝v) , ↝Π S↝ T↝ , 
      Λ-η (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T) 
          (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢t) 
                (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-trans (≈-sym S≈S₁) S≈S₂))) 
                        (≈-sym T≈T₁)) refl)) refl 

⫢L-β : ∀ {j} →
       U.Γ′ ⫢ U.t′ ∶ U.T′ →
       -----------------------------
       U.Γ′ ⫢ unlift (liftt j U.t′) ≈ U.t′ ∶ U.T′
⫢L-β ⫢t′ 
  with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′ 
    = _ , _ , _ , _ , _ , Γ↝ , ↝unlift (↝liftt t↝) , t↝ , T↝ , L-β _ ⊢t

⫢L-η : ∀ {i j} →
       ⫢ U.Γ′ → 
       U.Γ′ ⫢ U.T′ ∶ Se i →
       U.Γ′ ⫢ U.t′ ∶ Liftt j U.T′ →
       -----------------------------
       U.Γ′ ⫢ U.t′ ≈ liftt j (unlift U.t′) ∶ Liftt j U.T′
⫢L-η ⫢Γ′ ⫢T′ ⫢t′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
     | _ , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt ← ⫢t′ 
  with refl ← ⊢T:Se-lvl ⊢T
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ , ⊢LiftT₁ ← presup-tm ⊢t
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
  with refl , ⊢T₁ ← Liftt-inv ⊢LiftT₁
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
     = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝liftt (↝unlift t↝) , ↝Liftt T↝ , L-η _ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢t) (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym T≈T₁))))

⫢[I] : U.Γ′ ⫢ U.t′ ∶ U.T′ →
       ---------------------
       U.Γ′ ⫢ U.t′ U.[ I ] ≈ U.t′ ∶ U.T′
⫢[I] ⫢t′
  with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ ↝I , t↝ , T↝ , [I] ⊢t

⫢[wk] : ∀ {i x} →
        ⫢ U.Γ′ →
        U.Γ′ ⫢ U.S′ ∶ Se i →
        x ∶ U.T′ ∈! U.Γ′ →
        ---------------------
        U.S′ ∷ U.Γ′ ⫢ v x U.[ wk ] ≈ v (1 + x) ∶ U.T′ U.[ wk ]
⫢[wk] ⫢Γ′ ⫢S′ x∈Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ 
     | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
  with refl ← ⊢T:Se-lvl ⊢S
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢S))
  with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′
    = _ , _ , _ , _ , _ , ↝∷ Γ↝ S↝ , ↝sub ↝v ↝wk , ↝v , ↝sub T↝ ↝wk , [wk] ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) x∈Γ

⫢[∘]  : ⫢ U.Ψ′ → -- extra condition
        ⫢ U.Δ′ → -- extra condition
        U.Γ′ ⫢s U.τ′ ∶ U.Ψ′ →
        U.Ψ′ ⫢s U.σ′ ∶ U.Δ′ →
        U.Δ′ ⫢ U.t′ ∶ U.T′ →
        ---------------------
        U.Γ′ ⫢ U.t′ U.[ U.σ′ ∘ U.τ′ ] ≈ U.t′ U.[ U.σ′ ] U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ∘ U.τ′ ]
⫢[∘] ⫢Ψ′ ⫢Δ′ ⫢τ′ ⫢σ′ ⫢t′
  with Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
     | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ , Ψ₁ , τ , Γ↝ , Ψ₁↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
     | Ψ₂ , Δ₁ , σ  , Ψ₂↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
     | i , Δ₂ , t , T , Δ₂↝ , t↝ , T↝ , ⊢t , IHT ← ⫢t′ 
  with ⊢Ψ₁ ← proj₂ (presup-s ⊢τ)
     | ⊢Ψ₂ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢t)
  with Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
     | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
  with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ (↝∘ σ↝ τ↝) , ↝sub (↝sub t↝ σ↝) τ↝ , ↝sub T↝ (↝∘ σ↝ τ↝) , [∘] ⊢τ (ctxeq-s (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) ⊢σ) (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢t)

⫢[,]-v-ze : ∀ {i} →
            ⫢ U.Γ′ → -- extra condition
            ⫢ U.Δ′ → -- extra condition
            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
            U.Δ′ ⫢ U.S′ ∶ Se i →
            U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
            ---------------------
            U.Γ′ ⫢ v 0 U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ U.s′ ∶ U.S′ U.[ U.σ′ ]
⫢[,]-v-ze ⫢Γ′ ⫢Δ′ ⫢σ ⫢S′ ⫢s′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ
     | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | i , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , IHs ← ⫢s′
  with refl ← ⊢T:Se-lvl ⊢S
  with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢Γ₂ , ⊢S₁[σ₁] ← presup-tm ⊢s
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
  with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁] 
  with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
  with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
  with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁)
  with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , s↝ , ↝sub S↝ σ↝ , 
      [,]-v-ze (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) 
               (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S) 
               (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₂) ⊢σ₁) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁)) ))

⫢[,]-v-su : ∀ {i x} →
            ⫢ U.Γ′ → -- extra condition
            ⫢ U.Δ′ → -- extra condition
            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
            U.Δ′ ⫢ U.S′ ∶ Se i →
            U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
            x ∶ U.T′ ∈! U.Δ′ →
            ---------------------
            U.Γ′ ⫢ v (1 + x) U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ v x U.[ U.σ′ ] ∶ U.T′ U.[ U.σ′ ]          
⫢[,]-v-su ⫢Γ′ ⫢Δ′ ⫢σ ⫢S′ ⫢s′ x∈Δ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
     | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ
     | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | i , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , IHs ← ⫢s′
  with refl ← ⊢T:Se-lvl ⊢S
  with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
     | ⊢Γ₂ , ⊢S₁[σ₁] ← presup-tm ⊢s
     | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
  with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁] 
  with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
  with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
  with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁) 
  with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
  with j , T , T↝ , x∈Δ ← U⇒A-vlookup Δ↝ x∈Δ′ 
    = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , ↝sub ↝v σ↝ , ↝sub T↝ σ↝ , 
        [,]-v-su (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S) 
        (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₂) ⊢σ₁) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁)) )) 
        x∈Δ

⫢≈-conv : ∀ {i} →
          ⫢ U.Γ′ → -- extra condition
          U.Γ′ ⫢ U.S′ ∶ Se i → -- extra condition
          U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
          U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i → 
          ---------------------
          U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′
⫢≈-conv ⫢Γ′ ⫢S′ s′≈t′ S′≈T′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
     | _ , Γ₂ , s , t , S₁ , Γ₂↝ , s↝ , t↝ , S₁↝ , s≈t ← s′≈t′
     | _ , Γ₃ , S₂ , T , _ , Γ₃↝ , S₂↝ , T↝ , ↝Se , S≈T ← S′≈T′
  with refl ← ⊢T:Se-lvl ⊢S 
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
     | ⊢Γ₂ , ⊢s , ⊢t , ⊢S₁ ← presup-≈ s≈t
     | ⊢Γ₃ , ⊢S₂ , ⊢T , _ ← presup-≈ S≈T
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃ 
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢S₁)
     | S≈S₂ ← IHS S₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢S₂)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
    = _ , _ , _ , _ , _ , Γ↝ , s↝ , t↝ , T↝ , ≈-conv (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) S≈T))
    
⫢≈-sym : U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
         ---------------------
         U.Γ′ ⫢ U.t′ ≈ U.s′ ∶ U.S′
⫢≈-sym s′≈t′
  with _ , Γ , s , t , S , Γ↝ , s↝ , t↝ , S↝ , s≈t ← s′≈t′
    = _ , _ , _ , _ , _ , Γ↝ , t↝ , s↝ , S↝ , ≈-sym s≈t

⫢≈-trans : ⫢ U.Γ′ →
           U.Γ′ ⫢ U.t′ ∶ U.S′ →
           U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
           U.Γ′ ⫢ U.t′ ≈ U.r′ ∶ U.S′ →
           ---------------------
           U.Γ′ ⫢ U.s′ ≈ U.r′ ∶ U.S′
⫢≈-trans ⫢Γ′ ⫢t′ s′≈t′ t′≈r′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | _ , Γ₁ , t , S , Γ₁↝ , t↝ , S↝ , ⊢t , IHt ← ⫢t′
     | _ , Γ₂ , s , t₁ , S₁ , Γ₂↝ , s↝ , t₁↝ , S₁↝ , s≈t ← s′≈t′
     | _ , Γ₃ , t₂ , r , S₂ , Γ₃↝ , t₂↝ , r↝ , S₂↝ , t≈r ← t′≈r′ 
  with ⊢Γ₁ ← proj₁ (presup-tm ⊢t)
     | ⊢Γ₂ , ⊢s , ⊢t₁ , ⊢S₁ ← presup-≈ s≈t
     | ⊢Γ₃ , ⊢t₂ , ⊢r , ⊢S₂ ← presup-≈ t≈r
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃ 
  with t≈t₁ ← IHt t₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢t₁)
     | t≈t₂ ← IHt t₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢t₂)
  with refl , S≈S₁ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₁)))
     | refl , S≈S₂ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₂)))
  with t₁≈t₂ ← ≈-trans (≈-sym t≈t₁) (≈-conv t≈t₂ (≈-trans (≈-sym S≈S₂) S≈S₁))
    = _ , _ , _ , _ , _ , Γ↝ , s↝ , r↝ , S↝ , 
      ≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t₁≈t₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁) )) (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) t≈r) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂) )))