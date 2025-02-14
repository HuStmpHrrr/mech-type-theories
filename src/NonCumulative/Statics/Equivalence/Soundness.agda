
{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Statics.Equivalence.Soundness (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

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
open import NonCumulative.Statics.Equivalence.Transfer

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
⫢ Γ′ = ∃ λ Γ → (A.⊢ Γ × Γ [↝] Γ′ × (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ))

_⫢_∶_ : U.Ctx → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ∶ T′ =  ∃₂ λ i Γ → ∃₂ λ t T →
                  (Γ [↝] Γ′) ×
                  (t ↝ t′) ×
                  (T ↝ T′) ×
                  Γ A.⊢ t ∶[ i ] T ×
                  (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) ×
                  (∀ {tᵢ iᵢ Tᵢ} →
                      tᵢ ↝ t′ →
                      Γ ⊢ tᵢ ∶[ iᵢ ] Tᵢ →
                      Γ A.⊢ t ≈ tᵢ ∶[ iᵢ ] Tᵢ)

_⫢s_∶_ : U.Ctx → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ∶ Δ′ = 
  ∃₂ λ Γ Δ → ∃ λ σ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × Γ A.⊢s σ ∶ Δ ×
     (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) ×
     (∀ {σᵢ Δᵢ} → σᵢ ↝s σ′ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s σ ≈ σᵢ ∶ Δᵢ)

⫢_≈_ : U.Ctx → U.Ctx → Set
⫢ Γ′ ≈ Δ′ = ∃₂ λ Γ Δ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × A.⊢ Γ ≈ Δ × 
               (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
               (∀ {Δᵢ} → Δᵢ [↝] Δ′ → A.⊢ Δᵢ → A.⊢ Δ ≈ Δᵢ)

_⫢_≈_∶_ : U.Ctx → U.Exp → U.Exp → U.Typ → Set
Γ′ ⫢ t′ ≈ s′ ∶ T′ = 
  ∃₂ λ i Γ → ∃₂ λ t s → ∃ λ T → (Γ [↝] Γ′) × (t ↝ t′) × (s ↝ s′) × (T ↝ T′) × Γ A.⊢ t ≈ s ∶[ i ] T × 
     (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
     (∀ {tᵢ iᵢ Tᵢ} →
      tᵢ ↝ t′ →
      Γ ⊢ tᵢ ∶[ iᵢ ] Tᵢ →
      Γ A.⊢ t ≈ tᵢ ∶[ iᵢ ] Tᵢ) × 
     (∀ {sᵢ iᵢ Tᵢ} →
      sᵢ ↝ s′ →
      Γ ⊢ sᵢ ∶[ iᵢ ] Tᵢ →
      Γ A.⊢ s ≈ sᵢ ∶[ iᵢ ] Tᵢ)

_⫢s_≈_∶_ : U.Ctx → U.Subst → U.Subst → U.Ctx → Set
Γ′ ⫢s σ′ ≈ τ′ ∶ Δ′ = ∃₂ λ Γ Δ → ∃₂ λ σ τ → (Γ [↝] Γ′) × (Δ [↝] Δ′) × (σ ↝s σ′) × (τ ↝s τ′) × Γ A.⊢s σ ≈ τ ∶ Δ × 
  (∀ {Γᵢ} → Γᵢ [↝] Γ′ → A.⊢ Γᵢ → A.⊢ Γ ≈ Γᵢ) × 
  (∀ {σᵢ Δᵢ} → σᵢ ↝s σ′ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s σ ≈ σᵢ ∶ Δᵢ) × 
  (∀ {τᵢ Δᵢ} → τᵢ ↝s τ′ → Γ A.⊢s τᵢ ∶ Δᵢ → Γ A.⊢s τ ≈ τᵢ ∶ Δᵢ)

⫢⊢[] : ⫢ []
⫢⊢[] = _ , ⊢[] , ↝[] , λ { ↝[] ⊢[] → []-≈ }

⫢[]-≈ : ⫢ [] ≈ []
⫢[]-≈ = _ , _ , ↝[] , ↝[] , []-≈ , (λ { ↝[] ⊢[] → []-≈ }) , (λ { ↝[] ⊢[] → []-≈ })

⫢⊢∷ : ∀ {i} →
      ⫢ U.Γ′ →
      U.Γ′ ⫢ U.T′ ∶ Se i →
      --------------------
      ⫢ U.T′ ∷ U.Γ′
⫢⊢∷  {Γ′} ⫢Γ′ ⫢T′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
     | i , Γ₁ , T , .(Se _) , Γ₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T
  with Γ≈Γ₁  ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T)) = _ , ⊢∷ ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) , ↝∷ Γ↝ T↝ , helper
    where
      helper : ∀ { Γᵢ } → Γᵢ [↝] _ → A.⊢ Γᵢ → A.⊢ _ ≈ Γᵢ
      helper (↝∷ {T = Tᵢ} ↝Γᵢ ↝Tᵢ) (⊢∷ ⊢Γᵢ ⊢Tᵢ)
        with Γ≈Γᵢ ← IHΓ ↝Γᵢ ⊢Γᵢ
        with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γᵢ) Γ≈Γ₁) ⊢Tᵢ)
        with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ∷-cong-simp Γ≈Γᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈Tᵢ)

⫢∷-cong : ∀ {i} →
          ⫢ U.Γ′ ≈ U.Δ′ →
          U.Γ′ ⫢ U.T′ ∶ Se i →
          U.Δ′ ⫢ U.S′ ∶ Se i →
          U.Γ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →
          U.Δ′ ⫢ U.T′ ≈ U.S′ ∶ Se i →
          --------------------
          ⫢ U.T′ ∷ U.Γ′ ≈ U.S′ ∷ U.Δ′
⫢∷-cong Γ′≈Δ′ ⫢T′ ⫢S′ Γ⫢T≈S′ Δ⫢T≈S′
  with Γ , Δ , Γ↝ , Δ↝ , Γ≈Δ , IHΓ , IHΔ ← Γ′≈Δ′
     | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | _ , Δ₁ , S , _ , Δ₁↝ , S↝ , ↝Se , ⊢S , _ , IHS ← ⫢S′
     | _ , Γ₂ , T₁ , S₁ , _ , Γ₂↝ , T↝₁ , S↝₁ , ↝Se , T₁≈S₁ , _ ← Γ⫢T≈S′ 
  with refl ← ⊢T:Se-lvl ⊢T
  with refl ← ⊢T:Se-lvl ⊢S
  with ⊢Γ₂ , ⊢T₁ , ⊢S₁ , _  ← presup-≈ T₁≈S₁
  with ⊢Γ , ⊢Δ ← presup-⊢≈ Γ≈Δ 
  with refl ← ⊢T:Se-lvl ⊢T₁ 
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢T))
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₁ (presup-tm ⊢S)) 
  with T≈T₁ ← IHT T↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂)  Γ≈Γ₁) ⊢T₁)
     | S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) (⊢≈-trans Γ≈Δ Δ≈Δ₁)) ⊢S₁) 
  = _ , _ , ↝∷ Γ↝ T↝ , ↝∷ Δ↝ S↝ , ∷-cong-simp Γ≈Δ ((≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈T₁) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) T₁≈S₁) (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) (⊢≈-sym Γ≈Δ)) (≈-sym S≈S₁))))) , IHT∷Γ , IHS∷Δ
  where 
    IHT∷Γ : ∀ { Γᵢ } → Γᵢ [↝] _ → A.⊢ Γᵢ → A.⊢ _ ≈ Γᵢ
    IHT∷Γ (↝∷ {T = Tᵢ} ↝Γᵢ ↝Tᵢ) (⊢∷ ⊢Γᵢ ⊢Tᵢ)
      with Γ≈Γᵢ ← IHΓ ↝Γᵢ ⊢Γᵢ
      with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γᵢ) Γ≈Γ₁) ⊢Tᵢ) 
      with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ∷-cong-simp Γ≈Γᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) T≈Tᵢ)

    IHS∷Δ : ∀ { Δᵢ } → Δᵢ [↝] _ → A.⊢ Δᵢ → A.⊢ _ ≈ Δᵢ
    IHS∷Δ (↝∷ {T = Sᵢ} ↝Δᵢ ↝Sᵢ) (⊢∷ ⊢Δᵢ ⊢Sᵢ) 
      with Δ≈Δᵢ ← IHΔ ↝Δᵢ ⊢Δᵢ 
      with S≈Sᵢ ← IHS ↝Sᵢ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δᵢ) Δ≈Δ₁) ⊢Sᵢ) 
      with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ))) = ∷-cong-simp Δ≈Δᵢ (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) S≈Sᵢ)

⫢N-wf : ⫢ U.Γ′ →
        U.Γ′ ⫢ N ∶ Se 0
⫢N-wf ⫢Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝N , ↝Se , N-wf ⊢Γ , IHΓ , λ { ↝N ⊢N → ≈-refl ⊢N }

⫢Se-wf : ∀ {i} →
         ⫢ U.Γ′ →
         U.Γ′ ⫢ Se i ∶ Se (1 + i)
⫢Se-wf ⫢Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝Se , ↝Se , Se-wf _ ⊢Γ , IHΓ , λ { ↝Se ⊢Se → ≈-refl ⊢Se }

⫢Liftt-wf : ∀ {i n} →
            U.Γ′ ⫢ U.T′ ∶ Se i →
            U.Γ′ ⫢ Liftt n U.T′ ∶ Se (n + i)
⫢Liftt-wf ⫢T′
  with _ , Γ , T , .(Se _) , Γ↝ , T↝ , ↝Se , ⊢T , IHΓ , IHT ← ⫢T′
  with refl ← ⊢T:Se-lvl ⊢T = _ , _ , _ , _ , Γ↝ , ↝Liftt T↝ , ↝Se , Liftt-wf _ ⊢T , IHΓ , IHLiftT
    where
      IHLiftT : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
      IHLiftT (↝Liftt tᵢ↝) ⊢Lifttᵢ
        with Liftt-inv′ ⊢Lifttᵢ
      ... | refl , ⊢Tᵢ , ≈Se
        with IHT tᵢ↝ ⊢Tᵢ
      ... | T≈Tᵢ
        with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
      ... | refl = ≈-conv (Liftt-cong _ T≈Tᵢ) (≈-sym ≈Se)

⫢Π-wf : ∀ {i j k} →
        U.Γ′ ⫢ U.S′ ∶ Se i →
        (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
        k ≡ max i j →
        --------------------
        U.Γ′ ⫢ Π U.S′ U.T′ ∶ Se k
⫢Π-wf ⫢S′ ⫢T′ k≡maxij
  with _ , Γ , S , _ , Γ↝ , S↝ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
     | _ , _ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₁ S↝₁) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′ 
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T 
  with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢T) 
  with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
  with S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁))) 
  = _ , _ , _ , _ , Γ↝ , ↝Π S↝ T↝ , ↝Se , Π-wf ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢T) k≡maxij , IHΓ , IHΠST
  where
    IHΠST : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHΠST (↝Π Sᵢ↝ Tᵢ↝) ⊢Πtᵢ
      with refl , ≈Se , ⊢Sᵢ , ⊢Tᵢ ← Π-inv′ ⊢Πtᵢ
      with S≈Sᵢ ← IHS Sᵢ↝ ⊢Sᵢ 
      with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ))) 
      with Sᵢ≈S₁ ← ≈-trans (≈-sym S≈Sᵢ) S≈S₁ 
      with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ Sᵢ≈S₁) ⊢Tᵢ) 
      with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) = ≈-conv (Π-cong ⊢S S≈Sᵢ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) T≈Tᵢ) refl) (≈-sym ≈Se)

⫢vlookup : ∀ {x} →
           ⫢ U.Γ′ →
           x ∶ U.T′ ∈! U.Γ′ →
           ------------
           U.Γ′ ⫢ v x ∶ U.T′
⫢vlookup ⫢Γ′ x∈Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
  with  _ , _ , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , Γ↝ , ↝v , T↝ , vlookup ⊢Γ x∈Γ , IHΓ , λ { ↝v ⊢v → ≈-refl ⊢v }

⫢ze-I : ⫢ U.Γ′ →
        ------------------
        U.Γ′ ⫢ ze ∶ N
⫢ze-I ⫢Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝ze , ↝N , ze-I ⊢Γ , IHΓ , λ { ↝ze ⊢ze → ≈-refl ⊢ze }

⫢su-I : U.Γ′ ⫢ U.t′ ∶ N →
        U.Γ′ ⫢ su U.t′ ∶ N
⫢su-I ⫢t′
  with _ , Γ , t , .N , Γ↝ , t↝ , ↝N , ⊢t , IHΓ , IHt ← ⫢t′
  with  ⊢t∶N-lvl ⊢t
...  | refl = _ , _ , _ , _ , Γ↝ , ↝su t↝ , ↝N , (su-I ⊢t) , IHΓ , IHsu
  where
    IHsu : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    IHsu (↝su t₁↝) ⊢sut₁
      with su-inv ⊢sut₁
    ...  | refl , T₁≈N , ⊢t₁ = ≈-conv (su-cong (IHt t₁↝ ⊢t₁)) (≈-sym T₁≈N)

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

⫢N-E : ∀ {i} →
       (N ∷ U.Γ′) ⫢ U.T′ ∶ Se i →
       U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
       (U.T′ ∷ N ∷ U.Γ′) ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
       U.Γ′ ⫢ U.t′ ∶ N →
       --------------------------
       U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ U.[| U.t′ ∶ N ]
⫢N-E  ⫢T′ ⫢s′ ⫢r′ ⫢t′
  with _ , _ , T , _ , (↝∷ Γ₁↝ ↝N) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | j , Γ , s , _ , Γ↝ , s↝ , ↝sub {t = T₁} T↝₁ (↝, ↝I ↝ze ↝N) , ⊢s , IHΓ , IHs ← ⫢s′
     | k , _ , r , _ , (↝∷ {T = T₃} (↝∷ Γ₂↝ ↝N) T↝₃) , r↝ , ↝sub {t = T₂} T↝₂ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , _ , IHr ← ⫢r′
     | _ , Γ₃ , t , _ , Γ₃↝ , t↝ , ↝N , ⊢t , _ , IHt ← ⫢t′ 
  with (⊢∷ {Γ = Γ₁} ⊢Γ₁ ⊢N₁) ← proj₁ (presup-tm ⊢T)
     | ⊢Γ , ⊢T₁[|ze] ← presup-tm ⊢s
     | (⊢∷ (⊢∷ ⊢Γ₂ ⊢N₂) ⊢T₃) , ⊢T₂[wkwk,ze] ← (presup-tm ⊢r) 
  with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
     | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂) 
  with refl ← ⊢T:Se-lvl ⊢T
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
     | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
     | Γ≈Γ₃ ← IHΓ Γ₃↝ (proj₁ (presup-tm ⊢t)) 
  with T≈T₃ ← IHT T↝₃ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl ⊢N₂)) ⊢T₃) 
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃))) 
  = _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ t↝ , ↝sub T↝ (↝, ↝I t↝ ↝N) , N-E (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) ⊢T) ⊢s_ ⊢r_ ⊢t_ , IHΓ , IHrec
  where
    N∷Γ₁≈N∷Γ = ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
    Γ₁≈Γ₂ = ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
    N∷Γ₁≈N∷Γ₂ = ∷-cong-simp Γ₁≈Γ₂ (≈-refl ⊢N₁)

    ⊢s_ : Γ ⊢ s ∶[ _ ] T A.[| ze ∶ N₀ ]
    ⊢s_ 
      with SeS , refl , ⊢T₁ ← T[I,ze]-inv ⊢T₁[|ze] 
      with T≈T₁ ← IHT T↝₁ (ctxeq-tm (∷-cong-simp Γ≈Γ₁ (≈-refl (N-wf ⊢Γ))) ⊢T₁)
      with refl , Sej≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
      = conv ⊢s ([]-cong-Se′ (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) (≈-conv (≈-sym T≈T₁) (≈-sym Sej≈))) (⊢I,ze ⊢Γ))

    ⊢r_ : (T ↙ _) L.∷ N₀ L.∷ Γ ⊢ r ∶[ _ ] sub T ((wk ∘ wk) , su (v 1) ∶ N₀) 
    ⊢r_ 
      with SeS , refl , ⊢T₂ ← T[wkwk,suv1]-inv ⊢T₂[wkwk,ze]
      with T≈T₂ ← IHT T↝₂ (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ₁≈Γ₂) (≈-refl ⊢N₂)) ⊢T₂)
      with refl , Sej≈SeS ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
      = conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) (ctxeq-≈ N∷Γ₁≈N∷Γ₂ (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-conv (≈-sym T≈T₂) (≈-sym Sej≈SeS))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T))))
        
    ⊢t_ : Γ ⊢ t ∶[ _ ] N
    ⊢t_
      with refl ← ⊢t∶N-lvl ⊢t = (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢t)
      
    IHrec : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHrec (↝rec ↝Tᵢ ↝sᵢ ↝rᵢ ↝tᵢ) ⊢rectᵢ 
      with rec-inv ⊢rectᵢ
    ...  | refl , ⊢Tᵢ , ⊢sᵢ , ⊢rᵢ , ⊢tᵢ , Tᵢ≈ 
      with T≈Tᵢ ← IHT ↝Tᵢ (ctxeq-tm (⊢≈-sym N∷Γ₁≈N∷Γ) ⊢Tᵢ) 
      with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ)))
      with T₃∷N∷Γ₂≈Tᵢ∷N∷Γ ← ∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) (ctxeq-≈ N∷Γ₁≈N∷Γ₂ (≈-trans (≈-sym T≈T₃) T≈Tᵢ))
      with s≈sᵢ ← IHs ↝sᵢ ⊢sᵢ
         | r≈rᵢ ← IHr ↝rᵢ (ctxeq-tm (⊢≈-sym T₃∷N∷Γ₂≈Tᵢ∷N∷Γ) ⊢rᵢ)
         | t≈tᵢ ← IHt ↝tᵢ (ctxeq-tm Γ≈Γ₃ ⊢tᵢ)
      = ≈-conv (≈-sym (rec-cong ⊢Tᵢ (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T≈Tᵢ)) (≈-sym s≈sᵢ) (ctxeq-≈ T₃∷N∷Γ₂≈Tᵢ∷N∷Γ (≈-sym r≈rᵢ)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym t≈tᵢ)))) 
        (≈-sym Tᵢ≈)

⫢Λ-I : ∀ {i} →
       U.Γ′ ⫢ U.S′ ∶ Se i →
       (U.S′ ∷ U.Γ′) ⫢ U.t′ ∶ U.T′ →
       --------------------
       U.Γ′ ⫢ Λ U.S′ U.t′ ∶ Π U.S′ U.T′
⫢Λ-I {i = i} ⫢S′ ⫢t′
  with  _ , Γ , S , _ , Γ↝ , S↝ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
     | k , _ , t , T , (↝∷ {T = S₁} Γ↝₁ S↝₁) , t↝ , T↝ , ⊢t , _ , IHt ← ⫢t′
  with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢t)
  with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
  with S≈S₁ ← IHS S↝₁ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
  with refl ← ⊢T:Se-lvl ⊢S
  = _ , _ , _ , _ , Γ↝ , ↝Λ S↝ t↝ , ↝Π {i = i} {j = k} S↝ T↝ , Λ-I ⊢S (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢t) refl , IHΓ , IHΛ
  where
    IHΛ : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHΛ (↝Λ {i = i} Sᵢ↝ tᵢ↝) ⊢Λtᵢ
      with jᵢ , Tᵢ , Tᵢ≈ , i≡maxjᵢ , ⊢tᵢ ← Λ-inv′ ⊢Λtᵢ 
      with ⊢∷ ⊢Γ ⊢Sᵢ , _ ← presup-tm ⊢tᵢ
      with S≈Sᵢ ← IHS Sᵢ↝ ⊢Sᵢ
      with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈Sᵢ)))
      with S₁≈S₂ ← ctxeq-≈ Γ≈Γ₁ (≈-trans (≈-sym S≈S₁) S≈Sᵢ)
      with Sᵢ∷Γ≈S₁∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁)  S₁≈S₂
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm (⊢≈-sym Sᵢ∷Γ≈S₁∷Γ₁) ⊢tᵢ)
      = ≈-conv (≈-sym (Λ-cong ⊢Sᵢ (≈-sym S≈Sᵢ) (ctxeq-≈ Sᵢ∷Γ≈S₁∷Γ₁ (≈-sym t≈tᵢ)) i≡maxjᵢ)) (≈-sym Tᵢ≈)

⫢Λ-E : ∀ {i j} →
       U.Γ′ ⫢ U.S′ ∶ Se i →
       U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
       U.Γ′ ⫢ U.r′ ∶ Π U.S′ U.T′ →
       U.Γ′ ⫢ U.s′ ∶ U.S′ →
       --------------------
       U.Γ′ ⫢ U.r′ $ U.s′ ∶ U.T′ U.[| U.s′ ∶ U.S′ ]
⫢Λ-E ⫢S′ ⫢T′ ⫢r′ ⫢s′
  with  _ , Γ , S , _ , Γ↝ , S↝S′ , ↝Se , ⊢S , IHΓ , IHS ← ⫢S′
     | _ , .(S₁ ↙ _) L.∷ Γ₁ , T , .(Se _) , (↝∷ {T = S₁} Γ↝₁ S↝₁S′) , T↝ , ↝Se , ⊢T , _ , IHT ← ⫢T′
     | k , Γ₂ , r , _ , Γ↝₂ , r↝r′ , ↝Π S↝₂S′ T↝T′ , ⊢r , _ , IHr ← ⫢r′
     | j , Γ₃ , s , S₃ , Γ↝₃ , s↝s′ , S↝₃S′ , ⊢s , _ , IHs ← ⫢s′ 
  with refl ← ⊢T:Se-lvl ⊢S
     | refl ← ⊢T:Se-lvl ⊢T 
  with ⊢∷ ⊢Γ₁ ⊢S₁ ← proj₁ (presup-tm ⊢T)
     | ⊢Γ₂ , ⊢ΠS₂T₁ ← presup-tm ⊢r
     | ⊢Γ₃ , ⊢S₃ ← presup-tm ⊢s
  with IHΓ Γ↝₁ ⊢Γ₁
     | IHΓ Γ↝₂ ⊢Γ₂
     | IHΓ Γ↝₃ ⊢Γ₃
...  | Γ≈Γ₁ | Γ≈Γ₂ | Γ≈Γ₃ 
  with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
  with S≈S₁ ← IHS S↝₁S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁)
     | S≈S₂ ← IHS S↝₂S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₂)
     | S≈S₃ ← IHS S↝₃S′ (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₃) 
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
     | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃))) 
  with T≈T₁ ← IHT T↝T′ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₂ (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁) 
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
  = _ , _ , _ , _ , Γ↝ , ↝$ r↝r′ s↝s′ , ↝sub T↝ (↝, ↝I s↝s′ S↝S′) , 
    Λ-E ⊢S 
        (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-sym S≈S₁))) ⊢T) 
        (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢r) 
              (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢S₂) (≈-sym S≈S₂) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (ctxeq-≈ Γ≈Γ₁ (≈-trans (≈-sym S≈S₁) S≈S₂))) (≈-sym T≈T₁)) refl)) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢s) (≈-sym S≈S₃)) 
        refl , 
    IHΓ , IHrs
  where
    IHrs : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHrs (↝$ rᵢ↝ sᵢ↝) ⊢Λrs
      with j , k , Sᵢ , Tᵢ , ⊢rᵢ , ⊢sᵢ , i≡maxjk , ≈T[|s] ← $-inv ⊢Λrs
      with _ , ⊢Sᵢ , ⊢Tᵢ ← Π-inv (proj₂ (presup-tm ⊢rᵢ)) 
      with rᵢ≈r ← IHr rᵢ↝ (ctxeq-tm Γ≈Γ₂ ⊢rᵢ)
         | sᵢ≈s ← IHs sᵢ↝ (ctxeq-tm Γ≈Γ₃ ⊢sᵢ) = ≈-conv (≈-sym ($-cong ⊢Sᵢ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) (≈-sym rᵢ≈r)) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) (≈-sym sᵢ≈s)) i≡maxjk)) (≈-sym ≈T[|s])

⫢L-I : ∀ {j} →
       U.Γ′ ⫢ U.t′ ∶ U.T′ →
       --------------------
       U.Γ′ ⫢ liftt j U.t′ ∶ Liftt j U.T′
⫢L-I ⫢t′
  with i , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHΓ , IHt ← ⫢t′
    = _ , _ , _ , _ , Γ↝ , ↝liftt t↝ , ↝Liftt T↝ , L-I _ ⊢t , IHΓ , IHlift
  where
    IHlift : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHlift (↝liftt tᵢ↝) ⊢lifttᵢ
      with liftt-inv ⊢lifttᵢ
    ... | jᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ = ≈-conv (liftt-cong _ (IHt tᵢ↝ ⊢tᵢ))  (≈-sym Tᵢ≈)

⫢L-E : ∀ {i j} →
       U.Γ′ ⫢ U.T′ ∶ Se i →
       U.Γ′ ⫢ U.t′ ∶ Liftt j U.T′ →
       --------------------
       U.Γ′ ⫢ unlift U.t′ ∶ U.T′
⫢L-E ⫢T′ ⫢t′
  with i , Γ , T , _ , Γ↝ , T↝ , ↝Se , ⊢T , IHΓ , IHT ← ⫢T′
     | j , Γ₁ , t , _ , Γ₁↝ , t↝ , ↝Liftt T₁↝ , ⊢t , _ , IHt ← ⫢t′ 
  with ⊢Γ₁ , ⊢LifttT₁ ← presup-tm ⊢t
  with refl , ⊢T₁ ← Liftt-inv ⊢LifttT₁
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
  with refl ← ⊢T:Se-lvl ⊢T
  with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T₁)
  with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) 
  = _ , _ , _ , _ , Γ↝ , ↝unlift t↝ , T↝ , 
    L-E _ ⊢T (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢t) (Liftt-cong _ (≈-sym T≈T₁))) , 
    IHΓ , IHlift

  where
    IHlift : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHlift (↝unlift tᵢ↝) ⊢unlifttᵢ
      with jᵢ , nᵢ , Sᵢ , refl , ⊢tᵢ , Tᵢ≈ ← unlift-inv ⊢unlifttᵢ
      with _ , ⊢Tᵢ ← Liftt-inv (proj₂ (presup-tm ⊢tᵢ))
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ) 
      = ≈-conv (unlift-cong _ ⊢Tᵢ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t≈tᵢ))  (≈-sym Tᵢ≈)

⫢t[σ] : U.Δ′ ⫢ U.t′ ∶ U.T′ →
        U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
        --------------------
        U.Γ′ ⫢ U.t′ U.[ U.σ′ ] ∶ U.T′ U.[ U.σ′ ]
⫢t[σ] ⫢t′ ⫢σ′
  with i , Δ , t , T , Δ↝ , t↝ , T↝ , ⊢t , IHΔ , IHt ← ⫢t′
     | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
  = _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub T↝ σ↝ , t[σ] ⊢t (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) , IHΓ , IHt[σ] 
  where 
    IHt[σ] : ∀ {tᵢ iᵢ Tᵢ} → tᵢ ↝ _ → Γ A.⊢ tᵢ ∶[ iᵢ ] Tᵢ → Γ ⊢ _ ≈ tᵢ ∶[ iᵢ ] Tᵢ
    IHt[σ] (↝sub tᵢ↝ σᵢ↝) ⊢tᵢ[σ]
      with Δᵢ , S , ⊢σᵢ , ⊢tᵢ , ≈S[σᵢ] ← t[σ]-inv ⊢tᵢ[σ]
      with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
      with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
      with Δᵢ≈Δ ← ⊢≈-trans (⊢≈-sym Δ₁≈Δᵢ) (⊢≈-sym Δ≈Δ₁)
      = ≈-conv (≈-sym ([]-cong (≈-sym (IHt tᵢ↝ (ctxeq-tm Δᵢ≈Δ ⊢tᵢ))) (s-≈-sym (IHσ σᵢ↝ (s-conv ⊢σᵢ Δᵢ≈Δ))))) (≈-sym ≈S[σᵢ])

⫢conv : ∀ {i} →
        U.Γ′ ⫢ U.t′ ∶ U.S′ →
        U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
        --------------------
        U.Γ′ ⫢ U.t′ ∶ U.T′
⫢conv ⫢t′ S′≈T′
  with i , Γ , t , S₁ , Γ↝ , t↝ , S₁↝ , ⊢t , IHΓ , IHt ← ⫢t′
     | _ , Γ₁ , S , T , _ , Γ₁↝ , S↝ , T↝ , ↝Se , S≈T , _ , IHS , _ ← S′≈T′ 
  with ⊢Γ₁ , ⊢S , _ , _ ← presup-≈ S≈T
  with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
  with refl ← ⊢T:Se-lvl ⊢S 
  with S≈S₁ ← IHS S₁↝ (ctxeq-tm Γ≈Γ₁ (proj₂ (presup-tm ⊢t))) 
  with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
  = _ , _ , _ , _ , Γ↝ , t↝ , T↝ , conv ⊢t (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans (≈-sym S≈S₁) S≈T)) , IHΓ , IHt

⫢s-I : ⫢ U.Γ′ →
       --------------------
       U.Γ′ ⫢s I ∶ U.Γ′
⫢s-I ⫢Γ′
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , Γ↝ , Γ↝ , ↝I , s-I ⊢Γ , IHΓ , λ { ↝I ⊢σᵢ → s-≈-refl ⊢σᵢ }

⫢s-wk : ⫢ U.T′ ∷ U.Γ′ →
        --------------------
        U.T′ ∷ U.Γ′ ⫢s wk ∶ U.Γ′
⫢s-wk ⫢T∷Γ′
  with .((_ ↙ _) L.∷ _) , ⊢∷ ⊢Γ ⊢T , ↝∷ Γ↝ T↝ , IHΓ ← ⫢T∷Γ′ = _ , _ , _ , ↝∷ Γ↝ T↝ , Γ↝ , ↝wk , s-wk (⊢∷ ⊢Γ ⊢T) , IHΓ , λ { ↝wk ⊢σᵢ → s-≈-refl ⊢σᵢ }

⫢s-∘ :  U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
        U.Δ′ ⫢s U.τ′ ∶ U.Ψ′ →
        --------------------
        U.Γ′ ⫢s U.τ′ ∘ U.σ′ ∶ U.Ψ′
⫢s-∘ ⫢σ′ ⫢τ′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHτ ← ⫢σ′
     | Δ , Ψ , τ , Δ↝ , Ψ↝ , τ↝ , ⊢τ , IHΔ , IHσ ← ⫢τ′ 
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
  = _ , _ , _ , Γ↝ , Ψ↝ , ↝∘ τ↝ σ↝ , s-∘ ⊢σ  (ctxeq-s Δ≈Δ₁ ⊢τ) , IHΓ , IHτ∘σ
  where 
    IHτ∘σ : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
    IHτ∘σ (↝∘ {σ = τᵢ} {τ = σᵢ} τᵢ↝ σᵢ↝) ⊢σᵢ∘τᵢ 
      with ∘-inv ⊢σᵢ∘τᵢ
    ...  | Ψᵢ , ⊢σᵢ , ⊢τᵢ
      with σ≈σᵢ ← (IHτ σᵢ↝ ⊢σᵢ)  
      with Δ₁≈Ψᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
      with Δ≈Ψᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Ψᵢ
      with τ≈τᵢ ← IHσ τᵢ↝ (ctxeq-s (⊢≈-sym Δ≈Ψᵢ) ⊢τᵢ)  = ∘-cong σ≈σᵢ (ctxeq-s-≈ Δ≈Ψᵢ τ≈τᵢ) 

⫢s-, : ∀ {i} →
       U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
       U.Δ′ ⫢ U.T′ ∶ Se i →
       U.Γ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
       -------------------------
       U.Γ′ ⫢s U.σ′ , U.t′ ∶ U.T′ ∶ U.T′ ∷ U.Δ′
⫢s-, ⫢σ′ ⫢T′ ⫢t′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | _ , Δ , T , _ , Δ↝ , T↝ , ↝Se , ⊢T , IHΔ , IHT ← ⫢T′
     | i , Γ₁ , t , _ , Γ₁↝ , t↝ , (↝sub {T₁} T↝₁ σ↝₁) , ⊢t , _ , IHt ← ⫢t′
  with refl ← ⊢T:Se-lvl ⊢T 
  with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢t))
     | Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
  = _ , _ , _ , Γ↝ , ↝∷ Δ↝ T↝ , (↝, σ↝ t↝ T↝) , 
    s-, (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) ⊢T ⊢t_ , IHΓ , IHσ,t
      --  _ , _ , _ , Γ↝ , ↝∷ Δ↝ T↝ , (↝, σ↝ t↝ T↝) , s-, (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) ⊢t_ , IHσ,t
  where
    ⊢t_ : Γ ⊢ t ∶[ _ ] sub T σ
    ⊢t_
      with ⊢T₁[σ] ← proj₂ (presup-tm ⊢t)
      with Δ₂ , S , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
      with σ≈σ₁ ← IHσ σ↝₁ (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ₁) 
      with Δ₁≈Δ₂ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁))) 
      with Δ₂≈Δ ← ⊢≈-trans (⊢≈-sym Δ₁≈Δ₂) (⊢≈-sym Δ≈Δ₁)
      with T≈T₁ ← IHT T↝₁ (ctxeq-tm Δ₂≈Δ ⊢T₁) 
      with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) 
      = conv (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢t) ([]-cong-Se (ctxeq-≈ (⊢≈-sym Δ₂≈Δ) (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se))) (proj₁ (proj₂ (proj₂ (presup-s-≈ σ≈σ₁)))) (s-≈-sym σ≈σ₁))

    IHσ,t : (∀ {σᵢ Δᵢ} → σᵢ ↝s _ → Γ A.⊢s σᵢ ∶ Δᵢ → Γ A.⊢s _ ≈ σᵢ ∶ Δᵢ)
    IHσ,t  (↝, {σ = σᵢ} {t = tᵢ} {T = Tᵢ} σᵢ↝ tᵢ↝ Tᵢ↝) ⊢σᵢ,
      with ,-inv ⊢σᵢ,
    ...  | Δᵢ , ⊢σᵢ , ⊢tᵢ , ≈T∷Δᵢ
      with ⊢Tᵢ[σᵢ] ← proj₂ (presup-tm ⊢tᵢ)
      with S , ⊢Tᵢ , Seᵢ≈S[σᵢ] ← t[σ]-inv′ ⊢Tᵢ[σᵢ] ⊢σᵢ
      with σ≈σᵢ ← IHσ σᵢ↝ ⊢σᵢ 
      with Δ₁≈Δᵢ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σᵢ))) 
      with Δ≈Δᵢ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δᵢ
      with T≈Tᵢ ← IHT Tᵢ↝ (ctxeq-tm (⊢≈-sym Δ≈Δᵢ) ⊢Tᵢ)
      with t≈tᵢ ← IHt tᵢ↝ (ctxeq-tm Γ≈Γ₁ ⊢tᵢ) 
      with refl , Sei≈ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈Tᵢ))) 
      = s-≈-conv (,-cong σ≈σᵢ 
                         (ctxeq-tm Δ≈Δᵢ ⊢T) 
                         (ctxeq-≈ Δ≈Δᵢ (≈-conv T≈Tᵢ (≈-sym Sei≈))) 
                         (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t≈tᵢ) ([]-cong-Se (≈-conv (≈-sym T≈Tᵢ) (≈-sym Sei≈)) (s-conv ⊢σᵢ (⊢≈-sym Δ≈Δᵢ)) (s-≈-conv (s-≈-sym σ≈σᵢ) (⊢≈-sym Δ≈Δᵢ))))) 
                 (⊢≈-trans (∷-cong″ (ctxeq-≈ Δ≈Δᵢ (≈-conv T≈Tᵢ (≈-sym Sei≈)))) ≈T∷Δᵢ) 

⫢s-conv : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
          ⫢ U.Δ′ ≈ U.Ψ′ →
          -------------------------
          U.Γ′ ⫢s U.σ′ ∶ U.Ψ′
⫢s-conv ⫢σ′ Δ′≈Ψ′
  with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′
     | Δ , Ψ , Δ↝ , Ψ↝ , Δ≈Ψ , IHΔ , _ ← Δ′≈Ψ′ 
  with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ)) 
     = _ , _ , _ , Γ↝ , Ψ↝ , σ↝ , s-conv ⊢σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Ψ) , IHΓ , IHσ

⫢N-[] : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
        --------------------
        U.Γ′ ⫢ N U.[ U.σ′ ] ≈ N ∶ Se 0
⫢N-[] ⫢σ′
  with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHΓ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝N σ↝ , ↝N , ↝Se , N-[] ⊢σ , IHΓ , helper , λ { ↝N ⊢N → ≈-refl ⊢N }
  where 
    helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
    helper (↝sub ↝N σ₁↝) ⊢N[σᵢ] 
      with Δᵢ , SeS , ⊢σᵢ , ⊢N , T≈ ← t[σ]-inv ⊢N[σᵢ] 
      with refl , T≈Se ← N:T-inv′ ⊢N
      with σᵢ≈σ ← IHσ σ₁↝ ⊢σᵢ
      = ≈-conv (≈-sym ([]-cong (≈-refl ⊢N) (s-≈-sym σᵢ≈σ))) (≈-sym T≈)

-- ⫢Se-[] : ∀ {i} →
--           U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           --------------------
--           U.Γ′ ⫢ Se i U.[ U.σ′ ] ≈ Se i ∶ Se (1 + i)
-- ⫢Se-[] ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝Se σ↝ , ↝Se , ↝Se , Se-[] _ ⊢σ

-- ⫢Liftt-[] : ∀ {i j} →
--             ⫢ U.Δ′ →
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.T′ ∶ Se i →
--             --------------------
--             U.Γ′ ⫢ Liftt j U.T′ U.[ U.σ′ ] ≈ Liftt j (U.T′ U.[ U.σ′ ]) ∶ Se (j + i)
-- ⫢Liftt-[] ⫢Δ′ ⫢σ′ ⫢T′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-tm ⊢T))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Liftt T↝) σ↝ , ↝Liftt (↝sub T↝ σ↝) , ↝Se , Liftt-[] _ ⊢σ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢T)

-- ⫢Π-[] : ∀ {i j k} →
--          ⫢ U.Δ′ →
--          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--          U.Δ′ ⫢ U.S′ ∶ Se i →
--          (U.S′ ∷ U.Δ′) ⫢ U.T′ ∶ Se j →
--          k ≡ max i j →
--          --------------------
--          U.Γ′ ⫢ Π U.S′ U.T′ U.[ U.σ′ ] ≈ Π (U.S′ U.[ U.σ′ ]) (U.T′ U.[ U.q U.S′ U.σ′ ]) ∶ Se k
-- ⫢Π-[] ⫢Δ′ ⫢σ′ ⫢S′ ⫢T′ k≡maxij
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--       | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--       | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--       | _ , _ , T , _ , (↝∷ {Γ = Δ₃} {T = S₁} Δ₃↝ S₁↝) , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--   with refl ← ⊢T:Se-lvl ⊢S
--     | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--     | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
--     | ⊢∷ ⊢Δ₃ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--     | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--     | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--   with Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₃
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Δ₂≈Δ₃) ⊢S₁)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Π S↝ T↝) σ↝ , ↝Π (↝sub S↝ σ↝) (↝sub T↝ (↝, (↝∘ σ↝ ↝wk) ↝v S↝)) , ↝Se ,
--       Π-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₃) (ctxeq-≈ Δ₂≈Δ₃ (≈-sym S≈S₁))) ⊢T) k≡maxij

-- ⫢Π-cong : ∀ {i j k S₁′ S₂′ T₁′ T₂′} →
--            ⫢ U.Γ′ → -- extra condition
--            U.Γ′ ⫢ S₁′ ∶ Se i →
--            U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
--            S₁′ ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se j →
--            k ≡ max i j →
--            --------------------
--            U.Γ′ ⫢ Π S₁′ T₁′ ≈ Π S₂′ T₂′ ∶ Se k
-- ⫢Π-cong ⫢Γ′ ⫢S₁′ S₁′≈S₂′ T₁′≈T₂′ k≡maxij
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S₁₁ , _ , Γ₁↝ , S₁₁↝ , ↝Se , ⊢S₁ , IHS₁ ← ⫢S₁′
--      | _ , Γ₂ , S₁₂ , S₂₁ , _ , Γ₂↝ , S₁₂↝ , S₂₁↝ , ↝Se , S₁₂≈S₂₁ ← S₁′≈S₂′
--      | _ , S∷Γ₃ , T₁₁ , T₂₁ , _ , (↝∷ {T = S₁₃} Γ₃↝ S₁₃↝) , T₁₁↝ , T₂₁↝ , ↝Se , T₁₁≈T₂₁ ← T₁′≈T₂′
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S₁)
--      | ⊢Γ₂ , ⊢S₁₂ , _ ← presup-≈ S₁₂≈S₂₁
--      | ⊢∷ ⊢Γ₃ ⊢S₁₃ ← proj₁ (presup-≈ T₁₁≈T₂₁)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with refl ← ⊢T:Se-lvl ⊢S₁
--      | refl ← ⊢T≈S:Se-lvl S₁₂≈S₂₁
--      | refl ← ⊢T≈S:Se-lvl T₁₁≈T₂₁
--   with Γ₂≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁
--      | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S₁≈S₁₂ ← IHS₁ S₁₂↝ (ctxeq-tm Γ₂≈Γ₁ ⊢S₁₂)
--      | S₁≈S₁₃ ← IHS₁ S₁₃↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₁₃)
--   with refl ← unique-lvl ⊢S₁ (proj₁ (proj₂ (presup-≈ S₁≈S₁₃)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝Π S₁₁↝ T₁₁↝ , ↝Π S₂₁↝ T₂₁↝ , ↝Se ,
--       Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-trans S₁≈S₁₂ (ctxeq-≈ Γ₂≈Γ₁ S₁₂≈S₂₁))) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁≈S₁₃))) T₁₁≈T₂₁) k≡maxij

-- ⫢Liftt-cong : ∀ {i j} →
--               U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
--               --------------------
--               U.Γ′ ⫢ Liftt j U.S′ ≈ Liftt j U.T′ ∶ Se (j + i)
-- ⫢Liftt-cong S′≈T′
--   with _ , Γ , S , T , _ , Γ↝ , S↝ , T↝ , ↝Se , S≈T ← S′≈T′
--   with refl ← ⊢T≈S:Se-lvl S≈T = _ , _ , _ , _ , _ , Γ↝ , ↝Liftt S↝ , ↝Liftt T↝ , ↝Se , Liftt-cong _ S≈T

-- ⫢v-≈ : ∀ {x} →
--        ⫢ U.Γ′ →
--        x ∶ U.T′ ∈! U.Γ′ →
--        --------------------
--        U.Γ′ ⫢ v x ≈ v x ∶ U.T′
-- ⫢v-≈ ⫢Γ′ x∈Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--   with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′ = _ , _ , _ , _ , _ , Γ↝ , ↝v , ↝v , T↝ , v-≈ ⊢Γ x∈Γ

-- ⫢ze-≈ : ⫢ U.Γ′ →
--         --------------------
--         U.Γ′ ⫢ ze ≈ ze ∶ N
-- ⫢ze-≈ ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝ze , ↝ze , ↝N , ze-≈ ⊢Γ

-- ⫢su-cong : U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ N →
--         --------------------
--         U.Γ′ ⫢ su U.s′ ≈ su U.t′ ∶ N
-- ⫢su-cong s′≈t′
--   with _ , Γ , s , t , _ , Γ↝ , s↝ , t↝ , ↝N , s≈t ← s′≈t′
--   with refl ← ⊢t≈s∶N-lvl s≈t
--     = _ , _ , _ , _ , _ , Γ↝ , ↝su s↝ , ↝su t↝ , ↝N , su-cong s≈t

-- ⫢rec-cong : ∀ {i T₁′ T₂′ s₁′ s₂′ r₁′ r₂′ t₁′ t₂′} →
--             ⫢ U.Γ′ → -- extra condition
--             N ∷ U.Γ′ ⫢ T₁′ ∶ Se i →
--             N ∷ U.Γ′ ⫢ T₁′ ≈ T₂′ ∶ Se i →
--             U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ T₁′ U.[| ze ∶ N ] →
--             T₁′ ∷ N ∷ U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ T₁′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--             U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ N →
--             --------------------
--             U.Γ′ ⫢ rec T₁′ s₁′ r₁′ t₁′ ≈ rec T₂′ s₂′ r₂′ t₂′ ∶ T₁′ U.[| t₁′ ∶ N ]
-- ⫢rec-cong ⫢Γ′ ⫢S′ T₁′≈T₂′ s₁′≈s₂′ r₁≈r₂′ t₁≈t₂′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , N∷Γ₁ , T₁₁ , _ , (↝∷ Γ₁↝ ↝N) , T₁₁↝ , ↝Se , ⊢T₁₁ , IHT₁ ← ⫢S′
--      | _ , N∷Γ₂ , T₁₂ , T₂₁ , _ , (↝∷ Γ₂↝ ↝N) , T₁₂↝ , T₂₁↝ , ↝Se , T₁₂≈T₂₁ ← T₁′≈T₂′
--      | _ , Γ₃ , s₁ , s₂ , _ , Γ₃↝ , s₁↝ , s₂↝ , ↝sub {t = T₁₃} T₁₃↝ (↝, ↝I ↝ze ↝N) , s₁≈s₂ ← s₁′≈s₂′
--      | _ , T₁∷N∷Γ₄ , r₁ , r₂ , _ , ↝∷ {T = T₁₅} (↝∷ Γ₄↝ ↝N) T₁₅↝ , r₁↝ , r₂↝ , ↝sub {t = T₁₄} T₁₄↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , r₁≈r₂ ← r₁≈r₂′
--      | _ , Γ₅ , t₁ , t₂ , N , Γ₅↝ , t₁↝ , t₂↝ , ↝N , t₁≈t₂ ← t₁≈t₂′
--   with refl ← ⊢T:Se-lvl ⊢T₁₁
--      | refl ← ⊢T≈S:Se-lvl T₁₂≈T₂₁
--   with _ , refl , ⊢T₁₃ ← T[I,ze]-inv (proj₂ (proj₂ (proj₂ (presup-≈ s₁≈s₂))))
--      | _ , refl , ⊢T₁₄ ← T[wkwk,suv1]-inv (proj₂ (proj₂ (proj₂ (presup-≈ r₁≈r₂))))
--   with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T₁₁)
--      | ⊢∷ ⊢Γ₂ ⊢N₂ ← proj₁ (presup-≈ T₁₂≈T₂₁)
--      | ⊢Γ₃ ← proj₁ (presup-≈ s₁≈s₂)
--      | ⊢∷ (⊢∷ ⊢Γ₄ ⊢N₃) ⊢T₁₅ ← proj₁ (presup-≈ r₁≈r₂)
--      | ⊢Γ₅ ← proj₁ (presup-≈ t₁≈t₂)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--      | Γ≈Γ₅ ← IHΓ Γ₅↝ ⊢Γ₅
--   with refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₃)
--      | refl ← ⊢t≈s∶N-lvl t₁≈t₂
--   with T₁₁≈T₁₂ ← IHT₁ T₁₂↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl ⊢N₂)) (proj₁ (proj₂ (presup-≈ T₁₂≈T₂₁))))
--      | T₁₁≈T₁₃ ← IHT₁ T₁₃↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₃))) ⊢T₁₃)
--      | T₁₁≈T₁₄ ← IHT₁ T₁₄↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) (≈-refl ⊢N₃)) ⊢T₁₄)
--      | T₁₁≈T₁₅ ← IHT₁ T₁₅↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) (≈-refl ⊢N₃)) ⊢T₁₅)
--   with refl , ≈Se ← unique-typ ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₃)))
--      | refl , ≈Se₁ ← unique-typ ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₄)))
--      | refl ← unique-lvl ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₅)))
--   with N∷Γ₁≈N∷Γ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
--      = _ , _ , _ , _ , _ , Γ↝ , ↝rec T₁₁↝ s₁↝ r₁↝ t₁↝ , ↝rec T₂₁↝ s₂↝ r₂↝ t₂↝ , ↝sub T₁₁↝ (↝, ↝I t₁↝ ↝N) ,
--       rec-cong (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)) ⊢T₁₁)
--                (≈-trans (ctxeq-≈ N∷Γ₁≈N∷Γ T₁₁≈T₁₂) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (≈-refl ⊢N₂)) T₁₂≈T₂₁))
--                (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) s₁≈s₂) ([]-cong-Se (≈-conv (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T₁₁≈T₁₃)) (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym ≈Se))) (⊢I,ze ⊢Γ) (s-≈-refl (⊢I,ze ⊢Γ))))
--                (≈-conv (ctxeq-≈ (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₄) (≈-refl ⊢N₃)) (ctxeq-≈ (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₄) (≈-refl ⊢N₁)) (≈-sym T₁₁≈T₁₅))) r₁≈r₂)
--                        ([]-cong-Se (≈-conv (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym T₁₁≈T₁₄)) (ctxeq-≈ N∷Γ₁≈N∷Γ (≈-sym ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T₁₁))) (s-≈-refl (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ₁≈N∷Γ ⊢T₁₁))))))
--                (ctxeq-≈ (⊢≈-sym Γ≈Γ₅) t₁≈t₂)

-- ⫢Λ-cong : ∀ {i S₁′ S₂′ t₁′ t₂′} →
--            ⫢ U.Γ′ → -- extra condition
--            U.Γ′ ⫢ S₁′ ∶ Se i →
--            U.Γ′ ⫢ S₁′ ≈ S₂′ ∶ Se i →
--            (S₁′ ∷ U.Γ′) ⫢ t₁′ ≈ t₂′ ∶ U.T′ →
--            --------------------
--            U.Γ′ ⫢ Λ S₁′ t₁′ ≈ Λ S₂′ t₂′ ∶ Π S₁′ U.T′
-- ⫢Λ-cong ⫢Γ′ ⫢S₁′ S₁′≈S₂′ ⫢t₁′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S₁₁ , _ , Γ₁↝ , S₁↝ , ↝Se , ⊢S₁₁ , IHS₁ ← ⫢S₁′
--      | _ , Γ₂ , S₁₂ , S₂₁ , _ , Γ₂↝ , S₁₂↝ , S₂₁↝ , ↝Se , S₁≈S₂ ← S₁′≈S₂′
--      | _ , S∷Γ₃ , t₁ , t₂ , T , ↝∷ {T = S₁₃} Γ₃↝ S₁₃↝ , t₁↝ , t₂↝ , T↝ , t₁≈t₂ ← ⫢t₁′
--   with refl ← ⊢T:Se-lvl ⊢S₁₁
--      | refl ← ⊢T≈S:Se-lvl S₁≈S₂
--   with ⊢∷ ⊢Γ₃ ⊢S₁₃ ← proj₁ (presup-≈ t₁≈t₂)
--      | ⊢Γ₂ , ⊢S₁₂ , _ ← presup-≈ S₁≈S₂
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢S₁₁))
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S₁₁≈S₁₂ ← IHS₁ S₁₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢S₁₂)
--      | S₁₁≈S₁₃ ← IHS₁ S₁₃↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₁₃)
--   with refl ← unique-lvl ⊢S₁₁ (proj₁ (proj₂ (presup-≈ S₁₁≈S₁₃)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝Λ S₁↝ t₁↝ , ↝Λ S₂₁↝ t₂↝ , ↝Π S₁↝ T↝ ,
--           Λ-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S₁₁) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁₁≈S₁₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) S₁≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁₁≈S₁₃))) t₁≈t₂) refl

-- ⫢$-cong : ∀ {i j s₁′ s₂′ r₁′ r₂′} →
--            ⫢ U.Γ′ → -- extra condition
--            U.Γ′ ⫢ U.S′ ∶ Se i →
--            (U.S′ ∷ U.Γ′) ⫢ U.T′ ∶ Se j →
--            U.Γ′ ⫢ r₁′ ≈ r₂′ ∶ Π U.S′ U.T′ →
--            U.Γ′ ⫢ s₁′ ≈ s₂′ ∶ U.S′ →
--            --------------------
--            U.Γ′ ⫢ r₁′ $ s₁′ ≈ r₂′ $ s₂′ ∶ U.T′ U.[| s₁′ ∶ U.S′ ]
-- ⫢$-cong ⫢Γ′ ⫢S′ ⫢T′ ⫢r₁′≈r₂′ ⫢s₁′≈s₂′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ↝₁ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , S₄∷Γ₂ , T , _ , ↝∷ {T = S₁} {i = i} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₃ , r₁ , r₂ , _ , Γ₃↝ , r₁↝ , r₂↝ , ↝Π S₂↝ T₁↝ , r₁≈r₂ ← ⫢r₁′≈r₂′
--      | _ , Γ₄ , s₁ , s₂ , S₃ , Γ₄↝ , s₁↝ , s₂↝ , S₃↝ , s₁≈s₂ ← ⫢s₁′≈s₂′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₃ , _ , _ , ⊢ΠS₂T₁ ← presup-≈ r₁≈r₂
--      | ⊢Γ₄ , _ , _ , ⊢S₃ ← presup-≈ s₁≈s₂
--   with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
--   with Γ≈Γ₁ ← IHΓ Γ↝₁ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--   with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--   with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
--      | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) ⊢S₃)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
--   with S₁≈S₂ ← ≈-trans (≈-sym S≈S₁) S≈S₂
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S₁≈S₂))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) =
--         _ , _ , _ , _ , _ , Γ↝ , ↝$ r₁↝ s₁↝ , ↝$ r₂↝ s₂↝ , ↝sub T↝ (↝, ↝I s₁↝ S↝) ,
--           $-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S)
--                  (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T)
--                  (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) r₁≈r₂) (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂))
--                                                                (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ S₁≈S₂)) (≈-sym T≈T₁)) refl))
--                  (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₄) s₁≈s₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃)))
--                  refl

-- ⫢liftt-cong : ∀ {j} →
--               U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′ →
--               --------------------
--               U.Γ′ ⫢ liftt j U.s′ ≈ liftt j U.t′ ∶ Liftt j U.T′
-- ⫢liftt-cong s′≈t′
--   with _ , Γ , s , t , T , Γ↝ , s↝ , t↝ , ↝T , s≈t ← s′≈t′ = _ , _ , _ , _ , _ , Γ↝ , ↝liftt s↝ , ↝liftt t↝ , ↝Liftt ↝T , liftt-cong _ s≈t

-- ⫢unliftt-cong : ∀ {i j} →
--                 ⫢ U.Γ′ → -- extra condition
--                 U.Γ′ ⫢ U.T′ ∶ Se i →
--                 U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ Liftt j U.T′ →
--                 --------------------
--                 U.Γ′ ⫢ unlift U.s′ ≈ unlift U.t′ ∶ U.T′
-- ⫢unliftt-cong ⫢Γ′ ⫢T′ ⫢s′≈t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , s , t , _ , Γ₂↝ , s↝ , t↝ , ↝Liftt {T = T₁} ↝T₁ , s≈t ← ⫢s′≈t′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , _ , _ , ⊢LifttT₁ ← presup-≈ s≈t
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--   with refl , ⊢T₁ ← Liftt-inv ⊢LifttT₁
--   with T≈T₁ ← IHT ↝T₁ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝unlift s↝ , ↝unlift t↝ , ↝T₁ , unlift-cong _ (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢T₁) (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t)

-- ⫢[]-cong : ⫢ U.Δ′ → -- extra condition
--            U.Δ′ ⫢ U.t′ ≈ U.s′ ∶ U.T′ →
--            U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--            --------------------
--            U.Γ′ ⫢ U.t′ U.[ U.σ′ ] ≈ U.s′ U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ]
-- ⫢[]-cong ⫢Δ′ t′≈s′ σ′≈τ′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | _ , Δ₁ , t , s , T , Δ₁↝ , t↝ , s↝ , ↝T , t≈s ← t′≈s′
--      | Γ , Δ₂ , σ , τ , Γ↝ , Δ₂↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₁ (presup-≈ t≈s))
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈τ))))
--      = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ σ↝ , ↝sub s↝ τ↝ , ↝sub ↝T σ↝ , []-cong (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) t≈s) σ≈τ

-- ⫢ze-[] :  U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           --------------------
--           U.Γ′ ⫢ ze U.[ U.σ′ ] ≈ ze ∶ N
-- ⫢ze-[] ⫢σ′
--   with Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′ = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝ze σ↝ , ↝ze , ↝N , ze-[] ⊢σ

-- ⫢su-[] : ⫢ U.Δ′ → -- extra condition
--          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--          U.Δ′ ⫢ U.t′ ∶ N →
--          --------------------
--          U.Γ′ ⫢ su U.t′ U.[ U.σ′ ] ≈ su (U.t′ U.[ U.σ′ ]) ∶ N
-- ⫢su-[] ⫢Δ′ ⫢σ′ ⫢t′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , t , _ , Δ₂↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢t∶N-lvl ⊢t
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ (proj₂ (presup-s ⊢σ))
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ (proj₁ (presup-tm ⊢t))
--       = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝su t↝) σ↝ , ↝su (↝sub t↝ σ↝) , ↝N , (su-[] (s-conv ⊢σ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂)) ⊢t)

-- ⫢rec-[] : ∀ {i} →
--           ⫢ U.Δ′ → -- extra condition
--           U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--           N ∷ U.Δ′ ⫢ U.T′ ∶ Se i →
--           U.Δ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
--           U.T′ ∷ N ∷ U.Δ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--           U.Δ′ ⫢ U.t′ ∶ N →
--           --------------------
--           U.Γ′ ⫢ rec U.T′ U.s′ U.r′ U.t′ U.[ U.σ′ ] ≈ rec (U.T′ U.[ U.q N U.σ′ ]) (U.s′ U.[ U.σ′ ]) (U.r′ U.[ U.q U.T′ (U.q N U.σ′) ]) (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.t′ U.[ U.σ′ ] ∶ N ]
-- ⫢rec-[] ⫢Δ′ ⫢σ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , _ , T , _ , ↝∷ {Γ = Δ₂} Δ₂↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | i , Δ₃ , s , _ , Δ₃↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
--      | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Δ₄} Δ₄↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
--      | _ , Δ₅ , t , _ , Δ₅↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢∷ ⊢Δ₂ ⊢N₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Δ₃ ← proj₁ (presup-tm ⊢s)
--      | ⊢∷ (⊢∷ ⊢Δ₄ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
--      | ⊢Δ₅ ← proj₁ (presup-tm ⊢t)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--      | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
--      | Δ≈Δ₅ ← IHΔ Δ₅↝ ⊢Δ₅
--   with Δ₂≈Δ₄ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₄
--   with refl ← ⊢T:Se-lvl ⊢T
--      | refl ← ⊢t∶N-lvl ⊢t
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--   with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
--      | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) (≈-refl (N-wf ⊢Δ₃))) ⊢T₁)
--      | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ₂≈Δ₄) (≈-refl ⊢N₂)) ⊢T₂)
--      | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ₂≈Δ₄) (≈-refl ⊢N₂)) ⊢T₃)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
--      | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
--      = _ , _ , _ , _ , _ , Γ↝ ,
--       ↝sub (↝rec T↝ s↝ r↝ t↝) σ↝ , ↝rec (↝sub T↝ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N)) (↝sub s↝ σ↝) (↝sub r↝ (↝, (↝∘ (↝, (↝∘ σ↝ ↝wk) ↝v ↝N) ↝wk) ↝v T↝)) (↝sub t↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub t↝ σ↝) ↝N) ,
--         rec-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁))
--                (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ⊢T)
--                (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym T≈T₁)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym ≈Se))) (⊢I,ze ⊢Δ)))
--                (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Δ≈Δ₄) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp Δ₂≈Δ₄ (≈-refl ⊢N₁)) (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (≈-conv (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Δ (N-wf  ⊢Δ)) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-refl ⊢N₁)) ⊢T)))))
--                (ctxeq-tm (⊢≈-sym Δ≈Δ₅) ⊢t)

-- ⫢Λ-[] : ∀ {i} →
--          ⫢ U.Δ′ → -- extra condition
--          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--          U.Δ′ ⫢ U.S′ ∶ Se i →
--          U.S′ ∷ U.Δ′ ⫢ U.t′ ∶ U.T′ →
--          --------------------
--          U.Γ′ ⫢ Λ U.S′ U.t′ U.[ U.σ′ ] ≈ Λ (U.S′ U.[ U.σ′ ]) (U.t′ U.[ U.q U.S′ U.σ′ ]) ∶ Π U.S′ U.T′ U.[ U.σ′ ]
-- ⫢Λ-[] ⫢Δ′ ⫢σ′ ⫢S′ ⫢t′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , t , T , ↝∷ {Γ = Δ₃} {T = S₁} Δ₃↝ S₁↝ , t↝ , ↝T , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Δ₃ ⊢S₁ ← proj₁ (presup-tm ⊢t)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢S₁)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝Λ S↝ t↝) σ↝ , ↝Λ (↝sub S↝ σ↝) (↝sub t↝ (↝, (↝∘ σ↝ ↝wk) ↝v S↝)) , ↝sub (↝Π S↝ ↝T) σ↝ , Λ-[] (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₃) (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₃) (≈-sym S≈S₁))) ⊢t) refl

-- ⫢$-[] : ∀ {i j} →
--          ⫢ U.Δ′ → -- extra condition
--          U.Δ′ ⫢ U.S′ ∶ Se i →
--          U.S′ ∷ U.Δ′ ⫢ U.T′ ∶ Se j →
--          U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--          U.Δ′ ⫢ U.r′ ∶ Π U.S′ U.T′ →
--          U.Δ′ ⫢ U.s′ ∶ U.S′ →
--          --------------------
--          U.Γ′ ⫢ (U.r′ $ U.s′) U.[ U.σ′ ] ≈ (U.r′ U.[ U.σ′ ]) $ (U.s′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ , U.s′ U.[ U.σ′ ] ∶ U.S′ ]
-- ⫢$-[] ⫢Δ′ ⫢S′ ⫢T′ ⫢σ′ ⫢r′ ⫢s′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | _ , Δ₁ , S , _ , Δ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , T , _ , ↝∷ {Γ = Δ₂} {T = S₁} Δ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | Γ , Δ₃ , σ , Γ↝ , Δ₃↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₄ , r , _ , Δ₄↝ , r↝ , ↝Π S₂↝ T₁↝ , ⊢r , IHr ← ⫢r′
--      | _ , Δ₅ , s , S₃ , Δ₅↝ , s↝ , S₃↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ ← proj₁ (presup-tm ⊢S)
--       | ⊢∷ ⊢Δ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--       | ⊢Δ₃ ← proj₂ (presup-s ⊢σ)
--       | ⊢Δ₄ , ⊢ΠS₂T₁ ← presup-tm ⊢r
--       | ⊢Δ₅ , ⊢S₃ ← presup-tm ⊢s
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--      | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
--      | Δ≈Δ₅ ← IHΔ Δ₅↝ ⊢Δ₅
--   with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
--      | Δ₄≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₂
--   with refl , Se≈ , ⊢S₂ , ⊢T₁ ← Π-inv′ ⊢ΠS₂T₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Δ₁≈Δ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₁) ⊢S₂)
--      | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₅) Δ≈Δ₁) ⊢S₃)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp Δ₄≈Δ₂ (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₄) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝$ r↝ s↝) σ↝ , ↝$ (↝sub r↝ σ↝) (↝sub s↝ σ↝) , ↝sub T↝ (↝, σ↝ (↝sub s↝ σ↝) S↝) ,
--       $-[] (ctxeq-tm (⊢≈-sym Δ≈Δ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (ctxeq-≈ Δ₁≈Δ₂ (≈-sym S≈S₁))) ⊢T)
--            (s-conv ⊢σ (⊢≈-sym Δ≈Δ₃)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₄) ⊢r) (Π-cong (ctxeq-tm (⊢≈-sym Δ≈Δ₄) ⊢S₂) (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Δ≈Δ₂) (≈-trans (ctxeq-≈ Δ₁≈Δ₂ (≈-sym S≈S₁)) (ctxeq-≈ Δ₁≈Δ₂ S≈S₂))) (≈-sym T≈T₁)) refl)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₅) ⊢s) (ctxeq-≈ (⊢≈-sym Δ≈Δ₁) (≈-sym S≈S₃))) refl

-- ⫢liftt-[] : ∀ {i j} →
--             ⫢ U.Δ′ → -- extra condition
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.T′ ∶ Se i →
--             U.Δ′ ⫢ U.t′ ∶ U.T′ →
--             ------------------------
--             U.Γ′ ⫢ liftt j U.t′ U.[ U.σ′ ] ≈ liftt j (U.t′ U.[ U.σ′ ]) ∶ Liftt j U.T′ U.[ U.σ′ ]
-- ⫢liftt-[] ⫢Δ′ ⫢σ′ ⫢T′ ⫢t′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Δ₃ , t , T₁ , Δ₃↝ , t↝ , T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Δ₃ , ⊢T₁ ← presup-tm ⊢t
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝liftt t↝) σ↝ , ↝liftt (↝sub t↝ σ↝) , ↝sub (↝Liftt T↝) σ↝ , liftt-[] _ (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢t) (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-sym T≈T₁)))

-- ⫢unlift-[] : ∀ {i j} →
--              ⫢ U.Δ′ → -- extra condition
--              U.Δ′ ⫢ U.T′ ∶ Se i →
--              U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--              U.Δ′ ⫢ U.t′ ∶ Liftt j U.T′ →
--              ---------------------------------
--              U.Γ′ ⫢ unlift U.t′ U.[ U.σ′ ] ≈ unlift (U.t′ U.[ U.σ′ ]) ∶ U.T′ U.[ U.σ′ ]
-- ⫢unlift-[] ⫢Δ′ ⫢T′ ⫢σ′ ⫢t′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Δ₃ , t , _ , Δ₃↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Δ₃ , ⊢LiftT₁ ← presup-tm ⊢t
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--   with refl , ⊢T₁ , _ ← Liftt-inv′ ⊢LiftT₁
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₂) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁))) = _ , _ , _ , _ , _ , Γ↝ , ↝sub (↝unlift t↝) σ↝ , ↝unlift (↝sub t↝ σ↝) , ↝sub T↝ σ↝ , unlift-[] _ (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T) (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁)) (conv (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢t) (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Δ≈Δ₂) (≈-sym T≈T₁))))

-- ⫢rec-β-ze : ∀ {i} →
--             ⫢ U.Γ′ → -- extra condition
--             N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
--             U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--             --------------------
--             U.Γ′ ⫢ rec U.T′ U.s′ U.r′ ze ≈ U.s′ ∶ U.T′ U.[| ze ∶ N ]
-- ⫢rec-β-ze ⫢Γ′ ⫢T′ ⫢s′ ⫢r′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
--      | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₃} Γ₃↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
--   with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ ← proj₁ (presup-tm ⊢s)
--      | ⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with refl ← ⊢T:Se-lvl ⊢T
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--   with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
--   with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
--      | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₂))) ⊢T₁)
--      | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₂)
--      | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₃)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
--      | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
--      = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ ↝ze , s↝ , ↝sub T↝ (↝, ↝I ↝ze ↝N) , rec-β-ze (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₁)) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym ≈Se))) (⊢I,ze ⊢Γ))) (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym  Γ₃≈Γ₁) (≈-refl ⊢N₁)) (≈-sym T≈T₃))) ⊢r)
--         ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ N∷Γ≈N∷Γ₁ ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf  ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T)))))

-- ⫢rec-β-su : ∀ {i} →
--             ⫢ U.Γ′ → -- extra condition
--             N ∷ U.Γ′ ⫢ U.T′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.T′ U.[| ze ∶ N ] →
--             U.T′ ∷ N ∷ U.Γ′ ⫢ U.r′ ∶ U.T′ U.[ (wk ∘ wk) , su (v 1) ∶ N ] →
--             U.Γ′ ⫢ U.t′ ∶ N →
--             --------------------------------
--             U.Γ′ ⫢ rec U.T′ U.s′ U.r′ (su U.t′) ≈ U.r′ U.[ (I , U.t′ ∶ N) , rec U.T′ U.s′ U.r′ U.t′ ∶ U.T′ ] ∶ U.T′ U.[| su U.t′ ∶ N ]
-- ⫢rec-β-su ⫢Γ′ ⫢T′ ⫢s′ ⫢r′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₁} Γ₁↝ ↝N , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = T₁} T₁↝ (↝, ↝I ↝ze ↝N) , ⊢s , IHs ← ⫢s′
--      | _ , _ , r , _ , (↝∷ (↝∷ {Γ = Γ₃} Γ₃↝ ↝N) T₃↝) , r↝ , ↝sub {t = T₂} T₂↝ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N) , ⊢r , IHr ← ⫢r′
--      | _ , Γ₄ , t , _ , Γ₄↝ , t↝ , ↝N , ⊢t , IHt ← ⫢t′
--   with ⊢∷ ⊢Γ₁ ⊢N₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ ← proj₁ (presup-tm ⊢s)
--      | ⊢∷ (⊢∷ ⊢Γ₃ ⊢N₂) ⊢T₃ ← proj₁ (presup-tm ⊢r)
--      | ⊢Γ₄ ← proj₁ (presup-tm ⊢t)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--   with Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with N∷Γ≈N∷Γ₁ ← ∷-cong-simp (⊢≈-sym Γ≈Γ₁) (≈-refl ⊢N₁)
--   with refl ← ⊢T:Se-lvl ⊢T
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₁)
--      | refl ← N≈⇒eq-lvl (≈-refl ⊢N₂)
--      | refl ← ⊢t∶N-lvl ⊢t
--   with _ , refl , ⊢T₁ ← T[I,ze]-inv (proj₂ (presup-tm ⊢s))
--      | _ , refl , ⊢T₂ ← T[wkwk,suv1]-inv (proj₂ (presup-tm ⊢r))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) (≈-refl (N-wf ⊢Γ₂))) ⊢T₁)
--      | T≈T₂ ← IHT T₂↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₂)
--      | T≈T₃ ← IHT T₃↝ (ctxeq-tm (∷-cong-simp Γ₃≈Γ₁ (≈-refl ⊢N₂)) ⊢T₃)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      | refl , ≈Se₁ ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₂)))
--      | refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₃)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝rec T↝ s↝ r↝ (↝su t↝) , ↝sub r↝ (↝, (↝, ↝I t↝ ↝N) (↝rec T↝ s↝ r↝ t↝) T↝) , ↝sub T↝ (↝, ↝I (↝su t↝) ↝N) ,
--       rec-β-su (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₁)) (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym ≈Se))) (⊢I,ze ⊢Γ)))
--         (conv (ctxeq-tm (∷-cong-simp (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (≈-refl ⊢N₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym  Γ₃≈Γ₁) (≈-refl ⊢N₁)) (≈-sym T≈T₃))) ⊢r) ([]-cong-Se′ (≈-conv (ctxeq-≈ N∷Γ≈N∷Γ₁ (≈-sym T≈T₂)) (≈-sym (ctxeq-≈ N∷Γ≈N∷Γ₁ ≈Se₁))) (⊢[wk∘wk],su[v1] (⊢∷ (⊢∷ ⊢Γ (N-wf ⊢Γ)) (ctxeq-tm N∷Γ≈N∷Γ₁ ⊢T))))) (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢t)

-- ⫢Λ-β : ∀ {i j} →
--         ⫢ U.Γ′ → -- extra condition
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
--         U.S′ ∷ U.Γ′ ⫢ U.t′ ∶ U.T′ →
--         U.Γ′ ⫢ U.s′ ∶ U.S′ →
--         --------------------
--         U.Γ′ ⫢ (Λ U.S′ U.t′) $ U.s′ ≈ U.t′ U.[| U.s′ ∶ U.S′ ] ∶ U.T′ U.[| U.s′ ∶ U.S′ ]
-- ⫢Λ-β ⫢Γ′ ⫢S′ ⫢T′ ⫢t′ ⫢s′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | j , _ , t , T₁ , ↝∷ {Γ = Γ₃} {T = S₂} Γ₃↝ S₂↝ , t↝ , T₁↝ , ⊢t , IHt ← ⫢t′
--      | i , Γ₄ , s , S₃ , Γ₄↝ , s↝ , S₃↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢∷ ⊢Γ₃ ⊢S₂ , ⊢T₁ ← presup-tm ⊢t
--      | ⊢Γ₄ , ⊢S₃ ← presup-tm ⊢s
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--      | Γ≈Γ₄ ← IHΓ Γ₄↝ ⊢Γ₄
--   with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--      | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
--      | S≈S₃ ← IHS S₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₄) Γ≈Γ₁) ⊢S₃)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₃)))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝$ (↝Λ S↝ t↝) s↝ , ↝sub t↝ (↝, ↝I s↝ S↝) , ↝sub T↝ (↝, ↝I s↝ S↝) ,
--       Λ-β (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S)
--           (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T)
--           (conv (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₃) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-sym S≈S₂))) ⊢t) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) (≈-sym T≈T₁)))
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₄) ⊢s) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₃)))

-- ⫢Λ-η : ∀ {i j} →
--         ⫢ U.Γ′ → -- extra condition
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         U.S′ ∷ U.Γ′ ⫢ U.T′ ∶ Se j →
--         U.Γ′ ⫢ U.t′ ∶ Π U.S′ U.T′ →
--         --------------------
--         U.Γ′ ⫢ U.t′ ≈ Λ U.S′ (U.t′ U.[ wk ] $ v 0) ∶ Π U.S′ U.T′
-- ⫢Λ-η ⫢Γ′ ⫢S′ ⫢T′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , _ , T , _ , ↝∷ {Γ = Γ₂} {T = S₁} Γ₂↝ S₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₃ , t , _ , Γ₃↝ , t↝ , ↝Π S₂↝ T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢S
--      | refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢∷ ⊢Γ₂ ⊢S₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₃ , ⊢ΠS₂T₁ ← presup-tm ⊢t
--   with refl , ⊢S₂ , ⊢T₁ ← Π-inv ⊢ΠS₂T₁
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with Γ₁≈Γ₂ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂
--      | Γ₃≈Γ₁ ← ⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-sym Γ₁≈Γ₂) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm Γ₃≈Γ₁ ⊢S₂)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (∷-cong-simp (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) (ctxeq-≈ (⊢≈-sym Γ₃≈Γ₁) (≈-trans (≈-sym S≈S₂) S≈S₁))) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝Λ S↝ (↝$ (↝sub t↝ ↝wk) ↝v) , ↝Π S↝ T↝ ,
--       Λ-η (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-tm (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-sym S≈S₁))) ⊢T)
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢t)
--                 (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₃) ⊢S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂)) (ctxeq-≈ (∷-cong-simp (⊢≈-sym Γ≈Γ₂) (ctxeq-≈ Γ₁≈Γ₂ (≈-trans (≈-sym S≈S₁) S≈S₂)))
--                         (≈-sym T≈T₁)) refl)) refl

-- ⫢L-β : ∀ {j} →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ →
--        -----------------------------
--        U.Γ′ ⫢ unlift (liftt j U.t′) ≈ U.t′ ∶ U.T′
-- ⫢L-β ⫢t′
--   with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝unlift (↝liftt t↝) , t↝ , T↝ , L-β _ ⊢t

-- ⫢L-η : ∀ {i j} →
--        ⫢ U.Γ′ →
--        U.Γ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ Liftt j U.T′ →
--        -----------------------------
--        U.Γ′ ⫢ U.t′ ≈ liftt j (unlift U.t′) ∶ Liftt j U.T′
-- ⫢L-η ⫢Γ′ ⫢T′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , T , _ , Γ₁↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | _ , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝Liftt T₁↝ , ⊢t , IHt ← ⫢t′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , ⊢LiftT₁ ← presup-tm ⊢t
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--   with refl , ⊢T₁ ← Liftt-inv ⊢LiftT₁
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢T₁)
--   with refl ← unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--      = _ , _ , _ , _ , _ , Γ↝ , t↝ , ↝liftt (↝unlift t↝) , ↝Liftt T↝ , L-η _ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢T) (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢t) (Liftt-cong _ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym T≈T₁))))

-- ⫢[I] : U.Γ′ ⫢ U.t′ ∶ U.T′ →
--        ---------------------
--        U.Γ′ ⫢ U.t′ U.[ I ] ≈ U.t′ ∶ U.T′
-- ⫢[I] ⫢t′
--   with _ , Γ , t , T , Γ↝ , t↝ , T↝ , ⊢t , IHt ← ⫢t′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ ↝I , t↝ , T↝ , [I] ⊢t

-- ⫢[wk] : ∀ {i x} →
--         ⫢ U.Γ′ →
--         U.Γ′ ⫢ U.S′ ∶ Se i →
--         x ∶ U.T′ ∈! U.Γ′ →
--         ---------------------
--         U.S′ ∷ U.Γ′ ⫢ v x U.[ wk ] ≈ v (1 + x) ∶ U.T′ U.[ wk ]
-- ⫢[wk] ⫢Γ′ ⫢S′ x∈Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ (proj₁ (presup-tm ⊢S))
--   with i , T , T↝ , x∈Γ ← U⇒A-vlookup Γ↝ x∈Γ′
--     = _ , _ , _ , _ , _ , ↝∷ Γ↝ S↝ , ↝sub ↝v ↝wk , ↝v , ↝sub T↝ ↝wk , [wk] ⊢Γ (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) x∈Γ

-- ⫢[∘]  : ⫢ U.Ψ′ → -- extra condition
--         ⫢ U.Δ′ → -- extra condition
--         U.Γ′ ⫢s U.τ′ ∶ U.Ψ′ →
--         U.Ψ′ ⫢s U.σ′ ∶ U.Δ′ →
--         U.Δ′ ⫢ U.t′ ∶ U.T′ →
--         ---------------------
--         U.Γ′ ⫢ U.t′ U.[ U.σ′ ∘ U.τ′ ] ≈ U.t′ U.[ U.σ′ ] U.[ U.τ′ ] ∶ U.T′ U.[ U.σ′ ∘ U.τ′ ]
-- ⫢[∘] ⫢Ψ′ ⫢Δ′ ⫢τ′ ⫢σ′ ⫢t′
--   with Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Ψ₁ , τ , Γ↝ , Ψ₁↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Ψ₂ , Δ₁ , σ , Ψ₂↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | i , Δ₂ , t , T , Δ₂↝ , t↝ , T↝ , ⊢t , IHT ← ⫢t′
--   with ⊢Ψ₁ ← proj₂ (presup-s ⊢τ)
--      | ⊢Ψ₂ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢t)
--   with Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub t↝ (↝∘ σ↝ τ↝) , ↝sub (↝sub t↝ σ↝) τ↝ , ↝sub T↝ (↝∘ σ↝ τ↝) , [∘] ⊢τ (ctxeq-s (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) ⊢σ) (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢t)

-- ⫢[,]-v-ze : ∀ {i} →
--             ⫢ U.Γ′ → -- extra condition
--             ⫢ U.Δ′ → -- extra condition
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.S′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
--             ---------------------
--             U.Γ′ ⫢ v 0 U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ U.s′ ∶ U.S′ U.[ U.σ′ ]
-- ⫢[,]-v-ze ⫢Γ′ ⫢Δ′ ⫢σ ⫢S′ ⫢s′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ
--      | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | i , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Γ₂ , ⊢S₁[σ₁] ← presup-tm ⊢s
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--   with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁)
--   with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , s↝ , ↝sub S↝ σ↝ ,
--       [,]-v-ze (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁))
--                (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S)
--                (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₂) ⊢σ₁) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))

-- ⫢[,]-v-su : ∀ {i x} →
--             ⫢ U.Γ′ → -- extra condition
--             ⫢ U.Δ′ → -- extra condition
--             U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--             U.Δ′ ⫢ U.S′ ∶ Se i →
--             U.Γ′ ⫢ U.s′ ∶ U.S′ U.[ U.σ′ ] →
--             x ∶ U.T′ ∈! U.Δ′ →
--             ---------------------
--             U.Γ′ ⫢ v (1 + x) U.[ U.σ′ , U.s′ ∶ U.S′ ] ≈ v x U.[ U.σ′ ] ∶ U.T′ U.[ U.σ′ ]
-- ⫢[,]-v-su ⫢Γ′ ⫢Δ′ ⫢σ ⫢S′ ⫢s′ x∈Δ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ
--      | _ , Δ₂ , S , _ , Δ₂↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | i , Γ₂ , s , _ , Γ₂↝ , s↝ , ↝sub {t = S₁} S₁↝ σ₁↝ , ⊢s , IHs ← ⫢s′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Γ₂ , ⊢S₁[σ₁] ← presup-tm ⊢s
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢S)
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--   with Δ₃ , _ , ⊢σ₁ , ⊢S₁ , _ ← t[σ]-inv ⊢S₁[σ₁]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₃≈Δ₂ ← (⊢≈-trans (⊢≈-sym Δ₁≈Δ₃) (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂))
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm Δ₃≈Δ₂ ⊢S₁)
--   with refl , ≈Se ← unique-typ ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--   with j , T , T↝ , x∈Δ ← U⇒A-vlookup Δ↝ x∈Δ′
--     = _ , _ , _ , _ , _ , Γ↝ , ↝sub ↝v (↝, σ↝ s↝ S↝) , ↝sub ↝v σ↝ , ↝sub T↝ σ↝ ,
--         [,]-v-su (s-conv (ctxeq-s (⊢≈-sym Γ≈Γ₁) ⊢σ) (⊢≈-sym Δ≈Δ₁)) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢S)
--         (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢s) ([]-cong-Se (ctxeq-≈ (⊢≈-sym Δ₃≈Δ₂) (≈-conv (≈-sym S≈S₁) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₂) ⊢σ₁) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))
--         x∈Δ

-- ⫢≈-conv : ∀ {i} →
--           ⫢ U.Γ′ → -- extra condition
--           U.Γ′ ⫢ U.S′ ∶ Se i → -- extra condition
--           U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--           U.Γ′ ⫢ U.S′ ≈ U.T′ ∶ Se i →
--           ---------------------
--           U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.T′
-- ⫢≈-conv ⫢Γ′ ⫢S′ s′≈t′ S′≈T′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , S , _ , Γ₁↝ , S↝ , ↝Se , ⊢S , IHS ← ⫢S′
--      | _ , Γ₂ , s , t , S₁ , Γ₂↝ , s↝ , t↝ , S₁↝ , s≈t ← s′≈t′
--      | _ , Γ₃ , S₂ , T , _ , Γ₃↝ , S₂↝ , T↝ , ↝Se , S≈T ← S′≈T′
--   with refl ← ⊢T:Se-lvl ⊢S
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢S)
--      | ⊢Γ₂ , ⊢s , ⊢t , ⊢S₁ ← presup-≈ s≈t
--      | ⊢Γ₃ , ⊢S₂ , ⊢T , _ ← presup-≈ S≈T
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with S≈S₁ ← IHS S₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢S₁)
--      | S≈S₂ ← IHS S₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢S₂)
--   with refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
--      | refl ← unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₂)))
--     = _ , _ , _ , _ , _ , Γ↝ , s↝ , t↝ , T↝ , ≈-conv (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) S≈T))

-- ⫢≈-sym : U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--          ---------------------
--          U.Γ′ ⫢ U.t′ ≈ U.s′ ∶ U.S′
-- ⫢≈-sym s′≈t′
--   with _ , Γ , s , t , S , Γ↝ , s↝ , t↝ , S↝ , s≈t ← s′≈t′
--     = _ , _ , _ , _ , _ , Γ↝ , t↝ , s↝ , S↝ , ≈-sym s≈t

-- ⫢≈-trans : ⫢ U.Γ′ → -- extra condition
--            U.Γ′ ⫢ U.t′ ∶ U.S′ →
--            U.Γ′ ⫢ U.s′ ≈ U.t′ ∶ U.S′ →
--            U.Γ′ ⫢ U.t′ ≈ U.r′ ∶ U.S′ →
--            ---------------------
--            U.Γ′ ⫢ U.s′ ≈ U.r′ ∶ U.S′
-- ⫢≈-trans ⫢Γ′ ⫢t′ s′≈t′ t′≈r′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | _ , Γ₁ , t , S , Γ₁↝ , t↝ , S↝ , ⊢t , IHt ← ⫢t′
--      | _ , Γ₂ , s , t₁ , S₁ , Γ₂↝ , s↝ , t₁↝ , S₁↝ , s≈t ← s′≈t′
--      | _ , Γ₃ , t₂ , r , S₂ , Γ₃↝ , t₂↝ , r↝ , S₂↝ , t≈r ← t′≈r′
--   with ⊢Γ₁ ← proj₁ (presup-tm ⊢t)
--      | ⊢Γ₂ , ⊢s , ⊢t₁ , ⊢S₁ ← presup-≈ s≈t
--      | ⊢Γ₃ , ⊢t₂ , ⊢r , ⊢S₂ ← presup-≈ t≈r
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with t≈t₁ ← IHt t₁↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢t₁)
--      | t≈t₂ ← IHt t₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢t₂)
--   with refl , S≈S₁ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₁)))
--      | refl , S≈S₂ ← unique-typ ⊢t (proj₁ (proj₂ (presup-≈ t≈t₂)))
--   with t₁≈t₂ ← ≈-trans (≈-sym t≈t₁) (≈-conv t≈t₂ (≈-trans (≈-sym S≈S₂) S≈S₁))
--     = _ , _ , _ , _ , _ , Γ↝ , s↝ , r↝ , S↝ ,
--       ≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₂) s≈t) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-trans (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) t₁≈t₂) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₁))) (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) t≈r) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) (≈-sym S≈S₂))))

-- ⫢I-≈ : ⫢ U.Γ′ →
--        ----------------
--         U.Γ′ ⫢s I ≈ I ∶ U.Γ′
-- ⫢I-≈ ⫢Γ′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--     = _ , _ , _ , _ , Γ↝ , Γ↝ , ↝I , ↝I , I-≈ ⊢Γ

-- ⫢wk-≈ : ⫢ U.S′ ∷ U.Γ′ →
--         ---------------------
--         U.S′ ∷ U.Γ′ ⫢s wk ≈ wk ∶ U.Γ′
-- ⫢wk-≈ ⫢S∷Γ′
--   with Γ , ⊢S∷Γ , S∷Γ↝@(↝∷ Γ↝ S↝) , IHΓ ← ⫢S∷Γ′ = _ , _ , _ , _ , S∷Γ↝ , Γ↝ , ↝wk , ↝wk , wk-≈ ⊢S∷Γ

-- ⫢∘-cong : ∀ {σ₁′ σ₂′ τ₁′ τ₂′} →
--           ⫢ U.Ψ′ → -- extra condition
--           U.Γ′ ⫢s τ₁′ ≈ τ₂′ ∶ U.Ψ′ →
--           U.Ψ′ ⫢s σ₁′ ≈ σ₂′ ∶ U.Δ′ →
--           ---------------------
--           U.Γ′ ⫢s σ₁′ ∘ τ₁′ ≈ σ₂′ ∘ τ₂′ ∶ U.Δ′
-- ⫢∘-cong ⫢Ψ′ τ₁′≈τ₂′ σ₁′≈σ₂′
--   with Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Γ , Ψ₁ , τ₁ , τ₂ , Γ↝ , Ψ₁↝ , τ₁↝ , τ₂↝ , τ₁≈τ₂ ← τ₁′≈τ₂′
--      | Ψ₂ , Δ , σ₁ , σ₂ , Ψ₂↝ , Δ↝ , σ₁↝ , σ₂↝ , σ₁≈σ₂ ← σ₁′≈σ₂′
--   with Ψ≈Ψ₁ ← IHΨ Ψ₁↝ (proj₂ (proj₂ (proj₂ (presup-s-≈ τ₁≈τ₂))))
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ (proj₁ (presup-s-≈ σ₁≈σ₂))
--   = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ σ₁↝ τ₁↝ , ↝∘ σ₂↝ τ₂↝ , ∘-cong (s-≈-conv τ₁≈τ₂ (⊢≈-sym Ψ≈Ψ₁)) (ctxeq-s-≈ (⊢≈-sym Ψ≈Ψ₂) σ₁≈σ₂)

-- ⫢,-cong : ∀ {i σ₁′ σ₂′ t₁′ t₂′ T₁′ T₂′ } →
--           ⫢ U.Γ′ → -- extra condition
--           ⫢ U.Δ′ → -- extra condition
--           U.Γ′ ⫢s σ₁′ ∶ U.Δ′ → -- extra condition
--           U.Γ′ ⫢s σ₁′ ≈ σ₂′ ∶ U.Δ′ →
--           U.Δ′ ⫢ T₁′ ∶ Se i →
--           U.Δ′ ⫢ T₁′ ≈ T₂′ ∶ Se i →
--           U.Γ′ ⫢ t₁′ ≈ t₂′ ∶ T₁′ U.[ σ₁′ ] →
--           ----------------------
--           U.Γ′ ⫢s (σ₁′ , t₁′ ∶ T₁′) ≈ (σ₂′ , t₂′ ∶ T₂′) ∶ T₁′ ∷ U.Δ′
-- ⫢,-cong ⫢Γ′ ⫢Δ′ ⫢σ₁′ σ₁′≈σ₂′ ⫢T₁′ T₁′≈T₂′ t₁′≈t₂′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ₁ , Δ₁ , σ₁ , Γ₁↝ , Δ₁↝ , σ₁↝ , ⊢σ₁ , IHσ₁ ← ⫢σ₁′
--      | Γ₂ , Δ₂ , σ₁₁ , σ₂ , Γ₂↝ , Δ₂↝ , σ₁₁↝ , σ₂↝ , σ₁≈σ₂ ← σ₁′≈σ₂′
--      | _ , Δ₃ , T₁₁ , _ , Δ₃↝ , T₁₁↝ , ↝Se , ⊢T₁₁ , IHT ← ⫢T₁′
--      | _ , Δ₄ , T₁₂ , T₂₁ , _ , Δ₄↝ , T₁₂↝ , T₂₁↝ , ↝Se , T₁≈T₂ ← T₁′≈T₂′
--      | i , Γ₃ , t₁ , t₂ , _ , Γ₃↝ , t₁↝ , t₂↝ , ↝sub {t = T₁₃} {σ = σ₁₂} T₁₃↝ σ₁₂↝ , t₁≈t₂ ← t₁′≈t₂′
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ₁
--      | ⊢Γ₂ , ⊢σ₁₁ , _ , ⊢Δ₂ ← presup-s-≈ σ₁≈σ₂
--      | ⊢Δ₃ ← proj₁ (presup-tm ⊢T₁₁)
--      | ⊢Δ₄ , ⊢T₁₂ , ⊢T₂₁ , _ ← presup-≈ T₁≈T₂
--      | ⊢Γ₃ , ⊢t₁ , ⊢t₂ , ⊢T₁₃[σ₁₂] ← presup-≈ t₁≈t₂
--   with Δ₅ , _ , ⊢σ₁₂ , ⊢T₁₃ , _ ← t[σ]-inv ⊢T₁₃[σ₁₂]
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--      | Δ≈Δ₄ ← IHΔ Δ₄↝ ⊢Δ₄
--   with σ₁≈σ₁₁ ← IHσ₁ σ₁₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁₁)
--      | σ₁≈σ₁₂ ← IHσ₁ σ₁₂↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢σ₁₂)
--   with Δ₁≈Δ₅ ← unique-ctx ⊢σ₁ (proj₁ (proj₂ (presup-s-≈ σ₁≈σ₁₂)))
--   with Δ≈Δ₅ ← ⊢≈-trans Δ≈Δ₁ Δ₁≈Δ₅
--   with refl ← ⊢T:Se-lvl ⊢T₁₁
--   with T₁₁≈T₁₂ ← IHT T₁₂↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₄) Δ≈Δ₃) ⊢T₁₂)
--      | T₁₁≈T₁₃ ← IHT T₁₃↝ (ctxeq-tm (⊢≈-trans (⊢≈-sym Δ≈Δ₅) Δ≈Δ₃) ⊢T₁₃)
--   with refl ← unique-lvl ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₂)))
--      | refl , ≈Se ← unique-typ ⊢T₁₁ (proj₁ (proj₂ (presup-≈ T₁₁≈T₁₃)))
--     = _ , _ , _ , _ , Γ↝ , ↝∷ Δ↝ T₁₁↝ , ↝, σ₁↝ t₁↝ T₁₁↝ , ↝, σ₂↝ t₂↝ T₂₁↝ ,
--       ,-cong (s-≈-trans (s-≈-conv (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) σ₁≈σ₁₁) (⊢≈-sym Δ≈Δ₂)) (s-≈-conv (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₂) σ₁≈σ₂) (⊢≈-sym Δ≈Δ₂)))
--              (ctxeq-tm (⊢≈-sym Δ≈Δ₃) ⊢T₁₁)
--              (≈-trans (ctxeq-≈ (⊢≈-sym Δ≈Δ₃) T₁₁≈T₁₂) (ctxeq-≈ (⊢≈-sym Δ≈Δ₄) T₁≈T₂))
--              (≈-conv (ctxeq-≈ (⊢≈-sym Γ≈Γ₃) t₁≈t₂) ([]-cong-Se (ctxeq-≈ (⊢≈-trans (⊢≈-sym Δ≈Δ₃) Δ≈Δ₅) (≈-conv (≈-sym T₁₁≈T₁₃) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₃) ⊢σ₁₂) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ₁≈σ₁₂))))

-- ⫢I-∘ : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s I ∘ U.σ′ ≈ U.σ′ ∶ U.Δ′
-- ⫢I-∘ ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ ↝I σ↝ , σ↝ , I-∘ ⊢σ

-- ⫢∘-I : U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s U.σ′ ∘ I ≈ U.σ′ ∶ U.Δ′
-- ⫢∘-I ⫢σ′
--   with Γ , Δ , σ , Γ↝ , Δ↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ σ↝ ↝I , σ↝ , ∘-I ⊢σ

-- ⫢∘-assoc : ∀ {ζ′ Ω′} →
--            ⫢ U.Δ′ → -- extra condition
--            ⫢ U.Ψ′ → -- extra condition
--            U.Ψ′ ⫢s ζ′ ∶ Ω′ →
--            U.Δ′ ⫢s U.τ′ ∶ U.Ψ′ →
--            U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--            ---------------------
--            U.Γ′ ⫢s (ζ′ ∘ U.τ′) ∘ U.σ′ ≈ ζ′ ∘ (U.τ′ ∘ U.σ′) ∶ Ω′
-- ⫢∘-assoc ⫢Δ′ ⫢Ψ′ ⫢ζ′ ⫢τ′ ⫢σ′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Γ , Δ₁ , σ , Γ↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | Δ₂ , Ψ₁ , τ , Δ₂↝ , Ψ₁↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Ψ₂ , Ω , ζ , Ψ₂↝ , Ω↝ , ζ↝ , ⊢ζ , IHζ ← ⫢ζ′
--   with ⊢Δ₁ ← proj₂ (presup-s ⊢σ)
--      | ⊢Δ₂ , ⊢Ψ₁ ← presup-s ⊢τ
--      | ⊢Ψ₂ ← proj₁ (presup-s ⊢ζ)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--     = _ , _ , _ , _ , Γ↝ , Ω↝ , ↝∘ (↝∘ ζ↝ τ↝) σ↝ , ↝∘ ζ↝ (↝∘ τ↝ σ↝) ,
--       ∘-assoc (ctxeq-s (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) ⊢ζ) (ctxeq-s (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢τ) ⊢σ

-- ⫢,-∘ : ∀ {i} →
--        ⫢ U.Δ′ → -- extra condition
--        ⫢ U.Ψ′ → -- extra condition
--        U.Δ′ ⫢s U.σ′ ∶ U.Ψ′ →
--        U.Ψ′ ⫢ U.T′ ∶ Se i →
--        U.Δ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
--        U.Γ′ ⫢s U.τ′ ∶ U.Δ′ →
--        ---------------------
--        U.Γ′ ⫢s (U.σ′ , U.t′ ∶ U.T′) ∘ U.τ′ ≈ (U.σ′ ∘ U.τ′) , U.t′ U.[ U.τ′ ] ∶ U.T′ ∶ U.T′ ∷ U.Ψ′
-- ⫢,-∘ ⫢Δ′ ⫢Ψ′ ⫢σ′ ⫢T′ ⫢t′ ⫢τ′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Ψ , ⊢Ψ , Ψ↝ , IHΨ ← ⫢Ψ′
--      | Δ₁ , Ψ₁ , σ , Δ₁↝ , Ψ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Ψ₂ , T , _ , Ψ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | i , Δ₂ , t , _ , Δ₂↝ , t↝ , ↝sub {t = T₁} T₁↝ σ₁↝ , ⊢t , IHt ← ⫢t′
--      | Γ , Δ₃ , τ , Γ↝ , Δ₃↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--   with refl ← ⊢T:Se-lvl ⊢T
--   with ⊢Δ₁ , ⊢Ψ₁ ← presup-s ⊢σ
--      | ⊢Ψ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Δ₂ , ⊢T₁[σ] ← presup-tm ⊢t
--      | _ , ⊢Δ₃ ← presup-s ⊢τ
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--      | Δ≈Δ₃ ← IHΔ Δ₃↝ ⊢Δ₃
--      | Ψ≈Ψ₁ ← IHΨ Ψ₁↝ ⊢Ψ₁
--      | Ψ≈Ψ₂ ← IHΨ Ψ₂↝ ⊢Ψ₂
--   with Δ₁≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₃
--      | Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₃
--   with Ψ₃ , _ , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Δ≈Δ₂) Δ≈Δ₁) ⊢σ₁)
--   with Ψ₁≈Ψ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Ψ₂≈Ψ₃ ← ⊢≈-trans (⊢≈-trans (⊢≈-sym Ψ≈Ψ₂) Ψ≈Ψ₁) Ψ₁≈Ψ₃
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Ψ₂≈Ψ₃) ⊢T₁)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--     = _ , _ , _ , _ , Γ↝ , ↝∷ Ψ↝ T↝ , ↝∘ (↝, σ↝ t↝ T↝) τ↝ , ↝, (↝∘ σ↝ τ↝) (↝sub t↝ τ↝) T↝ ,
--       ,-∘ (s-conv (ctxeq-s Δ₁≈Δ₃ ⊢σ) (⊢≈-sym Ψ≈Ψ₁)) (ctxeq-tm (⊢≈-sym Ψ≈Ψ₂) ⊢T)
--           (conv (ctxeq-tm Δ₂≈Δ₃ ⊢t) ([]-cong-Se (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se)) (ctxeq-s Δ₂≈Δ₃ (s-conv ⊢σ₁ (⊢≈-sym Ψ₂≈Ψ₃))) (ctxeq-s-≈ Δ₁≈Δ₃ (s-≈-conv (s-≈-sym σ≈σ₁) (⊢≈-sym Ψ₂≈Ψ₃))))) ⊢τ

-- ⫢p-, : ∀ {i} →
--        ⫢ U.Γ′ → -- extra condition
--        ⫢ U.Δ′ → -- extra condition
--        U.Γ′ ⫢s U.σ′ ∶ U.Δ′ →
--        U.Δ′ ⫢ U.T′ ∶ Se i →
--        U.Γ′ ⫢ U.t′ ∶ U.T′ U.[ U.σ′ ] →
--        ---------------------
--        U.Γ′ ⫢s U.p (U.σ′ , U.t′ ∶ U.T′) ≈ U.σ′ ∶ U.Δ′
-- ⫢p-, ⫢Γ′ ⫢Δ′ ⫢σ′ ⫢T′ ⫢t′
--   with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′
--      | Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ₁ , Δ₁ , σ , Γ₁↝ , Δ₁↝ , σ↝ , ⊢σ , IHσ ← ⫢σ′
--      | _ , Δ₂ , T , _ , Δ₂↝ , T↝ , ↝Se , ⊢T , IHT ← ⫢T′
--      | i , Γ₂ , t , _ , Γ₂↝ , t↝ , ↝sub {t = T₁} T₁↝ σ₁↝ , ⊢t , IHt ← ⫢t′
--   with ⊢Γ₁ , ⊢Δ₁ ← presup-s ⊢σ
--      | ⊢Δ₂ ← proj₁ (presup-tm ⊢T)
--      | ⊢Γ₂ , ⊢T₁[σ] ← presup-tm ⊢t
--   with Δ₃ , _ , ⊢σ₁ , ⊢T₁ , _ ← t[σ]-inv ⊢T₁[σ]
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂
--   with σ≈σ₁ ← IHσ σ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢σ₁)
--   with Δ₁≈Δ₃ ← unique-ctx ⊢σ (proj₁ (proj₂ (presup-s-≈ σ≈σ₁)))
--   with Δ₂≈Δ₃ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₂) (⊢≈-trans Δ≈Δ₁ Δ₁≈Δ₃)
--   with T≈T₁ ← IHT T₁↝ (ctxeq-tm (⊢≈-sym Δ₂≈Δ₃) ⊢T₁)
--   with refl , ≈Se ← unique-typ ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
--   with refl ← ⊢T:Se-lvl ⊢T
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , ↝∘ ↝wk (↝, σ↝ t↝ T↝) , σ↝ ,
--       p-, (ctxeq-s (⊢≈-sym Γ≈Γ₁) (s-conv ⊢σ (⊢≈-sym Δ≈Δ₁))) (ctxeq-tm (⊢≈-sym Δ≈Δ₂) ⊢T)
--           (conv (ctxeq-tm (⊢≈-sym Γ≈Γ₂) ⊢t) ([]-cong-Se (ctxeq-≈ Δ₂≈Δ₃ (≈-conv (≈-sym T≈T₁) (≈-sym ≈Se))) (ctxeq-s (⊢≈-sym Γ≈Γ₂) ⊢σ₁) (ctxeq-s-≈ (⊢≈-sym Γ≈Γ₁) (s-≈-sym σ≈σ₁))))

-- ⫢,-ext : U.Γ′ ⫢s U.σ′ ∶ U.T′ ∷ U.Δ′ →
--          ---------------------
--          U.Γ′ ⫢s U.σ′ ≈ U.p U.σ′ , v 0 U.[ U.σ′ ] ∶ U.T′ ∶ U.T′ ∷ U.Δ′
-- ⫢,-ext ⫢σ′
--   with Γ , Δ , σ , Γ↝ , ↝T∷Δ@(↝∷ Δ↝ T↝) , σ↝ , ⊢σ , IHσ ← ⫢σ′
--     = _ , _ , _ , _ , Γ↝ , ↝T∷Δ , σ↝ , ↝, (↝∘ ↝wk σ↝) (↝sub ↝v σ↝) T↝ , ,-ext ⊢σ

-- ⫢s-≈-sym : U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--            ---------------------
--            U.Γ′ ⫢s U.τ′ ≈ U.σ′ ∶ U.Δ′
-- ⫢s-≈-sym σ′≈τ′
--   with Γ , Δ , σ , τ , Γ↝ , Δ↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′
--     = _ , _ , _ , _ , Γ↝ , Δ↝ , τ↝ , σ↝ , s-≈-sym σ≈τ

-- ⫢s-≈-trans : ∀ {ζ′} →
--              ⫢ U.Γ′ → -- extra condition
--              U.Γ′ ⫢s U.τ′ ∶ U.Δ′ →
--              U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--              U.Γ′ ⫢s U.τ′ ≈ ζ′ ∶ U.Δ′ →
--              ---------------------
--              U.Γ′ ⫢s U.σ′ ≈ ζ′ ∶ U.Δ′
-- ⫢s-≈-trans ⫢Γ′ ⫢τ′ σ′≈τ′ τ′≈ζ′
--   with Γ , Γ↝ , ⊢Γ , IHΓ ← ⫢Γ′
--      | Γ₁ , Δ , τ , Γ₁↝ , Δ↝ , τ↝ , ⊢τ , IHτ ← ⫢τ′
--      | Γ₂ , Δ₁ , σ , τ₁ , Γ₂↝ , Δ₁↝ , σ↝ , τ₁↝ , σ≈τ ← σ′≈τ′
--      | Γ₃ , Δ₂ , τ₂ , ζ , Γ₃↝ , Δ₂↝ , τ₂↝ , ζ↝ , τ≈ζ ← τ′≈ζ′
--   with ⊢Γ₁ , ⊢Δ ← presup-s ⊢τ
--      | ⊢Γ₂ , _ , ⊢τ₁ , ⊢Δ₁ ← presup-s-≈ σ≈τ
--      | ⊢Γ₃ , ⊢τ₂ , _ , ⊢Δ₂ ← presup-s-≈ τ≈ζ
--   with Γ≈Γ₁ ← IHΓ Γ₁↝ ⊢Γ₁
--      | Γ≈Γ₂ ← IHΓ Γ₂↝ ⊢Γ₂
--      | Γ≈Γ₃ ← IHΓ Γ₃↝ ⊢Γ₃
--   with τ≈τ₁ ← IHτ τ₁↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₂) Γ≈Γ₁) ⊢τ₁)
--      | τ≈τ₂ ← IHτ τ₂↝ (ctxeq-s (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₁) ⊢τ₂)
--   with Δ≈Δ₁ ← unique-ctx ⊢τ (proj₁ (proj₂ (presup-s-≈ τ≈τ₁)))
--      | Δ≈Δ₂ ← unique-ctx ⊢τ (proj₁ (proj₂ (presup-s-≈ τ≈τ₂)))
--   with Δ₁≈Δ₂ ← ⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂
--   with τ₁≈τ₂ ← s-≈-trans (s-≈-sym τ≈τ₁) (s-≈-conv τ≈τ₂ (⊢≈-sym Δ₁≈Δ₂))
--     = _ , _ , _ , _ , Γ₂↝ , Δ₁↝ , σ↝ , ζ↝ , s-≈-trans σ≈τ (s-≈-trans (ctxeq-s-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₁) Γ≈Γ₂) τ₁≈τ₂) (s-≈-conv (ctxeq-s-≈ (⊢≈-trans (⊢≈-sym Γ≈Γ₃) Γ≈Γ₂) τ≈ζ) (⊢≈-sym Δ₁≈Δ₂)))

-- ⫢s-≈-conv : ⫢ U.Δ′ → -- extra condition
--             U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Δ′ →
--             ⫢ U.Δ′ ≈ U.Ψ′ →
--             ---------------------
--             U.Γ′ ⫢s U.σ′ ≈ U.τ′ ∶ U.Ψ′
-- ⫢s-≈-conv ⫢Δ′ σ′≈τ′ Δ′≈Ψ′
--   with Δ , ⊢Δ , Δ↝ , IHΔ ← ⫢Δ′
--      | Γ , Δ₁ , σ , τ , Γ↝ , Δ₁↝ , σ↝ , τ↝ , σ≈τ ← σ′≈τ′
--      | Δ₂ , Ψ , Δ₂↝ , Ψ↝ , Δ≈Ψ ← Δ′≈Ψ′
--   with ⊢Δ₁ ← proj₂ (proj₂ (proj₂ (presup-s-≈ σ≈τ)))
--      | ⊢Δ₂ ← proj₁ (presup-⊢≈ Δ≈Ψ)
--   with Δ≈Δ₁ ← IHΔ Δ₁↝ ⊢Δ₁
--      | Δ≈Δ₂ ← IHΔ Δ₂↝ ⊢Δ₂ = _ , _ , _ , _ , Γ↝ , Ψ↝ , σ↝ , τ↝ , s-≈-conv σ≈τ (⊢≈-trans (⊢≈-trans (⊢≈-sym Δ≈Δ₁) Δ≈Δ₂) Δ≈Ψ)

-- mutual
--   fundamental-⊢⇒⫢ : U.⊢ U.Γ →
--                     --------------------
--                     ⫢ U.Γ
--   fundamental-⊢⇒⫢ ⊢[] = ⫢⊢[]
--   fundamental-⊢⇒⫢ (⊢∷ ⊢Γ ⊢T) = ⫢⊢∷ (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T)

--   fundamental-⊢≈⇒⫢≈ : U.⊢ U.Γ ≈ U.Δ →
--                       --------------------
--                       ⫢ U.Γ ≈ U.Δ
--   fundamental-⊢≈⇒⫢≈ []-≈ = ⫢[]-≈
--   fundamental-⊢≈⇒⫢≈ (∷-cong ⊢Γ ⊢Δ Γ≈Δ ⊢S ⊢T Γ⊢S≈T Δ⊢S≈T) = ⫢∷-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢≈⇒⫢≈ Γ≈Δ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ Γ⊢S≈T) (fundamental-⊢t≈⇒⫢t≈ Δ⊢S≈T)

--   fundamental-⊢t⇒⫢t : U.Γ ⊢ U.t ∶ U.T →
--                       --------------------
--                       U.Γ ⫢ U.t ∶ U.T
--   fundamental-⊢t⇒⫢t (N-wf ⊢Γ) = ⫢N-wf (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (Se-wf i ⊢Γ) = ⫢Se-wf (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (Liftt-wf n ⊢T) = ⫢Liftt-wf (fundamental-⊢t⇒⫢t ⊢T)
--   fundamental-⊢t⇒⫢t (Π-wf ⊢Γ ⊢S ⊢T i≡maxjk) = ⫢Π-wf (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) i≡maxjk
--   fundamental-⊢t⇒⫢t (vlookup ⊢Γ x∈Γ) = ⫢vlookup (fundamental-⊢⇒⫢ ⊢Γ) x∈Γ
--   fundamental-⊢t⇒⫢t (ze-I ⊢Γ) = ⫢ze-I (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t⇒⫢t (su-I ⊢t) = ⫢su-I (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (N-E ⊢Γ ⊢T ⊢s ⊢r ⊢t) = ⫢N-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (Λ-I ⊢Γ ⊢S ⊢t) = ⫢Λ-I (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (Λ-E ⊢Γ ⊢S ⊢T ⊢r ⊢s) = ⫢Λ-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t⇒⫢t (L-I j ⊢t) = ⫢L-I (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (L-E j ⊢Γ ⊢T ⊢t) = ⫢L-E (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t⇒⫢t (t[σ] ⊢Δ ⊢t ⊢σ) = ⫢t[σ] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t⇒⫢t (conv ⊢Γ ⊢t ⊢S S≈T) = ⫢conv (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈T)

--   fundamental-⊢s⇒⫢s : U.Γ U.⊢s U.σ ∶ U.Δ →
--                       --------------------
--                       U.Γ ⫢s U.σ ∶ U.Δ
--   fundamental-⊢s⇒⫢s (s-I ⊢Γ) = ⫢s-I (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢s⇒⫢s (s-wk ⊢S∷Γ) = ⫢s-wk (fundamental-⊢⇒⫢ ⊢S∷Γ)
--   fundamental-⊢s⇒⫢s (s-∘ ⊢Δ ⊢τ ⊢σ) = ⫢s-∘ (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s⇒⫢s (s-, ⊢Γ ⊢Δ ⊢σ ⊢T ⊢t) = ⫢s-, (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢s⇒⫢s (s-conv ⊢Δ ⊢σ Δ≈Ψ) = ⫢s-conv (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢≈⇒⫢≈ Δ≈Ψ)

--   fundamental-⊢t≈⇒⫢t≈ : U.Γ ⊢ U.t ≈ U.s ∶ U.T →
--                         --------------------
--                         U.Γ ⫢ U.t ≈ U.s ∶ U.T
--   fundamental-⊢t≈⇒⫢t≈ (N-[] ⊢σ) = ⫢N-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (Se-[] i ⊢σ) = ⫢Se-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (Liftt-[] n ⊢Δ ⊢σ ⊢T) = ⫢Liftt-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T)
--   fundamental-⊢t≈⇒⫢t≈ (Π-[] ⊢Δ ⊢σ ⊢S ⊢T k≡maxij) = ⫢Π-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) k≡maxij
--   fundamental-⊢t≈⇒⫢t≈ (Π-cong ⊢Γ ⊢S S≈S′ T≈T′ k≡maxij) = ⫢Π-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈S′) (fundamental-⊢t≈⇒⫢t≈ T≈T′) k≡maxij
--   fundamental-⊢t≈⇒⫢t≈ (Liftt-cong j T≈T′) = ⫢Liftt-cong (fundamental-⊢t≈⇒⫢t≈ T≈T′)
--   fundamental-⊢t≈⇒⫢t≈ (v-≈ ⊢Γ x∈Γ) = ⫢v-≈ (fundamental-⊢⇒⫢ ⊢Γ) x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ (ze-≈ ⊢Γ) = ⫢ze-≈ (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢t≈⇒⫢t≈ (su-cong t≈t′) = ⫢su-cong (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (rec-cong ⊢Γ ⊢T T≈T′ s≈s′ r≈r′ t≈t′) = ⫢rec-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ T≈T′) (fundamental-⊢t≈⇒⫢t≈ s≈s′) (fundamental-⊢t≈⇒⫢t≈ r≈r′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-cong ⊢Γ ⊢S S≈S′ t≈t′) = ⫢Λ-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ S≈S′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ ($-cong ⊢Γ ⊢S ⊢T r≈r′ s≈s′) = ⫢$-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ r≈r′) (fundamental-⊢t≈⇒⫢t≈ s≈s′)
--   fundamental-⊢t≈⇒⫢t≈ (liftt-cong j t≈t′) = ⫢liftt-cong (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ (unlift-cong n ⊢Γ ⊢T t≈t′) = ⫢unliftt-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢t≈⇒⫢t≈ ([]-cong ⊢Δ t≈t′ σ≈σ′) = ⫢[]-cong (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t≈⇒⫢t≈ t≈t′) (fundamental-⊢s≈⇒⫢s≈ σ≈σ′)
--   fundamental-⊢t≈⇒⫢t≈ (ze-[] ⊢σ) = ⫢ze-[] (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢t≈⇒⫢t≈ (su-[] ⊢Δ ⊢σ ⊢t) = ⫢su-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (rec-[] ⊢Δ ⊢σ ⊢T ⊢s ⊢r ⊢t) = ⫢rec-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-[] ⊢Δ ⊢σ ⊢S ⊢t) = ⫢Λ-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ($-[] ⊢Δ ⊢S ⊢T ⊢σ ⊢r ⊢s) = ⫢$-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (liftt-[] n ⊢Δ ⊢σ ⊢T ⊢t) = ⫢liftt-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (unlift-[] n ⊢Δ ⊢T ⊢σ ⊢t) = ⫢unlift-[] (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (rec-β-ze ⊢Γ ⊢T ⊢s ⊢r) = ⫢rec-β-ze (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r)
--   fundamental-⊢t≈⇒⫢t≈ (rec-β-su ⊢Γ ⊢T ⊢s ⊢r ⊢t) = ⫢rec-β-su (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t⇒⫢t ⊢r) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-β ⊢Γ ⊢S ⊢T ⊢t ⊢s) = ⫢Λ-β (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (Λ-η ⊢Γ ⊢S ⊢T ⊢t) = ⫢Λ-η (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ (L-β j ⊢s) = ⫢L-β (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ (L-η n ⊢Γ ⊢T ⊢t) = ⫢L-η (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ([I] ⊢s) = ⫢[I] (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ ([wk] ⊢Γ ⊢S x∈Γ) = ⫢[wk] (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ ([∘] ⊢Γ′ ⊢Γ″ ⊢τ ⊢σ ⊢t) = ⫢[∘] (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢t≈⇒⫢t≈ ([,]-v-ze ⊢Γ ⊢Δ ⊢σ ⊢S ⊢s) = ⫢[,]-v-ze (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢s)
--   fundamental-⊢t≈⇒⫢t≈ ([,]-v-su ⊢Γ ⊢Δ ⊢σ ⊢S ⊢s x∈Γ) = ⫢[,]-v-su (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t⇒⫢t ⊢s)  x∈Γ
--   fundamental-⊢t≈⇒⫢t≈ (≈-conv ⊢Γ ⊢S t≈s T≈S) = ⫢≈-conv (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢S) (fundamental-⊢t≈⇒⫢t≈ t≈s) (fundamental-⊢t≈⇒⫢t≈ T≈S)
--   fundamental-⊢t≈⇒⫢t≈ (≈-sym t≈s) = ⫢≈-sym (fundamental-⊢t≈⇒⫢t≈ t≈s)
--   fundamental-⊢t≈⇒⫢t≈ (≈-trans ⊢Γ ⊢s t≈s s≈r) = ⫢≈-trans (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢t⇒⫢t ⊢s) (fundamental-⊢t≈⇒⫢t≈ t≈s) (fundamental-⊢t≈⇒⫢t≈ s≈r)

--   fundamental-⊢s≈⇒⫢s≈ : U.Γ U.⊢s U.σ ≈ U.τ ∶ U.Δ →
--                         --------------------
--                         U.Γ ⫢s U.σ ≈ U.τ ∶ U.Δ
--   fundamental-⊢s≈⇒⫢s≈ (I-≈ ⊢Γ) = ⫢I-≈ (fundamental-⊢⇒⫢ ⊢Γ)
--   fundamental-⊢s≈⇒⫢s≈ (wk-≈ ⊢T∷Γ) = ⫢wk-≈ (fundamental-⊢⇒⫢ ⊢T∷Γ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-cong ⊢Γ′ σ≈σ′ τ≈τ′) = ⫢∘-cong (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢s≈⇒⫢s≈ σ≈σ′) (fundamental-⊢s≈⇒⫢s≈ τ≈τ′)
--   fundamental-⊢s≈⇒⫢s≈ (,-cong ⊢Γ ⊢Δ ⊢σ σ≈τ ⊢T T≈T′ t≈t′) = ⫢,-cong (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t≈⇒⫢t≈ T≈T′) (fundamental-⊢t≈⇒⫢t≈ t≈t′)
--   fundamental-⊢s≈⇒⫢s≈ (I-∘ ⊢σ) = ⫢I-∘ (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-I ⊢σ) = ⫢∘-I (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (∘-assoc ⊢Γ″ ⊢Γ′ ⊢σ ⊢τ ⊢γ) = ⫢∘-assoc (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s⇒⫢s ⊢γ)
--   fundamental-⊢s≈⇒⫢s≈ (,-∘ ⊢Γ′ ⊢Γ″ ⊢σ ⊢T ⊢t ⊢τ) = ⫢,-∘ (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ″) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t) (fundamental-⊢s⇒⫢s ⊢τ)
--   fundamental-⊢s≈⇒⫢s≈ (p-, ⊢Γ′ ⊢Γ ⊢σ ⊢T ⊢t) = ⫢p-, (fundamental-⊢⇒⫢ ⊢Γ′) (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢s⇒⫢s ⊢σ) (fundamental-⊢t⇒⫢t ⊢T) (fundamental-⊢t⇒⫢t ⊢t)
--   fundamental-⊢s≈⇒⫢s≈ (,-ext ⊢σ) = ⫢,-ext (fundamental-⊢s⇒⫢s ⊢σ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-sym σ≈τ) = ⫢s-≈-sym (fundamental-⊢s≈⇒⫢s≈ σ≈τ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-trans ⊢Γ ⊢τ σ≈τ τ≈γ) = ⫢s-≈-trans (fundamental-⊢⇒⫢ ⊢Γ) (fundamental-⊢s⇒⫢s ⊢τ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢s≈⇒⫢s≈ τ≈γ)
--   fundamental-⊢s≈⇒⫢s≈ (s-≈-conv ⊢Δ σ≈τ Δ≈Ψ) = ⫢s-≈-conv (fundamental-⊢⇒⫢ ⊢Δ) (fundamental-⊢s≈⇒⫢s≈ σ≈τ) (fundamental-⊢≈⇒⫢≈ Δ≈Ψ)      