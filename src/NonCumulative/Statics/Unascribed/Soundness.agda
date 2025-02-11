
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
    where helper : ∀ {t₁ i₁ T₁} → t₁ ↝ _ → Γ A.⊢ t₁ ∶[ i₁ ] T₁ → Γ ⊢ _ ≈ t₁ ∶[ i₁ ] T₁
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
    ... | refl , ≈Se , ⊢S₁ , ⊢T₁
      with IHS S₁↝ (ctxeq-tm Γ≈Γ₁ ⊢S₁)
    ... | S≈S₁
      with unique-lvl ⊢S (proj₁ (proj₂ (presup-≈ S≈S₁)))
    ... | refl
      with S₁≈S₂ ← ≈-trans (≈-sym S≈S₁) S≈S₂
      with IHT T₁↝ (ctxeq-tm (∷-cong Γ≈Γ₂ ⊢S₁ ⊢S₂ (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S₁≈S₂) (ctxeq-≈ (⊢≈-sym Γ₁≈Γ₂) S₁≈S₂)) ⊢T₁)
    ... | T≈T₁
      with unique-lvl ⊢T (proj₁ (proj₂ (presup-≈ T≈T₁)))
    ... | refl = ≈-conv (Π-cong (ctxeq-tm (⊢≈-sym Γ≈Γ₁) ⊢S) (ctxeq-≈ (⊢≈-sym Γ≈Γ₁) S≈S₁) (ctxeq-≈ (⊢≈-sym S∷Γ≈S₂∷Γ₂) T≈T₁) refl) (≈-sym ≈Se)

⫢ze-I : ⫢ U.Γ′ →
      U.Γ′ ⫢ ze ∶ N
⫢ze-I ⫢Γ′ 
  with Γ , ⊢Γ , Γ↝ , IHΓ ← ⫢Γ′ = _ , _ , _ , _ , Γ↝ , ↝ze , ↝N , ze-I ⊢Γ , λ { ↝ze ⊢ze → ≈-refl ⊢ze }