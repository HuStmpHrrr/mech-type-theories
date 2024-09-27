{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module NonCumulative.Completeness.Consequences (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Completeness.LogRel
open import NonCumulative.Completeness.Fundamental fext

-- If two Se's are equivalent, then they have the same universe level.
Se≈⇒eq-lvl : ∀ {i j k l} →
             Γ ⊢ Se i ≈ Se j ∶[ l ] Se k →
             --------------------------
             i ≡ j × k ≡ 1 + i × l ≡ 1 + k
Se≈⇒eq-lvl Se≈
  with ⊨Γ , rel ← fundamental-t≈t′ Se≈
    with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
      with rel ρ∈
...     | record { ⟦T⟧ = .(U _) ; ⟦T′⟧ = .(U _) ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = U 1+k≡1+k x₁ }
        , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = .(U _) ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Se⟧ _ ; t≈t′ = t≈t′ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+k≡1+k))
        with U k≡1+i i≡j ← t≈t′ = i≡j , k≡1+i , 1+k≡1+k

Π-inv-gen : ∀ {i j k} →
            Γ ⊢ Π (S ↙ j) (T ↙ k) ∶[ 1 + i ] T′ →
            Γ ⊢ T′ ≈ Se i ∶[ 2 + i ] Se (1 + i) →
            ---------------------------------
            i ≡ max j k  × Γ ⊢ S ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + k ] Se k
Π-inv-gen (Π-wf ⊢Π ⊢Π₁ i≡maxjk) T′≈ = i≡maxjk , ⊢Π , ⊢Π₁
Π-inv-gen (conv ⊢Π T″≈) T′≈ = Π-inv-gen ⊢Π (≈-trans T″≈ T′≈)

Π-inv : ∀ {i j k} →
          Γ ⊢ Π (S ↙ j) (T ↙ k) ∶[ 1 + i ] (Se i) →
          i ≡ max j k × Γ ⊢ S ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + k ] Se k
Π-inv ⊢Π
  with ⊢Γ ← proj₁ (presup-tm ⊢Π) = Π-inv-gen ⊢Π (≈-refl (Se-wf _ ⊢Γ))

Liftt-inv-gen : ∀ {i j k} →
                Γ ⊢ Liftt j (S ↙ k) ∶[ 1 + i ] T →
                Γ ⊢ T ≈ Se i ∶[ 2 + i ] Se (1 + i) →
                --------------------------------
                i ≡ j + k × Γ ⊢ S ∶[ 1 + k ] Se k
Liftt-inv-gen (Liftt-wf _ ⊢Liftt) T≈ = refl , ⊢Liftt
Liftt-inv-gen (conv ⊢Liftt T′≈) T≈ = Liftt-inv-gen ⊢Liftt (≈-trans T′≈ T≈)

Liftt-inv : ∀ {i j k} →
            Γ ⊢ Liftt j (S ↙ k) ∶[ 1 + i ] Se i →
            i ≡ j + k × Γ ⊢ S ∶[ 1 + k ] Se k
Liftt-inv ⊢Liftt
  with ⊢Γ ← proj₁ (presup-tm ⊢Liftt) = Liftt-inv-gen ⊢Liftt (≈-refl (Se-wf _ ⊢Γ))