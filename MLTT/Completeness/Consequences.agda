{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module MLTT.Completeness.Consequences (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib

open import MLTT.Statics
open import MLTT.Statics.Properties
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Completeness.LogRel
open import MLTT.Completeness.Fundamental fext

-- If two Se's are equivalent, then they have the same universe level.
Se≈⇒eq-lvl : ∀ {i j k} →
             Γ ⊢ Se i ≈ Se j ∶ Se k →
             --------------------------
             i ≡ j
Se≈⇒eq-lvl Se≈
  with ⊨Γ , _ , rel ← fundamental-t≈t′ Se≈
     with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Se⟧ _ ; t≈t′ = t≈t′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ k<
           with U _ eq ← t≈t′ = eq

-- More precise Π typing inversion

Π-inv-gen : ∀ {i j} →
            Γ ⊢ Π S T ∶ T′ →
            Γ ⊢ T′ ≈ Se i ∶ Se j →
            ---------------------------------
            Γ ⊢ S ∶ Se i × S ∷ Γ ⊢ T ∶ Se i
Π-inv-gen (Π-wf ⊢S ⊢T) T′≈
  rewrite Se≈⇒eq-lvl T′≈ = ⊢S , ⊢T
Π-inv-gen (cumu ⊢Π) T′≈
  with ⊢Γ ← proj₁ (presup-tm ⊢Π)
    rewrite sym (Se≈⇒eq-lvl T′≈)
      with ⊢S , ⊢T ← Π-inv-gen ⊢Π (≈-refl (Se-wf _ ⊢Γ)) = cumu ⊢S , cumu ⊢T
Π-inv-gen (conv ⊢Π T″≈) T′≈ = Π-inv-gen ⊢Π (≈-trans (lift-⊢≈-Se-max T″≈) (lift-⊢≈-Se-max′ T′≈))


Π-inv : ∀ {i} →
        Γ ⊢ Π S T ∶ Se i →
        ---------------------------------
        Γ ⊢ S ∶ Se i × S ∷ Γ ⊢ T ∶ Se i
Π-inv ⊢Π
  with ⊢Γ ← proj₁ (presup-tm ⊢Π) = Π-inv-gen ⊢Π (≈-refl (Se-wf _ ⊢Γ))
