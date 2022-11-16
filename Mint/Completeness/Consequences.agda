{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module Mint.Completeness.Consequences (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import Mint.Statics
open import Mint.Statics.Properties
open import Mint.Semantics.Readback
open import Mint.Semantics.Properties.PER fext
open import Mint.Completeness fext
open import Mint.Completeness.LogRel
open import Mint.Completeness.Fundamental fext

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

-- More precise □ typing inversion

□-inv-gen : ∀ {i j} →
            Γ ⊢ □ T ∶ S →
            Γ ⊢ S ≈ Se i ∶ Se j →
            ---------------------
            [] ∷⁺ Γ ⊢ T ∶ Se i
□-inv-gen (□-wf ⊢T) S≈
  rewrite Se≈⇒eq-lvl S≈ = ⊢T
□-inv-gen (cumu ⊢□T) S≈
  with ⊢Γ ← proj₁ (presup-tm ⊢□T)
    rewrite sym (Se≈⇒eq-lvl S≈) = cumu (□-inv-gen ⊢□T (≈-refl (Se-wf _ ⊢Γ)))
□-inv-gen (conv ⊢□T S′≈) S≈ = □-inv-gen ⊢□T (≈-trans (lift-⊢≈-Se-max S′≈) (lift-⊢≈-Se-max′ S≈))

-- If □ T is in level i, then T is also in level i.
□-inv : ∀ {i} →
        Γ ⊢ □ T ∶ Se i →
        -------------------
        [] ∷⁺ Γ ⊢ T ∶ Se i
□-inv ⊢□T
  with ⊢Γ ← proj₁ (presup-tm ⊢□T) = □-inv-gen ⊢□T (≈-refl (Se-wf _ ⊢Γ))

-- Similar conclusion but for Π

Π-inv-gen : ∀ {i j} →
            Γ ⊢ Π S T ∶ T′ →
            Γ ⊢ T′ ≈ Se i ∶ Se j →
            ---------------------------------
            Γ ⊢ S ∶ Se i × S ∺ Γ ⊢ T ∶ Se i
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
        Γ ⊢ S ∶ Se i × S ∺ Γ ⊢ T ∶ Se i
Π-inv ⊢Π
  with ⊢Γ ← proj₁ (presup-tm ⊢Π) = Π-inv-gen ⊢Π (≈-refl (Se-wf _ ⊢Γ))

not-Se-≈-v0 : ∀ {i j} →
              T ∺ Γ ⊢ Se i ≈ v 0 ∶ Se j →
              ----------------------------
              ⊥
not-Se-≈-v0 Se≈v0
  with _ , nbeSe , nbev0 ← completeness Se≈v0
    with record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU _ (RU _) } ← NbE.nbe nbeSe
       | record { init = s-∺ _ _ ; nbe = record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦v⟧ _ ; ↓⟦t⟧ = RU _ () } } ← nbev0

not-Se-≈-N : ∀ {i j} →
             Γ ⊢ Se i ≈ N ∶ Se j →
             ----------------------------
             ⊥
not-Se-≈-N Se≈N
  with _ , nbeSe , nbeN ← completeness Se≈N
    with record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU _ (RU _) } ← NbE.nbe nbeSe
       | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦N⟧ ; ↓⟦t⟧ = RU _ () } ← NbE.nbe nbeN

not-Se-≈-Π : ∀ {i j} →
             Γ ⊢ Se i ≈ Π S T ∶ Se j →
             ----------------------------
             ⊥
not-Se-≈-Π Se≈Π
  with _ , nbeSe , nbeΠ ← completeness Se≈Π
    with record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU _ (RU _) } ← NbE.nbe nbeSe
       | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦Π⟧ _ ; ↓⟦t⟧ = RU _ () } ← NbE.nbe nbeΠ

not-Se-≈-□ : ∀ {i j} →
             Γ ⊢ Se i ≈ □ T ∶ Se j →
             ----------------------------
             ⊥
not-Se-≈-□ Se≈□
  with _ , nbeSe , nbe□ ← completeness Se≈□
    with record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU _ (RU _) } ← NbE.nbe nbeSe
       | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ⟦□⟧ _ ; ↓⟦t⟧ = RU _ () } ← NbE.nbe nbe□
