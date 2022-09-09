{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module MLTT.Completeness.Consequences (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib

open import MLTT.Statics
open import MLTT.Statics.Properties
open import MLTT.Semantics.Readback
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


InitEnvs-lookup : ∀ {x} →
                  x < len Γ →
                  InitEnvs Γ ρ →
                  ∃₂ λ A n → ρ x ≡ l′ A n
InitEnvs-lookup {T ∷ []} (s≤s z≤n) (s-∷ ρrel _)                  = -, 0 , refl
InitEnvs-lookup {T ∷ T′ ∷ Γ} {_} {ℕ.zero} (s≤s x<) (s-∷ ρrel _)  = -, ℕ.suc (len Γ) , refl
InitEnvs-lookup {T ∷ T′ ∷ Γ} {_} {ℕ.suc x} (s≤s x<) (s-∷ ρrel _) = InitEnvs-lookup x< ρrel

not-Se-≈-v : ∀ {i j x} →
             x < len Γ →
             Γ ⊢ Se i ≈ v x ∶ Se j → ⊥
not-Se-≈-v {x = x} x< eq
  with ⊨Γ , _ , rel ← fundamental-t≈t′ eq
     with _ , ρ , _ , ρrel , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈ | InitEnvs-lookup x< ρrel
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
           | _ , _ , eq
           rewrite 𝕌-wellfounded-≡-𝕌 _ k< | eq
           with t≈t′
...           | ()

not-Se-≈-N : ∀ {i j} →
             Γ ⊢ Se i ≈ N ∶ Se j → ⊥
not-Se-≈-N eq
  with ⊨Γ , _ , rel ← fundamental-t≈t′ eq
     with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦N⟧ ; t≈t′ = t≈t′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ k<
           with t≈t′
...           | ()

not-Se-≈-Π : ∀ {i j} →
             Γ ⊢ Se i ≈ Π S T ∶ Se j → ⊥
not-Se-≈-Π eq
  with ⊨Γ , _ , rel ← fundamental-t≈t′ eq
     with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Π⟧ _ ; t≈t′ = t≈t′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ k<
           with t≈t′
...           | ()

not-Se-≈-bundle : ∀ {i j x} →
                  x < len Γ →
                  Γ ⊢ Se i ≈ T ∶ Se j →
                  T ∈ v x ∷ N ∷ Π S S′ ∷ [] →
                  ⊥
not-Se-≈-bundle x< eq 0d = not-Se-≈-v x< eq
not-Se-≈-bundle x< eq 1d = not-Se-≈-N eq
not-Se-≈-bundle x< eq 2d = not-Se-≈-Π eq
