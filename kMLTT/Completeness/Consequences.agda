{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module kMLTT.Completeness.Consequences (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics
open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Fundamental fext

Se≈⇒eq-lvl : ∀ {i j k} →
             Γ ⊢ Se i ≈ Se j ∶ Se k →
             i ≡ j
Se≈⇒eq-lvl Se≈
  with fundamental-t≈t′ Se≈
...  | ⊨Γ , _ , rel
     with InitEnvs-related ⊨Γ
...     | _ , _ , _ , _ , ρ∈
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Se⟧ _ ; t≈t′ = t≈t′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ k<
           with t≈t′
...           | U _ eq = eq


□-inv-gen : ∀ {i j} →
            Γ ⊢ □ T ∶ S →
            Γ ⊢ S ≈ Se i ∶ Se j →
            ---------------------
            [] ∷⁺ Γ ⊢ T ∶ Se i
□-inv-gen (□-wf ⊢T) S≈
  with Se≈⇒eq-lvl S≈
...  | refl                 = ⊢T
□-inv-gen (cumu ⊢□T) S≈
  with presup-tm ⊢□T | Se≈⇒eq-lvl S≈
...  | ⊢Γ , _ | refl        = cumu (□-inv-gen ⊢□T (Se-≈ ⊢Γ))
□-inv-gen (conv ⊢□T S′≈) S≈ = □-inv-gen ⊢□T (≈-trans (lift-⊢≈-Se-max S′≈) (lift-⊢≈-Se-max′ S≈))


□-inv : ∀ {i} →
        Γ ⊢ □ T ∶ Se i →
        -------------------
        [] ∷⁺ Γ ⊢ T ∶ Se i
□-inv ⊢□T
  with presup-tm ⊢□T
...  | ⊢Γ , _ = □-inv-gen ⊢□T (Se-≈ ⊢Γ)


Π-inv-gen : ∀ {i j} →
            Γ ⊢ Π S T ∶ T′ →
            Γ ⊢ T′ ≈ Se i ∶ Se j →
            ---------------------
            Γ ⊢ S ∶ Se i × S ∺ Γ ⊢ T ∶ Se i
Π-inv-gen (Π-wf ⊢S ⊢T) T′≈
  with Se≈⇒eq-lvl T′≈
...  | refl                 = ⊢S , ⊢T
Π-inv-gen (cumu ⊢Π) T′≈
  with presup-tm ⊢Π | Se≈⇒eq-lvl T′≈
...  | ⊢Γ , _ | refl
     with Π-inv-gen ⊢Π (Se-≈ ⊢Γ)
...     | ⊢S , ⊢T           = cumu ⊢S , cumu ⊢T
Π-inv-gen (conv ⊢Π T″≈) T′≈ = Π-inv-gen ⊢Π (≈-trans (lift-⊢≈-Se-max T″≈) (lift-⊢≈-Se-max′ T′≈))


Π-inv : ∀ {i} →
        Γ ⊢ Π S T ∶ Se i →
        ---------------------
        Γ ⊢ S ∶ Se i × S ∺ Γ ⊢ T ∶ Se i
Π-inv ⊢Π
  with presup-tm ⊢Π
...  | ⊢Γ , _ = Π-inv-gen ⊢Π (Se-≈ ⊢Γ)
