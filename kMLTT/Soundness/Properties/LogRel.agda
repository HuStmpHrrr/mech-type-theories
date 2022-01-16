{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel

open import kMLTT.Soundness.Properties.NoFunExt.LogRel


Glu-wellfounded-≡′ : ∀ {i i′ j} (j<i : j < i) (j<i′ : j < i′) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ Glu-wellfounded i′ j<i′
Glu-wellfounded-≡′ (s≤s j<i) (s≤s j′<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                             λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j′<i))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) (A∈ : A ∈′ 𝕌 j) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ _⊢_®[ j ]_
Glu-wellfounded-≡ {_} {suc i} {j} (s≤s j<i) A∈ = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                                    λ {j′} → fext (λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j))

®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Γ ⊢ T ∶ Se i
®⇒ty (ne C≈C′) (⊢T , _)  = ⊢T
®⇒ty N T∼A          = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (U j<i eq) T∼A = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (□ A≈B) T∼A    = proj₁ (proj₂ (presup-≈ T≈))
  where open Glu□ T∼A
®⇒ty (Π iA RT) T∼A  = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T∼A

®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T
®El⇒ty (ne C≈C′) (ne _ , t∶T , _) = t∶T
®El⇒ty N (t∼a , T≈N)              = conv (®Nat⇒∶Nat t∼a (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒ty (U j<i eq) ((A∈ , T∼A) , T≈)
  rewrite Glu-wellfounded-≡ j<i A∈ = conv (®⇒ty A∈ T∼A) (≈-sym T≈)
®El⇒ty (□ A≈B) t∼a                = Glubox.t∶T t∼a
®El⇒ty (Π iA RT) t∼a              = GluΛ.t∶T t∼a
