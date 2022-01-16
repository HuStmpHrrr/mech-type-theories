{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel

open import kMLTT.Soundness.Properties.NoFunExt.LogRel


Glu-wellfounded-≡′ : ∀ {i i′ j} (j<i : j < i) (j<i′ : j < i′) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ Glu-wellfounded i′ j<i′
Glu-wellfounded-≡′ (s≤s j<i) (s≤s j′<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                             λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j′<i))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) (A∈ : A ∈′ 𝕌 j) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ _⊢_®[ j ]_
Glu-wellfounded-≡ {_} {suc i} {j} (s≤s j<i) A∈ = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                                    λ {j′} → fext (λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j))

®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T
®El⇒ty (ne C≈C′) (ne _ , t∶T , _) = t∶T
®El⇒ty N (t∼a , T≈N)              = conv (®Nat⇒∶Nat t∼a (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒ty (U j<i eq) ((A∈ , T∼A) , T≈)
  rewrite Glu-wellfounded-≡ j<i A∈ = conv (®⇒ty A∈ T∼A) (≈-sym T≈)
®El⇒ty (□ A≈B) t∼a                = Glubox.t∶T t∼a
®El⇒ty (Π iA RT) t∼a              = GluΛ.t∶T t∼a

®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → a ∈′ El i A≈B
®El⇒∈El (ne C≈C′) (a∈⊥ , _)         = a∈⊥
®El⇒∈El N (t∼a , _)                 = ®Nat⇒∈Nat t∼a
®El⇒∈El (U j<i eq) ((A∈ , _) , _)
  rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = A∈
®El⇒∈El (□ A≈B) t∼a                 = Glubox.a∈El t∼a
®El⇒∈El (Π iA RT) t∼a               = GluΛ.a∈El t∼a

®El⇒® : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C′) (ne c≈c′ , _ , ⊢T , rel) = ⊢T , λ ⊢σ → proj₁ (rel ⊢σ)
®El⇒® N (_ , T≈N)                        = T≈N
®El⇒® (U j<i eq) (_ , T≈)                = T≈
®El⇒® (□ A≈B) t∼a                        = record
  { GT   = GT
  ; T≈   = T≈
  ; krip = λ {_} {σ} Ψs ⊢σ →
    let open □Krip (krip Ψs ⊢σ)
    in ®El⇒® (A≈B (ins (mt σ) (len Ψs))) rel 
  }
  where open Glubox t∼a
®El⇒® (Π iA RT) t∼a                      = record
  { IT   = IT
  ; OT   = OT
  ; T≈   = T≈
  ; krip = λ {_} {σ} ⊢σ →
    let open ΛRel (krip ⊢σ)
    in record
    { IT-rel = IT-rel
    ; OT-rel = λ s∼a a∈ → 
      let open ΛKripke (ap-rel s∼a a∈)
      in ®El⇒® (ΠRT.T≈T′ (RT (mt σ) a∈)) ®fa
    }
  }
  where open GluΛ t∼a
