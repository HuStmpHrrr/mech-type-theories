{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Properties of the gluing models for terms and types
module NonCumulative.Soundness.Properties.LogRel (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Properties.PER (fext)
open import NonCumulative.Soundness.LogRel

open import NonCumulative.Soundness.Properties.NoFunExt.LogRel public

Glu-wellfounded-≡′ : ∀ {j i i′} → (j<i : j < i) → (j<i′ : j < i′) →
  (λ (univ : ∀ {l} → l < j → Ty) {A B} → Glu-wellfounded i j<i univ {A} {B}) ≡ (λ (univ : ∀ {l} → l < j → Ty) {A B} → Glu-wellfounded i′ j<i′ univ {A} {B})
Glu-wellfounded-≡′ {j} {i} {i′} (s≤s {j} j<i) (s≤s {j} j<i′) = fext λ (univ : ∀ {l} → l < j → Ty) → cong
  (λ (rc : ∀ {k} (k<i : k < j) (univ : ∀ {l} → l < k → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 k univ → Set) {A B} →
    Glu.⟦ j , rc , univ ⟧_⊢_®_)
  (implicit-extensionality fext λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j<i′))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) →  (λ {A B} → Glu-wellfounded i {j} j<i (𝕌-wellfounded j) {A} {B}) ≡ (_⊢_®[ j ]_)
Glu-wellfounded-≡ {j = j} (s≤s j<i) = cong
  (λ (rc : ∀ {k} (k<i : k < j) (univ : ∀ {l} → l < k → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 k univ → Set) {A B} → Glu.⟦ j , rc , 𝕌-wellfounded j ⟧_⊢_®_)
  (implicit-extensionality fext λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j)

 -- If t and a are related, then a is in the El PER model.
®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          -----------------------------
          a ∈′ El i A≈B
®El⇒∈El (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡′i , snd) = ne c≈c j≡i j≡′i
®El⇒∈El N′ (t®Nat , T≈N) = ®Nat⇒∈Nat t®Nat
®El⇒∈El {a = a} {i = i} (U {j} {j′ = _} i≡1+j j≡j′) record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = rel }
  rewrite 𝕌-wellfounded-≡-𝕌 (1 + j) (≤-reflexive refl) | 𝕌-wf-simpl i | sym (𝕌-wf-simpl j) = A∈𝕌
®El⇒∈El (Π eq jA RT j≡j' k≡k′) t® = a∈El
  where open GluΛ t®
®El⇒∈El (L eq A≈A′ j≡j' k≡k′) t® = a∈El
  where open Glul t®

Glu-wellfounded-≡-Glul : ∀ {j k} →
  (λ {l} l<k → Glu-wellfounded (j + k) {l} (Li≤ refl l<k)) ≡ Glu-wellfounded k
Glu-wellfounded-≡-Glul {j} {k} = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (Li≤ {j + k} refl l<k) l<k))

Glu-wellfounded-≡-GluΛ : ∀ {j k} →
  (λ {l} l<k → Glu-wellfounded (max j k) {l} (ΠO≤ refl l<k)) ≡ Glu-wellfounded k
Glu-wellfounded-≡-GluΛ {j} {k} = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (ΠO≤ {max j k} refl l<k) l<k))


®El⇒® : ∀ { i } → (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡í , record { t∶T = t∶T ; ⊢T = ⊢T ; krip = krip }) = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
®El⇒® N′ (_ , T≈N) = T≈N
®El⇒® (U _ _) t® = GluU.T≈ t®
®El⇒® (Π {j = j} {k = k} refl jA RT refl refl) record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip }
  rewrite 𝕌-wf-gen {max j k} k (λ l<k → ΠO≤ refl l<k) | Glu-wellfounded-≡-GluΛ {j} {k} = record
  { IT = IT
  ; OT = OT
  ; ⊢IT = ⊢IT
  ; ⊢OT = ⊢OT
  ; T≈ = T≈
  ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
      { IT-rel = IT-rel
      ; OT-rel = λ s® a∈ → let open ΛKripke (ap-rel s® a∈) in ®El⇒® (ΠRT.T≈T′ (RT a∈)) ®fa
      }
  }
®El⇒® (L′ {j} {k} kA) record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip }
  rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) | Glu-wellfounded-≡-Glul {j} {k} = record
  { UT = UT
  ; ⊢UT = ⊢UT
  ; T≈ = T≈
  ; krip = λ ⊢σ → let open lKripke (krip ⊢σ) in ®El⇒® kA ®ua
  }

-- If t and a are related, then the type of t is well-formed.
®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ T ∶[ 1 + i ] Se i
®El⇒ty A≈B t∼a = ®⇒ty A≈B (®El⇒® A≈B t∼a)