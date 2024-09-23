{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Properties of the gluing models for terms and types
module NonCumulative.Soundness.Properties.Inversion (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Semantics.Properties.PER (fext)
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel (fext)

-- this set of lemmas re-tie the knots to change all the Univ and Glu to their standard forms
-- i.e., 𝕌-wellfounded _ and Glu-wellfounded _

®-Π-inv : ∀ {i j k} →
  (i≡maxjk : i ≡ max j k) →
  (jA : A ≈ A′ ∈ 𝕌 j) →
  (RT : ∀ {a a′} →
    a ≈ a′ ∈ El j jA →
    ΠRT S (ρ ↦ a) S′ (ρ′ ↦ a′) (𝕌 k)) →
  (iA : Π j A (S ↙ k) ρ ≈ Π j A′ (S′ ↙ k) ρ′ ∈ 𝕌 i) → 
  GluΠ i j k Γ T (𝕌-wellfounded j) jA  (_⊢_®[ j ] jA) (λ a∈ → _⊢_®[ k ] (ΠRT.T≈T′ (RT a∈))) (_⊢_∶_®[ j ]_∈El jA) →
  Γ ⊢ T ®[ i ] iA
®-Π-inv {j = j} {k = k} refl jA RT (Π i≡maxjk jA′ RT′ _ _) T®   
  rewrite 𝕌-wf-gen j (ΠI≤ i≡maxjk)
        | 𝕌-wf-gen k (ΠO≤ i≡maxjk)
        | Glu-wf-gen j (ΠI≤ i≡maxjk)
        | Glu-wf-gen k (ΠO≤ i≡maxjk) = record 
    { IT = _
    ; OT = _
    ; ⊢IT = ⊢IT
    ; ⊢OT = ⊢OT
    ; T≈ = T≈
    ; krip = λ ⊢σ → let open ΠRel (krip ⊢σ) in record 
      { IT-rel = ®-≡ jA jA′ IT-rel refl 
      ; OT-rel = λ s® a∈ → OT-helper a∈ s® OT-rel 
      } 
    }
    where open GluΠ T®
          OT-helper : (a∈′ : a ∈′ El j jA′) →
                        Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA′ →
                        (∀ {s a} → Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA →
                          (a∈ : a ∈′ El j jA) →
                          Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT a∈)) →
                        --------------------------------------------------------------
                        Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT′ a∈′)
          OT-helper a∈′ s® OT-rel 
            with El-one-sided jA′ jA a∈′
          ... | a∈ 
              with RT a∈ | RT′ a∈′ | OT-rel (®El-one-sided jA′ jA s®) a∈
          ...    | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                 | R 
                rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-one-sided T≈T′ T≈T′₁ R

®-L-inv : ∀ {i j k} →
  (kA : A ≈ A′ ∈ 𝕌 k) →
  (iA : Li j k A ≈ Li j k A′ ∈ 𝕌 i) → 
  (GluL i j k Γ T (_⊢_®[ k ] kA)) → 
  Γ ⊢ T ®[ i ] iA
®-L-inv {j = j} {k = k} kA (L i≡j+k kA′ _ _) T® 
  rewrite 𝕌-wf-gen k (Li≤ i≡j+k)
        | Glu-wf-gen k (Li≤ i≡j+k) = record 
  { UT = UT 
  ; ⊢UT = ⊢UT 
  ; T≈ = T≈ 
  ; krip = λ ⊢σ → ®-≡ kA kA′ (krip ⊢σ) refl 
  }
  where open GluL T®

®El-𝕌-inv :  ∀ {j}
  (jA : A ≈ A′ ∈ 𝕌 j) →
  (iA : U j ∈′ 𝕌 (1 + j)) → 
  (GluU j (1 + j) Γ t T a (𝕌-wellfounded j) (λ a∈ → Γ ⊢ t ®[ j ] a∈)) →
  Γ ⊢ t ∶ T ®[ 1 + j ] a ∈El iA
®El-𝕌-inv jA (U 1+j≡1+j _) record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = rel }
    rewrite Glu-wellfounded-≡ (≤-reflexive (sym 1+j≡1+j)) = record 
  { t∶T = t∶T
  ; T≈ = T≈ 
  ; A∈𝕌 = A∈𝕌 
  ; rel = rel 
  }

®El-Π-inv : ∀ {i j k} →
  (i≡maxjk : i ≡ max j k) →
  (jA : A ≈ A′ ∈ 𝕌 j) →
  (RT : ∀ {a a′} →
    a ≈ a′ ∈ El j jA →
    ΠRT S (ρ ↦ a) S′ (ρ′ ↦ a′) (𝕌 k)) →
  (iA : Π j A (S ↙ k) ρ ≈ Π j A′ (S′ ↙ k) ρ′ ∈ 𝕌 i) → 
  GluΛ i j k Γ t T a _ _ jA RT (_⊢_®[ j ] jA) (_⊢_∶_®[ j ]_∈El jA) (λ a∈ → _⊢_∶_®[ k ]_∈El (ΠRT.T≈T′ (RT a∈))) →
  Γ ⊢ t ∶ T ®[ i ] a ∈El iA
®El-Π-inv {j = j} {k = k} refl jA RT (Π i≡maxjk jA′ RT′ _ _) t® 
  rewrite 𝕌-wf-gen j (ΠI≤ i≡maxjk)
        | 𝕌-wf-gen k (ΠO≤ i≡maxjk)
        | Glu-wf-gen j (ΠI≤ i≡maxjk)
        | Glu-wf-gen k (ΠO≤ i≡maxjk) = record 
    { t∶T = t∶T
    ; a∈El = El-Π-𝕌 i≡maxjk jA′ RT′ (𝕌-irrel (proj₁ Π-bund) (Π-𝕌 jA′ RT′ i≡maxjk) (proj₂ Π-bund))
    ; IT = _
    ; OT = _
    ; ⊢IT = ⊢IT
    ; ⊢OT = ⊢OT
    ; T≈ = T≈
    ; krip = λ ⊢τ → let open ΛRel (krip ⊢τ) in record 
      { IT-rel = ®-≡ jA jA′ IT-rel refl 
      ; ap-rel = λ s® b∈ → helper b∈ s® ap-rel 
      }
    }
  where open GluΛ t®
        Π-bund = Π-bundle jA (λ a≈a′ → RT a≈a′ , a∈El a≈a′) refl
        helper : (b∈′ : b ∈′ El j jA′) → 
                 Δ ⊢ s ∶ sub IT σ ®[ j ] b ∈El jA′ → 
                 (∀ {s b} → Δ ⊢ s ∶ sub IT σ ®[ j ] b ∈El jA →
                    (b∈ : b ∈′ El j jA) → 
                    ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT b∈))) → 
                 ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT′ b∈′))
        helper b∈′ s®′ ap-rel with 
          𝕌-irrel jA′ jA b∈′ | ®El-≡ jA′ jA s®′ refl
        ... | b∈ | s® 
          with ap-rel s® b∈ 
        ... | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa } 
            with RT′ b∈′ | RT b∈ 
        ... | record { ⟦T⟧ = ⟦T⟧₁ ; ⟦T′⟧ = ⟦T′⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ } 
            | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } 
          rewrite ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧ | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record 
            { fa = _
            ; ↘fa = ↘fa
            ; ®fa = ®El-≡ _ _ ®fa refl
            } 

®El-Li-inv : ∀ {i j k} 
    (i≡j+k : i ≡ j + k) →
    (kA : A ≈ A′ ∈ 𝕌 k) →
    (iA : Li j k A ≈ Li j k A′ ∈ 𝕌 i) → 
    (Glul i j _ Γ t T a (𝕌-wellfounded k) kA (_⊢_∶_®[ k ]_∈El kA)) → 
    Γ ⊢ t ∶ T ®[ i ] a ∈El iA
®El-Li-inv {j = j} {k = k} refl kA iA t®
  with iA
... | L i≡j+k kA′ _ _ 
  rewrite 𝕌-wf-gen k (Li≤ i≡j+k)
        | Glu-wf-gen k (Li≤ i≡j+k) = record
    { t∶T = t∶T
    ; UT = UT
    ; ⊢UT = ⊢UT
    ; a∈El = El-L-𝕌 kA′ i≡j+k (𝕌-irrel (proj₁ L-bund) (L-𝕌 kA′ i≡j+k) (proj₂ L-bund))
    ; T≈ = T≈
    ; krip = λ ⊢τ → let module lkrip = lKripke (krip ⊢τ) in record 
        { ua = lkrip.ua 
        ; ↘ua = lkrip.↘ua 
        ; ®ua = ®El-≡ kA kA′ lkrip.®ua refl 
        } 
    }
  where open Glul t®
        L-bund = L-bundle {j = j} kA a∈El refl