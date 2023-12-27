{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Cumulativity of the gluing models for terms and types
module MLTT.Soundness.Cumulativity (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import MLTT.Statics.Properties
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Soundness.LogRel
open import MLTT.Soundness.Realizability fext
open import MLTT.Soundness.Properties.LogRel fext


-- Similar to cumulativity of the PER model, we also need a lowering lemma in order to
-- establish cumulativity (®El-lower).  Unlike the PER model, lowering in the gluing
-- model is a bit more difficult because we need to have one extra assumption of
-- syntactic and semantic types glued in the lower level. By exploiting this
-- assumption, we replace everything about types to the lower level in the gluing of
-- terms.
mutual

  ®-cumu-step : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
                Γ ⊢ T ®[ i ] A≈B →
                -----------------------------
                Γ ⊢ T ®[ 1 + i ] 𝕌-cumu-step i A≈B
  ®-cumu-step (ne C≈C′) (⊢T , rel) = cumu ⊢T , λ ⊢σ → ≈-cumu (rel ⊢σ)
  ®-cumu-step N T∼A                = ≈-cumu T∼A
  ®-cumu-step (U′ j<i) T∼A         = ≈-cumu T∼A
  ®-cumu-step (Π iA RT) T∼A        = record
    { IT   = IT
    ; OT   = OT
    ; ⊢OT  = cumu ⊢OT
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΠRel (krip ⊢σ)
      in record
      { IT-rel = ®-cumu-step iA IT-rel
      ; OT-rel = λ s∼a a∈ → ®-cumu-step (ΠRT.T≈T′ (RT (El-lower _ iA a∈))) (OT-rel (®El-lower iA IT-rel s∼a) (El-lower _ iA a∈))
      }
    }
    where open GluΠ T∼A


  ®El-cumu-step : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
                  Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                  ------------------------------------------
                  Γ ⊢ t ∶ T ®[ 1 + i ] a ∈El 𝕌-cumu-step i A≈B
  ®El-cumu-step (ne C≈C′) (ne c∈ , rel)    = ne c∈ , record
    { t∶T  = t∶T
    ; ⊢T   = cumu ⊢T
    ; krip = λ ⊢σ → let Tσ≈ , tσ≈ = krip ⊢σ in ≈-cumu Tσ≈ , tσ≈
    }
    where open GluNe rel
  ®El-cumu-step N (t∼a , T≈N)              = t∼a , ≈-cumu T≈N
  ®El-cumu-step (U′ j<i) t∼a
    rewrite Glu-wellfounded-≡ j<i
          | Glu-wellfounded-≡ (m≤n⇒m≤1+n j<i) = record
    { t∶T = t∶T
    ; T≈  = ≈-cumu T≈
    ; A∈𝕌 = A∈𝕌
    ; rel = rel
    }
    where open GluU t∼a
  ®El-cumu-step (Π iA RT) t∼a              = record
    { t∶T  = t∶T
    ; a∈El = El-cumu-step _ (Π iA RT) a∈El
    ; IT   = IT
    ; OT   = OT
    ; ⊢OT  = cumu ⊢OT
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΛRel (krip ⊢σ)
      in record
      { IT-rel = ®-cumu-step iA IT-rel
      ; ap-rel = λ s∼b b∈ →
        let open ΛKripke (ap-rel (®El-lower iA IT-rel s∼b) (El-lower _ iA b∈))
        in record
        { fa  = fa
        ; ↘fa = ↘fa
        ; ®fa = ®El-cumu-step (ΠRT.T≈T′ (RT (El-lower _ iA b∈))) ®fa
        }
      }
    }
    where open GluΛ t∼a


  -- This is tricky! We need to pass on the knowledge that T is related to A in a
  -- lower level 1 +h that ®El can be lowered! It cannot be done without this extra
  -- piece of knowledge.
  ®El-lower : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ T ®[ i ] A≈B →  --  This assumption is critically needed.
              Γ ⊢ t ∶ T ®[ 1 + i ] a ∈El 𝕌-cumu-step i A≈B →
              -----------------------------------------
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B
  ®El-lower (ne C≈C′) (⊢T , rel) (ne c∈⊥ , rel′) = ne c∈⊥ , record
    { t∶T  = t∶T
    ; ⊢T   = ⊢T
    ; krip = λ ⊢σ → rel ⊢σ , proj₂ (krip ⊢σ)
    }
    where open GluNe rel′ hiding (⊢T)
  ®El-lower N T∼A (t∼a , _)                      = t∼a , T∼A
  ®El-lower (U′ j<i) T∼A t∼a
    rewrite Glu-wellfounded-≡ j<i
          | Glu-wellfounded-≡ (m≤n⇒m≤1+n j<i)       = record
    { t∶T = t∶T
    ; T≈  = T∼A
    ; A∈𝕌 = A∈𝕌
    ; rel = rel
    }
    where open GluU t∼a
  ®El-lower (Π iA RT) T∼A t∼a                    = record
    { t∶T  = t∶T
    ; a∈El = El-lower _ (Π iA RT) a∈El
    ; IT   = T.IT
    ; OT   = T.OT
    ; ⊢OT  = T.⊢OT
    ; T≈   = T.T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΛRel (krip ⊢σ)
          module Π = ΠRel (T.krip ⊢σ)
          iAcu = 𝕌-cumu-step _ iA
      in record
      { IT-rel = Π.IT-rel
      ; ap-rel = λ s∼b b∈ →
        let open ΛKripke (ap-rel (®El-resp-T≈ iAcu
                                              (®El-cumu-step iA s∼b)
                                              (®⇒≈ iAcu (®-cumu-step iA Π.IT-rel) IT-rel))
                                 (El-cumu-step _ iA b∈))
            RT₁      = RT b∈
            RT₂      = RT (El-lower _ iA (El-cumu-step _ iA b∈))
            T≈T′     = ΠRT.T≈T′ RT₁
            T≈T′cumu = 𝕌-cumu-step _ T≈T′
            ®fa′     = ®El-≡ (𝕌-cumu-step _ (ΠRT.T≈T′ RT₂))
                             T≈T′cumu
                             ®fa
                             (⟦⟧-det (ΠRT.↘⟦T⟧ RT₂) (ΠRT.↘⟦T⟧ RT₁))
        in record
        { fa  = fa
        ; ↘fa = ↘fa
        ; ®fa = ®El-lower T≈T′ (Π.OT-rel s∼b b∈)
                          (®El-resp-T≈ T≈T′cumu ®fa′
                                       (®⇒≈ T≈T′cumu (®El⇒® T≈T′cumu ®fa′) (®-cumu-step T≈T′ (Π.OT-rel s∼b b∈))))
        }
      }
    }
    where module T = GluΠ T∼A
          open GluΛ t∼a

-- Push cumulativity to any higher level.
®-cumu-steps : ∀ {i} j
               (A≈B : A ≈ B ∈ 𝕌 i) →
               Γ ⊢ T ®[ i ] A≈B →
               -----------------------------
               Γ ⊢ T ®[ j + i ] 𝕌-cumu-steps i j A≈B
®-cumu-steps zero A≈B T∼A    = T∼A
®-cumu-steps (suc j) A≈B T∼A = ®-cumu-step (𝕌-cumu-steps _ j A≈B) (®-cumu-steps j A≈B T∼A)


®El-cumu-steps : ∀ {i} j
                 (A≈B : A ≈ B ∈ 𝕌 i) →
                 Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                 ------------------------------------------
                 Γ ⊢ t ∶ T ®[ j + i ] a ∈El 𝕌-cumu-steps i j A≈B
®El-cumu-steps zero A≈B t∼a    = t∼a
®El-cumu-steps (suc j) A≈B t∼a = ®El-cumu-step (𝕌-cumu-steps _ j A≈B) (®El-cumu-steps j A≈B t∼a)


®-cumu : ∀ {i j}
         (A≈B : A ≈ B ∈ 𝕌 i) →
         Γ ⊢ T ®[ i ] A≈B →
         (i≤j : i ≤ j) →
         -----------------------------
         Γ ⊢ T ®[ j ] 𝕌-cumu i≤j A≈B
®-cumu {i = i} A≈B T∼A i≤j
  with ®-cumu-steps (≤-diff i≤j) A≈B T∼A
...  | rel = helper (𝕌-cumu-steps i (≤-diff i≤j) A≈B) (𝕌-cumu i≤j A≈B) rel (trans (ℕₚ.+-comm (≤-diff i≤j) i) (≤-diff-+ i≤j))
  where helper : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ i ] A≈B → i ≡ j → Γ ⊢ T ®[ j ] A≈B′
        helper A≈B A≈B′ T∼A refl = ®-one-sided A≈B A≈B′ T∼A

®El-cumu : ∀ {i j}
           (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           (i≤j : i ≤ j) →
           -----------------------------
           Γ ⊢ t ∶ T ®[ j ] a ∈El 𝕌-cumu i≤j A≈B
®El-cumu {i = i} A≈B t∼a i≤j
  with ®El-cumu-steps (≤-diff i≤j) A≈B t∼a
...  | rel = helper (𝕌-cumu-steps i (≤-diff i≤j) A≈B) (𝕌-cumu i≤j A≈B) rel (trans (ℕₚ.+-comm (≤-diff i≤j) i) (≤-diff-+ i≤j))
  where helper : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → i ≡ j → Γ ⊢ t ∶ T ®[ j ] a ∈El A≈B′
        helper A≈B A≈B′ t∼a refl = ®El-one-sided A≈B A≈B′ t∼a

®El-lowers : ∀ {i} j
             (A≈B : A ≈ B ∈ 𝕌 i) →
             Γ ⊢ T ®[ i ] A≈B →
             Γ ⊢ t ∶ T ®[ j + i ] a ∈El 𝕌-cumu-steps i j A≈B →
             -----------------------------
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B
®El-lowers 0       A≈B T∼A t∼a = t∼a
®El-lowers (suc j) A≈B T∼A t∼a = ®El-lowers j A≈B T∼A (®El-lower (𝕌-cumu-steps _ j A≈B) (®-cumu-steps j A≈B T∼A) t∼a)


-- Given cumulativity and lowering, we can obtain a generalization of both, stating
-- that if types are related in any level, then we can adjust the gluing for terms to
-- this level, regardless of the original level.
®El-irrel : ∀ {i j}
            (A≈B : A ≈ B ∈ 𝕌 i) →
            (A≈B′ : A ≈ B′ ∈ 𝕌 j) →
            Γ ⊢ T ®[ j ] A≈B′ →
            Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
            -----------------------------
            Γ ⊢ t ∶ T ®[ j ] a ∈El A≈B′
®El-irrel {i = i} {j} A≈B A≈B′ T∼A t∼a
  with i ≤? j
...  | yes i≤j = ®El-one-sided (𝕌-cumu i≤j A≈B) A≈B′ (®El-cumu A≈B t∼a i≤j)
...  | no  i≰j
    with ≰⇒≥ i≰j
...    | i≥j
      rewrite sym (m∸n+n≡m i≥j) = ®El-lowers (i ∸ j) A≈B′ T∼A (®El-one-sided A≈B (𝕌-cumu-steps _ (i ∸ j) A≈B′) t∼a)


-- The master lemma which handles everything you need to deal with universe levels.
--
-- This proof is not very straightforward. We have:
--
--     A ≈ A′ at level i
--     B ≈ B′ at level j
--     A ≈ B at level k
--     t : T ∼ a ∈ El A at level i
--     T ≈ T′ at level k
--
-- Our goal is t : T′ ∼ a ∈ El B at level j
--
-- We proceed as follows:
--
-- t : T  ∼ a ∈ El A at level max i k          (by cumulativity)
-- t : T′ ∼ a ∈ El A at level max i k          (T ≈ T′ at level max i k)
-- t : T′ ∼ a ∈ El A at level max j (max i k)  (cumulativity)
--
-- The previous step lifts the gluing relation to a high enough level so that we can
-- move a to B
--
-- t : T′ ∼ a ∈ El B at level max j (max i k)  (by transportation due to A ≈ B)
-- t : T′ ∼ a ∈ El B at level j                (by lowering)
®El-master : ∀ {i j k} →
             (A≈A′ : A ≈ A′ ∈ 𝕌 i)
             (B≈B′ : B ≈ B′ ∈ 𝕌 j)
             (A≈B : A ≈ B ∈ 𝕌 k) →
             Γ ⊢ T′ ®[ j ] B≈B′ →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈A′ →
             Γ ⊢ T ≈ T′ ∶ Se k →
             ------------------------------
             Γ ⊢ t ∶ T′ ®[ j ] a ∈El B≈B′
®El-master {i = i} {j} {k} A≈A′ B≈B′ A≈B T′∼B t∼a T≈T′
  = ®El-irrel B≈B′↑ B≈B′ T′∼B
    (®El-transport A≈A′↑↑ B≈B′↑ (𝕌-cumu k≤m′ A≈B)
    (®El-cumu A≈A′↑
    (®El-resp-T≈ A≈A′↑
    (®El-cumu A≈A′ t∼a i≤m) (lift-⊢≈-Se-max′ T≈T′))
              m≤m′))
  where m      = max i k
        i≤m    = m≤m⊔n i k
        k≤m    = m≤n⊔m i k
        m′     = max j m
        j≤m′   = m≤m⊔n j m
        m≤m′   = m≤n⊔m j m
        k≤m′   = ≤-trans k≤m m≤m′
        A≈A′↑  = 𝕌-cumu i≤m A≈A′
        A≈A′↑↑ = 𝕌-cumu m≤m′ A≈A′↑
        B≈B′↑  = 𝕌-cumu j≤m′ B≈B′
