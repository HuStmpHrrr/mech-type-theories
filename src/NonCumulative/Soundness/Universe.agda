{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for universes
module NonCumulative.Soundness.Universe (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Properties.Liftt
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Bundle fext
open import NonCumulative.Soundness.Properties.Substitutions fext
open import NonCumulative.Soundness.ToSyntax fext
open import NonCumulative.Soundness.Realizability fext

Se-wf′ : ∀ {i} →
         ⊩ Γ →
         ------------------
         Γ ⊩ Se i ∶[ 2 + i ] Se (1 + i)
Se-wf′ {_} {i} ⊩Γ = record
  { ⊩Γ = ⊩Γ
  ; krip = krip
  }
  where
    krip : ∀ {Δ σ ρ} →
               Δ ⊢s σ ∶ ⊩Γ ® ρ →
               GluExp _ Δ (Se _) (Se _) σ ρ
    krip σ®
      with s®⇒⊢s ⊩Γ σ®
    ... | ⊢σ = record
      { ⟦T⟧ = _
      ; ⟦t⟧ = _
      ; ↘⟦T⟧ = ⟦Se⟧ _
      ; ↘⟦t⟧ = ⟦Se⟧ _
      ; T∈𝕌 = U′
      ; t∼⟦t⟧ = record
          { t∶T = t[σ] (Se-wf _ (⊩⇒⊢ ⊩Γ)) ⊢σ
          ; T≈ = Se-[] _ ⊢σ
          ; A∈𝕌 = U′
          ; rel = Se-[] _ ⊢σ
          }
      }

Liftt-wf′ : ∀ {i j } →
            Γ ⊩ S ∶[ 1 + i ] Se i →
            -------------------
            Γ ⊩ Liftt j (S ↙ i) ∶[ 1 + (j + i) ] Se (j + i)
Liftt-wf′ {S = S} {i = i} {j = j} ⊩S = record
  { ⊩Γ = ⊩Γ
  ; krip = helper
  }
  where
    open _⊩_∶[_]_ ⊩S
    helper : ∀ {Δ σ ρ} →
              Δ ⊢s σ ∶ ⊩Γ ® ρ →
              GluExp (1 + (j + i)) Δ (Liftt j (S ↙ i)) (Se _) σ ρ
    helper {Δ = Δ} {σ = σ} σ® with
      s®⇒⊢s ⊩Γ σ® | krip σ®
    ... | ⊢σ
        | record { ⟦T⟧ = U _ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = U 1+i≡1+i _ ; t∼⟦t⟧ = t∼⟦t⟧ }
        rewrite Glu-wellfounded-≡ (≤-reflexive (sym 1+i≡1+i)) = record
        { ⟦T⟧ = _
        ; ⟦t⟧ = _
        ; ↘⟦T⟧ = ⟦Se⟧ _
        ; ↘⟦t⟧ = ⟦Liftt⟧ ↘⟦t⟧
        ; T∈𝕌 = U′
        ; t∼⟦t⟧ = ®El-𝕌-𝕌 (L-𝕌 A∈𝕌 refl) U′ (record
          { t∶T = t[σ] (Liftt-wf _ ⊢S) ⊢σ
          ; T≈ = Se-[] _ ⊢σ
          ; A∈𝕌 = L-𝕌 A∈𝕌 refl
          ; rel = ®-L-𝕌 A∈𝕌 (L-𝕌 A∈𝕌 refl) (record
            { UT = _
            ; ⊢UT = t[σ]-Se ⊢S ⊢σ
            ; T≈ = Liftt-[] _ ⊢σ ⊢S
            ; krip = λ {Δ′} {τ} ⊢τ → ®-mon A∈𝕌 A∈𝕌 rel ⊢τ })
          })
        }
        where
          open GluU t∼⟦t⟧
          ⊢S = ⊩⇒⊢-tm ⊩S

L-I′ : ∀ {i j} →
       Γ ⊩ t ∶[ i ] T →
       --------------------------
       Γ ⊩ liftt j t ∶[ j + i ] Liftt j (T ↙ i)
L-I′ {t = t} {T = T} {i = i} {j = j} ⊩t = record
  { ⊩Γ = ⊩Γ
  ; krip = helper
  }
  where
    open _⊩_∶[_]_ ⊩t
    helper : ∀ {Δ σ ρ} →
              Δ ⊢s σ ∶ ⊩Γ ® ρ →
              GluExp (j + i) Δ (liftt j t) (Liftt j (T ↙ i)) σ ρ
    helper {Δ} {σ} σ® with
      s®⇒⊢s ⊩Γ σ® | krip σ®
    ... | ⊢σ
        | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
          { ⟦T⟧ = _
          ; ⟦t⟧ = _
          ; ↘⟦T⟧ = ⟦Liftt⟧ ↘⟦T⟧
          ; ↘⟦t⟧ = ⟦liftt⟧ ↘⟦t⟧
          ; T∈𝕌 = L-𝕌 T∈𝕌 refl
          ; t∼⟦t⟧ = ®El-Li-𝕌 refl T∈𝕌 (L-𝕌 T∈𝕌 refl) (record
            { t∶T = t[σ] (L-I _ ⊢t) ⊢σ
            ; UT = T [ σ ]
            ; ⊢UT = t[σ]-Se ⊢T ⊢σ
            ; a∈El = record { ua = _ ; ub = _ ; ↘ua = li↘ ; ↘ub = li↘ ; ua≈ub = ®El⇒∈El _ t∼⟦t⟧ }
            ; T≈ = Liftt-[] _ ⊢σ ⊢T
            ; krip = λ {Δ′} {τ} ⊢τ → record { ua = _ ; ↘ua = li↘ ; ®ua = ®El-mon′ T∈𝕌
                (®El-resp-≈ T∈𝕌 t∼⟦t⟧ (≈-trans ([]-cong (≈-sym (L-β _ ⊢t)) (s-≈-refl ⊢σ)) (unlift-[] _ ⊢T ⊢σ (L-I _ ⊢t)))) ⊢τ }
            })
          }
      where
        ⊢t = ⊩⇒⊢-tm ⊩t
        ⊢T = proj₂ (presup-tm ⊢t)

L-E′ : ∀ {i j} →
       Γ ⊩ T ∶[ 1 + i ] Se i →
       Γ ⊩ t ∶[ j + i ] Liftt j (T ↙ i) →
       --------------------------
       Γ ⊩ unlift t ∶[ i ] T
L-E′ {T = T} {t = t} {i = i} {j = j} record {⊩Γ = ⊩Γ ; krip = Tkrip} ⊩t = record
  { ⊩Γ = ⊩Γ
  ; krip = helper
  }
  where
    module t = _⊩_∶[_]_ ⊩t

    helper : ∀ {Δ σ ρ} →
              Δ ⊢s σ ∶ ⊩Γ ® ρ →
              GluExp i Δ (unlift t) T σ ρ
    helper {Δ} {σ} σ®
      with s®⇒⊢s ⊩Γ σ®
        | Tkrip σ®
        | t.krip (s®-irrel ⊩Γ t.⊩Γ σ®)
    ... | ⊢σ
        | record { ⟦T⟧ = .(U i) ; ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .(i) ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U 1+i≡1+i i≡i
                  ; t∼⟦t⟧ = record { t∶T = T∶U ; T≈ = Se≈Se ; A∈𝕌 = T∈𝕌 ; rel = rel } }
        | record { ⟦T⟧ = .(Li j i ⟦T⟧′) ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦Liftt⟧ {A = ⟦T⟧′} ↘⟦T⟧′ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = L j+i≡j+i iA _ _
                  ; t∼⟦t⟧ = record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip } }
        rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
          rewrite 𝕌-wf-gen {j + i} i (Li≤ j+i≡j+i)
                | 𝕌-wf-gen {1 + i} i (λ l<i → <-trans l<i (≤-reflexive (sym 1+i≡1+i)))
                | Glu-wf-gen {j + i} i (Li≤ j+i≡j+i)
                | Glu-wellfounded-≡ (≤-reflexive (sym 1+i≡1+i)) = record
                  { ⟦T⟧ = _
                  ; ⟦t⟧ = _
                  ; ↘⟦T⟧ = ↘⟦T⟧
                  ; ↘⟦t⟧ = ⟦unlift⟧ ↘⟦t⟧ ↘ua
                  ; T∈𝕌 = iA
                  ; t∼⟦t⟧ = ®El-resp-≈ _ (®El-resp-T≈ _ ®ua eq₁) eq₂
                  }
      where
        ⊢Δ = proj₁ (presup-s ⊢σ)
        open lKripke (krip (⊢wI ⊢Δ))
        open ER

        ⊢T = proj₂ (inv-Liftt-wf (⊩⇒⊢-ty ⊩t))
        ⊢t = ⊩⇒⊢-tm ⊩t

        eq₁ : Δ ⊢ sub UT I ≈ sub T σ ∶[ ℕ.suc i ] Se i
        eq₁ = ®⇒≈ _ (®El⇒® _ ®ua) (®-≡ _ iA rel refl)

        eq₂ : Δ ⊢ sub (unlift (sub t σ)) I ≈ sub (unlift t) σ ∶[ i ] sub T σ
        eq₂ = begin
                sub (unlift (sub t σ)) I ≈⟨ [I] (L-E _ (t[σ]-Se ⊢T ⊢σ) (conv t∶T (Liftt-[] _ ⊢σ ⊢T))) ⟩
                unlift (sub t σ) ≈⟨ ≈-sym (unlift-[] _ ⊢T ⊢σ ⊢t)  ⟩
                sub (unlift t) σ
              ∎