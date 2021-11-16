{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext


I-≈′ : ⊨ Γ →
       --------------
       Γ ⊨s I ≈ I ∶ Γ
I-≈′ ⊨Γ = ⊨Γ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts I ρ I ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
          { ⟦σ⟧  = _
          ; ⟦δ⟧  = _
          ; ↘⟦σ⟧ = ⟦I⟧
          ; ↘⟦δ⟧ = ⟦I⟧
          ; σ≈δ  = ρ≈ρ′
          ; nat  = λ κ → ⟦I⟧
          ; nat′ = λ κ → ⟦I⟧
          }


-- p-cong    : Γ ⊨s σ ≈ σ′ ∶ T ∺ Δ →
--             ----------------------
--             Γ ⊨s p σ ≈ p σ′ ∶ Δ


∘-cong′ : Γ ⊨s τ ≈ τ′ ∶ Γ′ →
          Γ′ ⊨s σ ≈ σ′ ∶ Γ″ →
          ----------------
          Γ ⊨s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
∘-cong′ {_} {τ} {τ′} {_} {σ} {σ′} (⊨Γ , ⊨Γ′ , τ≈τ′) (⊨Γ′₁ , ⊨Γ″ , σ≈σ′) = ⊨Γ , ⊨Γ″ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts (σ ∘ τ) ρ (σ′ ∘ τ′) ρ′ ⟦ ⊨Γ″ ⟧ρ
        helper ρ≈ρ′ = record
          { ⟦σ⟧  = σ.⟦σ⟧
          ; ⟦δ⟧  = σ.⟦δ⟧
          ; ↘⟦σ⟧ = ⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧
          ; ↘⟦δ⟧ = ⟦∘⟧ τ.↘⟦δ⟧ σ.↘⟦δ⟧
          ; σ≈δ  = σ.σ≈δ
          ; nat  = λ κ → ⟦∘⟧ (τ.nat κ) (σ.nat κ)
          ; nat′ = λ κ → ⟦∘⟧ (τ.nat′ κ) (σ.nat′ κ)
          }
          where module τ = RelSubsts (τ≈τ′ ρ≈ρ′)
                module σ = RelSubsts (σ≈σ′ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))

,-cong′ : ∀ {i} →
          Γ ⊨s σ ≈ σ′ ∶ Δ →
          Δ ⊨ T ∶ Se i →
          Γ ⊨ t ≈ t′ ∶ (T [ σ ]) →
          -----------------------------
          Γ ⊨s σ , t ≈ σ′ , t′ ∶ (T ∺ Δ)
,-cong′ {_} {σ} {σ′} {_} {T} {t} {t′} (⊨Γ , ⊨Δ , σ≈σ′) ((⊨Δ₁ , rel) , ⊨T) ((⊨Γ₁ , rel′) , t≈t′) = ⊨Γ , ∷-cong ⊨Δ helper , helper′
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ → RelTyp T ρ T ρ′
        helper ρ≈ρ′
          with ⊨-irrel ⊨Δ ⊨Δ₁ ρ≈ρ′
        ...  | ρ≈ρ′₁
             with rel ρ≈ρ′₁ | ⊨T ρ≈ρ′₁
        ...     | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = i , U j<i eq }
                | res
                rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = RelExp⇒RepTyp′ res

        helper′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts (σ , t) ρ (σ′ , t′) ρ′ ⟦ ∷-cong ⊨Δ helper ⟧ρ
        helper′ {ρ} {ρ′} ρ≈ρ′
          with ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′
        ...  | ρ≈ρ′₁
             with σ≈σ′ ρ≈ρ′ | rel′ ρ≈ρ′₁ | t≈t′ ρ≈ρ′₁
        ...     | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ ; nat = nat₁ ; nat′ = nat′₁ }
                | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = i , T≈T′ }
                | record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧
                with subst₂ (_≈_∈ ⟦ ⊨Δ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) σ≈δ
        ...        | σ≈δ₁ = record
            { ⟦σ⟧  = ⟦σ⟧ ↦ ⟦t⟧
            ; ⟦δ⟧  = ⟦δ⟧ ↦ ⟦t′⟧
            ; ↘⟦σ⟧ = ⟦,⟧ ↘⟦σ⟧ ↘⟦t⟧
            ; ↘⟦δ⟧ = ⟦,⟧ ↘⟦δ⟧ ↘⟦t′⟧
            ; σ≈δ  = σ≈δ₁ , t≈t′₁
            ; nat  = λ κ → subst (⟦ σ , t ⟧s ρ [ κ ] ↘_) (sym (↦-mon ⟦σ⟧ ⟦t⟧ κ)) (⟦,⟧ (nat₁ κ) (nat κ))
            ; nat′ = λ κ → subst (⟦ σ′ , t′ ⟧s ρ′ [ κ ] ↘_) (sym (↦-mon ⟦δ⟧ ⟦t′⟧ κ)) (⟦,⟧ (nat′₁ κ) (nat′ κ))
            }
            where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El∞ (RelTyp.T≈T′ (helper σ≈δ₁))
                  t≈t′₁
                    with ⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ₁
                  ...  | σ≈δ₂
                       with rel σ≈δ₂ | ⊨T σ≈δ₂
                  ...     | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = i , U j<i _ }
                          | record { ⟦t⟧ = ⟦t⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; t≈t′ = t≈t′₁ }
                          rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                          with subst (⟦ T ⟧_↘ ⟦t⟧₁) (drop-↦ ⟦σ⟧ ⟦t⟧) ↘⟦t⟧₁
                  ...        | ↘⟦t⟧₂
                             rewrite ⟦⟧-det ↘⟦t⟧₂ ↘⟦T⟧ = El-one-sided T≈T′ t≈t′₁ t≈t′

-- ；-cong    : ∀ {n} Ψs →
--             Γ ⊨s σ ≈ σ′ ∶ Δ →
--             ⊨ Ψs ++⁺ Γ →
--             len Ψs ≡ n →
--             --------------------------------------
--             Ψs ++⁺ Γ ⊨s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Δ


I-∘′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s I ∘ σ ≈ σ ∶ Δ
I-∘′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts (I ∘ σ) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { ⟦σ⟧  = ⟦σ⟧
          ; ⟦δ⟧  = ⟦δ⟧
          ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ ⟦I⟧
          ; ↘⟦δ⟧ = ↘⟦δ⟧
          ; σ≈δ  = σ≈δ
          ; nat  = λ κ → ⟦∘⟧ (nat κ) ⟦I⟧
          ; nat′ = nat′
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


∘-I′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s σ ∘ I ≈ σ ∶ Δ
∘-I′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts (σ ∘ I) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { ⟦σ⟧  = ⟦σ⟧
          ; ⟦δ⟧  = ⟦δ⟧
          ; ↘⟦σ⟧ = ⟦∘⟧ ⟦I⟧ ↘⟦σ⟧
          ; ↘⟦δ⟧ = ↘⟦δ⟧
          ; σ≈δ  = σ≈δ
          ; nat  = λ κ → ⟦∘⟧ ⟦I⟧ (nat κ)
          ; nat′ = nat′
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


-- ∘-assoc   : ∀ {Γ‴} →
--             Γ′ ⊨s σ ∶ Γ →
--             Γ″ ⊨s σ′ ∶ Γ′ →
--             Γ‴ ⊨s σ″ ∶ Γ″ →
--             ---------------------------------------
--             Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
-- ,-∘       : ∀ {i} →
--             Γ′ ⊨s σ ∶ Γ″ →
--             Γ″ ⊨ T ∶ Se i →
--             Γ′ ⊨ t ∶ T [ σ ] →
--             Γ ⊨s τ ∶ Γ′ →
--             ---------------------------------------------
--             Γ ⊨s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∺ Γ″
-- p-∘       : Γ′ ⊨s σ ∶ T ∺ Γ″ →
--             Γ ⊨s τ ∶ Γ′ →
--             ------------------------------
--             Γ ⊨s p σ ∘ τ ≈ p (σ ∘ τ) ∶ Γ″
-- ；-∘       : ∀ {n} Ψs →
--             Γ′ ⊨s σ ∶ Γ″ →
--             Γ ⊨s τ ∶ Ψs ++⁺ Γ′ →
--             len Ψs ≡ n →
--             ------------------------------
--             Γ ⊨s σ ； n ∘ τ ≈ (σ ∘ τ ∥ n) ； L τ n ∶ [] ∷⁺ Γ″
-- p-,       : ∀ {i} →
--             Γ′ ⊨s σ ∶ Γ →
--             Γ ⊨ T ∶ Se i →
--             Γ′ ⊨ t ∶ T [ σ ] →
--             -------------------------
--             Γ′ ⊨s p (σ , t) ≈ σ ∶ Γ
-- ,-ext     : Γ′ ⊨s σ ∶ T ∺ Γ →
--             ----------------------------------
--             Γ′ ⊨s σ ≈ p σ , v 0 [ σ ] ∶ T ∺ Γ
-- ；-ext     : Γ ⊨s σ ∶ [] ∷⁺ Δ →
--             -----------------------------------
--             Γ ⊨s σ ≈ (σ ∥ 1) ； L σ 1 ∶ [] ∷⁺ Δ
-- s-≈-sym   : Γ ⊨s σ ≈ σ′ ∶ Δ →
--             ------------------
--             Γ ⊨s σ′ ≈ σ ∶ Δ
-- s-≈-trans : Γ ⊨s σ ≈ σ′ ∶ Δ →
--             Γ ⊨s σ′ ≈ σ″ ∶ Δ →
--             -------------------
--             Γ ⊨s σ ≈ σ″ ∶ Δ
-- s-≈-conv  : Γ ⊨s σ ≈ σ′ ∶ Δ →
--             ⊨ Δ ≈ Δ′ →
--             ------------------
--             Γ ⊨s σ ≈ σ′ ∶ Δ′
