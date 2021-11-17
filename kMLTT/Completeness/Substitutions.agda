{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Contexts fext


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
,-cong′ {_} {σ} {σ′} {_} {T} {t} {t′} (⊨Γ , ⊨Δ , σ≈σ′) (⊨Δ₁ , ⊨T) (⊨Γ₁ , t≈t′) = ⊨Γ , ∷-cong ⊨Δ helper , helper′
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ → RelTyp T ρ T ρ′
        helper = ∷-cong-helper (⊨Δ₁ , ⊨T) ⊨Δ

        helper′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts (σ , t) ρ (σ′ , t′) ρ′ ⟦ ∷-cong ⊨Δ helper ⟧ρ
        helper′ {ρ} {ρ′} ρ≈ρ′
          with ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′
        ...  | ρ≈ρ′₁
             with σ≈σ′ ρ≈ρ′ | t≈t′ ρ≈ρ′₁
        ...     | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ ; nat = nat₁ ; nat′ = nat′₁ }
                | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = i , T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
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
                       with ⊨T σ≈δ₂
                  ...     | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = i , U j<i _ }
                          , record { ⟦t⟧ = ⟦t⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; t≈t′ = t≈t′₁ }
                          rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                          with subst (⟦ T ⟧_↘ ⟦t⟧₁) (drop-↦ ⟦σ⟧ ⟦t⟧) ↘⟦t⟧₁
                  ...        | ↘⟦t⟧₂
                             rewrite ⟦⟧-det ↘⟦t⟧₂ ↘⟦T⟧ = El-one-sided T≈T′ t≈t′₁ t≈t′


；-cong′ : ∀ {n} Ψs →
           Γ ⊨s σ ≈ σ′ ∶ Δ →
           ⊨ (Ψs ++⁺ Γ) →
           len Ψs ≡ n →
           --------------------------------------
           (Ψs ++⁺ Γ) ⊨s σ ； n ≈ σ′ ； n ∶ ([] ∷⁺ Δ)
；-cong′ {_} {σ} {σ′} {_} {n} Ψs (⊨Γ , ⊨Δ , σ≈σ′) ⊨ΨsΓ refl = ⊨ΨsΓ , κ-cong ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨ΨsΓ ⟧ρ → RelSubsts (σ ； n) ρ (σ′ ； n) ρ′ ⟦ κ-cong ⊨Δ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨-irrel (⊨-resp-∥ Ψs Ψs ⊨ΨsΓ refl) ⊨Γ (⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ refl ρ≈ρ′)
        ...  | ρ≈ρ′∥n = record
          { ⟦σ⟧  = ext ⟦σ⟧ (L ρ n)
          ; ⟦δ⟧  = ext ⟦δ⟧ (L ρ′ n)
          ; ↘⟦σ⟧ = ⟦；⟧ ↘⟦σ⟧
          ; ↘⟦δ⟧ = ⟦；⟧ ↘⟦δ⟧
          ; σ≈δ  = σ≈δ , ⟦⟧ρ-resp-L ⊨ΨsΓ ρ≈ρ′ (≤-trans (s≤s (m≤m+n n _)) (≤-reflexive (sym (length-++⁺′ Ψs _))))
          ; nat  = λ κ → subst (⟦ σ ； n ⟧s ρ [ κ ] ↘_) (trans (cong (ext (⟦σ⟧ [ κ ∥ L ρ n ])) (L-ρ-[] ρ κ n))
                                                              (sym (ext-mon ⟦σ⟧ (L ρ n) κ)))
                               (⟦；⟧ (subst (⟦ σ ⟧s_↘ ⟦σ⟧ [ κ ∥ L ρ n ]) (sym (ρ-∥-[] ρ κ n)) (nat (κ ∥ L ρ n))))
          ; nat′ = λ κ → subst (⟦ σ′ ； n ⟧s ρ′ [ κ ] ↘_) (trans (cong (ext (⟦δ⟧ [ κ ∥ L ρ′ n ])) (L-ρ-[] ρ′ κ n))
                                                                (sym (ext-mon ⟦δ⟧ (L ρ′ n) κ)))
                               (⟦；⟧ (subst (⟦ σ′ ⟧s_↘ ⟦δ⟧ [ κ ∥ L ρ′ n ]) (sym (ρ-∥-[] ρ′ κ n)) (nat′ (κ ∥ L ρ′ n))))
          }
          where open RelSubsts (σ≈σ′ ρ≈ρ′∥n)


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


∘-assoc′ : ∀ {Γ‴} →
           Γ′ ⊨s σ ∶ Γ →
           Γ″ ⊨s σ′ ∶ Γ′ →
           Γ‴ ⊨s σ″ ∶ Γ″ →
           ---------------------------------------
           Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
∘-assoc′ {_} {σ} {_} {_} {σ′} {σ″} (⊨Γ′ , ⊨Γ , ⊨σ) (⊨Γ″ , ⊨Γ′₁ , ⊨σ′) (⊨Γ‴ , ⊨Γ″₁ , ⊨σ″) = ⊨Γ‴ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ‴ ⟧ρ → RelSubsts (σ ∘ σ′ ∘ σ″) ρ (σ ∘ (σ′ ∘ σ″)) ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
            { ⟦σ⟧  = σ.⟦σ⟧
            ; ⟦δ⟧  = σ.⟦δ⟧
            ; ↘⟦σ⟧ = ⟦∘⟧ σ″.↘⟦σ⟧ (⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧)
            ; ↘⟦δ⟧ = ⟦∘⟧ (⟦∘⟧ σ″.↘⟦δ⟧ σ′.↘⟦δ⟧) σ.↘⟦δ⟧
            ; σ≈δ  = σ.σ≈δ
            ; nat  = λ κ → ⟦∘⟧ (σ″.nat κ) (⟦∘⟧ (σ′.nat κ) (σ.nat κ))
            ; nat′ = λ κ → ⟦∘⟧ (⟦∘⟧ (σ″.nat′ κ) (σ′.nat′ κ)) (σ.nat′ κ)
            }
          where module σ″ = RelSubsts (⊨σ″ ρ≈ρ′)
                module σ′ = RelSubsts (⊨σ′ (⊨-irrel ⊨Γ″₁ ⊨Γ″ σ″.σ≈δ))
                module σ  = RelSubsts (⊨σ (⊨-irrel ⊨Γ′₁ ⊨Γ′ σ′.σ≈δ))


,-∘′ : ∀ {i} →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ″ ⊨ T ∶ Se i →
       Γ′ ⊨ t ∶ (T [ σ ]) →
       Γ ⊨s τ ∶ Γ′ →
       ---------------------------------------------
       Γ ⊨s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ (T ∺ Γ″)
,-∘′ {_} {σ} {_} {T} {t} {_} {τ} (⊨Γ′ , ⊨Γ″ , ⊨σ) (⊨Γ″₁ , ⊨T) (⊨Γ′₁ , ⊨t) (⊨Γ , ⊨Γ′₂ , ⊨τ) = ⊨Γ , ∷-cong ⊨Γ″ helper , helper″
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ″ ⟧ρ → RelTyp T ρ T ρ′
        helper = ∷-cong-helper (⊨Γ″₁ , ⊨T) ⊨Γ″

        helper′ : (A≈B : A ≈ B ∈ 𝕌∞) → a ≈ b ∈ El∞ A≈B → (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ″ ⟧ρ) → ⟦ T ⟧ ρ ↘ A → a ≈ b ∈ El∞ (RelTyp.T≈T′ (helper ρ≈ρ′))
        helper′ (i , A≈B) a≈b ρ≈ρ′ ↘A
          with ⊨-irrel ⊨Γ″ ⊨Γ″₁ ρ≈ρ′
        ...  | ρ≈ρ′₁
             with ⊨T ρ≈ρ′₁
        ...     | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = i , U j<i eq }
                , record { ⟦t⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; t≈t′ = T≈T′₁ }
                rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                      | ⟦⟧-det ↘A ↘⟦t⟧ = El-one-sided A≈B T≈T′₁ a≈b

        helper″ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelSubsts ((σ , t) ∘ τ) ρ ((σ ∘ τ) , t [ τ ]) ρ′ ⟦ ∷-cong ⊨Γ″ helper ⟧ρ
        helper″ {ρ} {ρ′} ρ≈ρ′
          with ⊨τ ρ≈ρ′
        ...  | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ ; nat = nat ; nat′ = nat′ }
             with ⊨t (⊨-irrel ⊨Γ′₂ ⊨Γ′₁ σ≈δ) | ⊨σ (⊨-irrel ⊨Γ′₂ ⊨Γ′ σ≈δ)
        ...     | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = i , T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat₂ ; nat′ = nat′₂ }
                | record { ⟦σ⟧ = ⟦σ⟧₁ ; ⟦δ⟧ = ⟦δ⟧₁ ; ↘⟦σ⟧ = ↘⟦σ⟧₁ ; ↘⟦δ⟧ = ↘⟦δ⟧₁ ; σ≈δ = σ≈δ₁ ; nat = nat₁ ; nat′ = nat′₁ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧₁
                with subst₂ (_≈_∈ ⟦ _ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) σ≈δ₁
        ...        | σ≈δ₂ = record
          { ⟦σ⟧  = ⟦σ⟧₁ ↦ ⟦t⟧
          ; ⟦δ⟧  = ⟦δ⟧₁ ↦ ⟦t′⟧
          ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ (⟦,⟧ ↘⟦σ⟧₁ ↘⟦t⟧)
          ; ↘⟦δ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦δ⟧ ↘⟦δ⟧₁) (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)
          ; σ≈δ  = σ≈δ₂ , t≈t′₁
          ; nat  = λ κ → ⟦∘⟧ (nat κ) (subst (⟦ σ , t ⟧s ⟦σ⟧ [ κ ] ↘_) (sym (↦-mon ⟦σ⟧₁ ⟦t⟧ κ)) (⟦,⟧ (nat₁ κ) (nat₂ κ)))
          ; nat′ = λ κ → subst (⟦ (σ ∘ τ) , t [ τ ] ⟧s ρ′ [ κ ] ↘_) (sym (↦-mon ⟦δ⟧₁ ⟦t′⟧ κ))
                               (⟦,⟧ (⟦∘⟧ (nat′ κ) (nat′₁ κ)) (⟦[]⟧ (nat′ κ) (nat′₂ κ)))
          }
          where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El∞ (RelTyp.T≈T′ (helper σ≈δ₂))
                t≈t′₁ = helper′ (-, T≈T′) t≈t′ σ≈δ₂ (subst (⟦ T ⟧_↘ _) (sym (drop-↦ _ _)) ↘⟦T⟧)


-- -- -- ；-∘       : ∀ {n} Ψs →
-- -- --             Γ′ ⊨s σ ∶ Γ″ →
-- -- --             Γ ⊨s τ ∶ Ψs ++⁺ Γ′ →
-- -- --             len Ψs ≡ n →
-- -- --             ------------------------------
-- -- --             Γ ⊨s σ ； n ∘ τ ≈ (σ ∘ τ ∥ n) ； L τ n ∶ [] ∷⁺ Γ″
-- -- -- p-,       : ∀ {i} →
-- -- --             Γ′ ⊨s σ ∶ Γ →
-- -- --             Γ ⊨ T ∶ Se i →
-- -- --             Γ′ ⊨ t ∶ T [ σ ] →
-- -- --             -------------------------
-- -- --             Γ′ ⊨s p (σ , t) ≈ σ ∶ Γ
-- -- -- ,-ext     : Γ′ ⊨s σ ∶ T ∺ Γ →
-- -- --             ----------------------------------
-- -- --             Γ′ ⊨s σ ≈ p σ , v 0 [ σ ] ∶ T ∺ Γ
-- -- -- ；-ext     : Γ ⊨s σ ∶ [] ∷⁺ Δ →
-- -- --             -----------------------------------
-- -- --             Γ ⊨s σ ≈ (σ ∥ 1) ； L σ 1 ∶ [] ∷⁺ Δ
-- -- -- s-≈-sym   : Γ ⊨s σ ≈ σ′ ∶ Δ →
-- -- --             ------------------
-- -- --             Γ ⊨s σ′ ≈ σ ∶ Δ
-- -- -- s-≈-trans : Γ ⊨s σ ≈ σ′ ∶ Δ →
-- -- --             Γ ⊨s σ′ ≈ σ″ ∶ Δ →
-- -- --             -------------------
-- -- --             Γ ⊨s σ ≈ σ″ ∶ Δ
-- -- -- s-≈-conv  : Γ ⊨s σ ≈ σ′ ∶ Δ →
-- -- --             ⊨ Δ ≈ Δ′ →
-- -- --             ------------------
-- -- --             Γ ⊨s σ ≈ σ′ ∶ Δ′
