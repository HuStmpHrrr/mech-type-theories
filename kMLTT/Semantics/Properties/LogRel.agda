{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.PER
open import kMLTT.Semantics.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext

mutual

  ⊨-sym : ⊨ Γ ≈ Δ → ⊨ Δ ≈ Γ
  ⊨-sym []-≈                              = []-≈
  ⊨-sym (κ-cong Γ≈Δ)                      = κ-cong (⊨-sym Γ≈Δ)
  ⊨-sym (∷-cong {Γ} {Δ} {T} {T′} Γ≈Δ rel) = ∷-cong (⊨-sym Γ≈Δ) helper
    where helper : ρ ≈ ρ′ ∈ ⟦ ⊨-sym Γ≈Δ ⟧ρ → RelTyp T′ ρ T ρ′
          helper ρ≈ρ′ = record
            { ⟦T⟧   = ⟦T′⟧
            ; ⟦T′⟧  = ⟦T⟧
            ; ↘⟦T⟧  = ↘⟦T′⟧
            ; ↘⟦T′⟧ = ↘⟦T⟧
            ; T≈T′  = 𝕌∞-sym T≈T′
            ; nat   = nat′
            ; nat′  = nat
            }
            where open RelTyp (rel (⟦⟧ρ-sym (⊨-sym Γ≈Δ) Γ≈Δ ρ≈ρ′))

  ⟦⟧ρ-sym : (Γ≈Δ : ⊨ Γ ≈ Δ) (Δ≈Γ : ⊨ Δ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ′ ≈ ρ ∈ ⟦ Δ≈Γ ⟧ρ
  ⟦⟧ρ-sym []-≈ []-≈ ρ≈ρ′                        = tt
  ⟦⟧ρ-sym (κ-cong Γ≈Δ) (κ-cong Δ≈Γ) (ρ≈ρ′ , eq) = ⟦⟧ρ-sym Γ≈Δ Δ≈Γ ρ≈ρ′ , sym eq
  ⟦⟧ρ-sym {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT) (∷-cong Δ≈Γ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
    with ⟦⟧ρ-sym Γ≈Δ Δ≈Γ ρ≈ρ′
  ...  | ρ′≈ρ                                   = ρ′≈ρ , helper
    where helper : lookup ρ′ 0 ≈ lookup ρ 0 ∈ El∞ (RelTyp.T≈T′ (RT′ ρ′≈ρ))
          helper
            with RT ρ≈ρ′ | RT′ ρ′≈ρ
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = i , T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = j , T≈T′₁ }
               rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁
                     | ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁ = 𝕌-irrel (𝕌-sym T≈T′) T≈T′₁ (El-sym T≈T′ (𝕌-sym T≈T′) ρ0≈ρ′0)


⟦⟧ρ-one-sided : (Γ≈Δ : ⊨ Γ ≈ Δ) (Γ≈Δ′ : ⊨ Γ ≈ Δ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ′ ⟧ρ
⟦⟧ρ-one-sided []-≈ []-≈ ρ≈ρ′                                    = tt
⟦⟧ρ-one-sided (κ-cong Γ≈Δ) (κ-cong Γ≈Δ′) (ρ≈ρ′ , eq)            = ⟦⟧ρ-one-sided Γ≈Δ Γ≈Δ′ ρ≈ρ′ , eq
⟦⟧ρ-one-sided {_} {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT) (∷-cong Γ≈Δ′ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
  with ⟦⟧ρ-one-sided Γ≈Δ Γ≈Δ′ ρ≈ρ′
...  | ρ≈ρ′₁ = ρ≈ρ′₁ , helper
    where helper : lookup ρ 0 ≈ lookup ρ′ 0 ∈ El∞ (RelTyp.T≈T′ (RT′ ρ≈ρ′₁))
          helper
            with RT ρ≈ρ′ | RT′ ρ≈ρ′₁
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = i , T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = j , T≈T′₁ }
               rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁ = El-one-sided T≈T′ T≈T′₁ ρ0≈ρ′0


⊨-irrel : (Γ≈Δ Γ≈Δ′ : ⊨ Γ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ′ ⟧ρ
⊨-irrel = ⟦⟧ρ-one-sided


⟦⟧ρ-one-sided′ : (Γ≈Δ : ⊨ Γ ≈ Δ) (Γ′≈Δ : ⊨ Γ′ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ′≈Δ ⟧ρ
⟦⟧ρ-one-sided′ Γ≈Δ Γ′≈Δ ρ≈ρ′ = ⟦⟧ρ-sym (⊨-sym Γ′≈Δ) Γ′≈Δ (⟦⟧ρ-one-sided (⊨-sym Γ≈Δ) (⊨-sym Γ′≈Δ) (⟦⟧ρ-sym Γ≈Δ (⊨-sym Γ≈Δ) ρ≈ρ′))

mutual

  ⊨-trans : ⊨ Γ ≈ Γ′ → ⊨ Γ′ ≈ Γ″ → ⊨ Γ ≈ Γ″
  ⊨-trans []-≈ []-≈                                                             = []-≈
  ⊨-trans (κ-cong Γ≈Γ′) (κ-cong Γ′≈Γ″)                                          = κ-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″)
  ⊨-trans (∷-cong {_} {_} {T} {T′} Γ≈Γ′ RT) (∷-cong {_} {_} {_} {T″} Γ′≈Γ″ RT′) = ∷-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″) helper
    where helper : ρ ≈ ρ′ ∈ ⟦ ⊨-trans Γ≈Γ′ Γ′≈Γ″ ⟧ρ → RelTyp T ρ T″ ρ′
          helper ρ≈ρ′
            with ⊨-refl Γ≈Γ′
          ...  | Γ≈Γ
               with RT (⟦⟧ρ-one-sided Γ≈Γ Γ≈Γ′ (⟦⟧ρ-refl (⊨-trans Γ≈Γ′ Γ′≈Γ″) Γ≈Γ ρ≈ρ′))
                  | RT′ (⟦⟧ρ-one-sided′ (⊨-trans Γ≈Γ′ Γ′≈Γ″) Γ′≈Γ″ ρ≈ρ′)
          ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′  ; nat = nat }
                  | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ ; nat′ = nat′ }
                  rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
            { ⟦T⟧   = _
            ; ⟦T′⟧  = _
            ; ↘⟦T⟧  = ↘⟦T⟧
            ; ↘⟦T′⟧ = ↘⟦T′⟧₁
            ; T≈T′  = 𝕌∞-trans T≈T′ T≈T′₁
            ; nat   = nat
            ; nat′  = nat′
            }

  ⟦⟧ρ-trans : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ′≈Γ″ : ⊨ Γ′ ≈ Γ″) (Γ≈Γ″ : ⊨ Γ ≈ Γ″) →
              ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ″ ∈ ⟦ Γ′≈Γ″ ⟧ρ → ρ ≈ ρ″ ∈ ⟦ Γ≈Γ″ ⟧ρ
  ⟦⟧ρ-trans []-≈ []-≈ []-≈ ρ≈ρ′ ρ′≈ρ″                                            = tt
  ⟦⟧ρ-trans (κ-cong Γ≈Γ′) (κ-cong Γ′≈Γ″) (κ-cong Γ≈Γ″) (ρ≈ρ′ , eq) (ρ′≈ρ″ , eq′) = ⟦⟧ρ-trans Γ≈Γ′ Γ′≈Γ″ Γ≈Γ″ ρ≈ρ′ ρ′≈ρ″ , trans eq eq′
  ⟦⟧ρ-trans {_} {_} {_} {ρ} {ρ′} {ρ″} (∷-cong Γ≈Γ′ RT) (∷-cong Γ′≈Γ″ RT′) (∷-cong Γ≈Γ″ RT″) (ρ≈ρ′ , ρ0≈ρ′0) (ρ′≈ρ″ , ρ′0≈ρ″0)
    with ⟦⟧ρ-trans Γ≈Γ′ Γ′≈Γ″ Γ≈Γ″ ρ≈ρ′ ρ′≈ρ″
  ...  | ρ≈ρ″                                                                    = ρ≈ρ″ , helper
    where helper : lookup ρ 0 ≈ lookup ρ″ 0 ∈ El∞ (RelTyp.T≈T′ (RT″ ρ≈ρ″))
          helper
            with RT ρ≈ρ′ | RT′ ρ′≈ρ″ | RT″ ρ≈ρ″
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = i , T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = j , T≈T′₁ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = k , T≈T′₂ }
               rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁
                     | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₂
                     | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧₂ = 𝕌-irrel (𝕌-trans T≈T′ T≈T′₁) T≈T′₂
                                                      (El-trans T≈T′ T≈T′₁ (𝕌-trans T≈T′ T≈T′₁) ρ0≈ρ′0 ρ′0≈ρ″0)

  ⊨-refl : ⊨ Γ ≈ Γ′ → ⊨ Γ ≈ Γ
  ⊨-refl Γ≈Γ′ = ⊨-trans Γ≈Γ′ (⊨-sym Γ≈Γ′)

  ⟦⟧ρ-refl : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ≈Γ : ⊨ Γ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ ∈ ⟦ Γ≈Γ ⟧ρ
  ⟦⟧ρ-refl Γ≈Γ′ Γ≈Γ ρ≈ρ′ = ⟦⟧ρ-trans Γ≈Γ′ (⊨-sym Γ≈Γ′) Γ≈Γ ρ≈ρ′ (⟦⟧ρ-sym Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ≈ρ′)

⊨-isPER : IsPartialEquivalence ⊨_≈_
⊨-isPER = record
  { sym   = ⊨-sym
  ; trans = ⊨-trans
  }

⊨-PER : PartialSetoid _ _
⊨-PER = record
  { Carrier              = Ctxs
  ; _≈_                  = ⊨_≈_
  ; isPartialEquivalence = ⊨-isPER
  }

module ⊨R = PS ⊨-PER

⟦⟧ρ-swap : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ′≈Γ : ⊨ Γ′ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ′≈Γ ⟧ρ
⟦⟧ρ-swap Γ≈Γ′ Γ′≈Γ ρ≈ρ′ = ⟦⟧ρ-one-sided′ (⊨-refl Γ≈Γ′) Γ′≈Γ (⟦⟧ρ-one-sided Γ≈Γ′ (⊨-refl Γ≈Γ′) ρ≈ρ′)

⟦⟧ρ-sym′ : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ ∈ ⟦ Γ≈Γ′ ⟧ρ
⟦⟧ρ-sym′ Γ≈Γ′ ρ≈ρ′ = ⟦⟧ρ-swap (⊨-sym Γ≈Γ′) Γ≈Γ′ (⟦⟧ρ-sym Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ≈ρ′)

⟦⟧ρ-trans′ : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ″ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ″ ∈ ⟦ Γ≈Γ′ ⟧ρ
⟦⟧ρ-trans′ Γ≈Γ′ ρ≈ρ′ ρ′≈ρ″ = ⟦⟧ρ-one-sided (⊨-refl Γ≈Γ′) Γ≈Γ′
                                           (⟦⟧ρ-trans Γ≈Γ′ (⊨-sym Γ≈Γ′) (⊨-refl Γ≈Γ′)
                                                      ρ≈ρ′ (⟦⟧ρ-swap Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ′≈ρ″))

⟦⟧ρ-isPER : (Γ≈Δ : ⊨ Γ ≈ Δ) → IsPartialEquivalence ⟦ Γ≈Δ ⟧ρ
⟦⟧ρ-isPER Γ≈Δ = record
  { sym   = ⟦⟧ρ-sym′ Γ≈Δ
  ; trans = ⟦⟧ρ-trans′ Γ≈Δ
  }

⟦⟧ρ-PER : ⊨ Γ ≈ Δ → PartialSetoid _ _
⟦⟧ρ-PER Γ≈Δ = record
  { Carrier              = Envs
  ; _≈_                  = ⟦ Γ≈Δ ⟧ρ
  ; isPartialEquivalence = ⟦⟧ρ-isPER Γ≈Δ
  }

module ⟦⟧ρR {Γ Δ} (Γ≈Δ : ⊨ Γ ≈ Δ) = PS (⟦⟧ρ-PER Γ≈Δ)


⟦⟧ρ-mon : ∀ (Γ≈Δ : ⊨ Γ ≈ Δ) (κ : UnMoT) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ [ κ ] ≈ ρ′ [ κ ] ∈ ⟦ Γ≈Δ ⟧ρ
⟦⟧ρ-mon []-≈ κ ρ≈ρ′ = tt
⟦⟧ρ-mon {_} {_} {ρ} {ρ′} (κ-cong Γ≈Δ) κ (ρ≈ρ′ , eq)
  rewrite ρ-∥-[] ρ κ 1
        | ρ-∥-[] ρ′ κ 1
        | eq        = ⟦⟧ρ-mon Γ≈Δ (κ ∥ L ρ′ 1) ρ≈ρ′ , refl
⟦⟧ρ-mon {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT) κ (ρ≈ρ′ , ρ0≈ρ′0)
  rewrite sym (drop-mon ρ κ)
        | sym (drop-mon ρ′ κ)
        with ⟦⟧ρ-mon Γ≈Δ κ ρ≈ρ′
...        | ρ≈ρ′₁  = ρ≈ρ′₁ , helper
  where helper : lookup ρ 0 [ κ ] ≈ lookup ρ′ 0 [ κ ] ∈ El∞ (RelTyp.T≈T′ (RT ρ≈ρ′₁))
        helper
          with RT ρ≈ρ′ | RT ρ≈ρ′₁
        ...  | record { T≈T′ = i , T≈T′ ; nat = nat ; nat′ = nat′ }
             | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = j , T≈T′₁ }
             rewrite ⟦⟧-det ↘⟦T⟧₁ (nat κ)
                   | ⟦⟧-det ↘⟦T′⟧₁ (nat′ κ) = El-mon T≈T′ κ T≈T′₁ ρ0≈ρ′0


⊨-resp-len : ⊨ Γ ≈ Δ → len Γ ≡ len Δ
⊨-resp-len []-≈           = refl
⊨-resp-len (κ-cong Γ≈Δ)   = cong suc (⊨-resp-len Γ≈Δ)
⊨-resp-len (∷-cong Γ≈Δ _) = ⊨-resp-len Γ≈Δ

⟦⟧ρ-resp-L : ∀ {n} (Γ≈Δ : ⊨ Γ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → n < len Γ → L ρ n ≡ L ρ′ n
⟦⟧ρ-resp-L []-≈ ρ≈ρ′ (s≤s z≤n)                     = refl
⟦⟧ρ-resp-L (κ-cong Γ≈Δ) (ρ≈ρ′ , eq) (s≤s z≤n)      = refl
⟦⟧ρ-resp-L (κ-cong Γ≈Δ) (ρ≈ρ′ , eq) (s≤s (s≤s n<)) = cong₂ _+_ eq (⟦⟧ρ-resp-L Γ≈Δ ρ≈ρ′ (s≤s n<))
⟦⟧ρ-resp-L {_} {_} {ρ} {ρ′} {n} (∷-cong Γ≈Δ _) (ρ≈ρ′ , _) n<
  with ⟦⟧ρ-resp-L Γ≈Δ ρ≈ρ′ n<
...  | res
     rewrite L-drop n ρ
           | L-drop n ρ′                           = res


⊨-resp-∥ : ∀ Ψs Ψs′ → ⊨ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ → len Ψs ≡ len Ψs′ → ⊨ Γ ≈ Δ
⊨-resp-∥ [] [] Γ≈Δ eq                                      = Γ≈Δ
⊨-resp-∥ (.[] ∷ Ψs) (.[] ∷ Ψs′) (κ-cong Γ≈Δ) eq            = ⊨-resp-∥ Ψs Ψs′ Γ≈Δ (suc-injective eq)
⊨-resp-∥ ((_ ∷ Ψ) ∷ Ψs) ((_ ∷ Ψ′) ∷ Ψs′) (∷-cong Γ≈Δ _) eq = ⊨-resp-∥ (Ψ ∷ Ψs) (Ψ′ ∷ Ψs′) Γ≈Δ eq


⟦⟧ρ-resp-∥ : ∀ Ψs Ψs′ (Γ≈Δ : ⊨ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ) (eq : len Ψs ≡ len Ψs′) →
               ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ∥ (len Ψs) ≈ ρ′ ∥ (len Ψs) ∈ ⟦ ⊨-resp-∥ Ψs Ψs′ Γ≈Δ eq ⟧ρ
⟦⟧ρ-resp-∥ [] [] Γ≈Δ eq ρ≈ρ′                                            = ρ≈ρ′
⟦⟧ρ-resp-∥ (_ ∷ Ψs) (_ ∷ Ψs′) (κ-cong Γ≈Δ) eq (ρ≈ρ′ , _)                = ⟦⟧ρ-resp-∥ Ψs Ψs′ Γ≈Δ (suc-injective eq) ρ≈ρ′
⟦⟧ρ-resp-∥ ((_ ∷ Ψ) ∷ Ψs) ((_ ∷ Ψ′) ∷ Ψs′) (∷-cong Γ≈Δ _) eq (ρ≈ρ′ , _) = ⟦⟧ρ-resp-∥ (Ψ ∷ Ψs) (Ψ′ ∷ Ψs′) Γ≈Δ eq ρ≈ρ′
