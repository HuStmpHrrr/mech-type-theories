{-# OPTIONS --without-K --safe #-}

module PTT.StaticsProps where

open import Lib
open import PTT.Statics
open import Relation.Binary using (PartialSetoid)

import Data.Nat.Properties as ℕₚ
import Relation.Binary.Reasoning.PartialSetoid as PS

⊢PartialSetoid : Env → Typ → PartialSetoid _ _
⊢PartialSetoid Γ T = record
  { Carrier              = Exp
  ; _≈_                  = λ t t′ → Γ ⊢ t ≈ t′ ∶ T
  ; isPartialEquivalence = record
    { sym   = ≈-sym
    ; trans = ≈-trans
    }
  }

module PS′ {o ℓ} (P : PartialSetoid o ℓ) where
  open PS P public
  module P = PartialSetoid P
  open P

  step-≈-close : ∀ x y → x ≈ y → x IsRelatedTo y
  step-≈-close x y x∼y = relTo x∼y

  infix 4 step-≈-close

  syntax step-≈-close x y x≈y = x ≈!⟨ x≈y ⟩ y ∎

module TR {Γ T} = PS′ (⊢PartialSetoid Γ T)

inv-Π-wf : Γ ⊢ Π S T ∶ T′ →
           ----------------
           S ∷ Γ ⊢ T
inv-Π-wf (Π-wf ⊢S ⊢T _ _) = _ , ⊢T
inv-Π-wf (conv ⊢Π x)      = inv-Π-wf ⊢Π

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ----------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here = _ , conv (t[σ] ⊢T (S-↑ ⊢TΓ)) (≈-≲ (Se-[] (S-↑ ⊢TΓ) ℕₚ.≤-refl))
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T            = i , conv (t[σ] ⊢T (S-↑ (⊢∷ ⊢Γ ⊢S))) (≈-≲ (Se-[] (S-↑ ⊢TΓ) ℕₚ.≤-refl))

mutual
  ty⇒env-ty-wf : Γ ⊢ t ∶ T →
              ------------
              ⊢ Γ × Γ ⊢ T
  ty⇒env-ty-wf (N-wf i ⊢Γ)       = ⊢Γ , suc i , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (Se-wf ⊢Γ _)      = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (Π-wf ⊢S ⊢T _ _)
    with ty⇒env-ty-wf ⊢S
  ...  | ⊢Γ , _ , _              = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (vlookup ⊢Γ T∈Γ)  = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  ty⇒env-ty-wf (ze-I ⊢Γ)         = ⊢Γ , 0 , N-wf 0 ⊢Γ
  ty⇒env-ty-wf (su-I t)          = ty⇒env-ty-wf t
  ty⇒env-ty-wf (N-E ⊢Π ⊢s ⊢r ⊢t)
    with ty⇒env-ty-wf ⊢Π
  ...  | ⊢Γ , _                  = ⊢Γ , _ , conv (Λ-E ⊢Π ⊢t) (≈-≲ (Se-[] (S-, ⊢I (N-wf 0 ⊢Γ) (conv ⊢t (≈-≲ (≈-sym (N-[] 0 ⊢I))))) ℕₚ.≤-refl))
    where ⊢I = S-I ⊢Γ
  ty⇒env-ty-wf (Λ-I t) with ty⇒env-ty-wf t
  ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T        = ⊢Γ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
  ty⇒env-ty-wf (Λ-E ⊢r ⊢s)
    with ty⇒env-ty-wf ⊢r | ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _ , ⊢Π | _ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T               = ⊢Γ , _ , conv (t[σ] ⊢T I,s) (≈-≲ (Se-[] I,s ℕₚ.≤-refl))
    where S[I] = ≈-≲ (≈-sym ([I] ⊢S))
          I,s  = S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S))))
  ty⇒env-ty-wf (t[σ] ⊢t ⊢σ)
    with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢σ
  ...  | ⊢Δ , _ , ⊢T | ⊢Γ , _    = ⊢Γ , _ , conv (t[σ] ⊢T ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))
  ty⇒env-ty-wf (conv ⊢t S≲T)
    with ty⇒env-ty-wf ⊢t | ≲⇒env-ty-wf S≲T
  ...  | ⊢Γ , _ | _ , i , _ , ⊢T = ⊢Γ , _ , ⊢T

  tys⇒env-wf : Γ ⊢s σ ∶ Δ →
              ------------
              ⊢ Γ × ⊢ Δ
  tys⇒env-wf (S-↑ ⊢SΓ@(⊢∷ ⊢Γ _)) = ⊢SΓ , ⊢Γ
  tys⇒env-wf (S-I ⊢Γ)            = ⊢Γ , ⊢Γ
  tys⇒env-wf (S-∘ ⊢τ ⊢σ)
    with tys⇒env-wf ⊢τ | tys⇒env-wf ⊢σ
  ...  | ⊢Γ , _ | _ , ⊢Δ         = ⊢Γ , ⊢Δ
  tys⇒env-wf (S-, ⊢σ ⊢S ⊢s)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                 = ⊢Γ , ⊢∷ ⊢Δ ⊢S

  ≲⇒env-ty-wf : Γ ⊢ S ≲ T →
                ------------------------------------------
                ⊢ Γ × ∃ λ i → Γ ⊢ S ∶ Se i × Γ ⊢ T ∶ Se i
  ≲⇒env-ty-wf (Se-≲ ⊢Γ i≤j) = ⊢Γ , _ , Se-wf ⊢Γ (s≤s i≤j) , Se-wf ⊢Γ ℕₚ.≤-refl
  ≲⇒env-ty-wf (≈-≲ S≈T)
    with ty-eq⇒env-ty-wf-gen S≈T
  ...  | ⊢Γ , ⊢S , ⊢T       = ⊢Γ , _ , ⊢S , ⊢T

  ty-eq⇒env-ty-wf-gen : Γ ⊢ s ≈ t ∶ T →
                        -----------------------
                        ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T
  ty-eq⇒env-ty-wf-gen (N-[] i ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (N-wf i ⊢Δ) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , N-wf i ⊢Γ
  ty-eq⇒env-ty-wf-gen (Se-[] ⊢σ i<j)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (Se-wf ⊢Δ i<j) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , Se-wf ⊢Γ i<j
  ty-eq⇒env-ty-wf-gen (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (Π-wf ⊢S ⊢T i≤k j≤k) ⊢σ) Sek[] , Π-wf ⊢S[σ] (conv (t[σ] ⊢T qσ) Sej[]) i≤k j≤k
    where Sek[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
          Sei[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
          ⊢S[σ] = conv (t[σ] ⊢S ⊢σ) Sei[]
          ⊢SΓ   = ⊢∷ ⊢Γ ⊢S[σ]
          qσ    = S-, (S-∘ (S-↑ ⊢SΓ) ⊢σ) ⊢S
                      (conv (vlookup ⊢SΓ here) (≈-≲ (≈-sym (≈-conv ([∘] (S-↑ ⊢SΓ) ⊢σ ⊢S)
                                               (≈-≲ (Se-[] (S-∘ (S-↑ ⊢SΓ) ⊢σ) ℕₚ.≤-refl))))))
          Sej[] = ≈-≲ (Se-[] qσ ℕₚ.≤-refl)
  ty-eq⇒env-ty-wf-gen (Π-cong S≈S′ T≈T′ i≤k j≤k)
    with ty-eq⇒env-ty-wf-gen S≈S′ | ty-eq⇒env-ty-wf-gen T≈T′
  ...  | ⊢Γ , ⊢S , ⊢S′ | _ , ⊢T , ⊢T′ = ⊢Γ , Π-wf ⊢S ⊢T i≤k j≤k , Π-wf ⊢S′ {!!} {!!} {!!}
  ty-eq⇒env-ty-wf-gen (v-≈ x x₁)                    = {!!}
  ty-eq⇒env-ty-wf-gen (ze-≈ x)                      = {!!}
  ty-eq⇒env-ty-wf-gen (su-cong s≈t)                 = {!!}
  ty-eq⇒env-ty-wf-gen (rec-cong s≈t s≈t₁ s≈t₂ s≈t₃) = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)                  = {!!}
  ty-eq⇒env-ty-wf-gen ($-cong s≈t s≈t₁)             = {!!}
  ty-eq⇒env-ty-wf-gen ([]-cong x s≈t)               = {!!}
  ty-eq⇒env-ty-wf-gen (ze-[] x)                     = {!!}
  ty-eq⇒env-ty-wf-gen (su-[] x x₁)                  = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-[] x x₁)                   = {!!}
  ty-eq⇒env-ty-wf-gen ($-[] x x₁ x₂)                = {!!}
  ty-eq⇒env-ty-wf-gen (rec-[] x x₁ x₂ x₃ x₄)        = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-ze x x₁ x₂)            = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-su x x₁ x₂ x₃)         = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-β x x₁)                    = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-η x)                       = {!!}
  ty-eq⇒env-ty-wf-gen ([I] x)                       = {!!}
  ty-eq⇒env-ty-wf-gen (↑-lookup ⊢Γ x)               = {!!}
  ty-eq⇒env-ty-wf-gen ([∘] x x₁ x₂)                 = {!!}
  ty-eq⇒env-ty-wf-gen ([,]-v-ze x x₁ x₂)            = {!!}
  ty-eq⇒env-ty-wf-gen ([,]-v-su x x₁ x₂ x₃)         = {!!}
  ty-eq⇒env-ty-wf-gen (≈-conv s≈t x) = {!!}
  ty-eq⇒env-ty-wf-gen (≈-sym s≈t)                   = {!!}
  ty-eq⇒env-ty-wf-gen (≈-trans s≈t s≈t₁)            = {!!}
