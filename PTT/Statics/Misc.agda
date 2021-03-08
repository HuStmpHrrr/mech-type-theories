{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Misc where

open import Lib
open import PTT.Statics

open import Relation.Binary using (PartialSetoid)

import Data.Nat.Properties as ℕₚ
import Relation.Binary.Reasoning.PartialSetoid as PS
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

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

⊢sPartialSetoid : Env → Env → PartialSetoid _ _
⊢sPartialSetoid Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = λ σ σ′ → Γ ⊢s σ ≈ σ′ ∶ Δ
  ; isPartialEquivalence = record
    { sym   = S-≈-sym
    ; trans = S-≈-trans
    }
  }

module TRS {Γ Δ} = PS′ (⊢sPartialSetoid Γ Δ)

inv-Π-wf : Γ ⊢ Π S T ∶ T′ →
           ----------------
           S ∷ Γ ⊢ T
inv-Π-wf (Π-wf ⊢S ⊢T _ _) = _ , ⊢T
inv-Π-wf (conv ⊢Π _)      = inv-Π-wf ⊢Π

inv-Π-wf′ : Γ ⊢ Π S T ∶ T′ →
            ----------------
            Γ ⊢ S
inv-Π-wf′ (Π-wf ⊢S ⊢T _ _) = _ , ⊢S
inv-Π-wf′ (conv ⊢Π _)      = inv-Π-wf′ ⊢Π

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ----------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here = _ , conv (t[σ] ⊢T (S-↑ ⊢TΓ)) (≈-≲ (Se-[] (S-↑ ⊢TΓ) ℕₚ.≤-refl))
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T            = i , conv (t[σ] ⊢T (S-↑ (⊢∷ ⊢Γ ⊢S))) (≈-≲ (Se-[] (S-↑ ⊢TΓ) ℕₚ.≤-refl))

vlookup-inv : ∀ {x} →
              Γ ⊢ v x ∶ T →
              ∃ λ T′ → (x ∶ T′ ∈! Γ) × Star (λ S U → Γ ⊢ S ≲ U) T′ T
vlookup-inv (vlookup _ T∈Γ) = _ , T∈Γ , ε
vlookup-inv (conv ⊢x S≲T)
  with vlookup-inv ⊢x
...  | T″ , T″∈Γ , T″≲T = T″ , T″∈Γ , T″≲T ◅◅ S≲T ◅ ε

N-≈ : ∀ i →
      ⊢ Γ →
      Γ ⊢ N ≈ N ∶ Se i
N-≈ i ⊢Γ = begin
  N       ≈˘⟨ N-[] i (S-I ⊢Γ) ⟩
  N [ I ] ≈!⟨ N-[] i (S-I ⊢Γ) ⟩
  N       ∎
  where open TR

Se-≈ : ∀ {i j} →
       ⊢ Γ →
       i < j →
       Γ ⊢ Se i ≈ Se i ∶ Se j
Se-≈ {_} {i} {j} ⊢Γ i<j = begin
  Se i       ≈˘⟨ Se-[] (S-I ⊢Γ) i<j ⟩
  Se i [ I ] ≈!⟨ Se-[] (S-I ⊢Γ) i<j ⟩
  Se i       ∎
  where open TR

mutual
  ≈-refl : Γ ⊢ t ∶ T →
           --------------
           Γ ⊢ t ≈ t ∶ T
  ≈-refl (N-wf i ⊢Γ)          = N-≈ i ⊢Γ
  ≈-refl (Se-wf ⊢Γ i<j)       = Se-≈ ⊢Γ i<j
  ≈-refl (Π-wf ⊢S ⊢T i≤k j≤k) = Π-cong ⊢S (≈-refl ⊢S) (≈-refl ⊢T) i≤k j≤k
  ≈-refl (vlookup T∈Γ ⊢Γ)     = v-≈ T∈Γ ⊢Γ
  ≈-refl (ze-I ⊢Γ)            = ze-≈ ⊢Γ
  ≈-refl (su-I ⊢t)            = su-cong (≈-refl ⊢t)
  ≈-refl (N-E ⊢T ⊢s ⊢r ⊢t)    = rec-cong (≈-refl ⊢T) (≈-refl ⊢s) (≈-refl ⊢r) (≈-refl ⊢t)
  ≈-refl (Λ-I ⊢t)             = Λ-cong (≈-refl ⊢t)
  ≈-refl (Λ-E ⊢r ⊢s)          = $-cong (≈-refl ⊢r) (≈-refl ⊢s)
  ≈-refl (t[σ] ⊢t ⊢σ)         = []-cong (S-≈-refl ⊢σ) (≈-refl ⊢t)
  ≈-refl (conv ⊢t S≲T)        = ≈-conv (≈-refl ⊢t) S≲T

  S-≈-refl : Γ ⊢s σ ∶ Δ →
             --------------
             Γ ⊢s σ ≈ σ ∶ Δ
  S-≈-refl (S-↑ ⊢SΔ)      = ↑-≈ ⊢SΔ
  S-≈-refl (S-I ⊢Γ)       = I-≈ ⊢Γ
  S-≈-refl (S-∘ ⊢τ ⊢σ)    = ∘-cong (S-≈-refl ⊢τ) (S-≈-refl ⊢σ)
  S-≈-refl (S-, ⊢σ ⊢S ⊢s) = ,-cong ⊢S (S-≈-refl ⊢σ) (≈-refl ⊢s)
  S-≈-refl (S-conv ≲ ⊢σ)  = S-≈-conv ≲ (S-≈-refl ⊢σ)

conv-* : ⊢ Γ →
         Γ ⊢ t ∶ T [ σ ] →
         Γ ⊢s σ ∶ Δ →
         Star (λ S U → Δ ⊢ S ≲ U) T T′ →
         Γ ⊢ t ∶ T′ [ σ ]
conv-* ⊢Γ ⊢t ⊢σ ε                    = ⊢t
conv-* ⊢Γ ⊢t ⊢σ (Se-≲ ⊢Δ i≤j ◅ T≲T′) = conv-* ⊢Γ (conv (conv (conv ⊢t (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)))
                                                                      (Se-≲ ⊢Γ i≤j))
                                                                      (≈-≲ (≈-sym (Se-[] ⊢σ ℕₚ.≤-refl)))) ⊢σ T≲T′
conv-* ⊢Γ ⊢t ⊢σ (≈-≲ T≈S ◅ S≲T′)     = conv-* ⊢Γ (conv ⊢t (≈-≲ (≈-conv ([]-cong (S-≈-refl ⊢σ) T≈S) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))))) ⊢σ S≲T′

≈-conv-* : ⊢ Γ →
           Γ ⊢ t ≈ t′ ∶ T [ σ ] →
           Γ ⊢s σ ∶ Δ →
           Star (λ S U → Δ ⊢ S ≲ U) T T′ →
           Γ ⊢ t ≈ t′ ∶ T′ [ σ ]
≈-conv-* ⊢Γ t≈t′ ⊢σ ε                    = t≈t′
≈-conv-* ⊢Γ t≈t′ ⊢σ (Se-≲ ⊢Δ i≤j ◅ T≲T′) = ≈-conv-* ⊢Γ (≈-conv (≈-conv (≈-conv t≈t′ (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)))
                                                                                    (Se-≲ ⊢Γ i≤j))
                                                                                    (≈-≲ (≈-sym (Se-[] ⊢σ ℕₚ.≤-refl))))
                                                       ⊢σ T≲T′
≈-conv-* ⊢Γ t≈t′ ⊢σ (≈-≲ T≈S ◅ S≲T′)     = ≈-conv-* ⊢Γ (≈-conv t≈t′ (≈-≲ (≈-conv ([]-cong (S-≈-refl ⊢σ) T≈S) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))))) ⊢σ S≲T′

infix 4 _⊢s*_

_⊢s*_ : Env → Env → Set
Γ ⊢s* Δ = Star (λ Γ Δ → ∃ λ σ → Γ ⊢s σ ∶ Δ × ⊢ Δ) Γ Δ

iter-[] : Exp →
          Γ ⊢s* Δ →
          Exp
iter-[] t ε                    = t
iter-[] t ((τ , ⊢τ , _) ◅ ⊢σ*) = iter-[] t ⊢σ* [ τ ]

iter-[]-Se : ∀ {i j} →
             ⊢ Γ →
             (⊢σ* : Γ ⊢s* Δ) →
             i < j →
             Γ ⊢ iter-[] (Se i) ⊢σ* ≈ Se i ∶ Se j
iter-[]-Se ⊢Γ ε i<j                      = Se-≈ ⊢Γ i<j
iter-[]-Se ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) i<j = begin
  iter-[] (Se _) ⊢σ* [ τ ] ≈⟨ ≈-conv ([]-cong (S-≈-refl ⊢τ) (iter-[]-Se ⊢Γ′ ⊢σ* i<j)) (≈-≲ (Se-[] ⊢τ ℕₚ.≤-refl)) ⟩
  Se _ [ τ ]               ≈!⟨ Se-[] ⊢τ i<j ⟩
  Se _                     ∎
  where open TR

≈-Se-inter-[] : ∀ {i} →
                ⊢ Γ →
                (⊢σ* : Γ ⊢s* Δ) →
                Γ ⊢ S ≈ T ∶ iter-[] (Se i) ⊢σ* →
                Γ ⊢ S ≈ T ∶ Se i
≈-Se-inter-[] _ ε S≈T                       = S≈T
≈-Se-inter-[] ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) S≈T = ≈-conv S≈T (≈-≲ (≈-trans (≈-conv ([]-cong ⊢τ≈ (iter-[]-Se ⊢Γ′ ⊢σ* ℕₚ.≤-refl))
                                                                               (≈-≲ (Se-[] ⊢τ ℕₚ.≤-refl)))
                                                              (Se-[] ⊢τ ℕₚ.≤-refl)))
  where ⊢τ≈ = S-≈-refl ⊢τ

inter-[]-≈ : ∀ {i} →
             ⊢ Γ →
             (⊢σ* : Γ ⊢s* Δ) →
             Δ ⊢ S ≈ T ∶ Se i →
             Γ ⊢ iter-[] S ⊢σ* ≈ iter-[] T ⊢σ* ∶ iter-[] (Se i) ⊢σ*
inter-[]-≈ ⊢Γ ε S≈T                      = S≈T
inter-[]-≈ ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) S≈T = []-cong (S-≈-refl ⊢τ) (inter-[]-≈ ⊢Γ′ ⊢σ* S≈T)

≈-conv-subst* : ⊢ Γ →
                (⊢σ* : Γ ⊢s* Δ) →
                Γ ⊢ t ≈ t′ ∶ iter-[] S ⊢σ* →
                Δ ⊢ S ≲ T →
                Γ ⊢ t ≈ t′ ∶ iter-[] T ⊢σ*
≈-conv-subst* ⊢Γ ⊢σ* t≈t′ (Se-≲ ⊢Δ i≤j) = ≈-conv (≈-conv (≈-conv t≈t′
                                                                 (≈-≲ (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl)))
                                                         (Se-≲ ⊢Γ i≤j))
                                                 (≈-≲ (≈-sym (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl)))
≈-conv-subst* ⊢Γ ⊢σ* t≈t′ (≈-≲ S≈T)     = ≈-conv t≈t′ (≈-≲ (≈-conv (inter-[]-≈ ⊢Γ ⊢σ* S≈T) (≈-≲ (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl))))

vlookup-cond : ∀ {x} Δ →
                 ⊢ T′ ∷ Δ ++ S ∷ Γ →
                 ⊢ T′ ∷ Δ ++ S′ ∷ Γ →
                 x ∶ T ∈! Δ ++ S ∷ Γ →
                 x ∶ T ∈! Δ ++ S′ ∷ Γ ⊎ Σ (Δ ++ S′ ∷ Γ ⊢s* Γ) λ ⊢σ* → (x ∶ iter-[] S′ ⊢σ* ∈! Δ ++ S′ ∷ Γ) × T ≡ iter-[] S ⊢σ*
vlookup-cond [] (⊢∷ (⊢∷ ⊢Γ _) _) (⊢∷ (⊢∷ _ ⊢S′) _) here = inj₂ ((↑ , S-↑ (⊢∷ ⊢Γ ⊢S′) , ⊢Γ) ◅ ε , here , refl)
vlookup-cond [] _ _ (there T∈Γ′)                        = inj₁ (there T∈Γ′)
vlookup-cond (U ∷ Δ) (⊢∷ ⊢Γ′ _) _ here                  = inj₁ here
vlookup-cond (U ∷ Δ) (⊢∷ (⊢∷ ⊢ΔSΓ ⊢U) _) (⊢∷ (⊢∷ ⊢ΔS′Γ ⊢U′) _) (there T∈Γ′)
    with vlookup-cond Δ (⊢∷ ⊢ΔSΓ ⊢U) (⊢∷ ⊢ΔS′Γ ⊢U′) T∈Γ′
... | inj₁ T∈Γ″                                         = inj₁ (there T∈Γ″)
... | inj₂ (⊢σ* , S″∈Γ″ , refl)                         = inj₂ ((↑ , S-↑ (⊢∷ ⊢ΔS′Γ ⊢U′) , ⊢ΔS′Γ) ◅ ⊢σ* , there S″∈Γ″ , refl)

≲-refl : ∀ {i} →
         Γ ⊢ T ∶ Se i →
         ---------------
         Γ ⊢ T ≲ T
≲-refl T = ≈-≲ (≈-refl T)

env≲-refl : ⊢ Γ →
            ---------
            ⊢ Γ ≲ Γ
env≲-refl ⊢[]        = ≈[]
env≲-refl (⊢∷ ⊢Γ ⊢T) = ≈∷ (env≲-refl ⊢Γ) (≲-refl ⊢T) ⊢T
