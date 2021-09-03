{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Misc where

open import Lib
open import PTT.Statics

open import Relation.Binary using (PartialSetoid)

import Data.Nat.Properties as ℕₚ
import Relation.Binary.Reasoning.PartialSetoid as PS
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

⊢PartialSetoid : Ctx → Typ → PartialSetoid _ _
⊢PartialSetoid Γ T = record
  { Carrier              = Exp
  ; _≈_                  = λ t t′ → Γ ⊢ t ≈ t′ ∶ T
  ; isPartialEquivalence = record
    { sym   = ≈-sym
    ; trans = ≈-trans
    }
  }

module TR {Γ T} = PS (⊢PartialSetoid Γ T)

⊢sPartialSetoid : Ctx → Ctx → PartialSetoid _ _
⊢sPartialSetoid Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = λ σ σ′ → Γ ⊢s σ ≈ σ′ ∶ Δ
  ; isPartialEquivalence = record
    { sym   = S-≈-sym
    ; trans = S-≈-trans
    }
  }

module TRS {Γ Δ} = PS (⊢sPartialSetoid Γ Δ)

inv-Π-wf : Γ ⊢ Π S T ∶ T′ →
           ----------------
           S ∷ Γ ⊢ T
inv-Π-wf (Π-wf ⊢S ⊢T) = _ , ⊢T
inv-Π-wf (cumu ⊢Π)    = inv-Π-wf ⊢Π
inv-Π-wf (conv ⊢Π _)  = inv-Π-wf ⊢Π

inv-Π-wf′ : Γ ⊢ Π S T ∶ T′ →
            ----------------
            Γ ⊢ S
inv-Π-wf′ (Π-wf ⊢S ⊢T) = _ , ⊢S
inv-Π-wf′ (cumu ⊢Π)    = inv-Π-wf′ ⊢Π
inv-Π-wf′ (conv ⊢Π _)  = inv-Π-wf′ ⊢Π

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ----------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here = _ , conv (t[σ] ⊢T (S-↑ ⊢TΓ)) (_ , Se-[] _ (S-↑ ⊢TΓ))
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T                = _ , conv (t[σ] ⊢T (S-↑ ⊢TΓ)) (_ , Se-[] _ (S-↑ ⊢TΓ))

-- vlookup-inv : ∀ {x} →
--               Γ ⊢ v x ∶ T →
--               ∃ λ T′ → (x ∶ T′ ∈! Γ) × Star (λ S U → Γ ⊢ S ≈ U) T′ T
-- vlookup-inv (vlookup _ T∈Γ) = _ , T∈Γ , ε
-- vlookup-inv (cumu ⊢t) = {!vlookup-inv ⊢t!}
-- vlookup-inv (conv ⊢x S≲T)
--   with vlookup-inv ⊢x
-- ...  | T″ , T″∈Γ , T″≲T = T″ , T″∈Γ , T″≲T ◅◅ S≲T ◅ ε

N-≈ : ∀ i →
      ⊢ Γ →
      Γ ⊢ N ≈ N ∶ Se i
N-≈ i ⊢Γ = begin
  N       ≈˘⟨ N-[] i (S-I ⊢Γ) ⟩
  N [ I ] ≈⟨ N-[] i (S-I ⊢Γ) ⟩
  N       ∎
  where open TR

Se-≈ : ∀ {i} →
       ⊢ Γ →
       Γ ⊢ Se i ≈ Se i ∶ Se (1 + i)
Se-≈ {_} {i} ⊢Γ = begin
  Se i       ≈˘⟨ Se-[] i (S-I ⊢Γ) ⟩
  Se i [ I ] ≈⟨ Se-[] i (S-I ⊢Γ) ⟩
  Se i       ∎
  where open TR

mutual
  ≈-refl : Γ ⊢ t ∶ T →
           --------------
           Γ ⊢ t ≈ t ∶ T
  ≈-refl (N-wf i ⊢Γ)       = N-≈ i ⊢Γ
  ≈-refl (Se-wf i ⊢Γ)      = Se-≈ ⊢Γ
  ≈-refl (Π-wf ⊢S ⊢T)      = Π-cong (≈-refl ⊢S) (≈-refl ⊢T)
  ≈-refl (vlookup T∈Γ ⊢Γ)  = v-≈ T∈Γ ⊢Γ
  ≈-refl (ze-I ⊢Γ)         = ze-≈ ⊢Γ
  ≈-refl (su-I ⊢t)         = su-cong (≈-refl ⊢t)
  ≈-refl (N-E ⊢T ⊢s ⊢r ⊢t) = rec-cong (≈-refl ⊢T) (≈-refl ⊢s) (≈-refl ⊢r) (≈-refl ⊢t)
  ≈-refl (Λ-I ⊢t)          = Λ-cong (≈-refl ⊢t)
  ≈-refl (Λ-E ⊢r ⊢s)       = $-cong (≈-refl ⊢r) (≈-refl ⊢s)
  ≈-refl (t[σ] ⊢t ⊢σ)      = []-cong (S-≈-refl ⊢σ) (≈-refl ⊢t)
  ≈-refl (cumu ⊢t)         = ≈-cumu (≈-refl ⊢t)
  ≈-refl (conv ⊢t S≲T)     = ≈-conv (≈-refl ⊢t) S≲T

  S-≈-refl : Γ ⊢s σ ∶ Δ →
             --------------
             Γ ⊢s σ ≈ σ ∶ Δ
  S-≈-refl (S-↑ ⊢SΔ)      = ↑-≈ ⊢SΔ
  S-≈-refl (S-I ⊢Γ)       = I-≈ ⊢Γ
  S-≈-refl (S-∘ ⊢τ ⊢σ)    = ∘-cong (S-≈-refl ⊢τ) (S-≈-refl ⊢σ)
  S-≈-refl (S-, ⊢σ ⊢S ⊢s) = ,-cong ⊢S (S-≈-refl ⊢σ) (≈-refl ⊢s)

infix 4 _⊢s*_

_⊢s*_ : Ctx → Ctx → Set
Γ ⊢s* Δ = Star (λ Γ Δ → ∃ λ σ → Γ ⊢s σ ∶ Δ × ⊢ Δ) Γ Δ

iter-[] : Exp →
          Γ ⊢s* Δ →
          Exp
iter-[] t ε                    = t
iter-[] t ((τ , ⊢τ , _) ◅ ⊢σ*) = iter-[] t ⊢σ* [ τ ]

iter-[]-Se : ∀ {i} →
             ⊢ Γ →
             (⊢σ* : Γ ⊢s* Δ) →
             Γ ⊢ iter-[] (Se i) ⊢σ* ≈ Se i ∶ Se (1 + i)
iter-[]-Se ⊢Γ ε                      = Se-≈ ⊢Γ
iter-[]-Se ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) = begin
  iter-[] (Se _) ⊢σ* [ τ ] ≈⟨ ≈-conv ([]-cong (S-≈-refl ⊢τ) (iter-[]-Se ⊢Γ′ ⊢σ*)) (_ , Se-[] _ ⊢τ) ⟩
  Se _ [ τ ]               ≈⟨ Se-[] _ ⊢τ ⟩
  Se _                     ∎
  where open TR

lift-⊢-Se-step : ∀ {i} j →
                 Γ ⊢ T ∶ Se i →
                 Γ ⊢ T ∶ Se (j + i)
lift-⊢-Se-step zero ⊢T = ⊢T
lift-⊢-Se-step (suc j) ⊢T = cumu (lift-⊢-Se-step j ⊢T)

lift-⊢-Se : ∀ {i j} →
            Γ ⊢ T ∶ Se i →
            i ≤ j →
            Γ ⊢ T ∶ Se j
lift-⊢-Se ⊢T i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢-Se-step _ ⊢T

lift-⊢≈-Se-step : ∀ {i} j →
                  Γ ⊢ T ≈ T′ ∶ Se i →
                  Γ ⊢ T ≈ T′ ∶ Se (j + i)
lift-⊢≈-Se-step zero T≈T′    = T≈T′
lift-⊢≈-Se-step (suc j) T≈T′ = ≈-cumu (lift-⊢≈-Se-step j T≈T′)

lift-⊢≈-Se : ∀ {i j} →
             Γ ⊢ T ≈ T′ ∶ Se i →
             i ≤ j →
             Γ ⊢ T ≈ T′ ∶ Se j
lift-⊢≈-Se T≈T′ i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢≈-Se-step _ T≈T′

subst-N-stable : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Γ ⊢s σ′ ∶ Δ′ →
                 Γ ⊢ N [ σ ] ≈ N [ σ′ ] ∶ Se i
subst-N-stable ⊢σ ⊢σ′ = ≈-trans (N-[] _ ⊢σ) (≈-sym (N-[] _ ⊢σ′))

-- -- ≈-Se-inter-[] : ∀ {i} →
-- --                 ⊢ Γ →
-- --                 (⊢σ* : Γ ⊢s* Δ) →
-- --                 Γ ⊢ S ≈ T ∶ iter-[] (Se i) ⊢σ* →
-- --                 Γ ⊢ S ≈ T ∶ Se i
-- -- ≈-Se-inter-[] _ ε S≈T                       = S≈T
-- -- ≈-Se-inter-[] ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) S≈T = ≈-conv S≈T (≈-≲ (≈-trans (≈-conv ([]-cong ⊢τ≈ (iter-[]-Se ⊢Γ′ ⊢σ* ℕₚ.≤-refl))
-- --                                                                                (≈-≲ (Se-[] ⊢τ ℕₚ.≤-refl)))
-- --                                                               (Se-[] ⊢τ ℕₚ.≤-refl)))
-- --   where ⊢τ≈ = S-≈-refl ⊢τ

-- -- inter-[]-≈ : ∀ {i} →
-- --              ⊢ Γ →
-- --              (⊢σ* : Γ ⊢s* Δ) →
-- --              Δ ⊢ S ≈ T ∶ Se i →
-- --              Γ ⊢ iter-[] S ⊢σ* ≈ iter-[] T ⊢σ* ∶ iter-[] (Se i) ⊢σ*
-- -- inter-[]-≈ ⊢Γ ε S≈T                      = S≈T
-- -- inter-[]-≈ ⊢Γ ((τ , ⊢τ , ⊢Γ′) ◅ ⊢σ*) S≈T = []-cong (S-≈-refl ⊢τ) (inter-[]-≈ ⊢Γ′ ⊢σ* S≈T)

-- -- ≈-conv-subst* : ⊢ Γ →
-- --                 (⊢σ* : Γ ⊢s* Δ) →
-- --                 Γ ⊢ t ≈ t′ ∶ iter-[] S ⊢σ* →
-- --                 Δ ⊢ S ≲ T →
-- --                 Γ ⊢ t ≈ t′ ∶ iter-[] T ⊢σ*
-- -- ≈-conv-subst* ⊢Γ ⊢σ* t≈t′ (Se-≲ ⊢Δ i≤j) = ≈-conv (≈-conv (≈-conv t≈t′
-- --                                                                  (≈-≲ (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl)))
-- --                                                          (Se-≲ ⊢Γ i≤j))
-- --                                                  (≈-≲ (≈-sym (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl)))
-- -- ≈-conv-subst* ⊢Γ ⊢σ* t≈t′ (≈-≲ S≈T)     = ≈-conv t≈t′ (≈-≲ (≈-conv (inter-[]-≈ ⊢Γ ⊢σ* S≈T) (≈-≲ (iter-[]-Se ⊢Γ ⊢σ* ℕₚ.≤-refl))))

-- -- vlookup-cond : ∀ {x} Δ →
-- --                  ⊢ T′ ∷ Δ ++ S ∷ Γ →
-- --                  ⊢ T′ ∷ Δ ++ S′ ∷ Γ →
-- --                  x ∶ T ∈! Δ ++ S ∷ Γ →
-- --                  x ∶ T ∈! Δ ++ S′ ∷ Γ ⊎ Σ (Δ ++ S′ ∷ Γ ⊢s* Γ) λ ⊢σ* → (x ∶ iter-[] S′ ⊢σ* ∈! Δ ++ S′ ∷ Γ) × T ≡ iter-[] S ⊢σ*
-- -- vlookup-cond [] (⊢∷ (⊢∷ ⊢Γ _) _) (⊢∷ (⊢∷ _ ⊢S′) _) here = inj₂ ((↑ , S-↑ (⊢∷ ⊢Γ ⊢S′) , ⊢Γ) ◅ ε , here , refl)
-- -- vlookup-cond [] _ _ (there T∈Γ′)                        = inj₁ (there T∈Γ′)
-- -- vlookup-cond (U ∷ Δ) (⊢∷ ⊢Γ′ _) _ here                  = inj₁ here
-- -- vlookup-cond (U ∷ Δ) (⊢∷ (⊢∷ ⊢ΔSΓ ⊢U) _) (⊢∷ (⊢∷ ⊢ΔS′Γ ⊢U′) _) (there T∈Γ′)
-- --     with vlookup-cond Δ (⊢∷ ⊢ΔSΓ ⊢U) (⊢∷ ⊢ΔS′Γ ⊢U′) T∈Γ′
-- -- ... | inj₁ T∈Γ″                                         = inj₁ (there T∈Γ″)
-- -- ... | inj₂ (⊢σ* , S″∈Γ″ , refl)                         = inj₂ ((↑ , S-↑ (⊢∷ ⊢ΔS′Γ ⊢U′) , ⊢ΔS′Γ) ◅ ⊢σ* , there S″∈Γ″ , refl)
