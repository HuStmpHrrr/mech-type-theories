{-# OPTIONS --without-K --safe #-}

module PTT.StaticsProps where

open import Lib
open import PTT.Statics

open import Data.Sum
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
  ≈-refl (Λ-I ⊢S ⊢t)          = Λ-cong (≈-refl ⊢t)
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

v0-lookup : ⊢ Γ →
            Γ ⊢ S →
            ---------------------
            S ∷ Γ ⊢ v 0 ∶ S [ ↑ ]
v0-lookup ⊢Γ (_ , ⊢S) = vlookup (⊢∷ ⊢Γ ⊢S) here

vsuc-lookup : ∀ {x} →
              Γ ⊢ v x ∶ T →
              ⊢ S ∷ Γ →
              ---------------------------
              S ∷ Γ ⊢ v (suc x) ∶ T [ ↑ ]
vsuc-lookup ⊢x ⊢SΓ
  with vlookup-inv ⊢x
...  | _ , T∈Γ , T≲T′ = conv-* ⊢SΓ (vlookup ⊢SΓ (there T∈Γ)) (S-↑ ⊢SΓ) T≲T′

≲-refl : ∀ {i} →
         Γ ⊢ T ∶ Se i →
         ---------------
         Γ ⊢ T ≲ T
≲-refl T = ≈-≲ (≈-refl T)

env≲-refl : ⊢ Γ →
            ---------
            ⊢ Γ ≲ Γ
env≲-refl ⊢[]        = ≈[]
env≲-refl (⊢∷ ⊢Γ ⊢T) = ≈∷ (env≲-refl ⊢Γ) (≲-refl ⊢T)

mutual
  env-env-subst : ∀ {i} Δ →
                  Γ ⊢ S′ ≲ S →
                  ⊢ Δ ++ S ∷ Γ →
                  Γ ⊢ S′ ∶ Se i →
                  ---------------------
                  ⊢ Δ ++ S′ ∷ Γ
  env-env-subst []      S′≲S (⊢∷ ⊢Γ′ ⊢S) ⊢S′ = ⊢∷ ⊢Γ′ ⊢S′
  env-env-subst (T ∷ Δ) S′≲S (⊢∷ ⊢Γ′ ⊢T) ⊢S′ = ⊢∷ (env-env-subst Δ S′≲S ⊢Γ′ ⊢S′) (ty-env-subst S′≲S ⊢S′ ⊢T refl)

  vlookup-env-subst : ∀ {x i} Δ →
                      ⊢ Γ′ →
                      Γ ⊢ S′ ≲ S →
                      Γ ⊢ S′ ∶ Se i →
                      x ∶ T ∈! Γ′ →
                      Γ′ ≡ Δ ++ S ∷ Γ →
                      Δ ++ S′ ∷ Γ ⊢ v x ∶ T
  vlookup-env-subst [] (⊢∷ ⊢Γ′ ⊢S) S′≲S ⊢S′ here refl              = conv-* ⊢S′Γ (vlookup ⊢S′Γ here) (S-↑ ⊢S′Γ) (S′≲S ◅ ε)
    where ⊢S′Γ = ⊢∷ ⊢Γ′ ⊢S′
  vlookup-env-subst [] (⊢∷ ⊢Γ′ ⊢S) S′≲S ⊢S′ (there T∈Γ′) refl      = vlookup ⊢S′Γ (there T∈Γ′)
    where ⊢S′Γ = ⊢∷ ⊢Γ′ ⊢S′
  vlookup-env-subst (U ∷ Δ) (⊢∷ ⊢Γ′ ⊢U) S′≲S ⊢S′ here refl         = vlookup (⊢∷ (env-env-subst Δ S′≲S ⊢Γ′ ⊢S′) (ty-env-subst S′≲S ⊢S′ ⊢U refl)) here
  vlookup-env-subst (U ∷ Δ) (⊢∷ ⊢Γ′ ⊢U) S′≲S ⊢S′ (there T∈Γ′) refl = vsuc-lookup (vlookup-env-subst Δ ⊢Γ′ S′≲S ⊢S′ T∈Γ′ refl)
                                                                                 (⊢∷ (env-env-subst Δ S′≲S ⊢Γ′ ⊢S′) (ty-env-subst S′≲S ⊢S′ ⊢U refl))

  ty-env-subst : ∀ {i} →
                 Γ ⊢ S′ ≲ S →
                 Γ ⊢ S′ ∶ Se i →
                 Γ′ ⊢ t ∶ T →
                 Γ′ ≡ Δ ++ S ∷ Γ →
                 ---------------------
                 Δ ++ S′ ∷ Γ ⊢ t ∶ T
  ty-env-subst S′≲S ⊢S′ (N-wf i ⊢Γ′) refl                = N-wf i (env-env-subst _ S′≲S ⊢Γ′ ⊢S′)
  ty-env-subst S′≲S ⊢S′ (Se-wf ⊢Γ′ i<j) refl             = Se-wf (env-env-subst _ S′≲S ⊢Γ′ ⊢S′) i<j
  ty-env-subst S′≲S ⊢S′ (Π-wf {_} {S″} ⊢S ⊢T i≤k j≤k) eq = Π-wf (ty-env-subst S′≲S ⊢S′ ⊢S eq) (ty-env-subst {Δ = S″ ∷ _} S′≲S ⊢S′ ⊢T (cong (_ ∷_) eq)) i≤k j≤k
  ty-env-subst S′≲S ⊢S′ (vlookup ⊢Γ′ T∈Γ′) eq            = vlookup-env-subst _ ⊢Γ′ S′≲S ⊢S′ T∈Γ′ eq
  ty-env-subst S′≲S ⊢S′ (ze-I ⊢Γ′) refl                  = ze-I (env-env-subst _ S′≲S ⊢Γ′ ⊢S′)
  ty-env-subst S′≲S ⊢S′ (su-I ⊢t) eq                     = su-I (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-env-subst S′≲S ⊢S′ (N-E ⊢T ⊢s ⊢r ⊢t) eq             = N-E (ty-env-subst S′≲S ⊢S′ ⊢T eq) (ty-env-subst S′≲S ⊢S′ ⊢s eq) (ty-env-subst S′≲S ⊢S′ ⊢r eq) (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-env-subst S′≲S ⊢S′ (Λ-I {_} {S″} ⊢S″ ⊢t) eq         = Λ-I (ty-env-subst S′≲S ⊢S′ ⊢S″ eq) (ty-env-subst {Δ = S″ ∷ _} S′≲S ⊢S′ ⊢t (cong (_ ∷_) eq))
  ty-env-subst S′≲S ⊢S′ (Λ-E ⊢r ⊢s) eq                   = Λ-E (ty-env-subst S′≲S ⊢S′ ⊢r eq) (ty-env-subst S′≲S ⊢S′ ⊢s eq)
  ty-env-subst S′≲S ⊢S′ (t[σ] ⊢t ⊢σ) eq                  = t[σ] ⊢t (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  ty-env-subst S′≲S ⊢S′ (conv ⊢t T≲T′) refl              = conv (ty-env-subst S′≲S ⊢S′ ⊢t refl) (ty≲-env-subst S′≲S ⊢S′ T≲T′ refl)

  subst-env-subst : ∀ {i} Δ →
                    Γ ⊢ S′ ≲ S →
                    Γ ⊢ S′ ∶ Se i →
                    Γ′ ⊢s σ ∶ Δ′ →
                    Γ′ ≡ Δ ++ S ∷ Γ →
                    ---------------------
                    Δ ++ S′ ∷ Γ ⊢s σ ∶ Δ′
  subst-env-subst []      S′≲S ⊢S′ (S-↑ (⊢∷ ⊢SΔ′ _))  refl = S-↑ (⊢∷ ⊢SΔ′ ⊢S′)
  subst-env-subst (U ∷ Δ) S′≲S ⊢S′ (S-↑ (⊢∷ ⊢SΔ′ ⊢U)) refl = S-conv (env≲-env-subst Δ ⊢SΔ′ S′≲S ⊢S′ refl)
                                                                    (S-↑ (⊢∷ (env-env-subst Δ S′≲S ⊢SΔ′ ⊢S′)
                                                                             (ty-env-subst S′≲S ⊢S′ ⊢U refl)))
  subst-env-subst Δ S′≲S ⊢S′ (S-I ⊢Δ′)       refl          = S-conv (env≲-env-subst Δ ⊢Δ′ S′≲S ⊢S′ refl)
                                                                    (S-I (env-env-subst Δ S′≲S ⊢Δ′ ⊢S′))
  subst-env-subst Δ S′≲S ⊢S′ (S-∘ ⊢τ ⊢σ)     eq            = S-∘ (subst-env-subst Δ S′≲S ⊢S′ ⊢τ eq) ⊢σ
  subst-env-subst Δ S′≲S ⊢S′ (S-, ⊢σ ⊢S ⊢s)  eq            = S-, (subst-env-subst Δ S′≲S ⊢S′ ⊢σ eq) ⊢S (ty-env-subst S′≲S ⊢S′ ⊢s eq)
  subst-env-subst Δ S′≲S ⊢S′ (S-conv ≲Δ′ ⊢σ) eq            = S-conv ≲Δ′ (subst-env-subst Δ S′≲S ⊢S′ ⊢σ eq)

  ty≲-env-subst : ∀ {i} →
                  Γ ⊢ S′ ≲ S →
                  Γ ⊢ S′ ∶ Se i →
                  Γ′ ⊢ T ≲ T′ →
                  Γ′ ≡ Δ ++ S ∷ Γ →
                  ---------------------
                  Δ ++ S′ ∷ Γ ⊢ T ≲ T′
  ty≲-env-subst S′≲S ⊢S′ (Se-≲ ⊢Γ′ i≤j) refl = Se-≲ (env-env-subst _ S′≲S ⊢Γ′ ⊢S′) i≤j
  ty≲-env-subst S′≲S ⊢S′ (≈-≲ T≈T′) eq       = ≈-≲ (ty-≈-env-subst S′≲S ⊢S′ T≈T′ eq)

  env≲-env-subst : ∀ {i} Δ →
                   ⊢ Γ′ →
                   Γ ⊢ S′ ≲ S →
                   Γ ⊢ S′ ∶ Se i →
                   Γ′ ≡ Δ ++ S ∷ Γ →
                   ---------------------------
                   ⊢ Δ ++ S′ ∷ Γ ≲ Δ ++ S ∷ Γ
  env≲-env-subst [] (⊢∷ ⊢Γ _) S′≲S ⊢S′ refl        = ≈∷ (env≲-refl ⊢Γ) S′≲S
  env≲-env-subst (T ∷ Δ) (⊢∷ ⊢Γ′ ⊢T) S′≲S ⊢S′ refl = ≈∷ (env≲-env-subst Δ ⊢Γ′ S′≲S ⊢S′ refl) (≲-refl ⊢T)

  ty-≈-env-subst : ∀ {i} →
                   Γ ⊢ S′ ≲ S →
                   Γ ⊢ S′ ∶ Se i →
                   Γ′ ⊢ t ≈ t′ ∶ T →
                   Γ′ ≡ Δ ++ S ∷ Γ →
                   -------------------------
                   Δ ++ S′ ∷ Γ ⊢ t ≈ t′ ∶ T
  ty-≈-env-subst S′≲S ⊢S′ (N-[] i ⊢σ) eq                           = N-[] i (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  ty-≈-env-subst S′≲S ⊢S′ (Se-[] ⊢σ i<j) eq                        = Se-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) i<j
  ty-≈-env-subst S′≲S ⊢S′ (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k) eq               = Π-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) ⊢S ⊢T i≤k j≤k
  ty-≈-env-subst S′≲S ⊢S′ (Π-cong {_} {U} ⊢U S≈S′ T≈T′ i≤k j≤k) eq = Π-cong (ty-env-subst S′≲S ⊢S′ ⊢U eq)
                                                                            (ty-≈-env-subst S′≲S ⊢S′ S≈S′ eq)
                                                                            (ty-≈-env-subst {Δ = U ∷ _} S′≲S ⊢S′ T≈T′ (cong _ eq))
                                                                            i≤k j≤k
  ty-≈-env-subst S′≲S ⊢S′ (v-≈ ⊢Γ′ T∈Γ′) eq                        = ≈-refl (vlookup-env-subst _ ⊢Γ′ S′≲S ⊢S′ T∈Γ′ eq)
  ty-≈-env-subst S′≲S ⊢S′ (ze-≈ ⊢Γ′) refl                          = ze-≈ (env-env-subst _ S′≲S ⊢Γ′ ⊢S′)
  ty-≈-env-subst S′≲S ⊢S′ (su-cong t≈t′) eq                        = su-cong (ty-≈-env-subst S′≲S ⊢S′ t≈t′ eq)
  ty-≈-env-subst S′≲S ⊢S′ (rec-cong T≈T′ s≈s′ r≈r′ t≈t′) eq        = rec-cong (ty-≈-env-subst S′≲S ⊢S′ T≈T′ eq)
                                                                              (ty-≈-env-subst S′≲S ⊢S′ s≈s′ eq)
                                                                              (ty-≈-env-subst S′≲S ⊢S′ r≈r′ eq)
                                                                              (ty-≈-env-subst S′≲S ⊢S′ t≈t′ eq)
  ty-≈-env-subst S′≲S ⊢S′ (Λ-cong {U} t≈t′) eq                     = Λ-cong (ty-≈-env-subst {Δ = U ∷ _} S′≲S ⊢S′ t≈t′ (cong _ eq))
  ty-≈-env-subst S′≲S ⊢S′ ($-cong r≈r′ s≈s′) eq                    = $-cong (ty-≈-env-subst S′≲S ⊢S′ r≈r′ eq)
                                                                            (ty-≈-env-subst S′≲S ⊢S′ s≈s′ eq)
  ty-≈-env-subst S′≲S ⊢S′ ([]-cong σ≈σ′ t≈t′) eq                   = []-cong (subst-≈-env-subst _ S′≲S ⊢S′ σ≈σ′ eq ) t≈t′
  ty-≈-env-subst S′≲S ⊢S′ (ze-[] ⊢σ) eq                            = ze-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  ty-≈-env-subst S′≲S ⊢S′ (su-[] ⊢σ ⊢t) eq                         = su-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) ⊢t
  ty-≈-env-subst S′≲S ⊢S′ (Λ-[] ⊢σ ⊢t) eq                          = Λ-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) ⊢t
  ty-≈-env-subst S′≲S ⊢S′ ($-[] ⊢σ ⊢r ⊢s) eq                       = $-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) ⊢r ⊢s
  ty-≈-env-subst S′≲S ⊢S′ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t) eq               = rec-[] (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq) ⊢T ⊢s ⊢r ⊢t
  ty-≈-env-subst S′≲S ⊢S′ (rec-β-ze ⊢T ⊢t′ ⊢r) eq                  = rec-β-ze (ty-env-subst S′≲S ⊢S′ ⊢T eq)
                                                                              (ty-env-subst S′≲S ⊢S′ ⊢t′ eq)
                                                                              (ty-env-subst S′≲S ⊢S′ ⊢r eq)
  ty-≈-env-subst S′≲S ⊢S′ (rec-β-su ⊢T ⊢s ⊢r ⊢t) eq                = rec-β-su (ty-env-subst S′≲S ⊢S′ ⊢T eq)
                                                                              (ty-env-subst S′≲S ⊢S′ ⊢s eq)
                                                                              (ty-env-subst S′≲S ⊢S′ ⊢r eq)
                                                                              (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-≈-env-subst S′≲S ⊢S′ (Λ-β {S} ⊢t ⊢s) eq                       = Λ-β (ty-env-subst {Δ = S ∷ _} S′≲S ⊢S′ ⊢t (cong (_ ∷_) eq))
                                                                         (ty-env-subst S′≲S ⊢S′ ⊢s eq)
  ty-≈-env-subst S′≲S ⊢S′ (Λ-η ⊢t) eq                              = Λ-η (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-≈-env-subst S′≲S ⊢S′ ([I] ⊢t) eq                              = [I] (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-≈-env-subst {Δ = []} S′≲S ⊢S′ (↑-lookup (⊢∷ ⊢Γ _) T∈Γ) refl   = ↑-lookup (⊢∷ ⊢Γ ⊢S′) T∈Γ
  ty-≈-env-subst {Δ = U ∷ Δ} S′≲S ⊢S′ (↑-lookup ⊢UΔSΓ@(⊢∷ ⊢ΔSΓ ⊢U) T∈Γ) refl
    with vlookup-cond Δ ⊢UΔSΓ (⊢∷ (env-env-subst Δ S′≲S ⊢ΔSΓ ⊢S′) (ty-env-subst S′≲S ⊢S′ ⊢U refl)) T∈Γ
  ...  | inj₁ T∈Γ′                                                 = ↑-lookup (⊢∷ (env-env-subst Δ S′≲S ⊢ΔSΓ ⊢S′)
                                                                                  (ty-env-subst S′≲S ⊢S′ ⊢U refl)) T∈Γ′
  ...  | inj₂ (⊢σ* , S′∈Γ′ , refl)                                 = ≈-conv-subst* ⊢UΔS′Γ
                                                                                   ((↑ , S-↑ ⊢UΔS′Γ , ⊢ΔS′Γ) ◅ ⊢σ*)
                                                                                   (↑-lookup ⊢UΔS′Γ S′∈Γ′)
                                                                                   S′≲S
    where ⊢ΔS′Γ  = env-env-subst Δ S′≲S ⊢ΔSΓ ⊢S′
          ⊢UΔS′Γ = ⊢∷ ⊢ΔS′Γ (ty-env-subst S′≲S ⊢S′ ⊢U refl)
  ty-≈-env-subst S′≲S ⊢S′ ([∘] ⊢τ ⊢σ ⊢t) eq                        = [∘] (subst-env-subst _ S′≲S ⊢S′ ⊢τ eq)
                                                                         ⊢σ ⊢t
  ty-≈-env-subst S′≲S ⊢S′ ([,]-v-ze ⊢σ ⊢S ⊢t) eq                   = [,]-v-ze (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
                                                                              ⊢S (ty-env-subst S′≲S ⊢S′ ⊢t eq)
  ty-≈-env-subst S′≲S ⊢S′ ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ′) eq              = [,]-v-su (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
                                                                              ⊢S (ty-env-subst S′≲S ⊢S′ ⊢s eq) T∈Δ′
  ty-≈-env-subst S′≲S ⊢S′ (≈-conv t≈t′ U≲T) eq                     = ≈-conv (ty-≈-env-subst S′≲S ⊢S′ t≈t′ eq)
                                                                            (ty≲-env-subst S′≲S ⊢S′ U≲T eq)
  ty-≈-env-subst S′≲S ⊢S′ (≈-sym t≈t′) eq                          = ≈-sym (ty-≈-env-subst S′≲S ⊢S′ t≈t′ eq)
  ty-≈-env-subst S′≲S ⊢S′ (≈-trans t≈t′ t′≈t″) eq                  = ≈-trans (ty-≈-env-subst S′≲S ⊢S′ t≈t′ eq)
                                                                             (ty-≈-env-subst S′≲S ⊢S′ t′≈t″ eq)
  subst-≈-env-subst : ∀ {i} Δ →
                      Γ ⊢ S′ ≲ S →
                      Γ ⊢ S′ ∶ Se i →
                      Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                      Γ′ ≡ Δ ++ S ∷ Γ →
                      -------------------------
                      Δ ++ S′ ∷ Γ ⊢s σ ≈ σ′ ∶ Γ″
  subst-≈-env-subst [] S′≲S ⊢S′ (↑-≈ (⊢∷ ⊢UΓ″ _)) refl      = ↑-≈ (⊢∷ ⊢UΓ″ ⊢S′)
  subst-≈-env-subst (U ∷ Δ) S′≲S ⊢S′ (↑-≈ (⊢∷ ⊢Γ″ ⊢U)) refl = S-≈-conv (env≲-env-subst Δ ⊢Γ″ S′≲S ⊢S′ refl)
                                                                       (↑-≈ (⊢∷ (env-env-subst Δ S′≲S ⊢Γ″ ⊢S′)
                                                                                (ty-env-subst S′≲S ⊢S′ ⊢U refl)))
  subst-≈-env-subst Δ S′≲S ⊢S′ (I-≈ ⊢Γ″) refl               = S-≈-conv (env≲-env-subst Δ ⊢Γ″ S′≲S ⊢S′ refl)
                                                                       (I-≈ (env-env-subst Δ S′≲S ⊢Γ″ ⊢S′))
  subst-≈-env-subst Δ S′≲S ⊢S′ (∘-cong τ≈τ′ σ≈σ′) eq        = ∘-cong (subst-≈-env-subst Δ S′≲S ⊢S′ τ≈τ′ eq) σ≈σ′
  subst-≈-env-subst Δ S′≲S ⊢S′ (,-cong ⊢S σ≈σ′ s≈s′) eq     = ,-cong ⊢S (subst-≈-env-subst Δ S′≲S ⊢S′ σ≈σ′ eq) (ty-≈-env-subst S′≲S ⊢S′ s≈s′ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (↑-∘-, ⊢σ ⊢U ⊢s) eq          = ↑-∘-, (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
                                                                    ⊢U (ty-env-subst S′≲S ⊢S′ ⊢s eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (I-∘ ⊢σ) eq                  = I-∘ (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (∘-I ⊢σ) eq                  = ∘-I (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (∘-assoc ⊢σ ⊢σ′ ⊢σ″) eq      = ∘-assoc ⊢σ ⊢σ′ (subst-env-subst _ S′≲S ⊢S′ ⊢σ″ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (,-ext ⊢σ) eq                = ,-ext (subst-env-subst _ S′≲S ⊢S′ ⊢σ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (S-≈-conv Δ′≲Γ″ σ≈σ′) eq     = S-≈-conv Δ′≲Γ″ (subst-≈-env-subst Δ S′≲S ⊢S′ σ≈σ′ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (S-≈-sym σ≈σ′) eq            = S-≈-sym (subst-≈-env-subst Δ S′≲S ⊢S′ σ≈σ′ eq)
  subst-≈-env-subst Δ S′≲S ⊢S′ (S-≈-trans t≈t′ σ≈σ′) eq     = S-≈-trans (subst-≈-env-subst Δ S′≲S ⊢S′ t≈t′ eq)
                                                                        (subst-≈-env-subst Δ S′≲S ⊢S′ σ≈σ′ eq)


-- mutual

--   vlookup-env-subst : ∀ {x} →
--                       x ∶ T ∈! Δ →
--                       ⊢ Γ ≲ Δ →
--                       ⊢ Γ →
--                       Γ ⊢ v x ∶ T
--   vlookup-env-subst here (≈∷ Γ≲Δ S≲T) ⊢SΓ@(⊢∷ ⊢Γ ⊢S)  = conv-* ⊢SΓ (vlookup ⊢SΓ here) (S-↑ ⊢SΓ) (ty≲-env-subst S≲T Γ≲Δ ⊢Γ ◅ ε)
--   vlookup-env-subst (there T∈Δ) (≈∷ Γ≲Δ _) (⊢∷ ⊢Γ ⊢S) = vsuc-lookup (vlookup-env-subst T∈Δ Γ≲Δ ⊢Γ) (⊢∷ ⊢Γ ⊢S)

--   ty-env-subst : Δ ⊢ t ∶ T →
--                  ⊢ Γ ≲ Δ →
--                  ⊢ Γ →
--                  -------------
--                  Γ ⊢ t ∶ T
--   ty-env-subst (N-wf i _) Γ≲Δ ⊢Γ           = N-wf i ⊢Γ
--   ty-env-subst (Se-wf _ i<j) Γ≲Δ ⊢Γ        = Se-wf ⊢Γ i<j
--   ty-env-subst (Π-wf ⊢S ⊢T i≤k j≤k) Γ≲Δ ⊢Γ = {!!} -- Π-wf ⊢S′ (ty-env-subst ⊢T (≈∷ Γ≲Δ (≲-refl ⊢S)) (⊢∷ ⊢Γ ⊢S′)) i≤k j≤k
--     where ⊢S′                              = ty-env-subst ⊢S Γ≲Δ ⊢Γ
--   ty-env-subst (vlookup ⊢Δ here) (≈∷ Γ≲Δ S≲T) (⊢∷ ⊢Γ ⊢S) = conv-* ⊢SΓ (vlookup ⊢SΓ here) (S-↑ ⊢SΓ) (ty≲-env-subst S≲T Γ≲Δ ⊢Γ ◅ ε)
--     where ⊢SΓ = ⊢∷ ⊢Γ ⊢S
--   ty-env-subst (vlookup ⊢Δ (there T∈Γ′)) (≈∷ Γ≲Δ _) (⊢∷ ⊢Γ _) = {!!}
--   -- vlookup-env-subst T∈Γ′ Γ≲Δ ⊢Γ
--   ty-env-subst (ze-I _) Γ≲Δ ⊢Γ             = ze-I ⊢Γ
--   ty-env-subst (su-I ⊢t) Γ≲Δ ⊢Γ            = su-I (ty-env-subst ⊢t Γ≲Δ ⊢Γ)
--   ty-env-subst (N-E ⊢T ⊢s ⊢r ⊢t) Γ≲Δ ⊢Γ    = N-E (ty-env-subst ⊢T Γ≲Δ ⊢Γ)
--                                                  (ty-env-subst ⊢s Γ≲Δ ⊢Γ)
--                                                  (ty-env-subst ⊢r Γ≲Δ ⊢Γ)
--                                                  (ty-env-subst ⊢t Γ≲Δ ⊢Γ)
--   ty-env-subst (Λ-I ⊢S ⊢t) Γ≲Δ ⊢Γ          = Λ-I ⊢S′ (ty-env-subst ⊢t (≈∷ Γ≲Δ (≲-refl ⊢S)) (⊢∷ ⊢Γ ⊢S′))
--     where ⊢S′                              = ty-env-subst ⊢S Γ≲Δ ⊢Γ
--   ty-env-subst (Λ-E ⊢r ⊢s) Γ≲Δ ⊢Γ          = Λ-E (ty-env-subst ⊢r Γ≲Δ ⊢Γ) (ty-env-subst ⊢s Γ≲Δ ⊢Γ)
--   ty-env-subst (t[σ] ⊢t ⊢σ) Γ≲Δ ⊢Γ         = t[σ] ⊢t (subst-env-subst Γ≲Δ ⊢Γ ⊢σ)
--   ty-env-subst (conv ⊢t S≲T) Γ≲Δ ⊢Γ        = conv (ty-env-subst ⊢t Γ≲Δ ⊢Γ) (ty≲-env-subst S≲T Γ≲Δ ⊢Γ)

--   subst-env-subst : ⊢ Γ ≲ Δ →
--                     ⊢ Γ →
--                     Δ ⊢s σ ∶ Δ′ →
--                     -------------
--                     Γ ⊢s σ ∶ Δ′
--   subst-env-subst (≈∷ Γ≲Δ x) ⊢Γ (S-↑ ⊢SΔ′) = S-conv Γ≲Δ (S-↑ ⊢Γ)
--   subst-env-subst Γ≲Δ ⊢Γ (S-I ⊢Δ)          = S-conv Γ≲Δ (S-I ⊢Γ)
--   subst-env-subst Γ≲Δ ⊢Γ (S-∘ ⊢τ ⊢σ)       = S-∘ (subst-env-subst Γ≲Δ ⊢Γ ⊢τ) ⊢σ
--   subst-env-subst Γ≲Δ ⊢Γ (S-, ⊢σ ⊢S ⊢s)    = S-, (subst-env-subst Γ≲Δ ⊢Γ ⊢σ) ⊢S (ty-env-subst ⊢s Γ≲Δ ⊢Γ)
--   subst-env-subst Γ≲Δ ⊢Γ (S-conv Δ″≲Δ′ ⊢σ) = S-conv Δ″≲Δ′ (subst-env-subst Γ≲Δ ⊢Γ ⊢σ)

--   ty≲-env-subst : Δ ⊢ S ≲ T →
--                   ⊢ Γ ≲ Δ →
--                   ⊢ Γ →
--                   ------------
--                   Γ ⊢ S ≲ T
--   ty≲-env-subst (Se-≲ ⊢Δ i≤j) Γ≲Δ ⊢Γ = Se-≲ ⊢Γ i≤j
--   ty≲-env-subst (≈-≲ S≈T) Γ≲Δ ⊢Γ     = ≈-≲ (ty-≈-env-subst S≈T Γ≲Δ ⊢Γ)

--   ty-≈-env-subst : Δ ⊢ t ≈ t′ ∶ T →
--                    ⊢ Γ ≲ Δ →
--                    ⊢ Γ →
--                    -------------------------
--                    Γ ⊢ t ≈ t′ ∶ T
--   ty-≈-env-subst (N-[] i ⊢σ) Γ≲Δ ⊢Γ                    = {!!}
--   ty-≈-env-subst (Se-[] ⊢σ i<j) Γ≲Δ ⊢Γ                 = {!!}
--   ty-≈-env-subst (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k) Γ≲Δ ⊢Γ        = {!!}
--   ty-≈-env-subst (Π-cong ⊢U S≈S′ T≈T′ i≤k j≤k) Γ≲Δ ⊢Γ  = Π-cong (ty-env-subst ⊢U Γ≲Δ ⊢Γ)
--                                                                 (ty-≈-env-subst S≈S′ Γ≲Δ ⊢Γ)
--                                                                 {!!} i≤k j≤k
--   ty-≈-env-subst (v-≈ ⊢Γ′ T∈Γ′) Γ≲Δ ⊢Γ                 = {!!}
--   ty-≈-env-subst (ze-≈ ⊢Γ′) Γ≲Δ ⊢Γ                     = {!!}
--   ty-≈-env-subst (su-cong t≈t′) Γ≲Δ ⊢Γ                 = {!!}
--   ty-≈-env-subst (rec-cong T≈T′ s≈s′ r≈r′ t≈t′) Γ≲Δ ⊢Γ = {!!}
--   ty-≈-env-subst (Λ-cong {U} t≈t′) Γ≲Δ ⊢Γ              = {!!}
--   ty-≈-env-subst ($-cong r≈r′ s≈s′) Γ≲Δ ⊢Γ             = {!!}
--   ty-≈-env-subst ([]-cong σ≈σ′ t≈t′) Γ≲Δ ⊢Γ            = {!!}
--   ty-≈-env-subst (ze-[] ⊢σ) Γ≲Δ ⊢Γ                     = {!!}
--   ty-≈-env-subst (su-[] ⊢σ ⊢t) Γ≲Δ ⊢Γ                  = {!!}
--   ty-≈-env-subst (Λ-[] ⊢σ ⊢t) Γ≲Δ ⊢Γ                   = {!!}
--   ty-≈-env-subst ($-[] ⊢σ ⊢r ⊢s) Γ≲Δ ⊢Γ                = {!!}
--   ty-≈-env-subst (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t) Γ≲Δ ⊢Γ        = {!!}
--   ty-≈-env-subst (rec-β-ze ⊢T ⊢t′ ⊢r) Γ≲Δ ⊢Γ           = {!!}
--   ty-≈-env-subst (rec-β-su ⊢T ⊢s ⊢r ⊢t) Γ≲Δ ⊢Γ         = {!!}
--   ty-≈-env-subst (Λ-β {S} ⊢t ⊢s) Γ≲Δ ⊢Γ                = {!!}
--   ty-≈-env-subst (Λ-η ⊢t) Γ≲Δ ⊢Γ                       = {!!}
--   ty-≈-env-subst ([I] ⊢t) Γ≲Δ ⊢Γ                       = {!!}
--   ty-≈-env-subst (↑-lookup ⊢Δ T∈Δ) Γ≲Δ ⊢Γ              = {!!}
--   ty-≈-env-subst ([∘] ⊢τ ⊢σ ⊢t) Γ≲Δ ⊢Γ                 = {!!}
--   ty-≈-env-subst ([,]-v-ze ⊢σ ⊢S ⊢t) Γ≲Δ ⊢Γ            = {!!}
--   ty-≈-env-subst ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ′) Γ≲Δ ⊢Γ       = {!!}
--   ty-≈-env-subst (≈-conv t≈t′ U≲T) Γ≲Δ ⊢Γ              = {!!}
--   ty-≈-env-subst (≈-sym t≈t′) Γ≲Δ ⊢Γ                   = {!!}
--   ty-≈-env-subst (≈-trans t≈t′ t′≈t″) Γ≲Δ ⊢Γ           = {!!}

-- -- mutual
-- --   ty⇒env-ty-wf : Γ ⊢ t ∶ T →
-- --               ------------
-- --               ⊢ Γ × Γ ⊢ T
-- --   ty⇒env-ty-wf (N-wf i ⊢Γ)       = ⊢Γ , suc i , Se-wf ⊢Γ ℕₚ.≤-refl
-- --   ty⇒env-ty-wf (Se-wf ⊢Γ _)      = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
-- --   ty⇒env-ty-wf (Π-wf ⊢S ⊢T _ _)
-- --     with ty⇒env-ty-wf ⊢S
-- --   ...  | ⊢Γ , _ , _              = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
-- --   ty⇒env-ty-wf (vlookup ⊢Γ T∈Γ)  = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
-- --   ty⇒env-ty-wf (ze-I ⊢Γ)         = ⊢Γ , 0 , N-wf 0 ⊢Γ
-- --   ty⇒env-ty-wf (su-I t)          = ty⇒env-ty-wf t
-- --   ty⇒env-ty-wf (N-E ⊢Π ⊢s ⊢r ⊢t)
-- --     with ty⇒env-ty-wf ⊢Π
-- --   ...  | ⊢Γ , _                  = ⊢Γ , _ , conv (Λ-E ⊢Π ⊢t) (≈-≲ (Se-[] (S-, ⊢I (N-wf 0 ⊢Γ) (conv ⊢t (≈-≲ (≈-sym (N-[] 0 ⊢I))))) ℕₚ.≤-refl))
-- --     where ⊢I = S-I ⊢Γ
-- --   ty⇒env-ty-wf (Λ-I t) with ty⇒env-ty-wf t
-- --   ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T        = ⊢Γ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
-- --   ty⇒env-ty-wf (Λ-E ⊢r ⊢s)
-- --     with ty⇒env-ty-wf ⊢r | ty⇒env-ty-wf ⊢s
-- --   ...  | ⊢Γ , _ , ⊢Π | _ , _ , ⊢S
-- --        with inv-Π-wf ⊢Π
-- --   ...     | _ , ⊢T               = ⊢Γ , _ , conv (t[σ] ⊢T I,s) (≈-≲ (Se-[] I,s ℕₚ.≤-refl))
-- --     where S[I] = ≈-≲ (≈-sym ([I] ⊢S))
-- --           I,s  = S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S))))
-- --   ty⇒env-ty-wf (t[σ] ⊢t ⊢σ)
-- --     with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢σ
-- --   ...  | ⊢Δ , _ , ⊢T | ⊢Γ , _    = ⊢Γ , _ , conv (t[σ] ⊢T ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))
-- --   ty⇒env-ty-wf (conv ⊢t S≲T)
-- --     with ty⇒env-ty-wf ⊢t | ≲⇒env-ty-wf S≲T
-- --   ...  | ⊢Γ , _ | _ , i , _ , ⊢T = ⊢Γ , _ , ⊢T

-- --   tys⇒env-wf : Γ ⊢s σ ∶ Δ →
-- --               ------------
-- --               ⊢ Γ × ⊢ Δ
-- --   tys⇒env-wf (S-↑ ⊢SΓ@(⊢∷ ⊢Γ _)) = ⊢SΓ , ⊢Γ
-- --   tys⇒env-wf (S-I ⊢Γ)            = ⊢Γ , ⊢Γ
-- --   tys⇒env-wf (S-∘ ⊢τ ⊢σ)
-- --     with tys⇒env-wf ⊢τ | tys⇒env-wf ⊢σ
-- --   ...  | ⊢Γ , _ | _ , ⊢Δ         = ⊢Γ , ⊢Δ
-- --   tys⇒env-wf (S-, ⊢σ ⊢S ⊢s)
-- --     with tys⇒env-wf ⊢σ
-- --   ...  | ⊢Γ , ⊢Δ                 = ⊢Γ , ⊢∷ ⊢Δ ⊢S

-- --   ≲⇒env-ty-wf : Γ ⊢ S ≲ T →
-- --                 ------------------------------------------
-- --                 ⊢ Γ × ∃ λ i → Γ ⊢ S ∶ Se i × Γ ⊢ T ∶ Se i
-- --   ≲⇒env-ty-wf (Se-≲ ⊢Γ i≤j) = ⊢Γ , _ , Se-wf ⊢Γ (s≤s i≤j) , Se-wf ⊢Γ ℕₚ.≤-refl
-- --   ≲⇒env-ty-wf (≈-≲ S≈T)
-- --     with ty-eq⇒env-ty-wf-gen S≈T
-- --   ...  | ⊢Γ , ⊢S , ⊢T       = ⊢Γ , _ , ⊢S , ⊢T

-- --   ty-eq⇒env-ty-wf-gen : Γ ⊢ s ≈ t ∶ T →
-- --                         -----------------------
-- --                         ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T
-- --   ty-eq⇒env-ty-wf-gen (N-[] i ⊢σ)
-- --     with tys⇒env-wf ⊢σ
-- --   ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (N-wf i ⊢Δ) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , N-wf i ⊢Γ
-- --   ty-eq⇒env-ty-wf-gen (Se-[] ⊢σ i<j)
-- --     with tys⇒env-wf ⊢σ
-- --   ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (Se-wf ⊢Δ i<j) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , Se-wf ⊢Γ i<j
-- --   ty-eq⇒env-ty-wf-gen (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k)
-- --     with tys⇒env-wf ⊢σ
-- --   ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , conv (t[σ] (Π-wf ⊢S ⊢T i≤k j≤k) ⊢σ) Sek[] , Π-wf ⊢S[σ] (conv (t[σ] ⊢T qσ) Sej[]) i≤k j≤k
-- --     where Sek[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
-- --           Sei[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
-- --           ⊢S[σ] = conv (t[σ] ⊢S ⊢σ) Sei[]
-- --           ⊢SΓ   = ⊢∷ ⊢Γ ⊢S[σ]
-- --           qσ    = S-, (S-∘ (S-↑ ⊢SΓ) ⊢σ) ⊢S
-- --                       (conv (vlookup ⊢SΓ here) (≈-≲ (≈-sym (≈-conv ([∘] (S-↑ ⊢SΓ) ⊢σ ⊢S)
-- --                                                (≈-≲ (Se-[] (S-∘ (S-↑ ⊢SΓ) ⊢σ) ℕₚ.≤-refl))))))
-- --           Sej[] = ≈-≲ (Se-[] qσ ℕₚ.≤-refl)
-- --   ty-eq⇒env-ty-wf-gen (Π-cong S≈S′ T≈T′ i≤k j≤k)
-- --     with ty-eq⇒env-ty-wf-gen S≈S′ | ty-eq⇒env-ty-wf-gen T≈T′
-- --   ...  | ⊢Γ , ⊢S , ⊢S′ | _ , ⊢T , ⊢T′ = ⊢Γ , Π-wf ⊢S ⊢T i≤k j≤k , Π-wf ⊢S′ {!!} {!!} {!!}
-- --   ty-eq⇒env-ty-wf-gen (v-≈ x x₁)                    = {!!}
-- --   ty-eq⇒env-ty-wf-gen (ze-≈ x)                      = {!!}
-- --   ty-eq⇒env-ty-wf-gen (su-cong s≈t)                 = {!!}
-- --   ty-eq⇒env-ty-wf-gen (rec-cong s≈t s≈t₁ s≈t₂ s≈t₃) = {!!}
-- --   ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)                  = {!!}
-- --   ty-eq⇒env-ty-wf-gen ($-cong s≈t s≈t₁)             = {!!}
-- --   ty-eq⇒env-ty-wf-gen ([]-cong x s≈t)               = {!!}
-- --   ty-eq⇒env-ty-wf-gen (ze-[] x)                     = {!!}
-- --   ty-eq⇒env-ty-wf-gen (su-[] x x₁)                  = {!!}
-- --   ty-eq⇒env-ty-wf-gen (Λ-[] x x₁)                   = {!!}
-- --   ty-eq⇒env-ty-wf-gen ($-[] x x₁ x₂)                = {!!}
-- --   ty-eq⇒env-ty-wf-gen (rec-[] x x₁ x₂ x₃ x₄)        = {!!}
-- --   ty-eq⇒env-ty-wf-gen (rec-β-ze x x₁ x₂)            = {!!}
-- --   ty-eq⇒env-ty-wf-gen (rec-β-su x x₁ x₂ x₃)         = {!!}
-- --   ty-eq⇒env-ty-wf-gen (Λ-β x x₁)                    = {!!}
-- --   ty-eq⇒env-ty-wf-gen (Λ-η x)                       = {!!}
-- --   ty-eq⇒env-ty-wf-gen ([I] x)                       = {!!}
-- --   ty-eq⇒env-ty-wf-gen (↑-lookup ⊢Γ x)               = {!!}
-- --   ty-eq⇒env-ty-wf-gen ([∘] x x₁ x₂)                 = {!!}
-- --   ty-eq⇒env-ty-wf-gen ([,]-v-ze x x₁ x₂)            = {!!}
-- --   ty-eq⇒env-ty-wf-gen ([,]-v-su x x₁ x₂ x₃)         = {!!}
-- --   ty-eq⇒env-ty-wf-gen (≈-conv s≈t x) = {!!}
-- --   ty-eq⇒env-ty-wf-gen (≈-sym s≈t)                   = {!!}
-- --   ty-eq⇒env-ty-wf-gen (≈-trans s≈t s≈t₁)            = {!!}
