{-# OPTIONS --without-K --safe #-}

module PTT.Statics.CtxSubst where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Complement

import Data.List.Properties as Lₚ
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

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
  ty-env-subst S′≲S ⊢S′ (Λ-I {S″} ⊢t) eq                 = Λ-I (ty-env-subst {Δ = S″ ∷ _} S′≲S ⊢S′ ⊢t (cong (_ ∷_) eq))
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
  subst-env-subst (U ∷ Δ) S′≲S ⊢S′ (S-↑ (⊢∷ ⊢SΔ′ ⊢U)) refl = S-conv (env≲-env-subst Δ ⊢SΔ′ S′≲S ⊢S′)
                                                                    (S-↑ (⊢∷ (env-env-subst Δ S′≲S ⊢SΔ′ ⊢S′)
                                                                             (ty-env-subst S′≲S ⊢S′ ⊢U refl)))
  subst-env-subst Δ S′≲S ⊢S′ (S-I ⊢Δ′)       refl          = S-conv (env≲-env-subst Δ ⊢Δ′ S′≲S ⊢S′)
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
                   ⊢ Δ ++ S ∷ Γ →
                   Γ ⊢ S′ ≲ S →
                   Γ ⊢ S′ ∶ Se i →
                   ---------------------------
                   ⊢ Δ ++ S′ ∷ Γ ≲ Δ ++ S ∷ Γ
  env≲-env-subst [] (⊢∷ ⊢Γ _) S′≲S ⊢S′        = ≈∷ (env≲-refl ⊢Γ) S′≲S ⊢S′
  env≲-env-subst (T ∷ Δ) (⊢∷ ⊢Γ′ ⊢T) S′≲S ⊢S′ = ≈∷ (env≲-env-subst Δ ⊢Γ′ S′≲S ⊢S′) (≲-refl ⊢T) ⊢T

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
  subst-≈-env-subst (U ∷ Δ) S′≲S ⊢S′ (↑-≈ (⊢∷ ⊢Γ″ ⊢U)) refl = S-≈-conv (env≲-env-subst Δ ⊢Γ″ S′≲S ⊢S′)
                                                                       (↑-≈ (⊢∷ (env-env-subst Δ S′≲S ⊢Γ″ ⊢S′)
                                                                                (ty-env-subst S′≲S ⊢S′ ⊢U refl)))
  subst-≈-env-subst Δ S′≲S ⊢S′ (I-≈ ⊢Γ″) refl               = S-≈-conv (env≲-env-subst Δ ⊢Γ″ S′≲S ⊢S′)
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

mutual
  ty-env-substs-gen : ⊢ Γ ≲ Γ′ →
                      Δ ++ Γ′ ⊢ t ∶ T →
                      -------------------
                      Δ ++ Γ ⊢ t ∶ T
  ty-env-substs-gen ≈[] ⊢t                                              = ⊢t
  ty-env-substs-gen {_} {_} {Δ} (≈∷ {Γ} {Γ′} {S} {S′} Γ≲Γ′ S≲S′ ⊢S′) ⊢t = ty-env-subst (ty≲-env-substs-gen Γ≲Γ′ S≲S′) (ty-env-substs-gen Γ≲Γ′ ⊢S′) ⊢t″ refl
    where ⊢t′ = subst (_⊢ _ ∶ _) (sym (Lₚ.++-assoc Δ (S′ ∷ []) Γ′)) ⊢t
          ⊢t″ = subst (_⊢ _ ∶ _) (Lₚ.++-assoc Δ (S′ ∷ []) Γ) (ty-env-substs-gen Γ≲Γ′ ⊢t′)

  ty≲-env-substs-gen : ⊢ Γ ≲ Γ′ →
                       Δ ++ Γ′ ⊢ S ≲ T →
                       -------------------
                       Δ ++ Γ ⊢ S ≲ T
  ty≲-env-substs-gen ≈[] S≲T                                                = S≲T
  ty≲-env-substs-gen {_} {_} {Δ} (≈∷ {Γ} {Γ′} {S′} {T′} Γ≲Γ′ S′≲T′ ⊢T′) S≲T = ty≲-env-subst (ty≲-env-substs-gen Γ≲Γ′ S′≲T′) (ty-env-substs-gen Γ≲Γ′ ⊢T′) S≲T″ refl
    where S≲T′ = subst (_⊢ _ ≲ _) (sym (Lₚ.++-assoc Δ (T′ ∷ []) Γ′)) S≲T
          S≲T″ = subst (_⊢ _ ≲ _) (Lₚ.++-assoc Δ (T′ ∷ []) Γ) (ty≲-env-substs-gen Γ≲Γ′ S≲T′)

ty-env-substs : ⊢ Γ ≲ Γ′ →
                Γ′ ⊢ t ∶ T →
                --------------
                Γ ⊢ t ∶ T
ty-env-substs = ty-env-substs-gen {Δ = []}
