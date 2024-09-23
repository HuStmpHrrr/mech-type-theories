{-# OPTIONS --without-K --safe #-}

-- The overall properties of the Concise formulation which are used by later modules.
--
-- Many properties have been proved in the Full formulation. We can use the
-- equivalence between the Full and Concise formulation to bring existing conclusion
-- to this file so later modules can conveniently use these results.
module NonCumulative.Statics.Ascribed.Properties where

open import Lib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

-- open import MLTT.Statics.Syntax public
open import NonCumulative.Statics.Ascribed.Full
import NonCumulative.Statics.Ascribed.Presup as Presup
import NonCumulative.Statics.Ascribed.Refl as Refl
import NonCumulative.Statics.Ascribed.Misc as Misc
import NonCumulative.Statics.Ascribed.PER as PER
import NonCumulative.Statics.Ascribed.CtxEquiv as CtxEquiv
import NonCumulative.Statics.Ascribed.Properties.Contexts as Ctxₚ
import NonCumulative.Statics.Ascribed.Properties.Subst as Subₚ
open Misc
  using ( _[wk]*_)
  public

⊢≈-refl : ⊢ Γ →
          --------
          ⊢ Γ ≈ Γ
⊢≈-refl ⊢Γ = (Refl.≈-Ctx-refl ⊢Γ)

⊢≈-trans : ⊢ Γ ≈ Γ′ → ⊢ Γ′ ≈ Γ″ → ⊢ Γ ≈ Γ″
⊢≈-trans ⊢Γ≈Γ′ ⊢Γ′≈Γ′′ = PER.⊢≈-trans ⊢Γ≈Γ′ ⊢Γ′≈Γ′′

[]-cong-Se‴ : ∀ {i} → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se‴ ⊢T σ≈σ′ = Misc.[]-cong-Se″ ⊢T (proj₁ (proj₂ (Presup.presup-s-≈ σ≈σ′))) σ≈σ′

-- inversions of judgments

⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ⊢≈-refl ⊢Γ
⊢I-inv (s-conv ⊢I Δ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Δ′≈Δ

[I]-inv : ∀ { i } → Γ ⊢ t [ I ] ∶[ i ] T → Γ ⊢ t ∶[ i ] T
[I]-inv (t[σ] ⊢t[I] ⊢sI) with ⊢t ← CtxEquiv.ctxeq-tm (Ctxₚ.⊢≈-sym (⊢I-inv ⊢sI)) ⊢t[I] = conv ⊢t (≈-sym ([I] (proj₂ (Presup.presup-tm ⊢t))))
[I]-inv (conv ⊢t[I] S≈T) = conv ([I]-inv ⊢t[I]) S≈T

[I]-≈ˡ : ∀ {i} → Γ ⊢ t [ I ] ≈ s ∶[ i ] T [ I ] →
         ------------------------------
         Γ ⊢ t ≈ s ∶[ i ] T
[I]-≈ˡ ≈s
  with _ , ⊢t[I] , _ , ⊢T[I] ← Presup.presup-≈ ≈s = ≈-conv (≈-trans (≈-sym ([I] ⊢t)) ≈s) ([I] ⊢T)
  where ⊢t = [I]-inv ⊢t[I]
        ⊢T = [I]-inv ⊢T[I]

[I]-≈ˡ-Se : ∀ {i} →
            Γ ⊢ T [ I ] ≈ S ∶[ 1 + i ] Se i →
            ----------------------------
            Γ ⊢ T ≈ S ∶[ 1 + i ] Se i
[I]-≈ˡ-Se ≈S
  with _ , ⊢T[I] , _ ← Presup.presup-≈ ≈S = ≈-trans (≈-sym ([I] ⊢T)) ≈S
  where ⊢T = [I]-inv ⊢T[I]

∘I-inv : Γ ⊢s σ ∘ I ∶ Δ → ∃ λ Δ′ → Γ ⊢s σ ∶ Δ′ × ⊢ Δ ≈ Δ′
∘I-inv (s-∘ ⊢I ⊢σ) = -, CtxEquiv.ctxeq-s (Ctxₚ.⊢≈-sym (⊢I-inv ⊢I)) ⊢σ , ⊢≈-refl (proj₂ (Presup.presup-s ⊢σ))
∘I-inv (s-conv ⊢σI Δ″≈Δ)
  with Δ′ , ⊢σ , Δ″≈Δ′ ← ∘I-inv ⊢σI = -, ⊢σ , ⊢≈-trans (Ctxₚ.⊢≈-sym Δ″≈Δ) Δ″≈Δ′

∘I-inv′ : Γ ⊢s σ ∘ I ∶ Δ → Γ ⊢s σ ∶ Δ
∘I-inv′ ⊢σI
  with _ , ⊢σ , Δ′≈Δ ← ∘I-inv ⊢σI = s-conv ⊢σ (Ctxₚ.⊢≈-sym Δ′≈Δ)

[∘]-N : Δ ⊢ t ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ t [ σ ] [ τ ] ≈ t [ σ ∘ τ ] ∶[ 0 ] N
[∘]-N ⊢t ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢t)) (N-[] (s-∘ ⊢τ ⊢σ))

Exp≈-isPER : ∀ {i} → IsPartialEquivalence (Γ ⊢_≈_∶[ i ] T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : ∀ {i} → Ctx → Typ → PartialSetoid _ _
Exp≈-PER {i} Γ T = record
  { Carrier              = Exp
  ; _≈_                  = Γ ⊢_≈_∶[ i ] T
  ; isPartialEquivalence = Exp≈-isPER
  }

module ER {i Γ T} = PS (Exp≈-PER {i} Γ T)

Substs≈-isPER : IsPartialEquivalence (Γ ⊢s_≈_∶ Δ)
Substs≈-isPER = record
  { sym   = s-≈-sym
  ; trans = s-≈-trans
  }

Substs≈-PER : Ctx → Ctx → PartialSetoid _ _
Substs≈-PER Γ Δ = record
  { Carrier              = Subst
  ; _≈_                  = Γ ⊢s_≈_∶ Δ
  ; isPartialEquivalence = Substs≈-isPER
  }

module SR {Γ Δ} = PS (Substs≈-PER Γ Δ)

[]-q-∘-, : ∀ {i j} → (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j → Δ ⊢s σ ∶ Γ → Δ′ ⊢s τ ∶ Δ → Δ′ ⊢ t ∶[ i ] S [ σ ] [ τ ] →
           Δ′ ⊢ T [ (σ ∘ τ) , t ∶ (S ↙ i) ] ≈ T [ q (S ↙ i) σ ] [ τ , t ∶ (sub S σ ↙ i) ] ∶[ 1 + j ] Se j
[]-q-∘-, {S} {T = T} {σ = σ} {τ = τ} {t = t} {i = i} {j} ⊢T ⊢σ ⊢τ ⊢t
   with ⊢∷ ⊢Γ ⊢S ← proj₁ (Presup.presup-tm ⊢T)
     | ⊢Δ′ , ⊢Δ ← Presup.presup-s ⊢τ =  begin
     T [ (σ ∘ τ) , t ∶ (S ↙ i) ] ≈⟨ []-cong-Se‴ ⊢T
                                                 (,-cong (s-≈-trans (∘-cong (s-≈-sym (p-, ⊢τ ⊢Sσ ⊢t)) (Refl.s-≈-refl ⊢σ))
                                                        (s-≈-sym (∘-assoc ⊢σ
                                                                          (s-wk ⊢SσΔ)
                                                                          (s-, ⊢τ ⊢Sσ ⊢t)))) ⊢S (Refl.≈-refl ⊢S) (≈-conv (≈-sym ([,]-v-ze ⊢τ ⊢Sσ ⊢t)) (Misc.[∘]-Se ⊢S ⊢σ ⊢τ) )) ⟩
     T [ (σ ∘ wk ∘ τ , t ∶ (sub S σ ↙ i)) , v 0 [ τ , t ∶ (sub S σ ↙ i)  ] ∶ (S ↙ i)  ] ≈˘⟨ []-cong-Se‴ ⊢T
                                                                                                           (,-∘ (s-∘ (s-wk ⊢SσΔ) ⊢σ) ⊢S (conv (vlookup ⊢SσΔ here) (Misc.[∘]-Se ⊢S ⊢σ (s-wk ⊢SσΔ))) (s-, ⊢τ ⊢Sσ ⊢t)) ⟩
     T [ q (S ↙ i) σ ∘ (τ , t ∶ (sub S σ ↙ i)) ]                      ≈˘⟨ Misc.[∘]-Se ⊢T ⊢qσ ⊢τ,t ⟩
     T [ q (S ↙ i) σ ] [ τ , t ∶ (sub S σ ↙ i) ] ∎
   where open ER
         ⊢qσ  = Misc.⊢q ⊢Δ ⊢σ ⊢S
         ⊢Sσ  = Misc.t[σ]-Se ⊢S ⊢σ
         ⊢τ,t = s-, ⊢τ ⊢Sσ ⊢t
         ⊢SσΔ = ⊢∷ ⊢Δ ⊢Sσ

[]-q-∘-,′ : ∀ {i j} → (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + i ] Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶[ j ] S [ σ ] →  Δ ⊢ T [ σ , t ∶ (S ↙ j) ] ≈ T [ q (S ↙ j) σ ] [| t ∶ (sub S σ ↙ j) ] ∶[ 1 + i ] Se i
[]-q-∘-,′ ⊢T ⊢σ ⊢t
  with ⊢∷ ⊢Γ ⊢S ← proj₁ (Presup.presup-tm ⊢T)
      | ⊢Δ , ⊢Γ ← Presup.presup-s ⊢σ = ≈-trans ([]-cong-Se‴ ⊢T (,-cong (s-≈-sym (∘-I ⊢σ)) ⊢S (Refl.≈-refl ⊢S) (Refl.≈-refl ⊢t)))
                                         ([]-q-∘-, ⊢T ⊢σ (s-I ⊢Δ) (conv ⊢t (≈-sym ([I] ⊢Sσ))))
  where ⊢qσ = Misc.⊢q ⊢Δ ⊢σ ⊢S
        ⊢Sσ = Misc.t[σ]-Se ⊢S ⊢σ


I,∘≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢ t ∶[ i ] T → Δ ⊢s (I , t ∶ T ↙ i) ∘ σ ≈ σ , t [ σ ] ∶ T ↙ i ∶ (T ↙ i) ∷ Γ
I,∘≈, ⊢σ ⊢T ⊢t = Subₚ.[I,t]∘σ≈σ,t[σ] (⊢∷ (proj₁ (Presup.presup-tm ⊢t)) ⊢T) ⊢σ ⊢t


[]-I,-∘ : ∀ {i j} → (T ↙ i) ∷ Γ ⊢ S ∶[ 1 + j ] Se j → Δ ⊢s σ ∶ Γ → Γ ⊢ t ∶[ i ] T → Δ ⊢ S [| t ∶ T ↙ i ] [ σ ] ≈ S [ σ , t [ σ ] ∶ T ↙ i ] ∶[ 1 + j ] Se j
[]-I,-∘ {T = T} {S = S} {σ = σ} {t = t} {i = i} {j = j} ⊢S ⊢σ ⊢t
  with ⊢∷ ⊢Γ ⊢T ← proj₁ (Presup.presup-tm ⊢S) = begin
  S [| t ∶ T ↙ i ] [ σ ]    ≈⟨ Misc.[∘]-Se ⊢S ⊢I,t ⊢σ ⟩
  S [ (I , t ∶ T ↙ i) ∘ σ ] ≈⟨ []-cong-Se‴ ⊢S (I,∘≈, ⊢σ ⊢T ⊢t) ⟩
  S [ σ , t [ σ ] ∶ T ↙ i ] 
  ∎
  where open ER
        ⊢I,t = Misc.⊢I,t ⊢Γ ⊢T ⊢t
        
---------------------
-- other easy helpers

p-∘ : ∀ {i} → Γ ⊢s σ ∶ (T ↙ i) ∷ Δ →
      Γ′ ⊢s τ ∶ Γ →
      ------------------------------
      Γ′ ⊢s p (σ ∘ τ) ≈ p σ ∘ τ ∶ Δ
p-∘ ⊢σ ⊢τ = s-≈-sym (∘-assoc (s-wk (proj₂ (Presup.presup-s ⊢σ))) ⊢σ ⊢τ)


-- q related properties
module _ {i} {j : ℕ} (⊢σ : Γ ⊢s σ ∶ Δ)
         (⊢T : Δ ⊢ T ∶[ 1 + i ] Se i)
         (⊢τ : Δ′ ⊢s τ ∶ Γ)
         (⊢t : Δ′ ⊢ t ∶[ i ] T [ σ ] [ τ ]) where
  private
    ⊢Γ   = proj₁ (Presup.presup-s ⊢σ)
    ⊢Tσ  = Misc.t[σ]-Se ⊢T ⊢σ
    ⊢TσΓ = ⊢∷ ⊢Γ ⊢Tσ
    ⊢wk  = s-wk ⊢TσΓ
    ⊢σwk = s-∘ ⊢wk ⊢σ
    ⊢qσ  = Misc.⊢q ⊢Γ ⊢σ ⊢T
    ⊢τ,t = s-, ⊢τ ⊢Tσ ⊢t

    eq = begin
      σ ∘ wk ∘ (τ , t ∶  T [ σ ] ↙ i) ≈⟨ ∘-assoc ⊢σ ⊢wk ⊢τ,t ⟩
      σ ∘ (wk ∘ (τ , t ∶ T [ σ ] ↙ i)) ≈⟨ ∘-cong (p-, ⊢τ ⊢Tσ ⊢t) (Refl.s-≈-refl ⊢σ) ⟩
      σ ∘ τ ∎
      where open SR

  q∘,≈∘, : Δ′ ⊢s q (T ↙ i) σ ∘ (τ , t ∶ T [ σ ] ↙ i) ≈ (σ ∘ τ) , t ∶ T ↙ i ∶ (T ↙ i) ∷ Δ
  q∘,≈∘, = begin
    q (T ↙ i) σ ∘ (τ , t ∶ T [ σ ] ↙ i)   ≈⟨ ,-∘ ⊢σwk ⊢T (conv (vlookup ⊢TσΓ here) (Misc.[∘]-Se ⊢T ⊢σ ⊢wk)) ⊢τ,t ⟩
    (σ ∘ wk ∘ (τ , t ∶ T [ σ ] ↙ i)) , v 0 [ τ , t ∶ T [ σ ] ↙ i ] ∶ T ↙ i ≈⟨ ,-cong eq ⊢T (Refl.≈-refl ⊢T) (≈-conv ([,]-v-ze ⊢τ ⊢Tσ ⊢t)
                                                                                    ( ≈-trans (Misc.[∘]-Se ⊢T ⊢σ ⊢τ) (≈-sym ([]-cong-Se‴ ⊢T eq)) )) ⟩
    (σ ∘ τ) , t ∶ T ↙ i
    ∎
    where open SR

  []-q-, : (T ↙ i) ∷ Δ ⊢ s ∶[ j ] S →
           Δ′ ⊢ s [ q (T ↙ i) σ ] [ τ , t ∶ T [ σ ] ↙ i ] ≈ s [ (σ ∘ τ) , t ∶ T ↙ i ] ∶[ j ] S [ (σ ∘ τ) , t ∶ T ↙ i ]
  []-q-, {s} ⊢s
    with _ , ⊢S ← Presup.presup-tm ⊢s = begin
      s [ q (T ↙ i) σ ] [ τ , t ∶ T [ σ ] ↙ i ] ≈˘⟨ ≈-conv ([∘] ⊢τ,t ⊢qσ ⊢s) ([]-cong-Se‴ ⊢S q∘,≈∘,) ⟩
      s [ (q (T ↙ i) σ) ∘ ( τ , t ∶ T [ σ ] ↙ i) ] ≈⟨ ≈-conv ([]-cong (Refl.≈-refl ⊢s) q∘,≈∘,) ([]-cong-Se‴ ⊢S q∘,≈∘,) ⟩
      s [ (σ ∘ τ) , t ∶ T ↙ i ]
    ∎
    where open ER