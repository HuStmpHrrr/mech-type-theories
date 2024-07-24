{-# OPTIONS --without-K --safe #-}

-- The overall properties of the Concise formulation which are used by later modules.
--
-- Many properties have been proved in the Full formulation. We can use the
-- equivalence between the Full and Concise formulation to bring existing conclusion
-- to this file so later modules can conveniently use these results.
module MLTT.Statics.Properties where

open import Lib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

import MLTT.Statics.Full as F
open import MLTT.Statics.Concise as C
open import MLTT.Statics.Equiv
import MLTT.Statics.Presup as Presup
import MLTT.Statics.Refl as Refl
import MLTT.Statics.Misc as Misc
import MLTT.Statics.PER as PER
import MLTT.Statics.CtxEquiv as CtxEquiv
import MLTT.Statics.Properties.Contexts as Ctxₚ
import MLTT.Statics.Properties.Subst as Subₚ
open Misc
  using ( _[wk]*_)
  public


-- lifting of universe levels
lift-⊢-Se : ∀ {i j} →
            Γ ⊢ T ∶ Se i →
            i ≤ j →
            -----------------
            Γ ⊢ T ∶ Se j
lift-⊢-Se ⊢T i≤j = F⇒C-tm (Misc.lift-⊢-Se (C⇒F-tm ⊢T) i≤j)

lift-⊢-Se-max : ∀ {i j} →
                Γ ⊢ T ∶ Se i →
                -------------------
                Γ ⊢ T ∶ Se (i ⊔ j)
lift-⊢-Se-max ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max (C⇒F-tm ⊢T))

lift-⊢-Se-max′ : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (j ⊔ i)
lift-⊢-Se-max′ ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max′ (C⇒F-tm ⊢T))

lift-⊢≈-Se : ∀ {i j} →
             Γ ⊢ T ≈ T′ ∶ Se i →
             i ≤ j →
             --------------------
             Γ ⊢ T ≈ T′ ∶ Se j
lift-⊢≈-Se T≈T′ i≤j = F⇒C-≈ (Misc.lift-⊢≈-Se (C⇒F-≈ T≈T′) i≤j)

lift-⊢≈-Se-max : ∀ {i j} →
                 Γ ⊢ T ≈ T′ ∶ Se i →
                 ------------------------
                 Γ ⊢ T ≈ T′ ∶ Se (i ⊔ j)
lift-⊢≈-Se-max T≈T′ = F⇒C-≈ (Misc.lift-⊢≈-Se-max (C⇒F-≈ T≈T′))

lift-⊢≈-Se-max′ : ∀ {i j} →
                  Γ ⊢ T ≈ T′ ∶ Se i →
                  ------------------------
                  Γ ⊢ T ≈ T′ ∶ Se (j ⊔ i)
lift-⊢≈-Se-max′ T≈T′ = F⇒C-≈ (Misc.lift-⊢≈-Se-max′ (C⇒F-≈ T≈T′))

------------------------
-- various reflexivities

≈-refl : Γ ⊢ t ∶ T →
         --------------
         Γ ⊢ t ≈ t ∶ T
≈-refl ⊢t = ≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)

s-≈-refl : Γ ⊢s σ ∶ Δ →
           --------------
           Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl ⊢σ = s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ)

⊢≈-refl : ⊢ Γ →
          --------
          ⊢ Γ ≈ Γ
⊢≈-refl ⊢Γ = F⇒C-⊢≈ (Refl.≈-Ctx-refl (C⇒F-⊢ ⊢Γ))


----------------------------------------------
-- equivalence between context stacks is a PER

⊢≈-sym : ⊢ Γ ≈ Δ →
         ---------
         ⊢ Δ ≈ Γ
⊢≈-sym Γ≈Δ = F⇒C-⊢≈ (Ctxₚ.⊢≈-sym (C⇒F-⊢≈ Γ≈Δ))

⊢≈-trans : ⊢ Γ ≈ Γ′ →
           ⊢ Γ′ ≈ Γ″ →
           -----------
           ⊢ Γ ≈ Γ″
⊢≈-trans Γ≈Γ′ Γ′≈Γ″ = F⇒C-⊢≈ (PER.⊢≈-trans (C⇒F-⊢≈ Γ≈Γ′) (C⇒F-⊢≈ Γ′≈Γ″))

--------------------------------------------------
-- various properties of context stacks

≈⇒len≡ : ⊢ Γ ≈ Δ →
         -------------
         len Γ ≡ len Δ
≈⇒len≡ Γ≈Δ = Ctxₚ.≈⇒len≡ (C⇒F-⊢≈ Γ≈Δ)

⊢≈⇒len-head≡ : ⊢ Γ ≈ Δ →
               ---------------------------
               len Γ ≡ len Δ
⊢≈⇒len-head≡ []-≈            = refl
⊢≈⇒len-head≡ (∷-cong Γ≈Δ T≈) = cong suc (⊢≈⇒len-head≡ Γ≈Δ)

--------------------------------------------
-- presupposition of the Concise formulation

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ Γ≈Δ
  with ⊢Γ , ⊢Δ ← Ctxₚ.presup-⊢≈ (C⇒F-⊢≈ Γ≈Δ) = F⇒C-⊢ ⊢Γ , F⇒C-⊢ ⊢Δ

presup-tm : Γ ⊢ t ∶ T →
            ------------
            ⊢ Γ × Γ ⊢ T
presup-tm ⊢t
  with ⊢Γ , _ , ⊢T ← Presup.presup-tm (C⇒F-tm ⊢t) = F⇒C-⊢ ⊢Γ , -, F⇒C-tm ⊢T

presup-s : Γ ⊢s σ ∶ Δ →
           ------------
           ⊢ Γ × ⊢ Δ
presup-s ⊢σ
  with ⊢Γ , ⊢Δ ← Presup.presup-s (C⇒F-s ⊢σ) = F⇒C-⊢ ⊢Γ , F⇒C-⊢ ⊢Δ

presup-≈ : Γ ⊢ s ≈ t ∶ T →
           -----------------------------------
           ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
presup-≈ s≈t
  with ⊢Γ , ⊢s , ⊢t , _ , ⊢T ← Presup.presup-≈ (C⇒F-≈ s≈t) = F⇒C-⊢ ⊢Γ , F⇒C-tm ⊢s , F⇒C-tm ⊢t , -, F⇒C-tm ⊢T

presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
             -----------------------------------
             ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
presup-s-≈ σ≈τ
  with ⊨Γ , ⊢σ , ⊢τ , ⊢Δ ← Presup.presup-s-≈ (C⇒F-s-≈ σ≈τ) = F⇒C-⊢ ⊨Γ , F⇒C-s ⊢σ , F⇒C-s ⊢τ , F⇒C-⊢ ⊢Δ

-----------------------------------------------------------
-- respectfulness of context stack equivalence of judgments

ctxeq-tm : ⊢ Γ ≈ Δ →
           Γ ⊢ t ∶ T →
           -----------
           Δ ⊢ t ∶ T
ctxeq-tm Γ≈Δ ⊢t = F⇒C-tm (CtxEquiv.ctxeq-tm (C⇒F-⊢≈ Γ≈Δ) (C⇒F-tm ⊢t))

ctxeq-≈ : ⊢ Γ ≈ Δ →
          Γ ⊢ t ≈ t′ ∶ T →
          -----------------
          Δ ⊢ t ≈ t′ ∶ T
ctxeq-≈ Γ≈Δ t≈t′ = F⇒C-≈ (CtxEquiv.ctxeq-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-≈ t≈t′))

ctxeq-s : ⊢ Γ ≈ Δ →
          Γ ⊢s σ ∶ Γ′ →
          -----------
          Δ ⊢s σ ∶ Γ′
ctxeq-s Γ≈Δ ⊢σ = F⇒C-s (CtxEquiv.ctxeq-s (C⇒F-⊢≈ Γ≈Δ) (C⇒F-s ⊢σ))

ctxeq-s-≈ : ⊢ Γ ≈ Δ →
            Γ ⊢s σ ≈ σ′ ∶ Γ′ →
            ------------------
            Δ ⊢s σ ≈ σ′ ∶ Γ′
ctxeq-s-≈ Γ≈Δ σ≈σ′ = F⇒C-s-≈ (CtxEquiv.ctxeq-s-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-s-≈ σ≈σ′))


------
-- PER

Exp≈-isPER : IsPartialEquivalence (Γ ⊢_≈_∶ T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : Ctx → Typ → PartialSetoid _ _
Exp≈-PER Γ T = record
  { Carrier              = Exp
  ; _≈_                  = Γ ⊢_≈_∶ T
  ; isPartialEquivalence = Exp≈-isPER
  }

module ER {Γ T} = PS (Exp≈-PER Γ T)

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

---------------------
-- other easy helpers

p-∘ : Γ ⊢s σ ∶ T ∷ Δ →
      Γ′ ⊢s τ ∶ Γ →
      ------------------------------
      Γ′ ⊢s p (σ ∘ τ) ≈ p σ ∘ τ ∶ Δ
p-∘ ⊢σ ⊢τ = s-≈-sym (∘-assoc (s-wk (proj₂ (presup-s ⊢σ))) ⊢σ ⊢τ)

n∶T[wk]n∈!ΔTΓ : ∀ {n} →
                ⊢ Δ ++ T ∷ Γ →
                len Δ ≡ n →
                ------------------------------------
                n ∶ T [wk]* (suc n) ∈! Δ ++ T ∷ Γ
n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ eq = Misc.n∶T[wk]n∈!ΔTΓ (C⇒F-⊢ ⊢ΔTΓ) eq

⊢vn∶T[wk]suc[n] : ∀ {n} →
                  ⊢ Δ ++ T ∷ Γ →
                  len Δ ≡ n →
                  -------------------------------------
                  Δ ++ T ∷ Γ ⊢ v n ∶ T [wk]* (suc n)
⊢vn∶T[wk]suc[n] ⊢ΔTΓ eq = vlookup ⊢ΔTΓ (n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ eq)

-- A closed term cannot be neutral.

no-closed-Ne-gen : Γ ⊢ t ∶ T →
                   Γ ≡ [] →
                   ----------------
                   ¬ (t ≡ Ne⇒Exp u)
no-closed-Ne-gen {_} {_} {_} {v x} (vlookup _ ()) refl refl
no-closed-Ne-gen {_} {_} {_} {rec T z s u} (N-E _ _ _ ⊢u) eq refl  = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {u $ n} (Λ-E ⊢u _) eq refl            = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {_} (cumu ⊢u) eq refl                 = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {_} (conv ⊢u _) eq refl               = no-closed-Ne-gen ⊢u eq refl


no-closed-Ne : ¬ ([] ⊢ Ne⇒Exp u ∶ T)
no-closed-Ne ⊢u = no-closed-Ne-gen ⊢u refl refl

-- helper judgments

[]-cong-Se′ : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ ] ∶ Se i
[]-cong-Se′ T≈T′ ⊢σ = F⇒C-≈ (Misc.[]-cong-Se′ (C⇒F-≈ T≈T′) (C⇒F-s ⊢σ))

[]-cong-Se″ : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T [ σ′ ] ∶ Se i
[]-cong-Se″ ⊢T σ≈σ′ = F⇒C-≈ (Misc.[]-cong-Se″ (C⇒F-tm ⊢T) (C⇒F-s (proj₁ (proj₂ (presup-s-≈ σ≈σ′)))) (C⇒F-s-≈ σ≈σ′))

[]-cong-N′ : Δ ⊢ t ≈ t′ ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ≈ t′ [ σ ] ∶ N
[]-cong-N′ T≈T′ ⊢σ = F⇒C-≈ (Misc.[]-cong-N′ (C⇒F-≈ T≈T′) (C⇒F-s ⊢σ))

[∘]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ T [ σ ] [ τ ] ≈ T [ σ ∘ τ ] ∶ Se i
[∘]-Se ⊢T ⊢σ ⊢τ = F⇒C-≈ (Misc.[∘]-Se (C⇒F-tm ⊢T) (C⇒F-s ⊢σ) (C⇒F-s ⊢τ))

[∘]-N : Δ ⊢ t ∶ N → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ t [ σ ] [ τ ] ≈ t [ σ ∘ τ ] ∶ N
[∘]-N ⊢t ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢t)) (N-[] 0 (s-∘ ⊢τ ⊢σ))

-- inversions of judgments

⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ⊢≈-refl ⊢Γ
⊢I-inv (s-conv ⊢I Δ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Δ′≈Δ

[I]-inv : Γ ⊢ t [ I ] ∶ T → Γ ⊢ t ∶ T
[I]-inv (t[σ] t∶T ⊢I)
  with ⊢t ← ctxeq-tm (⊢≈-sym (⊢I-inv ⊢I)) t∶T = conv ⊢t (≈-sym ([I] (proj₂ (proj₂ (presup-tm ⊢t)))))
[I]-inv (cumu t[I])     = cumu ([I]-inv t[I])
[I]-inv (conv t[I] S≈T) = conv ([I]-inv t[I]) S≈T

[I]-≈ˡ : Γ ⊢ t [ I ] ≈ s ∶ T [ I ] →
         ------------------------------
         Γ ⊢ t ≈ s ∶ T
[I]-≈ˡ ≈s
  with _ , ⊢t[I] , _ , _ , ⊢T[I] ← presup-≈ ≈s = ≈-conv (≈-trans (≈-sym ([I] ⊢t)) ≈s) ([I] ⊢T)
  where ⊢t = [I]-inv ⊢t[I]
        ⊢T = [I]-inv ⊢T[I]

[I]-≈ˡ-Se : ∀ {i} →
            Γ ⊢ T [ I ] ≈ S ∶ Se i →
            ----------------------------
            Γ ⊢ T ≈ S ∶ Se i
[I]-≈ˡ-Se ≈S
  with _ , ⊢T[I] , _ ← presup-≈ ≈S = ≈-trans (≈-sym ([I] ⊢T)) ≈S
  where ⊢T = [I]-inv ⊢T[I]

∘I-inv : Γ ⊢s σ ∘ I ∶ Δ → ∃ λ Δ′ → Γ ⊢s σ ∶ Δ′ × ⊢ Δ ≈ Δ′
∘I-inv (s-∘ ⊢I ⊢σ) = -, ctxeq-s (⊢≈-sym (⊢I-inv ⊢I)) ⊢σ , ⊢≈-refl (proj₂ (presup-s ⊢σ))
∘I-inv (s-conv ⊢σI Δ″≈Δ)
  with Δ′ , ⊢σ , Δ″≈Δ′ ← ∘I-inv ⊢σI = -, ⊢σ , ⊢≈-trans (⊢≈-sym Δ″≈Δ) Δ″≈Δ′

∘I-inv′ : Γ ⊢s σ ∘ I ∶ Δ → Γ ⊢s σ ∶ Δ
∘I-inv′ ⊢σI
  with _ , ⊢σ , Δ′≈Δ ← ∘I-inv ⊢σI = s-conv ⊢σ (⊢≈-sym Δ′≈Δ)

⊢wk-inv : T ∷ Γ ⊢s wk ∶ Δ → ⊢ Γ ≈ Δ
⊢wk-inv (s-wk (⊢∷ ⊢Γ _)) = ⊢≈-refl ⊢Γ
⊢wk-inv (s-conv ⊢wk ≈Δ)  = ⊢≈-trans (⊢wk-inv ⊢wk) ≈Δ

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

-- continue helper judgments

t[I] : Γ ⊢ t ∶ T →
       Γ ⊢ t [ I ] ∶ T
t[I] ⊢t
  with ⊢Γ , _ , ⊢T ← presup-tm ⊢t = conv (t[σ] ⊢t (s-I ⊢Γ)) ([I] ⊢T)

t[σ]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶ Se i
t[σ]-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

⊢q : ∀ {i} → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∷ Γ ⊢s q σ ∶ T ∷ Δ
⊢q ⊢σ ⊢T = F⇒C-s (Misc.⊢q (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢T))

⊢q-N : Γ ⊢s σ ∶ Δ → N ∷ Γ ⊢s q σ ∶ N ∷ Δ
⊢q-N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = F⇒C-s (Misc.⊢q-N (C⇒F-⊢ ⊢Γ) (C⇒F-⊢ ⊢Δ) (C⇒F-s ⊢σ))

q-cong : ∀ {i} → Γ ⊢s σ ≈ σ′ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∷ Γ ⊢s q σ ≈ q σ′ ∶ T ∷ Δ
q-cong {_} {σ} {σ′} {_} {T} σ≈σ′ ⊢T
  with ⊢Γ , ⊢σ , _ ← presup-s-≈ σ≈σ′ = ,-cong (∘-cong (wk-≈ ⊢TσΓ) σ≈σ′) ⊢T (≈-refl (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΓ))))
  where open ER
        ⊢Tσ  = t[σ]-Se ⊢T ⊢σ
        ⊢TσΓ = ⊢∷ ⊢Γ ⊢Tσ

⊢I,t : Γ ⊢ t ∶ T → Γ ⊢s I , t ∶ T ∷ Γ
⊢I,t ⊢t
  with ⊢Γ , _ , ⊢T ← presup-tm ⊢t = F⇒C-s (Misc.⊢I,t (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t))

---------------
-- The rest of helpers from this point are specialized helpers which we use in multiple places.
-- One can safely omit these helpers.

⊢I,ze : ⊢ Γ → Γ ⊢s I , ze ∶ N ∷ Γ
⊢I,ze ⊢Γ = ⊢I,t (ze-I ⊢Γ)

⊢[wk∘wk],su[v1] : ⊢ T ∷ N ∷ Γ → T ∷ N ∷ Γ ⊢s (wk ∘ wk) , su (v 1) ∶ N ∷ Γ
⊢[wk∘wk],su[v1] ⊢TNΓ = F⇒C-s (Misc.⊢[wk∘wk],su[v1] (C⇒F-⊢ ⊢TNΓ))

qI,≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶ Se i → Δ ⊢ s ∶ T [ σ ] → Δ ⊢s q σ ∘ (I , s) ≈ σ , s ∶ T ∷ Γ
qI,≈, {_} {σ} {_} {_} {s} ⊢σ ⊢T ⊢s
  with ⊢Δ , _ ← presup-s ⊢σ = F⇒C-s-≈ (Subₚ.qσ∘[I,t]≈σ,t (C⇒F-⊢ ⊢Δ) (C⇒F-tm ⊢T) (C⇒F-s ⊢σ) (C⇒F-tm ⊢s))


[]-q-∘-, : ∀ {i} → S ∷ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ′ ⊢s τ ∶ Δ → Δ′ ⊢ t ∶ S [ σ ] [ τ ] →  Δ′ ⊢ T [ (σ ∘ τ) , t ] ≈ T [ q σ ] [ τ , t ] ∶ Se i
[]-q-∘-, {_} {_} {T} {_} {σ} {_} {τ} {t} ⊢T ⊢σ ⊢τ ⊢t
  with ⊢∷ ⊢Γ ⊢S ← proj₁ (presup-tm ⊢T)
     | ⊢Δ′ , ⊢Δ ← presup-s ⊢τ = begin
  T [ (σ ∘ τ) , t ]                      ≈⟨ []-cong-Se″ ⊢T (,-cong (s-≈-trans (∘-cong (s-≈-sym (p-, ⊢τ ⊢Sσ ⊢t)) (s-≈-refl ⊢σ)) (s-≈-sym (∘-assoc ⊢σ (s-wk ⊢SσΔ) ⊢τ,t))) ⊢S
                                                                   (≈-sym (≈-conv ([,]-v-ze ⊢τ ⊢Sσ ⊢t) ([∘]-Se ⊢S ⊢σ ⊢τ)))) ⟩
  T [ (σ ∘ wk ∘ τ , t) , v 0 [ τ , t ] ] ≈˘⟨ []-cong-Se″ ⊢T (,-∘ (s-∘ (s-wk ⊢SσΔ) ⊢σ) ⊢S (conv (vlookup ⊢SσΔ here) ([∘]-Se ⊢S ⊢σ (s-wk ⊢SσΔ))) ⊢τ,t) ⟩
  T [ q σ ∘ τ , t ]                      ≈˘⟨ [∘]-Se ⊢T ⊢qσ ⊢τ,t ⟩
  T [ q σ ] [ τ , t ]                    ∎
  where open ER
        ⊢qσ  = ⊢q ⊢σ ⊢S
        ⊢Sσ  = t[σ]-Se ⊢S ⊢σ
        ⊢τ,t = s-, ⊢τ ⊢Sσ ⊢t
        ⊢SσΔ = ⊢∷ ⊢Δ ⊢Sσ

[]-q-∘-,′ : ∀ {i} → S ∷ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶ S [ σ ] →  Δ ⊢ T [ σ , t ] ≈ T [ q σ ] [| t ] ∶ Se i
[]-q-∘-,′ ⊢T ⊢σ ⊢t
  with ⊢∷ ⊢Γ ⊢S ← proj₁ (presup-tm ⊢T) = ≈-trans ([]-cong-Se″ ⊢T (,-cong (s-≈-sym (∘-I ⊢σ)) ⊢S (≈-refl ⊢t))) ([]-q-∘-, ⊢T ⊢σ (s-I (proj₁ (presup-s ⊢σ))) (conv ⊢t (≈-sym ([I] ⊢Sσ))))
  where ⊢qσ = ⊢q ⊢σ ⊢S
        ⊢Sσ = t[σ]-Se ⊢S ⊢σ


wk,v0≈I : ⊢ T ∷ Γ →
          -----------------------------
          T ∷ Γ ⊢s wk , v 0 ≈ I ∶ T ∷ Γ
wk,v0≈I ⊢TΓ = F⇒C-s-≈ (Subₚ.wk,v0≈I (C⇒F-⊢ ⊢TΓ))

[wk,v0] : ∀ {i} → S ∷ Γ ⊢ T ∶ Se i → S ∷ Γ ⊢ T [ wk , v 0 ] ≈ T ∶ Se i
[wk,v0] ⊢T = ≈-trans ([]-cong-Se″ ⊢T (wk,v0≈I (proj₁ (presup-tm ⊢T)))) ([I] ⊢T)

I,∘≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶ Se i → Γ ⊢ t ∶ T → Δ ⊢s (I , t) ∘ σ ≈ σ , t [ σ ] ∶ T ∷ Γ
I,∘≈, ⊢σ ⊢T ⊢t = F⇒C-s-≈ (Subₚ.[I,t]∘σ≈σ,t[σ] (C⇒F-⊢ (⊢∷ (proj₁ (presup-tm ⊢t)) ⊢T)) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t))

I,ze∘≈, : Δ ⊢s σ ∶ Γ → Δ ⊢s (I , ze) ∘ σ ≈ σ , ze ∶ N ∷ Γ
I,ze∘≈, ⊢σ = F⇒C-s-≈ (Subₚ.[I,ze]∘σ≈σ,ze (C⇒F-⊢ (proj₂ (presup-s ⊢σ))) (C⇒F-s ⊢σ))

[]-I,-∘ : ∀ {i} → T ∷ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Γ ⊢ t ∶ T → Δ ⊢ S [| t ] [ σ ] ≈ S [ σ , t [ σ ] ] ∶ Se i
[]-I,-∘ {_} {_} {S} {_} {σ} {t} ⊢S ⊢σ ⊢t
  with ⊢∷ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [| t ] [ σ ]    ≈⟨ [∘]-Se ⊢S I,t ⊢σ ⟩
  S [ (I , t) ∘ σ ] ≈⟨ []-cong-Se″ ⊢S (I,∘≈, ⊢σ ⊢T ⊢t) ⟩
  S [ σ , t [ σ ] ] ∎
  where open ER
        I,t = ⊢I,t ⊢t

[]-,-∘ : ∀ {i} → T ∷ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶ T [ σ ] → Δ′ ⊢s τ ∶ Δ → Δ′ ⊢ S [ σ , t ] [ τ ] ≈ S [ (σ ∘ τ) , t [ τ ] ] ∶ Se i
[]-,-∘ {_} {_} {S} {_} {σ} {t} {_} {τ} ⊢S ⊢σ ⊢t ⊢τ
  with ⊢∷ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [ σ , t ] [ τ ]       ≈⟨ [∘]-Se ⊢S ⊢σ,t ⊢τ ⟩
  S [ (σ , t) ∘ τ ]       ≈⟨ []-cong-Se″ ⊢S (,-∘ ⊢σ ⊢T ⊢t ⊢τ) ⟩
  S [ (σ ∘ τ) , t [ τ ] ] ∎
  where open ER
        ⊢σ,t = s-, ⊢σ ⊢T ⊢t

[]-I,ze-∘ : ∀ {i} → N ∷ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ S [| ze ] [ σ ] ≈ S [ σ , ze ] ∶ Se i
[]-I,ze-∘ {_} {S} {_} {σ} ⊢S ⊢σ
  with ⊢∷ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [| ze ] [ σ ]    ≈⟨ [∘]-Se ⊢S I,t ⊢σ ⟩
  S [ (I , ze) ∘ σ ] ≈⟨ []-cong-Se″ ⊢S (I,ze∘≈, ⊢σ) ⟩
  S [ σ , ze ]  ∎
  where open ER
        I,t = ⊢I,t (ze-I ⊢Γ)

[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN : ⊢ T ∷ N ∷ Δ →
                             Γ ⊢s σ ∶ Δ →
                             (T [ q σ ]) ∷ N ∷ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ (wk ∘ wk) ∶ Δ
[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN ⊢TNΔ ⊢σ = F⇒C-s-≈ (Subₚ.[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-⊢ ⊢TNΔ) (C⇒F-s ⊢σ))

wk∘wk∘,, : ∀ {i j} →
           Γ ⊢s σ ∶ Δ →
           Δ ⊢ T ∶ Se i →
           T ∷ Δ ⊢ S ∶ Se j →
           Γ ⊢ t ∶ T [ σ ] →
           Γ ⊢ s ∶ S [ σ , t ] →
           Γ ⊢s wk ∘ wk ∘ ((σ , t) , s) ≈ σ ∶ Δ
wk∘wk∘,, ⊢σ ⊢T ⊢S ⊢t ⊢s = F⇒C-s-≈ (Subₚ.wk∘wk∘,, (C⇒F-⊢ (proj₂ (presup-s ⊢σ))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s))

⊢N[wk]n≈N : ∀ {n} i Δ → ⊢ Δ ++ Γ → len Δ ≡ n → Δ ++ Γ ⊢ N [wk]* n ≈ N ∶ Se i
⊢N[wk]n≈N i Δ ⊢ΔΓ eql = F⇒C-≈ (Misc.⊢N[wk]n≈N i Δ (C⇒F-⊢ ⊢ΔΓ) eql)

⊢vn∶N : ∀ {n} Δ → ⊢ Δ ++ N ∷ Γ → len Δ ≡ n → Δ ++ N ∷ Γ ⊢ v n ∶ N
⊢vn∶N Δ ⊢ΔNΓ eql = F⇒C-tm (Misc.⊢vn∶N Δ (C⇒F-⊢ ⊢ΔNΓ) eql)

wk∘qσ≈σ∘wk : ∀ {i} →
             Δ ⊢ T ∶ Se i →
             Γ ⊢s σ ∶ Δ →
             (T [ σ ]) ∷ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk ⊢T ⊢σ = F⇒C-s-≈ (Subₚ.wk∘qσ≈σ∘wk (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-tm ⊢T) (C⇒F-s ⊢σ))

wk∘qσ≈σ∘wk-N : Γ ⊢s σ ∶ Δ →
               N ∷ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk-N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ctxeq-s-≈ (∷-cong (⊢≈-refl ⊢Γ) (N-[] 0 ⊢σ)) (wk∘qσ≈σ∘wk (N-wf 0 ⊢Δ) ⊢σ)

-- q related properties
module _ {i} (⊢σ : Γ ⊢s σ ∶ Δ)
         (⊢T : Δ ⊢ T ∶ Se i)
         (⊢τ : Δ′ ⊢s τ ∶ Γ)
         (⊢t : Δ′ ⊢ t ∶ T [ σ ] [ τ ]) where

  private
    ⊢Γ   = proj₁ (presup-s ⊢σ)
    ⊢Tσ  = t[σ]-Se ⊢T ⊢σ
    ⊢TσΓ = ⊢∷ ⊢Γ ⊢Tσ
    ⊢wk  = s-wk ⊢TσΓ
    ⊢σwk = s-∘ ⊢wk ⊢σ
    ⊢qσ  = ⊢q ⊢σ ⊢T
    ⊢τ,t = s-, ⊢τ ⊢Tσ ⊢t

    eq = begin
      σ ∘ wk ∘ (τ , t) ≈⟨ ∘-assoc ⊢σ ⊢wk ⊢τ,t ⟩
      σ ∘ (wk ∘ (τ , t)) ≈⟨ ∘-cong (p-, ⊢τ ⊢Tσ ⊢t) (s-≈-refl ⊢σ) ⟩
      σ ∘ τ ∎
      where open SR

  q∘,≈∘, : Δ′ ⊢s q σ ∘ (τ , t) ≈ (σ ∘ τ) , t ∶ T ∷ Δ
  q∘,≈∘, = begin
    q σ ∘ (τ , t)                      ≈⟨ ,-∘ ⊢σwk ⊢T (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ ⊢wk)) ⊢τ,t ⟩
    (σ ∘ wk ∘ (τ , t)) , v 0 [ τ , t ] ≈⟨ ,-cong eq ⊢T (≈-conv ([,]-v-ze ⊢τ ⊢Tσ ⊢t) (≈-trans ([∘]-Se ⊢T ⊢σ ⊢τ) (≈-sym ([]-cong-Se″ ⊢T eq)))) ⟩
    (σ ∘ τ) , t                        ∎
    where open SR

  []-q-, : T ∷ Δ ⊢ s ∶ S →
           Δ′ ⊢ s [ q σ ] [ τ , t ] ≈ s [ (σ ∘ τ) , t ] ∶ S [ (σ ∘ τ) , t ]
  []-q-, {s} ⊢s
    with _ , _ , ⊢S ← presup-tm ⊢s = begin
    s [ q σ ] [ τ , t ] ≈˘⟨ ≈-conv ([∘] ⊢τ,t ⊢qσ ⊢s) ([]-cong-Se″ ⊢S q∘,≈∘,) ⟩
    s [ q σ ∘ (τ , t) ] ≈⟨ ≈-conv ([]-cong (≈-refl ⊢s) q∘,≈∘,) ([]-cong-Se″ ⊢S q∘,≈∘,) ⟩
    s [ (σ ∘ τ) , t ]   ∎
    where open ER


module _ (⊢σ : Δ ⊢s σ ∶ Γ) (⊢τ : Δ′ ⊢s τ ∶ Δ) where
  private
    ⊢Δ  = proj₁ (presup-s ⊢σ)
    ⊢Γ  = proj₂ (presup-s ⊢σ)
    ⊢Δ′ = proj₁ (presup-s ⊢τ)

  q∘q-N : N ∷ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ N ∷ Γ
  q∘q-N = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ (N-wf 0 ⊢Γ) ⊢τwk
                                   (conv (vlookup ⊢NΔ′ here)
                                         (≈-trans (N-[] 0 ⊢wk) (≈-sym (≈-trans ([]-cong-Se′ (N-[] 0 ⊢σ) ⊢τwk) (N-[] 0 ⊢τwk))))) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) (N-wf 0 ⊢Γ)
                                    (≈-refl (conv (vlookup ⊢NΔ′ here) (≈-trans (N-[] 0 ⊢wk) (≈-sym (N-[] 0 (s-∘ ⊢wk (s-∘ ⊢τ ⊢σ))))))) ⟩
    q (σ ∘ τ)            ∎
    where open SR
          ⊢NΔ′ = ⊢∷ ⊢Δ′ (N-wf 0 ⊢Δ′)
          ⊢wk = s-wk ⊢NΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ


  q∘q : ∀ {i} → Γ ⊢ T ∶ Se i → (T [ σ ∘ τ ]) ∷ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ T ∷ Γ
  q∘q {T} {i} ⊢T = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ ⊢T ⊢τwk (conv (vlookup ⊢TΔ′ here) eq) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) ⊢T
                                    (≈-refl (conv (vlookup ⊢TΔ′ here) ([∘]-Se ⊢T ⊢στ ⊢wk))) ⟩
    q (σ ∘ τ)            ∎
    where ⊢στ = s-∘ ⊢τ ⊢σ
          ⊢TΔ′ = ⊢∷ ⊢Δ′ (t[σ]-Se ⊢T ⊢στ)
          ⊢wk  = s-wk ⊢TΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ
          eq : (T [ σ ∘ τ ]) ∷ Δ′ ⊢ T [ σ ∘ τ ] [ wk ] ≈ T [ σ ] [ τ ∘ wk ] ∶ Se i
          eq = let open ER in begin
            T [ σ ∘ τ ] [ wk ] ≈⟨ [∘]-Se ⊢T ⊢στ ⊢wk ⟩
            T [ σ ∘ τ ∘ wk ] ≈⟨ []-cong-Se″ ⊢T (∘-assoc ⊢σ ⊢τ ⊢wk) ⟩
            T [ σ ∘ (τ ∘ wk) ] ≈˘⟨ [∘]-Se ⊢T ⊢σ ⊢τwk ⟩
            T [ σ ] [ τ ∘ wk ] ∎

          open SR

-- Nat related helpers
module _ {i} (⊢T : N ∷ Δ ⊢ T ∶ Se i) (⊢σ : Γ ⊢s σ ∶ Δ) where
  private
    ⊢NΔ  = proj₁ (presup-tm ⊢T)
    ⊢TNΔ = ⊢∷ ⊢NΔ ⊢T
    ⊢Γ   = proj₁ (presup-s ⊢σ)

  rec-β-su-T-swap : (T [ q σ ]) ∷ N ∷ Γ ⊢ T [ (wk ∘ wk) , su (v 1) ] [ q (q σ) ] ≈ T [ q σ ] [ (wk ∘ wk) , su (v 1) ] ∶ Se i
  rec-β-su-T-swap = F⇒C-≈ (Subₚ.rec-β-su-T-swap (C⇒F-⊢ ⊢Γ) (C⇒F-⊢ ⊢TNΔ) (C⇒F-s ⊢σ))

module NatTyping {i} (⊢T : N ∷ Γ ⊢ T ∶ Se i) (⊢σ : Δ ⊢s σ ∶ Γ) where

  ⊢Δ     = proj₁ (presup-s ⊢σ)
  ⊢Γ     = proj₂ (presup-s ⊢σ)
  ⊢qσ    = ⊢q-N ⊢σ
  ⊢qqσ   = ⊢q ⊢qσ ⊢T
  ⊢Tqσ   = t[σ]-Se ⊢T ⊢qσ
  ⊢NΓ    = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
  ⊢TNΓ   = ⊢∷ ⊢NΓ ⊢T
  ⊢NΔ    = ⊢∷ ⊢Δ (N-wf 0 ⊢Δ)
  ⊢TqσNΔ = ⊢∷ ⊢NΔ ⊢Tqσ
  ⊢wk    = s-wk ⊢NΓ
  ⊢wk′   = s-wk ⊢TNΓ
  ⊢wkwk  = s-∘ ⊢wk′ ⊢wk
