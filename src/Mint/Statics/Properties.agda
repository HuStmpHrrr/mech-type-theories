{-# OPTIONS --without-K --safe #-}

-- The overall properties of the Concise formulation which are used by later modules.
--
-- Many properties have been proved in the Full formulation. We can use the
-- equivalence between the Full and Concise formulation to bring existing conclusion
-- to this file so later modules can conveniently use these results.
module Mint.Statics.Properties where

open import Lib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

import Mint.Statics.Full as F
open import Mint.Statics.Concise as C
open import Mint.Statics.Equiv
import Mint.Statics.Presup as Presup
import Mint.Statics.Refl as Refl
import Mint.Statics.Misc as Misc
import Mint.Statics.PER as PER
import Mint.Statics.CtxEquiv as CtxEquiv
import Mint.Statics.Properties.Contexts as Ctxₚ
import Mint.Statics.Properties.Substs as Subₚ
open import Mint.Statics.Properties.Ops as Ops
  using ( O-I
        ; O-∘
        ; O-p
        ; O-,
        ; O-+
        ; I-∥
        ; ∘-∥
        ; ∥-+
        )
  public
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
               len (head Γ) ≡ len (head Δ)
⊢≈⇒len-head≡ []-≈            = refl
⊢≈⇒len-head≡ (κ-cong Γ≈Δ)    = refl
⊢≈⇒len-head≡ (∺-cong Γ≈Δ T≈) = cong suc (⊢≈⇒len-head≡ Γ≈Δ)

≈⇒∥⇒∥ : ∀ Ψs →
        ⊢ Ψs ++⁺ Γ ≈ Δ →
        -----------------
        ∃₂ λ Ψs′ Δ′ → Δ ≡ Ψs′ ++⁺ Δ′ × len Ψs ≡ len Ψs′ × ⊢ Γ ≈ Δ′
≈⇒∥⇒∥ Ψs ΨsΓ≈Δ
  with Ψs′ , Δ′ , eq , eql , Γ≈Δ′ ← Ctxₚ.≈⇒∥⇒∥ Ψs (C⇒F-⊢≈ ΨsΓ≈Δ) = Ψs′ , Δ′ , eq , eql , F⇒C-⊢≈ Γ≈Δ′

⊢⇒∥⊢ : ∀ Ψs →
       ⊢ Ψs ++⁺ Γ →
       ------------
       ⊢ Γ
⊢⇒∥⊢ Ψs ⊢ΨsΓ = F⇒C-⊢ (Ctxₚ.⊢⇒∥⊢ Ψs (C⇒F-⊢ ⊢ΨsΓ))

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

-------------------------------------------------
-- Properties of truncation and truncation offset

O-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           -----------------
           O σ n ≡ O σ′ n
O-resp-≈ n σ≈σ′ = Ops.O-resp-≈ n (C⇒F-s-≈ σ≈σ′)

O-<-len : ∀ n →
          Γ ⊢s σ ∶ Δ →
          n < len Δ →
          --------------
          O σ n < len Γ
O-<-len n ⊢σ n<l = Ops.O-<-len n (C⇒F-s ⊢σ) n<l

≈O-<-len : ∀ n →
           Γ ⊢s σ ≈ τ ∶ Δ →
           n < len Δ →
           --------------
           O σ n < len Γ
≈O-<-len n σ≈τ n<l = Ops.≈O-<-len n (C⇒F-s-≈ σ≈τ) n<l

∥-⊢s′ : ∀ Ψs →
        Γ ⊢s σ ∶ Ψs ++⁺ Δ →
        ---------------------
        ∃₂ λ Ψs′ Γ′ → Γ ≡ Ψs′ ++⁺ Γ′
                    × len Ψs′ ≡ O σ (len Ψs)
                    × Γ′ ⊢s σ ∥ len Ψs ∶ Δ
∥-⊢s′ Ψs ⊢σ
  with Ψs′ , Γ′ , eq , eql , ⊢σ∥ ← Ops.∥-⊢s′ Ψs (C⇒F-s ⊢σ) = Ψs′ , Γ′ , eq , eql , F⇒C-s ⊢σ∥

∥-⊢s″ : ∀ Ψs Ψs′ →
        Ψs ++⁺ Γ ⊢s σ ∶ Ψs′ ++⁺ Δ →
        len Ψs ≡ O σ (len Ψs′) →
        ----------------------------
        Γ ⊢s σ ∥ len Ψs′ ∶ Δ
∥-⊢s″ Ψs Ψs′ ⊢σ Ψs≡Oσ
  with Ψs′ , Γ′ , eq , eql , ⊢σ∥ ← Ops.∥-⊢s′ Ψs′ (C⇒F-s ⊢σ)
    rewrite ++⁺-cancelˡ′ Ψs Ψs′ eq (trans Ψs≡Oσ (sym eql)) = F⇒C-s ⊢σ∥


∥-resp-≈′ : ∀ Ψs →
            Γ ⊢s σ ≈ σ′ ∶ Ψs ++⁺ Δ →
            --------------------------------------------------
            ∃₂ λ Ψs′ Γ′ → Γ ≡ Ψs′ ++⁺ Γ′
                        × len Ψs′ ≡ O σ (len Ψs)
                        × Γ′ ⊢s σ ∥ len Ψs ≈ σ′ ∥ len Ψs ∶ Δ
∥-resp-≈′ Ψs σ≈σ′
  with Ψs′ , Γ′ , eq , eql , σ≈σ′∥ ← Ops.∥-resp-≈′ Ψs (C⇒F-s-≈ σ≈σ′) = Ψs′ , Γ′ , eq , eql , F⇒C-s-≈ σ≈σ′∥

∥-resp-≈″ : ∀ Ψs Ψs′ →
            Ψs ++⁺ Γ ⊢s σ ≈ σ′ ∶ Ψs′ ++⁺ Δ →
            len Ψs ≡ O σ (len Ψs′) →
            --------------------------------------------------
            Γ ⊢s σ ∥ len Ψs′ ≈ σ′ ∥ len Ψs′ ∶ Δ
∥-resp-≈″ Ψs Ψs′ σ≈σ′ Ψs≡Oσ
  with Ψs′ , Γ′ , eq , eql , σ≈σ′∥ ← Ops.∥-resp-≈′ Ψs′ (C⇒F-s-≈ σ≈σ′)
    rewrite ++⁺-cancelˡ′ Ψs Ψs′ eq (trans Ψs≡Oσ (sym eql)) = F⇒C-s-≈ σ≈σ′∥

------
-- PER

Exp≈-isPER : IsPartialEquivalence (Γ ⊢_≈_∶ T)
Exp≈-isPER {Γ} {T} = record
  { sym   = ≈-sym
  ; trans = ≈-trans
  }

Exp≈-PER : Ctxs → Typ → PartialSetoid _ _
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

Substs≈-PER : Ctxs → Ctxs → PartialSetoid _ _
Substs≈-PER Γ Δ = record
  { Carrier              = Substs
  ; _≈_                  = Γ ⊢s_≈_∶ Δ
  ; isPartialEquivalence = Substs≈-isPER
  }

module SR {Γ Δ} = PS (Substs≈-PER Γ Δ)

---------------------
-- other easy helpers

p-∘ : Γ ⊢s σ ∶ T ∺ Δ →
      Γ′ ⊢s τ ∶ Γ →
      ------------------------------
      Γ′ ⊢s p (σ ∘ τ) ≈ p σ ∘ τ ∶ Δ
p-∘ ⊢σ ⊢τ = s-≈-sym (∘-assoc (s-wk (proj₂ (presup-s ⊢σ))) ⊢σ ⊢τ)

n∶T[wk]n∈!ΨTΓ : ∀ {n} →
                ⊢ Ψ ++⁻ T ∺ Γ →
                len Ψ ≡ n →
                ------------------------------------
                n ∶ T [wk]* (suc n) ∈! Ψ ++⁻ T ∺ Γ
n∶T[wk]n∈!ΨTΓ ⊢ΨTΓ eq = Misc.n∶T[wk]n∈!ΨTΓ (C⇒F-⊢ ⊢ΨTΓ) eq

⊢vn∶T[wk]suc[n] : ∀ {n} →
                  ⊢ Ψ ++⁻ T ∺ Γ →
                  len Ψ ≡ n →
                  -------------------------------------
                  Ψ ++⁻ T ∺ Γ ⊢ v n ∶ T [wk]* (suc n)
⊢vn∶T[wk]suc[n] ⊢ΨTΓ eq = vlookup ⊢ΨTΓ (n∶T[wk]n∈!ΨTΓ ⊢ΨTΓ eq)

-- A closed term cannot be neutral.

no-closed-Ne-gen : Γ ⊢ t ∶ T →
                   Γ ≡ [] ∷ [] →
                   ----------------
                   ¬ (t ≡ Ne⇒Exp u)
no-closed-Ne-gen {_} {_} {_} {v x} (vlookup _ ()) refl refl
no-closed-Ne-gen {_} {_} {_} {rec T z s u} (N-E _ _ _ ⊢u) eq refl  = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {u $ n} (Λ-E ⊢u _) eq refl            = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {unbox x u} (□-E [] ⊢u _ _) refl refl = no-closed-Ne-gen ⊢u refl refl
no-closed-Ne-gen {_} {_} {_} {_} (cumu ⊢u) eq refl                 = no-closed-Ne-gen ⊢u eq refl
no-closed-Ne-gen {_} {_} {_} {_} (conv ⊢u _) eq refl               = no-closed-Ne-gen ⊢u eq refl


no-closed-Ne : ¬ ([] ∷ [] ⊢ Ne⇒Exp u ∶ T)
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

[I；1]-inv : [] ∷⁺ Γ ⊢ t [ I ； 1 ] ∶ T → [] ∷⁺ Γ ⊢ t ∶ T
[I；1]-inv (t[σ] ⊢t ⊢I；1) = helper′ ⊢t ⊢I；1
  where helper : Γ′ ⊢s I ； 1 ∶ Δ → Γ′ ≡ [] ∷⁺ Γ → ⊢ Δ ≈ [] ∷⁺ Γ
        helper (s-； ([] ∷ []) ⊢σ (⊢κ ⊢Γ) _) refl = κ-cong (⊢≈-sym (⊢I-inv ⊢σ))
        helper (s-conv ⊢σ Δ′≈Δ) eq                = ⊢≈-trans (⊢≈-sym Δ′≈Δ) (helper ⊢σ eq)
        helper′ : Δ ⊢ t ∶ T → [] ∷⁺ Γ ⊢s I ； 1 ∶ Δ → [] ∷⁺ Γ ⊢ t ∶ sub T (I ； 1)
        helper′ ⊢t ⊢I；1
          with ⊢t ← ctxeq-tm (helper ⊢I；1 refl) ⊢t
            with ⊢κ ⊢Γ , _ , ⊢T ← presup-tm ⊢t = conv ⊢t (≈-sym (≈-trans ([]-cong-Se″ ⊢T (s-≈-sym (；-ext (s-I (⊢κ ⊢Γ))))) ([I] ⊢T)))
[I；1]-inv (cumu ⊢t)      = cumu ([I；1]-inv ⊢t)
[I；1]-inv (conv ⊢t ≈T)  = conv ([I；1]-inv ⊢t) ≈T

⊢wk-inv : T ∺ Γ ⊢s wk ∶ Δ → ⊢ Γ ≈ Δ
⊢wk-inv (s-wk (⊢∺ ⊢Γ _)) = ⊢≈-refl ⊢Γ
⊢wk-inv (s-conv ⊢wk ≈Δ)  = ⊢≈-trans (⊢wk-inv ⊢wk) ≈Δ

inv-□-wf : Γ ⊢ □ T ∶ T′ →
           ----------------
           [] ∷⁺ Γ ⊢ T
inv-□-wf (□-wf ⊢T)    = _ , ⊢T
inv-□-wf (cumu ⊢□T)   = inv-□-wf ⊢□T
inv-□-wf (conv ⊢□T _) = inv-□-wf ⊢□T

inv-Π-wf : Γ ⊢ Π S T ∶ T′ →
           ----------------
           S ∺ Γ ⊢ T
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

[,]-v-ze-Se : ∀ {i} →
              Γ ⊢s σ ∶ Δ →
              Γ ⊢ s ∶ Se i →
              -----------------------------------
              Γ ⊢ v 0 [ σ , s ] ≈ s ∶ Se i
[,]-v-ze-Se ⊢σ ⊢s = ≈-conv ([,]-v-ze ⊢σ (Se-wf _ (proj₂ (presup-s ⊢σ))) (conv ⊢s (≈-sym (Se-[] _ ⊢σ)))) (Se-[] _ ⊢σ)

⊢q : ∀ {i} → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∺ Γ ⊢s q σ ∶ T ∺ Δ
⊢q ⊢σ ⊢T = F⇒C-s (Misc.⊢q (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢T))

⊢q-N : Γ ⊢s σ ∶ Δ → N ∺ Γ ⊢s q σ ∶ N ∺ Δ
⊢q-N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = F⇒C-s (Misc.⊢q-N (C⇒F-⊢ ⊢Γ) (C⇒F-⊢ ⊢Δ) (C⇒F-s ⊢σ))

q-cong : ∀ {i} → Γ ⊢s σ ≈ σ′ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∺ Γ ⊢s q σ ≈ q σ′ ∶ T ∺ Δ
q-cong {_} {σ} {σ′} {_} {T} σ≈σ′ ⊢T
  with ⊢Γ , ⊢σ , _ ← presup-s-≈ σ≈σ′ = ,-cong (∘-cong (wk-≈ ⊢TσΓ) σ≈σ′) ⊢T (≈-refl (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΓ))))
  where open ER
        ⊢Tσ  = t[σ]-Se ⊢T ⊢σ
        ⊢TσΓ = ⊢∺ ⊢Γ ⊢Tσ

⊢I,t : Γ ⊢ t ∶ T → Γ ⊢s I , t ∶ T ∺ Γ
⊢I,t ⊢t
  with ⊢Γ , _ , ⊢T ← presup-tm ⊢t = F⇒C-s (Misc.⊢I,t (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t))

---------------
-- The rest of helpers from this point are specialized helpers which we use in multiple places.
-- One can safely omit these helpers.

⊢I,ze : ⊢ Γ → Γ ⊢s I , ze ∶ N ∺ Γ
⊢I,ze ⊢Γ = ⊢I,t (ze-I ⊢Γ)

⊢[wk∘wk],su[v1] : ⊢ T ∺ N ∺ Γ → T ∺ N ∺ Γ ⊢s (wk ∘ wk) , su (v 1) ∶ N ∺ Γ
⊢[wk∘wk],su[v1] ⊢TNΓ = F⇒C-s (Misc.⊢[wk∘wk],su[v1] (C⇒F-⊢ ⊢TNΓ))

qI,≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶ Se i → Δ ⊢ s ∶ T [ σ ] → Δ ⊢s q σ ∘ (I , s) ≈ σ , s ∶ T ∺ Γ
qI,≈, {_} {σ} {_} {_} {s} ⊢σ ⊢T ⊢s
  with ⊢Δ , _ ← presup-s ⊢σ = F⇒C-s-≈ (Subₚ.qσ∘[I,t]≈σ,t (C⇒F-⊢ ⊢Δ) (C⇒F-tm ⊢T) (C⇒F-s ⊢σ) (C⇒F-tm ⊢s))

[]-∘-； : ∀ {i} Ψs → ⊢ Ψs ++⁺ Δ′ → [] ∷⁺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ′ ⊢s τ ∶ Δ → Ψs ++⁺ Δ′ ⊢ T [ (σ ∘ τ) ； len Ψs ] ≈ T [ σ ； 1 ] [ τ ； len Ψs ] ∶ Se i
[]-∘-； {Δ′} {_} {T} {_} {σ} {τ} Ψs ⊢ΨsΔ′ ⊢T ⊢σ ⊢τ = begin
  T [ (σ ∘ τ) ； len Ψs ]      ≈˘⟨ subst (λ n → Ψs ++⁺ Δ′ ⊢ sub T (σ ； 1 ∘ τ ； len Ψs) ≈ sub T ((σ ∘ τ) ； n) ∶ Se _)
                                        (+-identityʳ (len Ψs))
                                        ([]-cong-Se″ ⊢T (；-∘ L.[ [] ] ⊢σ ⊢τ； refl)) ⟩
  T [ σ ； 1 ∘ τ ； len Ψs ]   ≈˘⟨ [∘]-Se ⊢T (s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl) ⊢τ； ⟩
  T [ σ ； 1 ] [ τ ； len Ψs ] ∎
  where open ER
        ⊢Δ = proj₁ (presup-s ⊢σ)
        ⊢τ； = s-； Ψs ⊢τ ⊢ΨsΔ′ refl

[]-∘-；′ : ∀ {i} Ψs → ⊢ Ψs ++⁺ Δ → [] ∷⁺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Ψs ++⁺ Δ ⊢ T [ σ ； len Ψs ] ≈ T [ σ ； 1 ] [ I ； len Ψs ] ∶ Se i
[]-∘-；′ {Δ} {_} {T} {σ} Ψs ⊢ΨsΔ ⊢T ⊢σ = begin
  T [ σ ； len Ψs ]            ≈⟨ []-cong-Se″ ⊢T (；-cong Ψs (s-≈-sym (∘-I ⊢σ)) ⊢ΨsΔ refl) ⟩
  T [ (σ ∘ I) ； len Ψs ]      ≈˘⟨ subst (λ n → Ψs ++⁺ Δ ⊢ sub T (σ ； 1 ∘ I ； len Ψs) ≈ sub T ((σ ∘ I) ； n) ∶ Se _)
                                        (+-identityʳ (len Ψs))
                                        ([]-cong-Se″ ⊢T (；-∘ L.[ [] ] ⊢σ ⊢I； refl)) ⟩
  T [ σ ； 1 ∘ I ； len Ψs ]   ≈˘⟨ [∘]-Se ⊢T (s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl) ⊢I； ⟩
  T [ σ ； 1 ] [ I ； len Ψs ] ∎
  where open ER
        ⊢Δ = proj₁ (presup-s ⊢σ)
        ⊢I； = s-； Ψs (s-I ⊢Δ) ⊢ΨsΔ refl

[]-；-∘ : ∀ {i} Ψs → [] ∷⁺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ′ ⊢s τ ∶ Ψs ++⁺ Δ → Δ′ ⊢ T [ (σ ∘ τ ∥ len Ψs) ； O τ (len Ψs) ] ≈ T [ σ ； len Ψs ] [ τ ] ∶ Se i
[]-；-∘ {_} {T} {_} {σ} {_} {τ} Ψs ⊢T ⊢σ ⊢τ = begin
  T [ (σ ∘ τ ∥ len Ψs) ； O τ (len Ψs) ] ≈˘⟨ []-cong-Se″ ⊢T (；-∘ Ψs ⊢σ ⊢τ refl) ⟩
  T [ σ ； len Ψs ∘ τ ]                  ≈˘⟨ [∘]-Se ⊢T (s-； Ψs ⊢σ ⊢ΨsΔ refl) ⊢τ ⟩
  T [ σ ； len Ψs ] [ τ ]                ∎
  where open ER
        ⊢ΨsΔ = proj₂ (presup-s ⊢τ)

[]-q-∘-, : ∀ {i} → S ∺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ′ ⊢s τ ∶ Δ → Δ′ ⊢ t ∶ S [ σ ] [ τ ] →  Δ′ ⊢ T [ (σ ∘ τ) , t ] ≈ T [ q σ ] [ τ , t ] ∶ Se i
[]-q-∘-, {_} {_} {T} {_} {σ} {_} {τ} {t} ⊢T ⊢σ ⊢τ ⊢t
  with ⊢∺ ⊢Γ ⊢S ← proj₁ (presup-tm ⊢T)
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
        ⊢SσΔ = ⊢∺ ⊢Δ ⊢Sσ

[]-q-∘-,′ : ∀ {i} → S ∺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶ S [ σ ] →  Δ ⊢ T [ σ , t ] ≈ T [ q σ ] [| t ] ∶ Se i
[]-q-∘-,′ ⊢T ⊢σ ⊢t
  with ⊢∺ ⊢Γ ⊢S ← proj₁ (presup-tm ⊢T) = ≈-trans ([]-cong-Se″ ⊢T (,-cong (s-≈-sym (∘-I ⊢σ)) ⊢S (≈-refl ⊢t))) ([]-q-∘-, ⊢T ⊢σ (s-I (proj₁ (presup-s ⊢σ))) (conv ⊢t (≈-sym ([I] ⊢Sσ))))
  where ⊢qσ = ⊢q ⊢σ ⊢S
        ⊢Sσ = t[σ]-Se ⊢S ⊢σ

I；1≈I : ⊢ Γ → [] ∷⁺ Γ ⊢s I ； 1 ≈ I ∶ [] ∷⁺ Γ
I；1≈I ⊢Γ = s-≈-sym (；-ext (s-I (⊢κ ⊢Γ)))

[I；1] : ∀ {i} → [] ∷⁺ Γ ⊢ T ∶ Se i → [] ∷⁺ Γ ⊢ T [ I ； 1 ] ≈ T ∶ Se i
[I；1] ⊢T
  with ⊢κ ⊢Γ ← proj₁ (presup-tm ⊢T) = ≈-trans ([]-cong-Se″ ⊢T (I；1≈I ⊢Γ)) ([I] ⊢T)

wk,v0≈I : ⊢ T ∺ Γ →
          -----------------------------
          T ∺ Γ ⊢s wk , v 0 ≈ I ∶ T ∺ Γ
wk,v0≈I ⊢TΓ = F⇒C-s-≈ (Subₚ.wk,v0≈I (C⇒F-⊢ ⊢TΓ))

[wk,v0] : ∀ {i} → S ∺ Γ ⊢ T ∶ Se i → S ∺ Γ ⊢ T [ wk , v 0 ] ≈ T ∶ Se i
[wk,v0] ⊢T = ≈-trans ([]-cong-Se″ ⊢T (wk,v0≈I (proj₁ (presup-tm ⊢T)))) ([I] ⊢T)

I,∘≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶ Se i → Γ ⊢ t ∶ T → Δ ⊢s (I , t) ∘ σ ≈ σ , t [ σ ] ∶ T ∺ Γ
I,∘≈, ⊢σ ⊢T ⊢t = F⇒C-s-≈ (Subₚ.[I,t]∘σ≈σ,t[σ] (C⇒F-⊢ (⊢∺ (proj₁ (presup-tm ⊢t)) ⊢T)) (C⇒F-s ⊢σ) (C⇒F-tm ⊢t))

I,ze∘≈, : Δ ⊢s σ ∶ Γ → Δ ⊢s (I , ze) ∘ σ ≈ σ , ze ∶ N ∺ Γ
I,ze∘≈, ⊢σ = F⇒C-s-≈ (Subₚ.[I,ze]∘σ≈σ,ze (C⇒F-⊢ (proj₂ (presup-s ⊢σ))) (C⇒F-s ⊢σ))

[]-I,-∘ : ∀ {i} → T ∺ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Γ ⊢ t ∶ T → Δ ⊢ S [| t ] [ σ ] ≈ S [ σ , t [ σ ] ] ∶ Se i
[]-I,-∘ {_} {_} {S} {_} {σ} {t} ⊢S ⊢σ ⊢t
  with ⊢∺ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [| t ] [ σ ]    ≈⟨ [∘]-Se ⊢S I,t ⊢σ ⟩
  S [ (I , t) ∘ σ ] ≈⟨ []-cong-Se″ ⊢S (I,∘≈, ⊢σ ⊢T ⊢t) ⟩
  S [ σ , t [ σ ] ] ∎
  where open ER
        I,t = ⊢I,t ⊢t

[]-,-∘ : ∀ {i} → T ∺ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶ T [ σ ] → Δ′ ⊢s τ ∶ Δ → Δ′ ⊢ S [ σ , t ] [ τ ] ≈ S [ (σ ∘ τ) , t [ τ ] ] ∶ Se i
[]-,-∘ {_} {_} {S} {_} {σ} {t} {_} {τ} ⊢S ⊢σ ⊢t ⊢τ
  with ⊢∺ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [ σ , t ] [ τ ]       ≈⟨ [∘]-Se ⊢S ⊢σ,t ⊢τ ⟩
  S [ (σ , t) ∘ τ ]       ≈⟨ []-cong-Se″ ⊢S (,-∘ ⊢σ ⊢T ⊢t ⊢τ) ⟩
  S [ (σ ∘ τ) , t [ τ ] ] ∎
  where open ER
        ⊢σ,t = s-, ⊢σ ⊢T ⊢t

[]-I,ze-∘ : ∀ {i} → N ∺ Γ ⊢ S ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ S [| ze ] [ σ ] ≈ S [ σ , ze ] ∶ Se i
[]-I,ze-∘ {_} {S} {_} {σ} ⊢S ⊢σ
  with ⊢∺ ⊢Γ ⊢T ← proj₁ (presup-tm ⊢S) = begin
  S [| ze ] [ σ ]    ≈⟨ [∘]-Se ⊢S I,t ⊢σ ⟩
  S [ (I , ze) ∘ σ ] ≈⟨ []-cong-Se″ ⊢S (I,ze∘≈, ⊢σ) ⟩
  S [ σ , ze ]  ∎
  where open ER
        I,t = ⊢I,t (ze-I ⊢Γ)

[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN : ⊢ T ∺ N ∺ Δ →
                             Γ ⊢s σ ∶ Δ →
                             (T [ q σ ]) ∺ N ∺ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ (wk ∘ wk) ∶ Δ
[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN ⊢TNΔ ⊢σ = F⇒C-s-≈ (Subₚ.[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-⊢ ⊢TNΔ) (C⇒F-s ⊢σ))

wk∘wk∘,, : ∀ {i j} →
           Γ ⊢s σ ∶ Δ →
           Δ ⊢ T ∶ Se i →
           T ∺ Δ ⊢ S ∶ Se j →
           Γ ⊢ t ∶ T [ σ ] →
           Γ ⊢ s ∶ S [ σ , t ] →
           Γ ⊢s wk ∘ wk ∘ ((σ , t) , s) ≈ σ ∶ Δ
wk∘wk∘,, ⊢σ ⊢T ⊢S ⊢t ⊢s = F⇒C-s-≈ (Subₚ.wk∘wk∘,, (C⇒F-⊢ (proj₂ (presup-s ⊢σ))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢S) (C⇒F-tm ⊢t) (C⇒F-tm ⊢s))

⊢N[wk]n≈N : ∀ {n} i Ψ → ⊢ Ψ ++⁻ Γ → len Ψ ≡ n → Ψ ++⁻ Γ ⊢ N [wk]* n ≈ N ∶ Se i
⊢N[wk]n≈N i Ψ ⊢ΨΓ eql = F⇒C-≈ (Misc.⊢N[wk]n≈N i Ψ (C⇒F-⊢ ⊢ΨΓ) eql)

⊢vn∶N : ∀ {n} Ψ → ⊢ Ψ ++⁻ N ∺ Γ → len Ψ ≡ n → Ψ ++⁻ N ∺ Γ ⊢ v n ∶ N
⊢vn∶N Ψ ⊢ΨNΓ eql = F⇒C-tm (Misc.⊢vn∶N Ψ (C⇒F-⊢ ⊢ΨNΓ) eql)

wk∘qσ≈σ∘wk : ∀ {i} →
             Δ ⊢ T ∶ Se i →
             Γ ⊢s σ ∶ Δ →
             (T [ σ ]) ∺ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk ⊢T ⊢σ = F⇒C-s-≈ (Subₚ.wk∘qσ≈σ∘wk (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-tm ⊢T) (C⇒F-s ⊢σ))

wk∘qσ≈σ∘wk-N : Γ ⊢s σ ∶ Δ →
               N ∺ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk-N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ctxeq-s-≈ (∺-cong (⊢≈-refl ⊢Γ) (N-[] 0 ⊢σ)) (wk∘qσ≈σ∘wk (N-wf 0 ⊢Δ) ⊢σ)

-- q related properties
module _ {i} (⊢σ : Γ ⊢s σ ∶ Δ)
         (⊢T : Δ ⊢ T ∶ Se i)
         (⊢τ : Δ′ ⊢s τ ∶ Γ)
         (⊢t : Δ′ ⊢ t ∶ T [ σ ] [ τ ]) where

  private
    ⊢Γ   = proj₁ (presup-s ⊢σ)
    ⊢Tσ  = t[σ]-Se ⊢T ⊢σ
    ⊢TσΓ = ⊢∺ ⊢Γ ⊢Tσ
    ⊢wk  = s-wk ⊢TσΓ
    ⊢σwk = s-∘ ⊢wk ⊢σ
    ⊢qσ  = ⊢q ⊢σ ⊢T
    ⊢τ,t = s-, ⊢τ ⊢Tσ ⊢t

    eq = begin
      σ ∘ wk ∘ (τ , t) ≈⟨ ∘-assoc ⊢σ ⊢wk ⊢τ,t ⟩
      σ ∘ (wk ∘ (τ , t)) ≈⟨ ∘-cong (p-, ⊢τ ⊢Tσ ⊢t) (s-≈-refl ⊢σ) ⟩
      σ ∘ τ ∎
      where open SR

  q∘,≈∘, : Δ′ ⊢s q σ ∘ (τ , t) ≈ (σ ∘ τ) , t ∶ T ∺ Δ
  q∘,≈∘, = begin
    q σ ∘ (τ , t)                      ≈⟨ ,-∘ ⊢σwk ⊢T (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ ⊢wk)) ⊢τ,t ⟩
    (σ ∘ wk ∘ (τ , t)) , v 0 [ τ , t ] ≈⟨ ,-cong eq ⊢T (≈-conv ([,]-v-ze ⊢τ ⊢Tσ ⊢t) (≈-trans ([∘]-Se ⊢T ⊢σ ⊢τ) (≈-sym ([]-cong-Se″ ⊢T eq)))) ⟩
    (σ ∘ τ) , t                        ∎
    where open SR

  []-q-, : T ∺ Δ ⊢ s ∶ S →
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

  q∘q-N : N ∺ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ N ∺ Γ
  q∘q-N = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ (N-wf 0 ⊢Γ) ⊢τwk
                                   (conv (vlookup ⊢NΔ′ here)
                                         (≈-trans (N-[] 0 ⊢wk) (≈-sym (≈-trans ([]-cong-Se′ (N-[] 0 ⊢σ) ⊢τwk) (N-[] 0 ⊢τwk))))) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) (N-wf 0 ⊢Γ)
                                    (≈-refl (conv (vlookup ⊢NΔ′ here) (≈-trans (N-[] 0 ⊢wk) (≈-sym (N-[] 0 (s-∘ ⊢wk (s-∘ ⊢τ ⊢σ))))))) ⟩
    q (σ ∘ τ)            ∎
    where open SR
          ⊢NΔ′ = ⊢∺ ⊢Δ′ (N-wf 0 ⊢Δ′)
          ⊢wk = s-wk ⊢NΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ


  q∘q : ∀ {i} → Γ ⊢ T ∶ Se i → (T [ σ ∘ τ ]) ∺ Δ′ ⊢s q σ ∘ q τ ≈ q (σ ∘ τ) ∶ T ∺ Γ
  q∘q {T} {i} ⊢T = begin
    q σ ∘ q τ            ≈⟨ q∘,≈∘, ⊢σ ⊢T ⊢τwk (conv (vlookup ⊢TΔ′ here) eq) ⟩
    (σ ∘ (τ ∘ wk)) , v 0 ≈˘⟨ ,-cong (∘-assoc ⊢σ ⊢τ ⊢wk) ⊢T
                                    (≈-refl (conv (vlookup ⊢TΔ′ here) ([∘]-Se ⊢T ⊢στ ⊢wk))) ⟩
    q (σ ∘ τ)            ∎
    where ⊢στ = s-∘ ⊢τ ⊢σ
          ⊢TΔ′ = ⊢∺ ⊢Δ′ (t[σ]-Se ⊢T ⊢στ)
          ⊢wk  = s-wk ⊢TΔ′
          ⊢τwk = s-∘ ⊢wk ⊢τ
          eq : (T [ σ ∘ τ ]) ∺ Δ′ ⊢ T [ σ ∘ τ ] [ wk ] ≈ T [ σ ] [ τ ∘ wk ] ∶ Se i
          eq = let open ER in begin
            T [ σ ∘ τ ] [ wk ] ≈⟨ [∘]-Se ⊢T ⊢στ ⊢wk ⟩
            T [ σ ∘ τ ∘ wk ] ≈⟨ []-cong-Se″ ⊢T (∘-assoc ⊢σ ⊢τ ⊢wk) ⟩
            T [ σ ∘ (τ ∘ wk) ] ≈˘⟨ [∘]-Se ⊢T ⊢σ ⊢τwk ⟩
            T [ σ ] [ τ ∘ wk ] ∎

          open SR

-- Nat related helpers
module _ {i} (⊢T : N ∺ Δ ⊢ T ∶ Se i) (⊢σ : Γ ⊢s σ ∶ Δ) where
  private
    ⊢NΔ  = proj₁ (presup-tm ⊢T)
    ⊢TNΔ = ⊢∺ ⊢NΔ ⊢T
    ⊢Γ   = proj₁ (presup-s ⊢σ)

  rec-β-su-T-swap : (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ (wk ∘ wk) , su (v 1) ] [ q (q σ) ] ≈ T [ q σ ] [ (wk ∘ wk) , su (v 1) ] ∶ Se i
  rec-β-su-T-swap = F⇒C-≈ (Subₚ.rec-β-su-T-swap (C⇒F-⊢ ⊢Γ) (C⇒F-⊢ ⊢TNΔ) (C⇒F-s ⊢σ))

module NatTyping {i} (⊢T : N ∺ Γ ⊢ T ∶ Se i) (⊢σ : Δ ⊢s σ ∶ Γ) where

  ⊢Δ     = proj₁ (presup-s ⊢σ)
  ⊢Γ     = proj₂ (presup-s ⊢σ)
  ⊢qσ    = ⊢q-N ⊢σ
  ⊢qqσ   = ⊢q ⊢qσ ⊢T
  ⊢Tqσ   = t[σ]-Se ⊢T ⊢qσ
  ⊢NΓ    = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
  ⊢TNΓ   = ⊢∺ ⊢NΓ ⊢T
  ⊢NΔ    = ⊢∺ ⊢Δ (N-wf 0 ⊢Δ)
  ⊢TqσNΔ = ⊢∺ ⊢NΔ ⊢Tqσ
  ⊢wk    = s-wk ⊢NΓ
  ⊢wk′   = s-wk ⊢TNΓ
  ⊢wkwk  = s-∘ ⊢wk′ ⊢wk
