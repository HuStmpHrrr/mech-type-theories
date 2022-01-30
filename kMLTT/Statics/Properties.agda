{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties where

open import Lib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

import kMLTT.Statics.Full as F
open import kMLTT.Statics.Concise as C
open import kMLTT.Statics.Equiv
import kMLTT.Statics.Presup as Presup
import kMLTT.Statics.Refl as Refl
import kMLTT.Statics.Misc as Misc
import kMLTT.Statics.PER as PER
import kMLTT.Statics.CtxEquiv as CtxEquiv
import kMLTT.Statics.Properties.Contexts as Ctxₚ
open import kMLTT.Statics.Properties.Ops as Ops
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


lift-⊢-Se : ∀ {i j} →
            Γ ⊢ T ∶ Se i →
            i ≤ j →
            Γ ⊢ T ∶ Se j
lift-⊢-Se ⊢T i≤j = F⇒C-tm (Misc.lift-⊢-Se (C⇒F-tm ⊢T) i≤j)

lift-⊢-Se-max : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (i ⊔ j)
lift-⊢-Se-max ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max (C⇒F-tm ⊢T))

lift-⊢-Se-max′ : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (j ⊔ i)
lift-⊢-Se-max′ ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max′ (C⇒F-tm ⊢T))

lift-⊢≈-Se : ∀ {i j} →
             Γ ⊢ T ≈ T′ ∶ Se i →
             i ≤ j →
             Γ ⊢ T ≈ T′ ∶ Se j
lift-⊢≈-Se T≈T′ i≤j = F⇒C-≈ (Misc.lift-⊢≈-Se (C⇒F-≈ T≈T′) i≤j)

lift-⊢≈-Se-max : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (i ⊔ j)
lift-⊢≈-Se-max T≈T′ = F⇒C-≈ (Misc.lift-⊢≈-Se-max (C⇒F-≈ T≈T′))

lift-⊢≈-Se-max′ : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (j ⊔ i)
lift-⊢≈-Se-max′ T≈T′ = F⇒C-≈ (Misc.lift-⊢≈-Se-max′ (C⇒F-≈ T≈T′))

N-≈ : ∀ i →
      ⊢ Γ →
      Γ ⊢ N ≈ N ∶ Se i
N-≈ i ⊢Γ = ≈-trans (≈-sym (N-[] i (s-I ⊢Γ))) (N-[] i (s-I ⊢Γ))

Se-≈ : ∀ {i} →
       ⊢ Γ →
       Γ ⊢ Se i ≈ Se i ∶ Se (1 + i)
Se-≈ {_} {i} ⊢Γ = ≈-trans (≈-sym (Se-[] i (s-I ⊢Γ))) (Se-[] i (s-I ⊢Γ))

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

⊢≈-sym : ⊢ Γ ≈ Δ →
         ---------
         ⊢ Δ ≈ Γ
⊢≈-sym Γ≈Δ = F⇒C-⊢≈ (Ctxₚ.⊢≈-sym (C⇒F-⊢≈ Γ≈Δ))

⊢≈-trans : ⊢ Γ ≈ Γ′ →
           ⊢ Γ′ ≈ Γ″ →
           -----------
           ⊢ Γ ≈ Γ″
⊢≈-trans Γ≈Γ′ Γ′≈Γ″ = F⇒C-⊢≈ (PER.⊢≈-trans (C⇒F-⊢≈ Γ≈Γ′) (C⇒F-⊢≈ Γ′≈Γ″))

⊢⇒∥⊢ : ∀ Ψs →
       ⊢ Ψs ++⁺ Γ →
       ------------
       ⊢ Γ
⊢⇒∥⊢ Ψs ⊢ΨsΓ = F⇒C-⊢ (Ctxₚ.⊢⇒∥⊢ Ψs (C⇒F-⊢ ⊢ΨsΓ))

presup-tm : Γ ⊢ t ∶ T →
            ------------
            ⊢ Γ × Γ ⊢ T
presup-tm ⊢t
  with Presup.presup-tm (C⇒F-tm ⊢t)
...  | ⊢Γ , _ , ⊢T = F⇒C-⊢ ⊢Γ , -, F⇒C-tm ⊢T

presup-s : Γ ⊢s σ ∶ Δ →
           ------------
           ⊢ Γ × ⊢ Δ
presup-s ⊢σ
  with Presup.presup-s (C⇒F-s ⊢σ)
...  | ⊢Γ , ⊢Δ = F⇒C-⊢ ⊢Γ , F⇒C-⊢ ⊢Δ

presup-≈ : Γ ⊢ s ≈ t ∶ T →
           -----------------------------------
           ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
presup-≈ s≈t
  with Presup.presup-≈ (C⇒F-≈ s≈t)
...  | ⊢Γ , ⊢s , ⊢t , _ , ⊢T = F⇒C-⊢ ⊢Γ , F⇒C-tm ⊢s , F⇒C-tm ⊢t , -, F⇒C-tm ⊢T

presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
             -----------------------------------
             ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
presup-s-≈ σ≈τ
  with Presup.presup-s-≈ (C⇒F-s-≈ σ≈τ)
...  | ⊨Γ , ⊢σ , ⊢τ , ⊢Δ = F⇒C-⊢ ⊨Γ , F⇒C-s ⊢σ , F⇒C-s ⊢τ , F⇒C-⊢ ⊢Δ

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

O-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           -----------------
           O σ n ≡ O σ′ n
O-resp-≈ n σ≈σ′ = Ops.O-resp-≈ n (C⇒F-s-≈ σ≈σ′)

∥-resp-≈′ : ∀ Ψs →
            Γ ⊢s σ ≈ σ′ ∶ Ψs ++⁺ Δ →
            --------------------------------------------------
            ∃₂ λ Ψs′ Γ′ →
              Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ O σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ≈ σ′ ∥ len Ψs ∶ Δ
∥-resp-≈′ Ψs σ≈σ′
  with Ops.∥-resp-≈′ Ψs (C⇒F-s-≈ σ≈σ′)
... | Ψs′ , Γ′ , eq , eql , σ≈σ′∥ = Ψs′ , Γ′ , eq , eql , F⇒C-s-≈ σ≈σ′∥


n∶T[wk]n∈!ΨTΓ : ∀ {n} → ⊢ Ψ ++⁻ T ∺ Γ → len Ψ ≡ n → n ∶ T [wk]* (suc n) ∈! Ψ ++⁻ T ∺ Γ
n∶T[wk]n∈!ΨTΓ ⊢ΨTΓ eq = Misc.n∶T[wk]n∈!ΨTΓ (C⇒F-⊢ ⊢ΨTΓ) eq

⊢vn∶T[wk]suc[n] : ∀ {n} → ⊢ Ψ ++⁻ T ∺ Γ → len Ψ ≡ n → Ψ ++⁻ T ∺ Γ ⊢ v n ∶ T [wk]* (suc n)
⊢vn∶T[wk]suc[n] ⊢ΨTΓ eq = vlookup ⊢ΨTΓ (n∶T[wk]n∈!ΨTΓ ⊢ΨTΓ eq)

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


-- other easy helpers

⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ⊢≈-refl ⊢Γ
⊢I-inv (s-conv ⊢I Δ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Δ′≈Δ

[I]-inv : Γ ⊢ t [ I ] ∶ T → Γ ⊢ t ∶ T
[I]-inv (t[σ] t∶T ⊢I)
  with ctxeq-tm (⊢≈-sym (⊢I-inv ⊢I)) t∶T
...  | ⊢t               = conv ⊢t (≈-sym ([I] (proj₂ (proj₂ (presup-tm ⊢t)))))
[I]-inv (cumu t[I])     = cumu ([I]-inv t[I])
[I]-inv (conv t[I] S≈T) = conv ([I]-inv t[I]) S≈T

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

[I；1]-inv : [] ∷⁺ Γ ⊢ t [ I ； 1 ] ∶ T → [] ∷⁺ Γ ⊢ t ∶ T
[I；1]-inv (t[σ] ⊢t ⊢I；1) = helper′ ⊢t ⊢I；1
  where helper : Γ′ ⊢s I ； 1 ∶ Δ → Γ′ ≡ [] ∷⁺ Γ → ⊢ Δ ≈ [] ∷⁺ Γ
        helper (s-； ([] ∷ []) ⊢σ (⊢κ ⊢Γ) _) refl = κ-cong (⊢≈-sym (⊢I-inv ⊢σ))
        helper (s-conv ⊢σ Δ′≈Δ) eq                = ⊢≈-trans (⊢≈-sym Δ′≈Δ) (helper ⊢σ eq)
        helper′ : Δ ⊢ t ∶ T → [] ∷⁺ Γ ⊢s I ； 1 ∶ Δ → [] ∷⁺ Γ ⊢ t ∶ sub T (I ； 1)
        helper′ ⊢t ⊢I；1
          with ctxeq-tm (helper ⊢I；1 refl) ⊢t
        ...  | ⊢t
          with presup-tm ⊢t
        ...  | ⊢κ ⊢Γ , _ , ⊢T = conv ⊢t (≈-sym (≈-trans ([]-cong-Se″ ⊢T (s-≈-sym (；-ext (s-I (⊢κ ⊢Γ))))) ([I] ⊢T)))
[I；1]-inv (cumu ⊢t)      = cumu ([I；1]-inv ⊢t)
[I；1]-inv (conv ⊢t ≈T)  = conv ([I；1]-inv ⊢t) ≈T

⊢wk-inv : T ∺ Γ ⊢s wk ∶ Δ → ⊢ Γ ≈ Δ
⊢wk-inv (s-wk (⊢∷ ⊢Γ _)) = ⊢≈-refl ⊢Γ
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

t[σ]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶ Se i
t[σ]-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

⊢q : ∀ {i} → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∺ Γ ⊢s q σ ∶ T ∺ Δ
⊢q ⊢σ ⊢T = F⇒C-s (Misc.⊢q (C⇒F-⊢ (proj₁ (presup-s ⊢σ))) (C⇒F-s ⊢σ) (C⇒F-tm ⊢T))

⊢I,t : Γ ⊢ t ∶ T → Γ ⊢s I , t ∶ T ∺ Γ
⊢I,t ⊢t
  with presup-tm ⊢t
...  | ⊢Γ , _ , ⊢T = F⇒C-s (Misc.⊢I,t (C⇒F-⊢ ⊢Γ) (C⇒F-tm ⊢T) (C⇒F-tm ⊢t))

qI,≈, : ∀ {i} → Δ ⊢s σ ∶ Γ → Γ ⊢ T ∶ Se i → Δ ⊢ s ∶ T [ σ ] → Δ ⊢s q σ ∘ (I , s) ≈ σ , s ∶ T ∺ Γ
qI,≈, {_} {σ} {_} {_} {s} ⊢σ ⊢T ⊢s
  with presup-s ⊢σ
...  | ⊢Δ , ⊢Γ = begin
  q σ ∘ (I , s)                      ≈⟨ ,-∘ (s-∘ (s-wk ⊢TσΔ) ⊢σ) ⊢T (conv (vlookup ⊢TσΔ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΔ))) ⊢I,s ⟩
  (σ ∘ wk ∘ (I , s)) , v 0 [ I , s ] ≈⟨ ,-cong σpI,≈σ
                                               ⊢T
                                               (≈-conv ([,]-v-ze (s-I ⊢Δ) ⊢Tσ ⊢s′)
                                                       (≈-trans ([I] ⊢Tσ)
                                                                ([]-cong-Se″ ⊢T (s-≈-sym σpI,≈σ)))) ⟩
  σ , s                              ∎
  where open SR
        ⊢I,s   = ⊢I,t ⊢s
        ⊢Tσ    = t[σ]-Se ⊢T ⊢σ
        ⊢TσΔ   = ⊢∷ ⊢Δ ⊢Tσ
        ⊢s′    = conv ⊢s (≈-sym ([I] ⊢Tσ))
        σpI,≈σ = begin
          σ ∘ wk ∘ (I , s) ≈⟨ ∘-assoc ⊢σ (s-wk ⊢TσΔ) ⊢I,s ⟩
          σ ∘ p (I , s)    ≈⟨ ∘-cong (p-, (s-I ⊢Δ) ⊢Tσ ⊢s′) (s-≈-refl ⊢σ) ⟩
          σ ∘ I            ≈⟨ ∘-I ⊢σ ⟩
          σ                ∎

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
  with presup-tm ⊢T | presup-s ⊢τ
...  | ⊢∷ ⊢Γ ⊢S , _ | ⊢Δ′ , ⊢Δ = begin
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

[]-q-∘-,′ : ∀ {i} → S ∺ Γ ⊢ T ∶ Se i → Δ ⊢s σ ∶ Γ → Δ ⊢ t ∶ S [ σ ] →  Δ ⊢ T [ σ , t ] ≈ T [ q σ ] [ I , t ] ∶ Se i
[]-q-∘-,′ ⊢T ⊢σ ⊢t
  with presup-tm ⊢T | presup-s ⊢σ
...  | ⊢∷ ⊢Γ ⊢S , _ | ⊢Δ , _ = ≈-trans ([]-cong-Se″ ⊢T (,-cong (s-≈-sym (∘-I ⊢σ)) ⊢S (≈-refl ⊢t))) ([]-q-∘-, ⊢T ⊢σ (s-I ⊢Δ) (conv ⊢t (≈-sym ([I] ⊢Sσ))))
  where ⊢qσ  = ⊢q ⊢σ ⊢S
        ⊢Sσ  = t[σ]-Se ⊢S ⊢σ

I；1≈I : ⊢ Γ → [] ∷⁺ Γ ⊢s I ； 1 ≈ I ∶ [] ∷⁺ Γ
I；1≈I ⊢Γ = s-≈-sym (；-ext (s-I (⊢κ ⊢Γ)))

[I；1] : ∀ {i} → [] ∷⁺ Γ ⊢ T ∶ Se i → [] ∷⁺ Γ ⊢ T [ I ； 1 ] ≈ T ∶ Se i
[I；1] ⊢T
  with presup-tm ⊢T
...  | ⊢κ ⊢Γ , _ = ≈-trans ([]-cong-Se″ ⊢T (I；1≈I ⊢Γ)) ([I] ⊢T)
