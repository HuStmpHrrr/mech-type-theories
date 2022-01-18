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

lift-⊢-Se-max : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (i ⊔ j)
lift-⊢-Se-max ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max (C⇒F-tm ⊢T))

lift-⊢-Se-max′ : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (j ⊔ i)
lift-⊢-Se-max′ ⊢T = F⇒C-tm (Misc.lift-⊢-Se-max′ (C⇒F-tm ⊢T))

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
