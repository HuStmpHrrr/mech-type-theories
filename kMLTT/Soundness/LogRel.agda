{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.LogRel where

open import Lib
open import Data.Nat

open import kMLTT.Statics public
open import kMLTT.Semantics.Domain public
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Evaluation public
open import kMLTT.Semantics.PER public

open import kMLTT.Soundness.Restricted public


mt : Substs → UMoT
mt I        = vone
mt wk       = vone
mt (σ , _)  = mt σ
mt (σ ； n) = ins (mt σ) n
mt (σ ∘ δ)  = mt σ ø mt δ

infix 4 _⊢_∶N®_∈Nat

data _⊢_∶N®_∈Nat : Ctxs → Exp → D → Set where
  ze : Γ ⊢ ze ∶N® ze ∈Nat
  su : Γ ⊢ t ≈ su t′ ∶ N →
       Γ ⊢ t′ ∶N® a ∈Nat →
       --------------------
       Γ ⊢ t ∶N® su a ∈Nat
  ne : (c∈ : c ∈′ Bot) →
       (∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let (u , _) = c∈ (map len Δ) (mt σ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ N) →
       -----------------------
       Γ ⊢ t ∶N® ↑ N c ∈Nat

®Nat⇒∈Nat : Γ ⊢ t ∶N® a ∈Nat → a ∈′ Nat
®Nat⇒∈Nat ze         = ze
®Nat⇒∈Nat (su _ rel) = su (®Nat⇒∈Nat rel)
®Nat⇒∈Nat (ne c∈ _)  = ne c∈


record Glu□ i Γ T (R : Substs → ℕ → Ctxs → Typ → Set) : Set where
  field
    GT   : Typ
    T≈   : Γ ⊢ T ≈ □ GT ∶ Se i
    krip : ∀ {Ψs Δ σ} → Δ ⊢r σ ∶ Γ → R σ (len Ψs) (Ψs ++⁺ Δ) (GT [ σ ； len Ψs ])


record □Krip Ψs Δ t T σ a (R : Substs → ℕ → Ctxs → Exp → Typ → D → Set) : Set where
  field
    ua  : D
    ↘ua : unbox∙ len Ψs , a [ mt σ ] ↘ ua
    rel : R σ (len Ψs) (Ψs ++⁺ Δ) (unbox (len Ψs) (t [ σ ])) (T [ σ ； len Ψs ]) ua


record Glubox i Γ t T a
              {A B} (A≈B : A ≈ B ∈ 𝕌 i)
              (R : Substs → ℕ → Ctxs → Exp → Typ → D → Set) : Set where
  field
    GT   : Typ
    t∶T  : Γ ⊢ t ∶ T
    aEl  : a ∈′ El i A≈B
    T≈   : Γ ⊢ T ≈ □ GT ∶ Se i
    krip : ∀ {Ψs Δ σ} → Δ ⊢r σ ∶ Γ → □Krip Ψs Δ t GT σ a R


record ΠKrip i Δ IT OT σ
             (iA : ∀ (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i)
             (RI : Substs → Ctxs → Typ → Set)
             (RO : ∀ {a a′} σ → a ≈ a′ ∈ El i (iA (mt σ)) → Ctxs → Typ → Set)
             (Rs : Substs → Ctxs → Exp → Typ → D → Set) : Set where
  field
    IT-rel : RI σ Δ (IT [ σ ])
    OT-rel : Rs σ Δ s (IT [ σ ]) a → (a∈ : a ∈′ El i (iA (mt σ))) → RO σ a∈ Δ (OT [ σ , s ])

record GluΠ i Γ T {A B}
            (iA : ∀ (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i)
            (RI : Substs → Ctxs → Typ → Set)
            (RO : ∀ {a a′} σ → a ≈ a′ ∈ El i (iA (mt σ)) → Ctxs → Typ → Set)
            (Rs : Substs → Ctxs → Exp → Typ → D → Set) : Set where
  field
    IT : Typ
    OT : Typ
    T≈ : Γ ⊢ T ≈ Π IT OT ∶ Se i
    krip : ∀ {Δ σ} → Δ ⊢r σ ∶ Γ → ΠKrip i Δ IT OT σ iA RI RO Rs

module Glu i (rec : ∀ {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set) where
  infix 4 _⊢_®_ _⊢_∶_®_∈El_

  mutual

    _⊢_®_ : Ctxs → Typ → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ T ® ne C≈C′      = ∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let V , _ = C≈C′ (map len Δ) (mt σ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
    Γ ⊢ T ® N            = Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ T ® U {j} j<i eq = Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ T ® □ A≈B        = Glu□ i Γ T (λ σ n → _⊢_® A≈B (ins (mt σ) n))
    Γ ⊢ T ® Π iA RT      = GluΠ i Γ T iA (λ σ → _⊢_® iA (mt σ)) (λ σ a∈ → _⊢_® ΠRT.T≈T′ (RT (mt σ) a∈)) (λ σ → _⊢_∶_®_∈El iA (mt σ))
    -- ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
                           -- × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ →
                           --             (Δ ⊢ IT [ σ ] ® iA (mt σ))
                           --           × ∀ {s a} (irel : Δ ⊢ s ∶ IT [ σ ] ® a ∈El iA (mt σ)) (a∈ : a ∈′ El i (iA (mt σ))) → Δ ⊢ OT [ σ , s ] ® ΠRT.T≈T′ (RT (mt σ) a∈)

    _⊢_∶_®_∈El_ : Ctxs → Exp → Typ → D → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ t ∶ T ® a ∈El ne C≈C′      = Σ (a ∈′ Neu)
                                   λ { (ne c≈c′) →
                                       ∀ {Δ σ} →
                                       Δ ⊢r σ ∶ Γ →
                                       let V , _ = C≈C′ (map len Δ) (mt σ)
                                           u , _ = c≈c′ (map len Δ) (mt σ)
                                       in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
                                        × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]
                                      }
    Γ ⊢ t ∶ T ® a ∈El N            = Γ ⊢ t ∶N® a ∈Nat × Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ t ∶ T ® a ∈El U {j} j<i eq = (Σ (a ∈′ 𝕌 j) λ a∈𝕌 → rec j<i Γ t a∈𝕌) × Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ t ∶ T ® a ∈El □ A≈B        = Glubox i Γ t T a (□ A≈B) (λ σ n → _⊢_∶_®_∈El A≈B (ins (mt σ) n))
    Γ ⊢ t ∶ T ® a ∈El Π iA RT      = Γ ⊢ t ∶ T × (a ∈′ El i (Π iA RT))
                                   × ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
                                                × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ →
                                                          (Δ ⊢ IT [ σ ] ® iA (mt σ))
                                                         × ∀ {s b} (irel : Δ ⊢ s ∶ IT [ σ ] ® b ∈El iA (mt σ)) (b∈ : b ∈′ El i (iA (mt σ))) → ∃ λ ap → a [ mt σ ] ∙ b ↘ ap × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ® ap ∈El ΠRT.T≈T′ (RT (mt σ) b∈)

-- infix 4 _⊢_®_ _⊢_∶_®_∈El_
