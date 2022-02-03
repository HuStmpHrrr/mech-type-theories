{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.LogRel where

open import Lib
open import Data.Nat
open import Data.Nat.Properties

open import kMLTT.Statics public
open import kMLTT.Semantics.Domain public
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
  ze : Γ ⊢ t ≈ ze ∶ N →
       -----------------
       Γ ⊢ t ∶N® ze ∈Nat
  su : Γ ⊢ t ≈ su t′ ∶ N →
       Γ ⊢ t′ ∶N® a ∈Nat →
       --------------------
       Γ ⊢ t ∶N® su a ∈Nat
  ne : (c∈ : c ∈′ Bot) →
       (∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let (u , _) = c∈ (map len Δ) (mt σ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ N) →
       -----------------------
       Γ ⊢ t ∶N® ↑ N c ∈Nat


record Glu□ i Γ T (R : Substs → ℕ → Ctxs → Typ → Set) : Set where
  field
    GT   : Typ
    T≈   : Γ ⊢ T ≈ □ GT ∶ Se i
    krip : ∀ Ψs → Δ ⊢r σ ∶ Γ → R σ (len Ψs) (Ψs ++⁺ Δ) (GT [ σ ； len Ψs ])


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
    a∈El : a ∈′ El i A≈B
    T≈   : Γ ⊢ T ≈ □ GT ∶ Se i
    krip : ∀ Ψs → Δ ⊢r σ ∶ Γ → □Krip Ψs Δ t GT σ a R


record ΠRel i Δ IT OT σ
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
    IT   : Typ
    OT   : Typ
    -- need this prop or it is too difficult to invert
    ⊢OT  : IT ∺ Γ ⊢ OT ∶ Se i
    T≈   : Γ ⊢ T ≈ Π IT OT ∶ Se i
    krip : Δ ⊢r σ ∶ Γ → ΠRel i Δ IT OT σ iA RI RO Rs


record ΛKripke Δ t T f a (R$ : Ctxs → Exp → Typ → D → Set) : Set where
  field
    fa : D
    ↘fa : f ∙ a ↘ fa
    ®fa : R$ Δ t T fa

record ΛRel i Δ t IT OT σ f
             (iA : ∀ (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i)
             (RI : Substs → Ctxs → Typ → Set)
             (Rs : Substs → Ctxs → Exp → Typ → D → Set)
             (R$ : ∀ {a a′} σ → a ≈ a′ ∈ El i (iA (mt σ)) → Ctxs → Exp → Typ → D → Set) : Set where
  field
    IT-rel : RI σ Δ (IT [ σ ])
    ap-rel : Rs σ Δ s (IT [ σ ]) b → (b∈ : b ∈′ El i (iA (mt σ))) → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ]) (f [ mt σ ]) b (R$ σ b∈)

  flipped-ap-rel : (b∈ : b ∈′ El i (iA (mt σ))) → ∀ {s} → Rs σ Δ s (IT [ σ ]) b → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ]) (f [ mt σ ]) b (R$ σ b∈)
  flipped-ap-rel b∈ R = ap-rel R b∈

record GluΛ i Γ t T a {A B T′ T″ ρ ρ′}
            (iA : ∀ (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i)
            (RT : ∀ {a a′} (κ : UMoT) → a ≈ a′ ∈ El i (iA κ) → ΠRT T′ (ρ [ κ ] ↦ a) T″ (ρ′ [ κ ] ↦ a′) (𝕌 i))
            (RI : Substs → Ctxs → Typ → Set)
            (Rs : Substs → Ctxs → Exp → Typ → D → Set)
            (R$ : ∀ {a a′} σ → a ≈ a′ ∈ El i (iA (mt σ)) → Ctxs → Exp → Typ → D → Set) : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    a∈El : a ∈′ El i (Π iA RT)
    IT   : Typ
    OT   : Typ
    -- need this prop or it is too difficult to invert
    ⊢OT  : IT ∺ Γ ⊢ OT ∶ Se i
    T≈   : Γ ⊢ T ≈ Π IT OT ∶ Se i
    krip : Δ ⊢r σ ∶ Γ → ΛRel i Δ t IT OT σ a iA RI Rs R$

record GluU j i Γ t T A (R : A ∈′ 𝕌 j → Set) : Set where
  field
    t∶T : Γ ⊢ t ∶ T
    T≈  : Γ ⊢ T ≈ Se j ∶ Se i
    A∈𝕌 : A ∈′ 𝕌 j
    rel : R A∈𝕌

record GluNe i Γ t T (c∈⊥ : c ∈′ Bot) (C≈C′ : C ≈ C′ ∈ Bot) : Set where
  field
    t∶T : Γ ⊢ t ∶ T
    ⊢T  : Γ ⊢ T ∶ Se i
    krip : Δ ⊢r σ ∶ Γ →
           let V , _ = C≈C′ (map len Δ) (mt σ)
               u , _ = c∈⊥ (map len Δ) (mt σ)
           in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
            × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]

module Glu i (rec : ∀ {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set) where
  infix 4 _⊢_®_ _⊢_∶_®_∈El_

  mutual

    _⊢_®_ : Ctxs → Typ → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ T ® ne C≈C′      = Γ ⊢ T ∶ Se i × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let V , _ = C≈C′ (map len Δ) (mt σ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
    Γ ⊢ T ® N            = Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ T ® U {j} j<i eq = Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ T ® □ A≈B        = Glu□ i Γ T (λ σ n → _⊢_® A≈B (ins (mt σ) n))
                           -- ∃ λ GT → Γ ⊢ T ≈ □ GT ∶ Se i
                           --   × ∀ Ψs → Δ ⊢r σ ∶ Γ → Ψs ++⁺ Δ ⊢ GT [ σ ； len Ψs ] ® A≈B (ins (mt σ) (len Ψs))
    Γ ⊢ T ® Π iA RT      = GluΠ i Γ T iA (λ σ → _⊢_® iA (mt σ)) (λ σ a∈ → _⊢_® ΠRT.T≈T′ (RT (mt σ) a∈)) (λ σ → _⊢_∶_®_∈El iA (mt σ))
                           -- ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
                           --    × IT ∺ Γ ⊢ OT ∶ Se i
                           --    × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ →
                           --                (Δ ⊢ IT [ σ ] ® iA (mt σ))
                           --              × ∀ {s a} (irel : Δ ⊢ s ∶ IT [ σ ] ® a ∈El iA (mt σ)) (a∈ : a ∈′ El i (iA (mt σ))) → Δ ⊢ OT [ σ , s ] ® ΠRT.T≈T′ (RT (mt σ) a∈)

    _⊢_∶_®_∈El_ : Ctxs → Exp → Typ → D → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ t ∶ T ® a ∈El ne C≈C′      = Σ (a ∈′ Neu) λ { (ne c∈⊥) → GluNe i Γ t T c∈⊥ C≈C′ }
    Γ ⊢ t ∶ T ® a ∈El N            = Γ ⊢ t ∶N® a ∈Nat × Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ t ∶ T ® a ∈El U {j} j<i eq = GluU j i Γ t T a (rec j<i Γ t)
    Γ ⊢ t ∶ T ® a ∈El □ A≈B        = Glubox i Γ t T a (□ A≈B) (λ σ n → _⊢_∶_®_∈El A≈B (ins (mt σ) n))
                                   -- Γ ⊢ t ∶ T × a ∈′ El i (□ A≈ B) ×
                                   -- ∃ λ GT → Γ ⊢ T ≈ □ GT ∶ Se i
                                   --   × ∀ Ψs → Δ ⊢r σ ∶ Γ → ∃ λ ub → unbox (len Ψs) ∙ a [ mt σ ] ↘ ub × Ψs ++⁺ Δ ⊢ unbox (len Ψs) (t [ σ ]) ∶ GT [ σ ； len Ψs ] ® ub ∈El (A≈B (ins (mt σ) (len Ψs)))
    Γ ⊢ t ∶ T ® a ∈El Π iA RT      = GluΛ i Γ t T a iA RT (λ σ → _⊢_® iA (mt σ)) (λ σ → _⊢_∶_®_∈El iA (mt σ)) (λ σ b∈ → _⊢_∶_®_∈El ΠRT.T≈T′ (RT (mt σ) b∈))
                                   -- Γ ⊢ t ∶ T × (a ∈′ El i (Π iA RT))
                                   --   × IT ∺ Γ ⊢ OT ∶ Se i
                                   --   × ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
                                   --                × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ →
                                   --                          (Δ ⊢ IT [ σ ] ® iA (mt σ))
                                   --                         × ∀ {s b} (irel : Δ ⊢ s ∶ IT [ σ ] ® b ∈El iA (mt σ)) (b∈ : b ∈′ El i (iA (mt σ))) → ∃ λ ap → a [ mt σ ] ∙ b ↘ ap × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ® ap ∈El ΠRT.T≈T′ (RT (mt σ) b∈)


Glu-wellfounded : ∀ i {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set
Glu-wellfounded .(suc _) {j} (s≤s j<i) = Glu._⊢_®_ j λ j′<j → Glu-wellfounded _ (≤-trans j′<j j<i)

private
  module G i = Glu i (Glu-wellfounded i)

infix 4 _⊢_®[_]_ _⊢_∶_®[_]_∈El_ _⊢_®_ _⊢_∶_®_∈El_

_⊢_®[_]_ : Ctxs → Typ → ∀ i → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ T ®[ i ] A≈B = G._⊢_®_ i Γ T A≈B

_⊢_∶_®[_]_∈El_ : Ctxs → Exp → Typ → ∀ i → D → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B = G._⊢_∶_®_∈El_ i Γ t T a A≈B

_⊢_®_ : Ctxs → Typ → A ≈ B ∈ 𝕌∞ → Set
Γ ⊢ T ® (i , A≈B) = Γ ⊢ T ®[ i ] A≈B

_⊢_∶_®_∈El_ : Ctxs → Exp → Typ → D → A ≈ B ∈ 𝕌∞ → Set
Γ ⊢ t ∶ T ® a ∈El (i , A≈B) = Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B

infix 4 _⊢_∶_®↓[_]_∈El_ _⊢_∶_®↑[_]_∈El_

record _⊢_∶_®↓[_]_∈El_ Γ t T i c (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    T∼A  : Γ ⊢ T ®[ i ] A≈B
    c∈⊥  : c ∈′ Bot
    krip : Δ ⊢r σ ∶ Γ → let u , _ = c∈⊥ (map len Δ) (mt σ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]


record _⊢_∶_®↑[_]_∈El_ Γ t T i a (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    T∼A  : Γ ⊢ T ®[ i ] A≈B
    a∈⊤  : ↓ A a ≈ ↓ B a ∈ Top
    krip : Δ ⊢r σ ∶ Γ → let w , _ = a∈⊤ (map len Δ) (mt σ) in Δ ⊢ t [ σ ] ≈ Nf⇒Exp w ∶ T [ σ ]


record Gluκ Γ σ Δ (ρ : Envs) (R : Ctxs → Substs → Envs → Set) : Set where
  field
    ⊢σ   : Γ ⊢s σ ∶ [] ∷⁺ Δ
    Ψs⁻  : List Ctx
    Γ∥   : Ctxs
    σ∥   : Substs
    Γ≡   : Γ ≡ Ψs⁻ ++⁺ Γ∥
    ≈σ∥  : Γ∥ ⊢s σ ∥ 1 ≈ σ∥ ∶ Δ
    O≡   : O σ 1 ≡ proj₁ (ρ 0)
    len≡ : len Ψs⁻ ≡ O σ 1
    step : R Γ∥ σ∥ (ρ ∥ 1)


record Glu∺ Γ σ T Δ (ρ : Envs) (R : Ctxs → Substs → Envs → Set) : Set where
  field
    ⊢σ   : Γ ⊢s σ ∶ T ∺ Δ
    pσ   : Substs
    v0σ  : Exp
    ⟦T⟧  : D
    lvl  : ℕ
    ⊢T   : Δ ⊢ T ∶ Se lvl
    ≈pσ  : Γ ⊢s p σ ≈ pσ ∶ Δ
    ≈v0σ : Γ ⊢ v 0 [ σ ] ≈ v0σ ∶ T [ pσ ]
    ↘⟦T⟧ : ⟦ T ⟧ drop ρ ↘ ⟦T⟧
    T∈𝕌  : ⟦T⟧ ∈′ 𝕌 lvl
    t∼ρ0 : Γ ⊢ v0σ ∶ (T [ pσ ]) ®[ lvl ] (lookup ρ 0) ∈El T∈𝕌
    step : R Γ pσ (drop ρ)


infix 4 _⊢s_∶_®_

_⊢s_∶_®_ : Ctxs → Substs → ⊢ Δ → Envs → Set
Γ ⊢s σ ∶ ⊢[] ® ρ              = Γ ⊢s σ ∶ [] ∷ []
Γ ⊢s σ ∶ ⊢κ {Δ} ⊢Δ ® ρ        = Gluκ Γ σ Δ ρ (_⊢s_∶ ⊢Δ ®_)
Γ ⊢s σ ∶ ⊢∺ {Δ} {T} ⊢Δ ⊢T ® ρ = Glu∺ Γ σ T Δ ρ (_⊢s_∶ ⊢Δ ®_)


record GluExp i Δ t T (σ : Substs) ρ : Set where
  field
    ⟦T⟧ : D
    ⟦t⟧ : D
    ↘⟦T⟧ : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    T∈𝕌  : ⟦T⟧ ∈′ 𝕌 i
    t∼⟦t⟧ : Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦t⟧ ∈El T∈𝕌

record GluSubsts Δ τ (⊢Γ′ : ⊢ Γ′) σ ρ : Set where
  field
    ⟦τ⟧    : Envs
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ ↘ ⟦τ⟧
    τσ∼⟦τ⟧ : Δ ⊢s τ ∘ σ ∶ ⊢Γ′ ® ⟦τ⟧


infix 4 _⊩_∶_ _⊩s_∶_

record _⊩_∶_ Γ t T : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    ⊢Γ   : ⊢ Γ
    lvl  : ℕ
    krip : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluExp lvl Δ t T σ ρ


record _⊩s_∶_ Γ τ Γ′ : Set where
  field
    ⊢τ   : Γ ⊢s τ ∶ Γ′
    ⊢Γ   : ⊢ Γ
    ⊢Γ′  : ⊢ Γ′
    krip : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluSubsts Δ τ ⊢Γ′ σ ρ
