{-# OPTIONS --without-K --safe #-}

-- Definitions of logical relations for the gluing model and semantic judgments
module Mint.Soundness.LogRel where

open import Lib hiding (lookup)
open import Data.Nat
open import Data.Nat.Properties

open import Mint.Statics public
open import Mint.Semantics.Domain public
open import Mint.Semantics.Evaluation public
open import Mint.Semantics.PER public

open import Mint.Soundness.Restricted public


-- This function transform a substitution into a UMoT
--
-- Since the model is Kripke, we have a notion of monotonicity on both syntactic and
-- semantic sides. On the syntactic side, the monotonicity is with respect to
-- substitutions; while on the semantic side, the monotonicity is with respect to
-- UMoTs. This function thus connects these two notions of monotonicity. In the
-- definition of the gluing model, the Kripke structure is substitutions, so we use
-- this function to obtain UMoTs to describe the monotonicity on the semantic side.
mt : Substs → UMoT
mt I        = vone
mt wk       = vone
mt (σ , _)  = mt σ
mt (σ ； n) = ins (mt σ) n
mt (σ ∘ δ)  = mt σ ø mt δ

-------------------------------------
-- Gluing models for terms and types

-- Gluing model for natural numbers
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

-- Helper concepts for the gluing model
--
-- These definitions are defined for the purpose of having more structural condition
-- management.  One can find unfolded definitions using conjunctions in the comments
-- near the definition of the gluing model.

-- Gluing model for □
--
-- Here R is always the gluing model for types GT
--
-- Essentially the gluing model recurses down to GT. The Kripke structure is decribed by the field krip.
record Glu□ i Γ T (R : Substs → ℕ → Ctxs → Typ → Set) : Set where
  field
    GT   : Typ
    T≈   : Γ ⊢ T ≈ □ GT ∶ Se i
    krip : ∀ Ψs → ⊢ Ψs ++⁺ Δ → Δ ⊢r σ ∶ Γ → R σ (len Ψs) (Ψs ++⁺ Δ) (GT [ σ ； len Ψs ])

-- Gluing model for the box constructor
--
-- Here R is always the gluing model for terms (unbox t)
--
-- The gluing model ensures coherence after elimination.
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
    krip : ∀ Ψs → ⊢ Ψs ++⁺ Δ → Δ ⊢r σ ∶ Γ → □Krip Ψs Δ t GT σ a R

-- Gluing model for Π
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


-- Gluing model for Λ
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

-- Gluing model for universes
record GluU j i Γ t T A (R : A ∈′ 𝕌 j → Set) : Set where
  field
    t∶T : Γ ⊢ t ∶ T
    T≈  : Γ ⊢ T ≈ Se j ∶ Se i
    A∈𝕌 : A ∈′ 𝕌 j
    rel : R A∈𝕌

-- Gluing model for neutral terms
record GluNe i Γ t T (c∈⊥ : c ∈′ Bot) (C≈C′ : C ≈ C′ ∈ Bot) : Set where
  field
    t∶T : Γ ⊢ t ∶ T
    ⊢T  : Γ ⊢ T ∶ Se i
    krip : Δ ⊢r σ ∶ Γ →
           let V , _ = C≈C′ (map len Δ) (mt σ)
               u , _ = c∈⊥ (map len Δ) (mt σ)
           in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
            × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]

-- The definition of the gluing model
--
-- Due to cumulative universes, we must do a well-founded induction on the universe
-- level i.  The gluing model has two relations:
--
-- Γ ⊢ T ® A≈B : T and A (and B) are related at level i. It is A≈B again due to the
-- proof relevant nature of MLTT.
--
-- Γ ⊢ t ∶ T ® a ∈El A≈B : t and a are related. t has type T and a is in El A≈B. T and
-- A≈B are related in level i.
module Glu i (rec : ∀ {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set) where
  infix 4 _⊢_®_ _⊢_∶_®_∈El_

  mutual

    _⊢_®_ : Ctxs → Typ → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ T ® ne C≈C′      = Γ ⊢ T ∶ Se i × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let V , _ = C≈C′ (map len Δ) (mt σ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
    Γ ⊢ T ® N            = Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ T ® U {j} j<i eq = Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ T ® □ A≈B        = Glu□ i Γ T (λ σ n → _⊢_® A≈B (ins (mt σ) n))
                           -- ∃ λ GT → Γ ⊢ T ≈ □ GT ∶ Se i
                           --   × ∀ Ψs → ⊢ Ψs ++⁺ Δ → Δ ⊢r σ ∶ Γ → Ψs ++⁺ Δ ⊢ GT [ σ ； len Ψs ] ® A≈B (ins (mt σ) (len Ψs))
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
                                   --   Γ ⊢ t ∶ T
                                   -- × Γ ⊢ T ≈ Se j ∶ Se i
                                   -- × A ∈′ 𝕌 j
                                   -- × Γ ⊢ t ® A∈𝕌
    Γ ⊢ t ∶ T ® a ∈El □ A≈B        = Glubox i Γ t T a (□ A≈B) (λ σ n → _⊢_∶_®_∈El A≈B (ins (mt σ) n))
                                   -- Γ ⊢ t ∶ T × a ∈′ El i (□ A≈ B) ×
                                   -- ∃ λ GT → Γ ⊢ T ≈ □ GT ∶ Se i
                                   --   × ∀ Ψs → ⊢ Ψs ++⁺ Δ → Δ ⊢r σ ∶ Γ → ∃ λ ub → unbox (len Ψs) ∙ a [ mt σ ] ↘ ub × Ψs ++⁺ Δ ⊢ unbox (len Ψs) (t [ σ ]) ∶ GT [ σ ； len Ψs ] ® ub ∈El (A≈B (ins (mt σ) (len Ψs)))
    Γ ⊢ t ∶ T ® a ∈El Π iA RT      = GluΛ i Γ t T a iA RT (λ σ → _⊢_® iA (mt σ)) (λ σ → _⊢_∶_®_∈El iA (mt σ)) (λ σ b∈ → _⊢_∶_®_∈El ΠRT.T≈T′ (RT (mt σ) b∈))
                                   -- Γ ⊢ t ∶ T × (a ∈′ El i (Π iA RT))
                                   --   × ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
                                   --                × IT ∺ Γ ⊢ OT ∶ Se i
                                   --                × ∀ {Δ σ} → Δ ⊢r σ ∶ Γ →
                                   --                          (Δ ⊢ IT [ σ ] ® iA (mt σ))
                                   --                         × ∀ {s b} (irel : Δ ⊢ s ∶ IT [ σ ] ® b ∈El iA (mt σ)) (b∈ : b ∈′ El i (iA (mt σ))) → ∃ λ ap → a [ mt σ ] ∙ b ↘ ap × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ® ap ∈El ΠRT.T≈T′ (RT (mt σ) b∈)


-- Similar to the PER model, we tie the knot using well-founded induction.
Glu-wellfounded : ∀ i {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set
Glu-wellfounded .(suc _) {j} (s≤s j<i) = Glu._⊢_®_ j λ j′<j → Glu-wellfounded _ (≤-trans j′<j j<i)

private
  module G i = Glu i (Glu-wellfounded i)

infix 4 _⊢_®[_]_ _⊢_∶_®[_]_∈El_

-- T and A are related at level i
_⊢_®[_]_ : Ctxs → Typ → ∀ i → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ T ®[ i ] A≈B = G._⊢_®_ i Γ T A≈B

-- t of type T and a of type A are related at level i
_⊢_∶_®[_]_∈El_ : Ctxs → Exp → Typ → ∀ i → D → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B = G._⊢_∶_®_∈El_ i Γ t T a A≈B


-- In the PER model, we have three extrema PERs: Bot, Top and TopT. They relates equal
-- neutral values, equal normal values and equal normal semantic types after readback,
-- respctively. Similarly, we need the same notions in the gluing model. We need:
--
-- ®↓         : t and c are related iff t and any readback of c are equivalent.
-- ®↑ (value) : t and a are related iff t and any readback of a are equivalent.
-- ®↑ (type)  : T and A are related iff T and any readback of A are equivalent.
infix 4 _⊢_∶_®↓[_]_∈El_ _⊢_∶_®↑[_]_∈El_  _⊢_®↑[_]_

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

record _⊢_®↑[_]_ Γ T i (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ T ∶ Se i
    A∈⊤  : A ≈ B ∈ TopT
    krip : Δ ⊢r σ ∶ Γ → let W , _ = A∈⊤ (map len Δ) (mt σ) in Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i


---------------------------------
-- Gluing model for substitutions

-- Helper predicates for each case of context stacks

-- R is always the gluing model for substitutions
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


-- R is always the gluing model for substitutions
record Glu∺ i Γ σ T Δ (ρ : Envs) (R : Ctxs → Substs → Envs → Set) : Set where
  field
    ⊢σ   : Γ ⊢s σ ∶ T ∺ Δ
    pσ   : Substs
    v0σ  : Exp
    ⟦T⟧  : D
    ≈pσ  : Γ ⊢s p σ ≈ pσ ∶ Δ
    ≈v0σ : Γ ⊢ v 0 [ σ ] ≈ v0σ ∶ T [ pσ ]
    ↘⟦T⟧ : ⟦ T ⟧ drop ρ ↘ ⟦T⟧
    T∈𝕌  : ⟦T⟧ ∈′ 𝕌 i
    t∼ρ0 : Γ ⊢ v0σ ∶ (T [ pσ ]) ®[ i ] (lookup ρ 0) ∈El T∈𝕌
    step : R Γ pσ (drop ρ)


-- On paper this predicate denotes Δ ⊢ T [ σ ] ®[ i ] ⟦T⟧(ρ)
record GluTyp i Δ T (σ : Substs) ρ : Set where
  field
    ⟦T⟧   : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
    T∼⟦T⟧ : Δ ⊢ T [ σ ] ®[ i ] T∈𝕌

-- The definition of gluing model for substitutions
--
-- Similar to the PER model where we use induction-recursion to relate the
-- interpretations of substitutions, here we also use induction-recursion to relate
-- substitutions and evaluation environments.
--
-- This definition is not seen in others' work (A. Abel, D. Gratzer, etc.), where the
-- gluing for substitutions are done by induction on simply the constructor of the
-- contexts (or context stacks in our case). This model will work for cumulative
-- universes in a set-theoretic model, because in these proof one crucial step after
-- proving cumulativity of the model is to take the limit of the universe level, and
-- then the universe level is not spoken of. In type theory, on the other hand, we
-- cannot take limits. This thus forces us to consider universe levels explicitly,
-- leading us to this more precise model.
--
-- Another benefit of this higher precision is that this model can be adapted to
-- non-cumulative universe pretty well. In aforementioned work, since the step of
-- taking limit is essential, the information about universe levels is gone. It
-- becomes unclear how one can easily remove the step of taking limits and adapt their
-- proofs to non-cumulativity. On the other hand, our model keeps track of unvierse
-- levels so there is no problem to obtain the level from our model whenever it is
-- needed.
infix 4 ⊩_ _⊢s_∶_®_

mutual

  -- This definition is almost the same as ⊢_ except that it has one more condition in
  -- ⊩∺.
  data ⊩_ : Ctxs → Set where
    ⊩[] : ⊩ [] ∷ []
    ⊩κ  : ⊩ Γ → ⊩ [] ∷⁺ Γ
    ⊩∺  : ∀ {i} (⊩Γ : ⊩ Γ) →
          Γ ⊢ T ∶ Se i →
          -- This condition says, given any related σ and ρ, T[σ] and its evaluation
          -- are related at level i.
          (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩Γ ® ρ → GluTyp i Δ T σ ρ) →
          ⊩ (T ∺ Γ)

  -- The gluing model for substitutions
  --
  -- This model glues substitutions and evaluation environments. It is recursive on ⊩_
  -- so this model is again inductive-recursive. We can see that in the ⊩∺ case, we
  -- use the universe level. This removes our need to take limits as done in a more
  -- set-thereotic setting.
  _⊢s_∶_®_ : Ctxs → Substs → ⊩ Δ → Envs → Set
  Δ ⊢s σ ∶ ⊩[] ® ρ                 = Δ ⊢s σ ∶ [] ∷ []
  Δ ⊢s σ ∶ ⊩κ {Γ} ⊩Γ ® ρ           = Gluκ Δ σ Γ ρ (_⊢s_∶ ⊩Γ ®_)
  Δ ⊢s σ ∶ ⊩∺ {Γ} {T} {i} ⊩Γ ⊢T gT ® ρ = Glu∺ i Δ σ T Γ ρ (_⊢s_∶ ⊩Γ ®_)

⊩⇒⊢ : ⊩ Γ → ⊢ Γ
⊩⇒⊢ ⊩[]          = ⊢[]
⊩⇒⊢ (⊩κ ⊩Γ)      = ⊢κ (⊩⇒⊢ ⊩Γ)
⊩⇒⊢ (⊩∺ ⊩Γ ⊢T _) = ⊢∺ (⊩⇒⊢ ⊩Γ) ⊢T

-- On paper this predicate denotes Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦ t ⟧(ρ) ∈El ⟦T⟧(ρ)
record GluExp i Δ t T (σ : Substs) ρ : Set where
  field
    ⟦T⟧   : D
    ⟦t⟧   : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
    t∼⟦t⟧ : Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦t⟧ ∈El T∈𝕌

record GluSubsts Δ τ (⊩Γ′ : ⊩ Γ′) σ ρ : Set where
  field
    ⟦τ⟧    : Envs
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ ↘ ⟦τ⟧
    τσ∼⟦τ⟧ : Δ ⊢s τ ∘ σ ∶ ⊩Γ′ ® ⟦τ⟧


------------------------------------
-- Definitions of semantic judgments

infix 4 _⊩_∶_ _⊩s_∶_

record _⊩_∶_ Γ t T : Set where
  field
    ⊩Γ   : ⊩ Γ
    -- This level always remembers the level of T and thus allows easy adaptation to non-cumulativity.
    lvl  : ℕ
    krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp lvl Δ t T σ ρ


record _⊩s_∶_ Γ τ Γ′ : Set where
  field
    ⊩Γ   : ⊩ Γ
    ⊩Γ′  : ⊩ Γ′
    krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluSubsts Δ τ ⊩Γ′ σ ρ
