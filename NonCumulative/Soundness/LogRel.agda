{-# OPTIONS --without-K --safe #-}

-- Definitions of logical relations for the gluing model and semantic judgments
module NonCumulative.Soundness.LogRel where

open import Lib
open import Data.Nat
open import Data.Nat.Properties

open import NonCumulative.Statics.Ascribed.Full public
open import NonCumulative.Semantics.Domain public
open import NonCumulative.Semantics.Evaluation public
open import NonCumulative.Semantics.PER public
open import NonCumulative.Soundness.Weakening public

-------------------------------------
-- Gluing models for terms and types

-- Gluing model for natural numbers
infix 4 _⊢_∶N®_∈Nat

data _⊢_∶N®_∈Nat : Ctx → Exp → D → Set where
  ze : Γ ⊢ t ≈ ze ∶[ 0 ] N →
       -----------------
       Γ ⊢ t ∶N® ze ∈Nat
  su : Γ ⊢ t ≈ su t′ ∶[ 0 ] N →
       Γ ⊢ t′ ∶N® a ∈Nat →
       --------------------
       Γ ⊢ t ∶N® su a ∈Nat
  ne : (c∈ : c ∈′ Bot) →
       (∀ {Δ σ} → Δ ⊢w σ ∶ Γ → let (u , _) = c∈ (len Δ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶[ 0 ] N) →
       -----------------------
       Γ ⊢ t ∶N® ↑ 0 N c ∈Nat

-- Helper concepts for the gluing model
--
-- These definitions are defined for the purpose of having more structural condition
-- management.  One can find unfolded definitions using conjunctions in the comments
-- near the definition of the gluing model.

-- Gluing model for Π
record ΠRel i Δ IT OT (σ : Subst)
             (iA : A ≈ B ∈ 𝕌 i)
             (RI : Ctx → Typ → Set)
             (RO : ∀ {a a′} → a ≈ a′ ∈ El i iA → Ctx → Typ → Set)
             (Rs : Ctx → Exp → Typ → D → Set) : Set where
  field
    IT-rel : RI Δ (IT [ σ ])
    OT-rel : Rs Δ s (IT [ σ ]) a → (a∈ : a ∈′ El i iA) → RO a∈ Δ (OT [ σ , s ∶ IT [ σ ] ↙ i ])


-- record GluΠ i Γ T {A B}
--             (iA : A ≈ B ∈ 𝕌 i)
--             (RI : Ctx → Typ → Set)
--             (RO : ∀ {a a′} → a ≈ a′ ∈ El i iA → Ctx → Typ → Set)
--             (Rs : Ctx → Exp → Typ → D → Set) : Set where
--   field
--     IT   : Typ
--     OT   : Typ
--     -- need this prop or it is too difficult to invert
--     ⊢OT  : IT ∷ Γ ⊢ OT ∶ Se i
--     T≈   : Γ ⊢ T ≈ Π IT OT ∶ Se i
--     krip : Δ ⊢w σ ∶ Γ → ΠRel i Δ IT OT σ iA RI RO Rs


-- -- Gluing model for Λ
-- record ΛKripke Δ t T f a (R$ : Ctx → Exp → Typ → D → Set) : Set where
--   field
--     fa : D
--     ↘fa : f ∙ a ↘ fa
--     ®fa : R$ Δ t T fa

-- record ΛRel i Δ t IT OT (σ : Subst ) f
--              (iA : A ≈ B ∈ 𝕌 i)
--              (RI : Ctx → Typ → Set)
--              (Rs : Ctx → Exp → Typ → D → Set)
--              (R$ : ∀ {a a′} → a ≈ a′ ∈ El i iA → Ctx → Exp → Typ → D → Set) : Set where
--   field
--     IT-rel : RI Δ (IT [ σ ])
--     ap-rel : Rs Δ s (IT [ σ ]) b → (b∈ : b ∈′ El i iA) → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ]) f b (R$ b∈)

--   flipped-ap-rel : (b∈ : b ∈′ El i iA) → ∀ {s} → Rs Δ s (IT [ σ ]) b → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ]) f b (R$ b∈)
--   flipped-ap-rel b∈ R = ap-rel R b∈

-- record GluΛ i Γ t T a {A B T′ T″ ρ ρ′}
--             (iA : A ≈ B ∈ 𝕌 i)
--             (RT : ∀ {a a′} → a ≈ a′ ∈ El i iA → ΠRT T′ (ρ ↦ a) T″ (ρ′ ↦ a′) (𝕌 i))
--             (RI : Ctx → Typ → Set)
--             (Rs : Ctx → Exp → Typ → D → Set)
--             (R$ : ∀ {a a′} → a ≈ a′ ∈ El i iA → Ctx → Exp → Typ → D → Set) : Set where
--   field
--     t∶T  : Γ ⊢ t ∶ T
--     a∈El : a ∈′ El i (Π iA RT)
--     IT   : Typ
--     OT   : Typ
--     -- need this prop or it is too difficult to invert
--     ⊢OT  : IT ∷ Γ ⊢ OT ∶ Se i
--     T≈   : Γ ⊢ T ≈ Π IT OT ∶ Se i
--     krip : Δ ⊢w σ ∶ Γ → ΛRel i Δ t IT OT σ a iA RI Rs R$

-- -- Gluing model for universes
-- record GluU j i Γ t T A (R : A ∈′ 𝕌 j → Set) : Set where
--   field
--     t∶T : Γ ⊢ t ∶ T
--     T≈  : Γ ⊢ T ≈ Se j ∶ Se i
--     A∈𝕌 : A ∈′ 𝕌 j
--     rel : R A∈𝕌

-- -- Gluing model for neutral terms
-- record GluNe i Γ t T (c∈⊥ : c ∈′ Bot) (C≈C′ : C ≈ C′ ∈ Bot) : Set where
--   field
--     t∶T : Γ ⊢ t ∶ T
--     ⊢T  : Γ ⊢ T ∶ Se i
--     krip : Δ ⊢w σ ∶ Γ →
--            let V , _ = C≈C′ (len Δ)
--                u , _ = c∈⊥ (len Δ)
--            in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
--             × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]


-- The definition of the gluing model
--
-- Due to cumulative universes, we must do a well-founded induction on the universe
-- level i.  The gluing model has two relations:
--
-- Γ ⊢ T ® A≈B : T and A (and B) are related at level i. It is A≈B again due to the
-- proof relevant nature of NonCumulative.
--
-- Γ ⊢ t ∶ T ® a ∈El A≈B : t and a are related. t has type T and a is in El A≈B. T and
-- A≈B are related in level i.

module Glu where

  mutual

    ®T : ∀ i (rc : ∀ {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set)
           (Univ : ∀ {j} → j < i → Ty) →
           ∀ {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 i Univ → Set
    ®T = {!!}

--     ®T : ∀ i (Univ : ∀ {j} → j < i → Ty)
--            (rc : ∀ {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set) →
--            Ctx → Typ → A ≈ B ∈ PERDef.𝕌 i Univ → Set
--     ®T i Univ rc Γ T (ne x x₁ x₂) = {!!}
--     ®T i Univ rc Γ T (N x) = {!!}
--     ®T i Univ rc Γ T (U x x₁) = {!!}
--     ®T i Univ rc Γ T (Π eq iA x x₁ x₂) = ®T _ (λ l<j → Univ (ΠI≤ eq l<j)) (λ j<i univ Δ T′ R → rc (≤-trans j<i {!!}) univ Δ T′ R) Γ {!!} iA
--     ®T i Univ rc Γ T (L eq x x₁ x₂) = {!!}

--     ®tm : ∀ i (Univ : ∀ {j} → j < i → Ty)
--             (rc : ∀ {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set) →
--             Ctx → Exp → Typ → D → A ≈ B ∈ PERDef.𝕌 i Univ → Set
--     ®tm i Univ rc Γ t T a (ne x x₁ x₂)      = {!!}
--     ®tm i Univ rc Γ t T a (N x)             = {!!}
--     ®tm i Univ rc Γ t T a (U {j} eq eq′)    = ®T j (λ l<j → Univ (≤-trans l<j {!!})) (λ l<j univ Δ T′ R → rc (≤-trans l<j {!!}) univ Δ T′ R) Γ t {!!}
--     ®tm i Univ rc Γ t T a (Π eq iA x x₁ x₂) = {!!}
--     ®tm i Univ rc Γ t T a (L eq x x₁ x₂)    = {!!}


-- -- module Glu i (Univ : ∀ {j} → j < i → Ty)
-- --              (rec : ∀ {j} (j<i : j < i) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j (λ l<j → Univ (<-trans l<j j<i)) → Set) where
-- --   infix 4 _⊢_®_ _⊢_∶_®_∈El_

-- --   mutual

-- --     _⊢_®_ : Ctx → Typ → A ≈ B ∈ PERDef.𝕌 i Univ → Set
-- --     Γ ⊢ T ® ne C≈C′ eq eq′     = Γ ⊢ T ∶[ 1 + i ] Se i × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ → let V , _ = C≈C′ (len Δ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶[ 1 + i ] Se i
-- --     Γ ⊢ T ® N eq               = Γ ⊢ T ≈ N ∶[ 1 ] Se 0
-- --     Γ ⊢ T ® U {j} eq eq′       = Γ ⊢ T ≈ Se j ∶[ 1 + i ] Se i
-- --     Γ ⊢ T ® Π {j = j} {_} {k} eq iA RT eq₁ eq₂ = {!!}
-- --       -- ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
-- --       --    × IT ∷ Γ ⊢ OT ∶ Se i
-- --       --    × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ →
-- --       --                (Δ ⊢ IT [ σ ] ® iA)
-- --       --              × ∀ {s a} (irel : Δ ⊢ s ∶ IT [ σ ] ® a ∈El iA) (a∈ : a ∈′ El i iA) → Δ ⊢ OT [ σ , s ] ® ΠRT.T≈T′ (RT a∈)
-- --     Γ ⊢ T ® L eq x x₁ x₂       = {!!}

-- --     _⊢_∶_®_∈El_ : Ctx → Exp → Typ → D → A ≈ B ∈ PERDef.𝕌 i Univ → Set
-- --     Γ ⊢ t ∶ T ® a ∈El A≈B = {!!}

-- -- --     _⊢_®_ : Ctx → Typ → A ≈ B ∈ 𝕌 i → Set
-- -- --     Γ ⊢ T ® ne C≈C′      = Γ ⊢ T ∶ Se i × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ → let V , _ = C≈C′ (len Δ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
-- -- --     Γ ⊢ T ® N            = Γ ⊢ T ≈ N ∶ Se i
-- -- --     Γ ⊢ T ® U {j} j<i eq = Γ ⊢ T ≈ Se j ∶ Se i
-- -- --     Γ ⊢ T ® Π iA RT      = GluΠ i Γ T iA (_⊢_® iA) (λ a∈ → _⊢_® ΠRT.T≈T′ (RT a∈)) (_⊢_∶_®_∈El iA)
-- -- --                            -- ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
-- -- --                            --    × IT ∷ Γ ⊢ OT ∶ Se i
-- -- --                            --    × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ →
-- -- --                            --                (Δ ⊢ IT [ σ ] ® iA)
-- -- --                            --              × ∀ {s a} (irel : Δ ⊢ s ∶ IT [ σ ] ® a ∈El iA) (a∈ : a ∈′ El i iA) → Δ ⊢ OT [ σ , s ] ® ΠRT.T≈T′ (RT a∈)

-- -- --     _⊢_∶_®_∈El_ : Ctx → Exp → Typ → D → A ≈ B ∈ 𝕌 i → Set
-- -- --     Γ ⊢ t ∶ T ® a ∈El ne C≈C′      = Σ (a ∈′ Neu) λ { (ne c∈⊥) → GluNe i Γ t T c∈⊥ C≈C′ }
-- -- --     Γ ⊢ t ∶ T ® a ∈El N            = Γ ⊢ t ∶N® a ∈Nat × Γ ⊢ T ≈ N ∶ Se i
-- -- --     Γ ⊢ t ∶ T ® a ∈El U {j} j<i eq = GluU j i Γ t T a (rec j<i Γ t)
-- -- --                                    --   Γ ⊢ t ∶ T
-- -- --                                    -- × Γ ⊢ T ≈ Se j ∶ Se i
-- -- --                                    -- × A ∈′ 𝕌 j
-- -- --                                    -- × Γ ⊢ t ® A∈𝕌
-- -- --     Γ ⊢ t ∶ T ® a ∈El Π iA RT      = GluΛ i Γ t T a iA RT (_⊢_® iA) (_⊢_∶_®_∈El iA) (λ b∈ → _⊢_∶_®_∈El ΠRT.T≈T′ (RT b∈))
-- -- --                                    -- Γ ⊢ t ∶ T × (a ∈′ El i (Π iA RT))
-- -- --                                    --   × ∃₂ λ IT OT → Γ ⊢ T ≈ Π IT OT ∶ Se i
-- -- --                                    --                × IT ∷ Γ ⊢ OT ∶ Se i
-- -- --                                    --                × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ →
-- -- --                                    --                          (Δ ⊢ IT [ σ ] ® iA (mt σ))
-- -- --                                    --                         × ∀ {s b} (irel : Δ ⊢ s ∶ IT [ σ ] ® b ∈El iA) (b∈ : b ∈′ El i iA) → ∃ λ ap → a [ mt σ ] ∙ b ↘ ap × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ® ap ∈El ΠRT.T≈T′ (RT b∈)


-- -- -- -- Similar to the PER model, we tie the knot using well-founded induction.
-- -- -- Glu-wellfounded : ∀ i {j} → j < i → ∀ {A B} → Ctx → Typ → A ≈ B ∈ 𝕌 j → Set
-- -- -- Glu-wellfounded .(suc _) {j} (s≤s j<i) = Glu._⊢_®_ j λ j′<j → Glu-wellfounded _ (≤-trans j′<j j<i)

-- -- -- private
-- -- --   module G i = Glu i (Glu-wellfounded i)

-- -- -- infix 4 _⊢_®[_]_ _⊢_∶_®[_]_∈El_

-- -- -- -- T and A are related at level i
-- -- -- _⊢_®[_]_ : Ctx → Typ → ∀ i → A ≈ B ∈ 𝕌 i → Set
-- -- -- Γ ⊢ T ®[ i ] A≈B = G._⊢_®_ i Γ T A≈B

-- -- -- -- t of type T and a of type A are related at level i
-- -- -- _⊢_∶_®[_]_∈El_ : Ctx → Exp → Typ → ∀ i → D → A ≈ B ∈ 𝕌 i → Set
-- -- -- Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B = G._⊢_∶_®_∈El_ i Γ t T a A≈B


-- -- -- -- In the PER model, we have three extrema PERs: Bot, Top and TopT. They relates equal
-- -- -- -- neutral values, equal normal values and equal normal semantic types after readback,
-- -- -- -- respctively. Similarly, we need the same notions in the gluing model. We need:
-- -- -- --
-- -- -- -- ®↓         : t and c are related iff t and any readback of c are equivalent.
-- -- -- -- ®↑ (value) : t and a are related iff t and any readback of a are equivalent.
-- -- -- -- ®↑ (type)  : T and A are related iff T and any readback of A are equivalent.
-- -- -- infix 4 _⊢_∶_®↓[_]_∈El_ _⊢_∶_®↑[_]_∈El_  _⊢_®↑[_]_

-- -- -- record _⊢_∶_®↓[_]_∈El_ Γ t T i c (A≈B : A ≈ B ∈ 𝕌 i) : Set where
-- -- --   field
-- -- --     t∶T  : Γ ⊢ t ∶ T
-- -- --     T∼A  : Γ ⊢ T ®[ i ] A≈B
-- -- --     c∈⊥  : c ∈′ Bot
-- -- --     krip : Δ ⊢w σ ∶ Γ → let u , _ = c∈⊥ (len Δ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]


-- -- -- record _⊢_∶_®↑[_]_∈El_ Γ t T i a (A≈B : A ≈ B ∈ 𝕌 i) : Set where
-- -- --   field
-- -- --     t∶T  : Γ ⊢ t ∶ T
-- -- --     T∼A  : Γ ⊢ T ®[ i ] A≈B
-- -- --     a∈⊤  : ↓ A a ≈ ↓ B a ∈ Top
-- -- --     krip : Δ ⊢w σ ∶ Γ → let w , _ = a∈⊤ (len Δ) in Δ ⊢ t [ σ ] ≈ Nf⇒Exp w ∶ T [ σ ]

-- -- -- record _⊢_®↑[_]_ Γ T i (A≈B : A ≈ B ∈ 𝕌 i) : Set where
-- -- --   field
-- -- --     t∶T  : Γ ⊢ T ∶ Se i
-- -- --     A∈⊤  : A ≈ B ∈ TopT
-- -- --     krip : Δ ⊢w σ ∶ Γ → let W , _ = A∈⊤ (len Δ) in Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i


-- -- -- ---------------------------------
-- -- -- -- Gluing model for substitutions

-- -- -- -- Helper predicates for each case of context stacks


-- -- -- -- R is always the gluing model for substitutions
-- -- -- record Glu∷ i Γ σ T Δ (ρ : Env) (R : Ctx → Subst → Env → Set) : Set where
-- -- --   field
-- -- --     ⊢σ   : Γ ⊢s σ ∶ T ∷ Δ
-- -- --     pσ   : Subst
-- -- --     v0σ  : Exp
-- -- --     ⟦T⟧  : D
-- -- --     ≈pσ  : Γ ⊢s p σ ≈ pσ ∶ Δ
-- -- --     ≈v0σ : Γ ⊢ v 0 [ σ ] ≈ v0σ ∶ T [ pσ ]
-- -- --     ↘⟦T⟧ : ⟦ T ⟧ drop ρ ↘ ⟦T⟧
-- -- --     T∈𝕌  : ⟦T⟧ ∈′ 𝕌 i
-- -- --     t∼ρ0 : Γ ⊢ v0σ ∶ (T [ pσ ]) ®[ i ] (lookup ρ 0) ∈El T∈𝕌
-- -- --     step : R Γ pσ (drop ρ)


-- -- -- -- On paper this predicate denotes Δ ⊢ T [ σ ] ®[ i ] ⟦T⟧(ρ)
-- -- -- record GluTyp i Δ T (σ : Subst) ρ : Set where
-- -- --   field
-- -- --     ⟦T⟧   : D
-- -- --     ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
-- -- --     T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
-- -- --     T∼⟦T⟧ : Δ ⊢ T [ σ ] ®[ i ] T∈𝕌

-- -- -- -- The definition of gluing model for substitutions
-- -- -- --
-- -- -- -- Similar to the PER model where we use induction-recursion to relate the
-- -- -- -- interpretations of substitutions, here we also use induction-recursion to relate
-- -- -- -- substitutions and evaluation environments.
-- -- -- --
-- -- -- -- This definition is not seen in others' work (A. Abel, D. Gratzer, etc.), where the
-- -- -- -- gluing for substitutions are done by induction on simply the constructor of the
-- -- -- -- contexts (or context stacks in our case). This model will work for cumulative
-- -- -- -- universes in a set-theoretic model, because in these proof one crucial step after
-- -- -- -- proving cumulativity of the model is to take the limit of the universe level, and
-- -- -- -- then the universe level is not spoken of. In type theory, on the other hand, we
-- -- -- -- cannot take limits. This thus forces us to consider universe levels explicitly,
-- -- -- -- leading us to this more precise model.
-- -- -- --
-- -- -- -- Another benefit of this higher precision is that this model can be adapted to
-- -- -- -- non-cumulative universe pretty well. In aforementioned work, since the step of
-- -- -- -- taking limit is essential, the information about universe levels is gone. It
-- -- -- -- becomes unclear how one can easily remove the step of taking limits and adapt their
-- -- -- -- proofs to non-cumulativity. On the other hand, our model keeps track of unvierse
-- -- -- -- levels so there is no problem to obtain the level from our model whenever it is
-- -- -- -- needed.
-- -- -- infix 4 ⊩_ _⊢s_∶_®_

-- -- -- mutual

-- -- --   -- This definition is almost the same as ⊢_ except that it has one more condition in
-- -- --   -- ⊩∷.
-- -- --   data ⊩_ : Ctx → Set where
-- -- --     ⊩[] : ⊩ []
-- -- --     ⊩∷  : ∀ {i} (⊩Γ : ⊩ Γ) →
-- -- --           Γ ⊢ T ∶ Se i →
-- -- --           -- This condition says, given any related σ and ρ, T[σ] and its evaluation
-- -- --           -- are related at level i.
-- -- --           (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩Γ ® ρ → GluTyp i Δ T σ ρ) →
-- -- --           ⊩ (T ∷ Γ)

-- -- --   -- The gluing model for substitutions
-- -- --   --
-- -- --   -- This model glues substitutions and evaluation environments. It is recursive on ⊩_
-- -- --   -- so this model is again inductive-recursive. We can see that in the ⊩∷ case, we
-- -- --   -- use the universe level. This removes our need to take limits as done in a more
-- -- --   -- set-thereotic setting.
-- -- --   _⊢s_∶_®_ : Ctx → Subst → ⊩ Δ → Env → Set
-- -- --   Δ ⊢s σ ∶ ⊩[] ® ρ                     = Δ ⊢s σ ∶ []
-- -- --   Δ ⊢s σ ∶ ⊩∷ {Γ} {T} {i} ⊩Γ ⊢T gT ® ρ = Glu∷ i Δ σ T Γ ρ (_⊢s_∶ ⊩Γ ®_)

-- -- -- ⊩⇒⊢ : ⊩ Γ → ⊢ Γ
-- -- -- ⊩⇒⊢ ⊩[]          = ⊢[]
-- -- -- ⊩⇒⊢ (⊩∷ ⊩Γ ⊢T _) = ⊢∷ (⊩⇒⊢ ⊩Γ) ⊢T

-- -- -- -- On paper this predicate denotes Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦ t ⟧(ρ) ∈El ⟦T⟧(ρ)
-- -- -- record GluExp i Δ t T (σ : Subst) ρ : Set where
-- -- --   field
-- -- --     ⟦T⟧   : D
-- -- --     ⟦t⟧   : D
-- -- --     ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
-- -- --     ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
-- -- --     T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
-- -- --     t∼⟦t⟧ : Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦t⟧ ∈El T∈𝕌

-- -- -- record GluSubst Δ τ (⊩Γ′ : ⊩ Γ′) σ ρ : Set where
-- -- --   field
-- -- --     ⟦τ⟧    : Env
-- -- --     ↘⟦τ⟧   : ⟦ τ ⟧s ρ ↘ ⟦τ⟧
-- -- --     τσ∼⟦τ⟧ : Δ ⊢s τ ∘ σ ∶ ⊩Γ′ ® ⟦τ⟧


-- -- -- ------------------------------------
-- -- -- -- Definitions of semantic judgments

-- -- -- infix 4 _⊩_∶_ _⊩s_∶_

-- -- -- record _⊩_∶_ Γ t T : Set where
-- -- --   field
-- -- --     ⊩Γ   : ⊩ Γ
-- -- --     -- This level always remembers the level of T and thus allows easy adaptation to non-cumulativity.
-- -- --     lvl  : ℕ
-- -- --     krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp lvl Δ t T σ ρ


-- -- -- record _⊩s_∶_ Γ τ Γ′ : Set where
-- -- --   field
-- -- --     ⊩Γ   : ⊩ Γ
-- -- --     ⊩Γ′  : ⊩ Γ′
-- -- --     krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluSubst Δ τ ⊩Γ′ σ ρ
