{-# OPTIONS --without-K --safe #-}

-- Definition of the PER model
--
-- The PER model relates two domain values such that the syntactic terms they
-- represent are equivalent. Since we are handling MLTT with full a ω universe, we must
-- use a feature, induction-recursion, to strengthen the logical power of the
-- meta-language.
module Mints.Semantics.PER where

open import Data.Nat.Properties

open import Lib
open import Mints.Semantics.Domain
open import Mints.Semantics.Evaluation
open import Mints.Semantics.Readback
open import Relation.Binary using (Rel)

Ty : Set₁
Ty = Rel D _

Evs : Set₁
Evs = Rel Envs _

-- Two neutral domain values are related if they are read back equal up to any UMoT
Bot : Dn → Dn → Set
Bot c c′ = ∀ ns (κ : UMoT) → ∃ λ u → Re ns - c [ κ ] ↘ u × Re ns - c′ [ κ ] ↘ u

-- Two normal domain values are related if they are read back equal up to any UMoT
Top : Df → Df → Set
Top d d′ = ∀ ns (κ : UMoT) → ∃ λ w → Rf ns - d [ κ ] ↘ w × Rf ns - d′ [ κ ] ↘ w

-- Two domain values intended to represent types are related if they are read back equal up to any UMoT
TopT : D → D → Set
TopT A B = ∀ ns (κ : UMoT) → ∃ λ W → Rty ns - A [ κ ] ↘ W × Rty ns - B [ κ ] ↘ W

-- A PER to model natural number values
data Nat : Ty where
  ze : ze ≈ ze ∈ Nat
  su : a ≈ b ∈ Nat →
       -----------------
       su a ≈ su b ∈ Nat
  ne : c ≈ c′ ∈ Bot →
       --------------------
       ↑ N c ≈ ↑ N c′ ∈ Nat

-- Neutral type values are related simply when the neutral values themselves are related by Bot
data Neu : Ty where
  ne : c ≈ c′ ∈ Bot →
       ---------------------
       ↑ A c ≈ ↑ A′ c′ ∈ Neu

-- Now we move on to defining the PER model. To model the universes, we use
-- Tarski-style encoding, i.e. for a universe level i, 𝕌 i is a PER relating two
-- domain values (or "codes") that are types (i.e. elements of the i'th level
-- universe). If A ≈ B ∈ 𝕌 i, then El i A relates two values that are elements of the
-- set encoded by A.
--
-- Unfortunately, this method only works on paper. In type theory, we must consider
-- the effect of proof relevance, when defining El, we must take a witness
-- A≈B : A ≈ B ∈ 𝕌 i instead of just A, and El is defined by recursion on A≈B, while 𝕌
-- itself is defined inductively, hence a induction-recursion definition.
--
-- Finally, we need a well-founded definition in order to handle cumulative
-- universe. In a non-cumulative setting, we expect that this extra well-founded layer
-- by the universe level can be taken away, because we can only grow the universe
-- level by one each time.


-- Helper definitions for the PER model

-- The record for relating return types of Π's
--
-- Here R is always 𝕌 i, so on paper, it represents ⟦T⟧(ρ) ≈ ⟦T′⟧(ρ′) ∈ 𝕌 i.
record ΠRT T ρ T′ ρ′ R : Set where
  field
    ⟦T⟧   : D
    ⟦T′⟧  : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦T′⟧ : ⟦ T′ ⟧ ρ′ ↘ ⟦T′⟧
    T≈T′  : ⟦T⟧ ≈ ⟦T′⟧ ∈ R

-- The record for relating values of type □ A
--
-- Here R is always El i A, so on paper, it represents unbox n a ≈ unbox n b ∈ El i (A [ ins vone n ]).
-- The modal transformation is needed to keep the value consistent.
-- For further explanations please refer to our paper.
record □̂ n (a b : D) R : Set where
  field
    ua    : D
    ub    : D
    ↘ua   : unbox∙ n , a ↘ ua
    ↘ub   : unbox∙ n , b ↘ ub
    ua≈ub : ua ≈ ub ∈ R

-- The record for relating values of type Π A T ρ
--
-- Here R is always El i ⟦T⟧(ρ ↦ a), so on paper, it represents f a ≈ f′ a′ ∈ El i ⟦T⟧(ρ ↦ a).
record Π̂ (f a f′ a′ : D) R : Set where
  field
    fa     : D
    fa′    : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    fa≈fa′ : fa ≈ fa′ ∈ R

module PERDef (i : ℕ) (Univ : ∀ {j} → j < i → Ty) where

  mutual

    data 𝕌 : Ty where
      ne : C ≈ C′ ∈ Bot →
           ↑ A C ≈ ↑ A′ C′ ∈ 𝕌
      N  : N ≈ N ∈ 𝕌
      U  : ∀ {j j′} →
           j < i →            -- cumulativity only requires j < i
           j ≡ j′ →           -- keeping equality here helps with --without-K settings
           --------------
           U j ≈ U j′ ∈ 𝕌
      □  : (∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌) →
           -- Due to modality, we must require PER model to be invariant under UMoT
           --------------------------------
           □ A ≈ □ A′ ∈ 𝕌
      Π  : (iA : ∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌) →
           (∀ {a a′} (κ : UMoT) →
              a ≈ a′ ∈ El (iA κ) →
              ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) 𝕌) →
           -------------------------
           Π A T ρ ≈ Π A′ T′ ρ′ ∈ 𝕌


    El : A ≈ B ∈ 𝕌 → Ty
    El (ne C≈C′)  = Neu
    El N          = Nat
    El (U j<i eq) = Univ j<i
    El (□ A≈A′)   = λ a b → ∀ n κ → □̂ n (a [ κ ]) (b [ κ ]) (El (A≈A′ (ins κ n)))
    El (Π iA RT)  = λ f f′ → ∀ {a b} κ (inp : a ≈ b ∈ El (iA κ)) → Π̂ (f [ κ ]) a (f′ [ κ ]) b (El (ΠRT.T≈T′ (RT κ inp)))

-- Now we tie the knot and expose 𝕌 and El in the wild.
𝕌-wellfounded : ∀ i {j} → j < i → Ty
𝕌-wellfounded .(suc _) (s≤s {j} j<i) = PERDef.𝕌 j (λ j′<j → 𝕌-wellfounded _ (≤-trans j′<j j<i))

private
  module M i = PERDef i (𝕌-wellfounded i)

open M hiding (𝕌; El) public

pattern U′ i<j = U i<j refl

𝕌 : ℕ → Ty
𝕌 = M.𝕌

-- cannot omit `i`. not sure why
El : ∀ i → A ≈ B ∈ 𝕌 i → Ty
El i = M.El i


-- On paper, it represents ⟦T⟧(ρ) ≈ ⟦T′⟧(ρ′) ∈ 𝕌 i.
record RelTyp i T ρ T′ ρ′ : Set where
  field
    ⟦T⟧   : D
    ⟦T′⟧  : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦T′⟧ : ⟦ T′ ⟧ ρ′ ↘ ⟦T′⟧
    T≈T′  : ⟦T⟧ ≈ ⟦T′⟧ ∈ 𝕌 i

-- PER model for context stacks and global evaluation environments
--
-- Again we use induction-recursion here in order to model related context stacks and
-- related evaluation environments.
--
-- ⊨ Γ ≈ Δ means that Γ and Δ are two related context stacks so that every
-- corresponding types in them are related after evaluation. The PER for global
-- evaluation environments is defined recursively on ⊨ Γ ≈ Δ. On paper, we write
--
--       ρ ≈ ρ′ ∈ ⟦ Γ ⟧
--
-- where ⊨ Γ ≈ Γ, but this again will not work in Agda due to proof relevance. For
-- this reason, we must prove some extra properties.
infix 4 ⊨_≈_ ⊨_
mutual
  data ⊨_≈_ : Ctxs → Ctxs → Set where
    []-≈   : ⊨ [] ∷ [] ≈ [] ∷ []
    κ-cong : ⊨ Γ ≈ Δ →
             -------------------
             ⊨ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
    ∺-cong : ∀ {i} →
             (Γ≈Δ : ⊨ Γ ≈ Δ) →
             (∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → RelTyp i T ρ T′ ρ′) →
             ----------------
             ⊨ T ∺ Γ ≈ T′ ∺ Δ

  ⟦_⟧ρ : ⊨ Γ ≈ Δ → Evs
  ⟦ []-≈ ⟧ρ ρ ρ′           = ⊤
  ⟦ κ-cong Γ≈Δ ⟧ρ ρ ρ′     = (ρ ∥ 1 ≈ ρ′ ∥ 1 ∈ ⟦ Γ≈Δ ⟧ρ) × proj₁ (ρ 0) ≡ proj₁ (ρ′ 0)
  ⟦ ∺-cong Γ≈Δ rel ⟧ρ ρ ρ′ = Σ (drop ρ ≈ drop ρ′ ∈ ⟦ Γ≈Δ ⟧ρ) λ ρ≈ρ′ → let open RelTyp (rel ρ≈ρ′) in lookup ρ 0 ≈ lookup ρ′ 0 ∈ El _ T≈T′

⊨_ : Ctxs → Set
⊨ Γ = ⊨ Γ ≈ Γ
