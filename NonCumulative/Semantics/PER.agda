{-# OPTIONS --without-K --safe #-}

-- Definition of the PER model
--
-- The PER model relates two domain values such that the syntactic terms they
-- represent are equivalent. Since we are handling NonCumulative with full a ω universe, we must
-- use a feature, induction-recursion, to strengthen the logical power of the
-- meta-language.
module NonCumulative.Semantics.PER where

open import Data.Nat.Properties

open import Lib
open import NonCumulative.Semantics.Domain
open import NonCumulative.Semantics.Evaluation
open import NonCumulative.Semantics.Readback
open import Relation.Binary using (Rel)

Ty : Set₁
Ty = Rel D _

Ev : Set₁
Ev = Rel Env _

-- Two neutral domain values are related if they are read back equal
Bot : Dn → Dn → Set
Bot c c′ = ∀ n → ∃ λ u → Re n - c ↘ u × Re n - c′ ↘ u

-- Two normal domain values are related if they are read back equal
Top : Df → Df → Set
Top d d′ = ∀ n → ∃ λ w → Rf n - d ↘ w × Rf n - d′ ↘ w

-- Two domain values intended to represent types are related if they are read back equal
TopT : ℕ → D → D → Set
TopT i A B = ∀ n → ∃ λ W → Rty n - A at i ↘ W × Rty n - B at i ↘ W

-- A PER to model natural number values
data Nat : Ty where
  ze : ze ≈ ze ∈ Nat
  su : a ≈ b ∈ Nat →
       -----------------
       su a ≈ su b ∈ Nat
  ne : c ≈ c′ ∈ Bot →
       --------------------
       ↑ 0 N c ≈ ↑ 0 N c′ ∈ Nat

-- Neutral type values are related simply when the neutral values themselves are related by Bot
data Neu : ℕ → Ty where
  ne : ∀ {i j j′} →
       c ≈ c′ ∈ Bot →
       j ≡ i →
       j′ ≡ i →
       ---------------------
       ↑ j A c ≈ ↑ j′ A′ c′ ∈ Neu i


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


record Unli R (a b : D) : Set where
  field
    ua    : D
    ub    : D
    ↘ua   : unli∙ a ↘ ua
    ↘ub   : unli∙ b ↘ ub
    ua≈ub : ua ≈ ub ∈ R


ΠI≤ : ∀ {i j k l} → i ≡ max j k → l < j → l < i
ΠI≤ {_} {j} {k} eq l<j = ≤-trans l<j (≤-trans (m≤m⊔n j k) (≤-reflexive (sym eq)))

ΠI≤′ : ∀ {i l} j k → i ≡ max j k → l < j → l < i
ΠI≤′ j k = ΠI≤

ΠO≤ : ∀ {i j k l} → i ≡ max j k → l < k → l < i
ΠO≤ {_} {j} {k} eq l<k = ≤-trans l<k (≤-trans (m≤n⊔m j k) (≤-reflexive (sym eq)))

ΠO≤′ : ∀ {i l} j k → i ≡ max j k → l < k → l < i
ΠO≤′ j k = ΠO≤

Li≤ : ∀ {i j k l} → i ≡ j + k → l < k → l < i
Li≤{_} {j} {k} eq l<k = ≤-trans l<k (≤-trans (m≤n+m k j) (≤-reflexive (sym eq)))

Li≤′ : ∀ {i l} j k → i ≡ j + k → l < k → l < i
Li≤′ j k = Li≤

module PERDef where

  mutual
    data 𝕌 i (Univ : ∀ {j} → j < i → Ty) : Ty where
      ne : ∀ {j j′} →
           C ≈ C′ ∈ Bot →
           j ≡ suc i →
           j′ ≡ suc i →
           -------------------------------
           ↑ j A C ≈ ↑ j′ A′ C′ ∈ 𝕌 i Univ
      N  : i ≡ 0 →
           ------------------
           N ≈ N ∈ 𝕌 i Univ
      U  : ∀ {j j′} →
           i ≡ suc j →
           j ≡ j′ →           -- keeping equality here helps with --without-K settings
           --------------
           U j ≈ U j′ ∈ 𝕌 i Univ
      Π  : ∀ {j j′ k k′}
             (eq : i ≡ max j k) →
           let Univj : ∀ {l} → l < j → Ty
               Univj = λ l<j → Univ (ΠI≤ eq l<j)
               Univk : ∀ {l} → l < k → Ty
               Univk = λ l<k → Univ (ΠO≤ eq l<k) in
           (iA : A ≈ A′ ∈ 𝕌 j Univj) →
           (∀ {a a′} →
              a ≈ a′ ∈ El j Univj iA →
              ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 k Univk)) →
           j ≡ j′ →
           k ≡ k′ →
           -------------------------
           Π j A (T ↙ k) ρ ≈ Π j′ A′ (T′ ↙ k′) ρ′ ∈ 𝕌 i Univ
      L  : ∀ {j j′ k k′}
             (eq : i ≡ j + k) →
           A ≈ A′ ∈ 𝕌 k (λ l<k → Univ (Li≤ eq l<k)) →
           j ≡ j′ →
           k ≡ k′ →
           Li j k A ≈ Li j′ k′ A′ ∈ 𝕌 i Univ


    El : ∀ i (Univ : ∀ {j} → j < i → Ty) → A ≈ B ∈ 𝕌 i Univ → Ty
    El i Univ (ne C≈C′ _ _)   = Neu i
    El i Univ (N _)           = Nat
    El i Univ (U eq _)        = Univ (≤-reflexive (sym eq))
    El i Univ (Π _ iA RT _ _) = λ f f′ → ∀ {a b} (inp : a ≈ b ∈ El _ {- j -} _ iA) → Π̂ f a f′ b (El _ {- k -} _ (ΠRT.T≈T′ (RT inp)))
    El i Univ (L eq A≈A′ _ _) = Unli (El _ _ A≈A′)


-- Now we tie the knot and expose 𝕌 and El in the wild.
𝕌-wellfounded : ∀ i {j} → j < i → Ty
𝕌-wellfounded .(suc _) (s≤s {j} j<i) = PERDef.𝕌 j (λ j′<j → 𝕌-wellfounded _ (≤-trans j′<j j<i))


open PERDef hiding (𝕌; El) public

pattern ne′ C≈C′ = ne C≈C′ refl refl
pattern N′ = N refl
pattern U′ {j} = U {j = j} refl refl
pattern Π′ {j} {k} iA RT = Π {j = j} {k = k} refl iA RT refl refl
pattern L′ {j} {k} A≈A′ = L {j = j} {k = k} refl A≈A′ refl refl

𝕌 : ℕ → Ty
𝕌 i = PERDef.𝕌 i (𝕌-wellfounded i)

El : ∀ i → A ≈ B ∈ 𝕌 i → Ty
El i = PERDef.El i (𝕌-wellfounded i)


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
-- ⊨ Γ ≈ Δ means that Γ and Δ are two related contexts so that every
-- corresponding types in them are related after evaluation. The PER for
-- evaluation environments is defined recursively on ⊨ Γ ≈ Δ. On paper, we write
--
--       ρ ≈ ρ′ ∈ ⟦ Γ ⟧
--
-- where ⊨ Γ ≈ Γ, but this again will not work in Agda due to proof relevance. For
-- this reason, we must prove some extra properties.
infix 4 ⊨_≈_ ⊨_
mutual
  data ⊨_≈_ : Ctx → Ctx → Set where
    []-≈   : ⊨ [] ≈ []
    ∷-cong : ∀ {i j} →
             (Γ≈Δ : ⊨ Γ ≈ Δ) →
             (∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → RelTyp i T ρ T′ ρ′) →
             i ≡ j →
             ----------------
             ⊨ (T ↙ i) ∷ Γ ≈ (T′ ↙ j) ∷ Δ

  ⟦_⟧ρ : ⊨ Γ ≈ Δ → Ev
  ⟦ []-≈ ⟧ρ ρ ρ′              = ⊤
  ⟦ ∷-cong Γ≈Δ rel eq ⟧ρ ρ ρ′ = Σ (drop ρ ≈ drop ρ′ ∈ ⟦ Γ≈Δ ⟧ρ) λ ρ≈ρ′ → let open RelTyp (rel ρ≈ρ′) in lookup ρ 0 ≈ lookup ρ′ 0 ∈ El _ T≈T′

⊨_ : Ctx → Set
⊨ Γ = ⊨ Γ ≈ Γ
