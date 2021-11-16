{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.PER where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.Readback
open import Relation.Binary using (Rel)

Ty : Set₁
Ty = Rel D _

Evs : Set₁
Evs = Rel Envs _

Bot : Dn → Dn → Set
Bot c c′ = ∀ ns (κ : UnMoT) → ∃ λ u → Re ns - c [ κ ] ↘ u × Re ns - c′ [ κ ] ↘ u

Top : Df → Df → Set
Top d d′ = ∀ ns (κ : UnMoT) → ∃ λ w → Rf ns - d [ κ ] ↘ w × Rf ns - d′ [ κ ] ↘ w

data Nat : Ty where
  ze : ze ≈ ze ∈ Nat
  su : a ≈ b ∈ Nat →
       -----------------
       su a ≈ su b ∈ Nat
  ne : c ≈ c′ ∈ Bot →
       --------------------
       ↑ N c ≈ ↑ N c′ ∈ Nat

data Neu : Ty where
  ne : c ≈ c′ ∈ Bot →
       ---------------------
       ↑ A c ≈ ↑ A′ c′ ∈ Neu

record ΠRT T ρ T′ ρ′ R : Set where
  field
    ⟦T⟧   : D
    ⟦T′⟧  : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦T′⟧ : ⟦ T′ ⟧ ρ′ ↘ ⟦T′⟧
    T≈T′  : ⟦T⟧ ≈ ⟦T′⟧ ∈ R
    nat   : ∀ (κ : UnMoT) → ⟦ T ⟧ ρ [ κ ] ↘ ⟦T⟧ [ κ ]
    nat′  : ∀ (κ : UnMoT) → ⟦ T′ ⟧ ρ′ [ κ ] ↘ ⟦T′⟧ [ κ ]

record □̂ n (a b : D) R : Set where
  field
    ua    : D
    ub    : D
    ↘ua   : unbox∙ n , a ↘ ua
    ↘ub   : unbox∙ n , b ↘ ub
    ua≈ub : ua ≈ ub ∈ R

record Π̂ (f a f′ a′ : D) R : Set where
  field
    fa     : D
    fa′    : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    fa≈fa′ : fa ≈ fa′ ∈ R
    nat    : ∀ (κ : UnMoT) → f [ κ ] ∙ a [ κ ] ↘ fa [ κ ]
    nat′   : ∀ (κ : UnMoT) → f′ [ κ ] ∙ a′ [ κ ] ↘ fa′ [ κ ]

module PERDef (i : ℕ) (Univ : ∀ {j} → j < i → Ty) where

  mutual

    data 𝕌 : Ty where
      ne : C ≈ C′ ∈ Bot →
           ↑ A C ≈ ↑ A′ C′ ∈ 𝕌
      N  : N ≈ N ∈ 𝕌
      U  : ∀ {j j′} →
           j < i →
           j ≡ j′ →             -- keeping equality here helps with --without-K settings
           --------------
           U j ≈ U j′ ∈ 𝕌
      □  : (∀ (κ : UnMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌) →
           --------------------------------
           □ A ≈ □ A′ ∈ 𝕌
      Π  : (iA : ∀ (κ : UnMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌) →
           (∀ {a a′} (κ : UnMoT) →
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

-- now we tie the knot and expose 𝕌 and El in the wild
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

𝕌∞ : Ty
𝕌∞ a b = ∃ λ i → a ≈ b ∈ 𝕌 i

El∞ : A ≈ B ∈ 𝕌∞ → Ty
El∞ (i , A≈B) a b = a ≈ b ∈ El i A≈B


record RelTyp T ρ T′ ρ′ : Set where
  field
    ⟦T⟧   : D
    ⟦T′⟧  : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦T′⟧ : ⟦ T′ ⟧ ρ′ ↘ ⟦T′⟧
    T≈T′  : ⟦T⟧ ≈ ⟦T′⟧ ∈ 𝕌∞
    nat   : ∀ (κ : UnMoT) → ⟦ T ⟧ ρ [ κ ] ↘ ⟦T⟧ [ κ ]
    nat′  : ∀ (κ : UnMoT) → ⟦ T′ ⟧ ρ′ [ κ ] ↘ ⟦T′⟧ [ κ ]

infix 4 ⊨_≈_
mutual
  data ⊨_≈_ : Ctxs → Ctxs → Set where
    []-≈   : ⊨ [] ∷ [] ≈ [] ∷ []
    κ-cong : ⊨ Γ ≈ Δ →
             -------------------
             ⊨ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
    ∷-cong : (Γ≈Δ : ⊨ Γ ≈ Δ) →
             (∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → RelTyp T ρ T′ ρ′) →
             ----------------
             ⊨ T ∺ Γ ≈ T′ ∺ Δ

  ⟦_⟧ρ : ⊨ Γ ≈ Δ → Evs
  ⟦ []-≈ ⟧ρ ρ ρ′           = ⊤
  ⟦ κ-cong Γ≈Δ ⟧ρ ρ ρ′     = (ρ ∥ 1 ≈ ρ′ ∥ 1 ∈ ⟦ Γ≈Δ ⟧ρ) × proj₁ (ρ 0) ≡ proj₁ (ρ′ 0)
  ⟦ ∷-cong Γ≈Δ rel ⟧ρ ρ ρ′ = Σ (drop ρ ≈ drop ρ′ ∈ ⟦ Γ≈Δ ⟧ρ) λ ρ≈ρ′ → let open RelTyp (rel ρ≈ρ′) in lookup ρ 0 ≈ lookup ρ′ 0 ∈ El∞ T≈T′

⊨_ : Ctxs → Set
⊨ Γ = ⊨ Γ ≈ Γ
