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
    El (□ A≈A′)   = λ a b → ∀ n κ → □̂ n (a [ κ ]) (b [ κ ]) (El (A≈A′ κ))
    El (Π iA RT)  = λ f f′ → ∀ {a b} κ (inp : a ≈ b ∈ El (iA κ)) → Π̂ (f [ κ ]) a (f′ [ κ ]) b (El (ΠRT.T≈T′ (RT κ inp)))

-- now we tie the knot and expose 𝕌 and El in the wild

private
  𝕌-wellfounded : ∀ i {j} → j < i → Ty
  𝕌-wellfounded .(suc _) (s≤s {j} j<i) = PERDef.𝕌 j (λ j′<j → 𝕌-wellfounded _ (≤-trans j′<j j<i))

  module M i = PERDef i (𝕌-wellfounded i)

open M hiding (𝕌; El) public

𝕌 : ℕ → Ty
𝕌 = M.𝕌

-- cannot omit `i`. not sure why
El : ∀ i → A ≈ B ∈ 𝕌 i → Ty
El i = M.El i
