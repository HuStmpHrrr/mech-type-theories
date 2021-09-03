{-# OPTIONS --without-K --safe #-}

module STLC.NBE where

open import Lib
open import STLC.Statics
open import Data.Unit using (tt; ⊤)

data Nf : Ctx → Typ → Set
data Ne : Ctx → Typ → Set

data Nf where
  *  : Nf Γ *
  pr : (s : Nf Γ S) (u : Nf Γ U) → Nf Γ (S X U)
  Λ  : Nf (S ∷ Γ) U → Nf Γ (S ⟶ U)
  ne : (t : Ne Γ T) → Nf Γ T

data Ne where
  var : T ∈ Γ → Ne Γ T
  π₁  : Ne Γ (S X U) → Ne Γ S
  π₂  : Ne Γ (S X U) → Ne Γ U
  _$_ : Ne Γ (S ⟶ U) → (s : Nf Γ S) → Ne Γ U

Nf⇒Trm : Nf Γ T → Trm Γ T
Ne⇒Trm : Ne Γ T → Trm Γ T

Nf⇒Trm *        = *
Nf⇒Trm (pr s u) = pr (Nf⇒Trm s) (Nf⇒Trm u)
Nf⇒Trm (Λ t)    = Λ (Nf⇒Trm t)
Nf⇒Trm (ne t)   = Ne⇒Trm t

Ne⇒Trm (var T∈Γ) = var T∈Γ
Ne⇒Trm (π₁ t)    = π₁ (Ne⇒Trm t)
Ne⇒Trm (π₂ t)    = π₂ (Ne⇒Trm t)
Ne⇒Trm (t $ s)   = Ne⇒Trm t $ Nf⇒Trm s

shiftₙ : Nf Γ T → Γ ⊆ Γ′ → Nf Γ′ T
shiftₑ : Ne Γ T → Γ ⊆ Γ′ → Ne Γ′ T

shiftₙ * Γ⊆Γ′        = *
shiftₙ (pr s u) Γ⊆Γ′ = pr (shiftₙ s Γ⊆Γ′) (shiftₙ u Γ⊆Γ′)
shiftₙ (Λ t) Γ⊆Γ′    = Λ (shiftₙ t (refl ∷ Γ⊆Γ′))
shiftₙ (ne t) Γ⊆Γ′   = ne (shiftₑ t Γ⊆Γ′)

shiftₑ (var T∈Γ) Γ⊆Γ′ = var (∈-⊆ T∈Γ Γ⊆Γ′)
shiftₑ (π₁ t) Γ⊆Γ′    = π₁ (shiftₑ t Γ⊆Γ′)
shiftₑ (π₂ t) Γ⊆Γ′    = π₂ (shiftₑ t Γ⊆Γ′)
shiftₑ (t $ s) Γ⊆Γ′   = shiftₑ t Γ⊆Γ′ $ shiftₙ s Γ⊆Γ′

shiftₙ-shiftₙ : ∀ (t : Nf Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) (Γ′⊆Γ″ : Γ′ ⊆ Γ″) →
  shiftₙ (shiftₙ t Γ⊆Γ′) Γ′⊆Γ″ ≡ shiftₙ t (⊆-trans Γ⊆Γ′ Γ′⊆Γ″)

shiftₑ-shiftₑ : ∀ (t : Ne Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) (Γ′⊆Γ″ : Γ′ ⊆ Γ″) →
  shiftₑ (shiftₑ t Γ⊆Γ′) Γ′⊆Γ″ ≡ shiftₑ t (⊆-trans Γ⊆Γ′ Γ′⊆Γ″)

shiftₙ-shiftₙ * Γ⊆Γ′ Γ′⊆Γ″        = refl
shiftₙ-shiftₙ (pr s u) Γ⊆Γ′ Γ′⊆Γ″ = cong₂ pr (shiftₙ-shiftₙ s Γ⊆Γ′ Γ′⊆Γ″) (shiftₙ-shiftₙ u Γ⊆Γ′ Γ′⊆Γ″)
shiftₙ-shiftₙ (Λ t) Γ⊆Γ′ Γ′⊆Γ″    = cong Λ (shiftₙ-shiftₙ t (refl ∷ Γ⊆Γ′) (refl ∷ Γ′⊆Γ″))
shiftₙ-shiftₙ (ne t) Γ⊆Γ′ Γ′⊆Γ″   = cong ne (shiftₑ-shiftₑ t Γ⊆Γ′ Γ′⊆Γ″)

shiftₑ-shiftₑ (var T∈Γ) Γ⊆Γ′ Γ′⊆Γ″ = cong var (∈-⊆-trans T∈Γ Γ⊆Γ′ Γ′⊆Γ″)
shiftₑ-shiftₑ (π₁ t) Γ⊆Γ′ Γ′⊆Γ″    = cong π₁ (shiftₑ-shiftₑ t Γ⊆Γ′ Γ′⊆Γ″)
shiftₑ-shiftₑ (π₂ t) Γ⊆Γ′ Γ′⊆Γ″    = cong π₂ (shiftₑ-shiftₑ t Γ⊆Γ′ Γ′⊆Γ″)
shiftₑ-shiftₑ (t $ s) Γ⊆Γ′ Γ′⊆Γ″   = cong₂ _$_ (shiftₑ-shiftₑ t Γ⊆Γ′ Γ′⊆Γ″) (shiftₙ-shiftₙ s Γ⊆Γ′ Γ′⊆Γ″)

-- ⟦_⊢_⟧ : Ctx → Typ → Set
-- ⟦_⊢_⟧′ : Ctx → Typ → Set

-- ⟦ Γ ⊢ T ⟧ = Nf Γ T × ⟦ Γ ⊢ T ⟧′

-- ⟦ Γ ⊢ * ⟧′     = ⊤
-- ⟦ Γ ⊢ S X U ⟧′ = ⟦ Γ ⊢ S ⟧ × ⟦ Γ ⊢ U ⟧
-- ⟦ Γ ⊢ S ⟶ U ⟧′ = ∀ {Γ′} → Γ ⊆ Γ′ → ⟦ Γ′ ⊢ S ⟧ → ⟦ Γ′ ⊢ U ⟧

module NBE₁ where
  ⟦_⊢_⟧ : Ctx → Typ → Set
  ⟦ Γ ⊢ * ⟧     = ⊤
  ⟦ Γ ⊢ S X U ⟧ = ⟦ Γ ⊢ S ⟧ × ⟦ Γ ⊢ U ⟧
  ⟦ Γ ⊢ S ⟶ U ⟧ = ∀ {Γ′} → Γ ⊆ Γ′ → ⟦ Γ′ ⊢ S ⟧ → ⟦ Γ′ ⊢ U ⟧

  reify : ⟦ Γ ⊢ T ⟧ → Nf Γ T
  reflect : Ne Γ T → ⟦ Γ ⊢ T ⟧

  reify {_} {*} sem           = *
  reify {_} {S X U} (s₁ , s₂) = pr (reify s₁) (reify s₂)
  reify {_} {S ⟶ U} sem       = Λ (reify (sem (S ∷ʳ ⊆-refl) (reflect (var 0d))))

  reflect {_} {*} t              = tt
  reflect {_} {S X U} t          = reflect (π₁ t) , reflect (π₂ t)
  reflect {_} {S ⟶ U} t Γ⊆Γ′ ⟦S⟧ = reflect (shiftₑ t Γ⊆Γ′ $ reify ⟦S⟧)

  shiftₛ : Γ ⊆ Γ′ → ⟦ Γ ⊢ T ⟧ → ⟦ Γ′ ⊢ T ⟧
  shiftₛ {_} {_} {*} Γ⊆Γ′ ⟦T⟧             = tt
  shiftₛ {_} {_} {S X U} Γ⊆Γ′ (⟦S⟧ , ⟦U⟧) = shiftₛ Γ⊆Γ′ ⟦S⟧ , shiftₛ Γ⊆Γ′ ⟦U⟧
  shiftₛ {_} {_} {S ⟶ U} Γ⊆Γ′ ⟦T⟧ Γ′⊆Γ″   = ⟦T⟧ (⊆-trans Γ⊆Γ′ Γ′⊆Γ″)

  ⟦_⇒_⟧ : Ctx → Ctx → Set
  ⟦_⇒_⟧ Γ = All ⟦ Γ ⊢_⟧

  eval : ⟦ Δ ⇒ Γ ⟧ → Trm Γ T → ⟦ Δ ⊢ T ⟧
  eval ΔΓ *              = tt
  eval ΔΓ (var T∈Γ)      = All′.lookup ΔΓ T∈Γ
  eval ΔΓ (pr s u)       = eval ΔΓ s , eval ΔΓ u
  eval ΔΓ (π₁ t)         = proj₁ (eval ΔΓ t)
  eval ΔΓ (π₂ t)         = proj₂ (eval ΔΓ t)
  eval ΔΓ (s $ u)        = eval ΔΓ s ⊆-refl (eval ΔΓ u)
  eval ΔΓ (Λ t) Δ⊆Γ′ ⟦S⟧ = eval (⟦S⟧ ∷ All′.map (shiftₛ Δ⊆Γ′) ΔΓ) t

  ⇒-id : ⟦ Γ ⇒ Γ ⟧
  ⇒-id {[]}    = []
  ⇒-id {T ∷ Γ} = reflect (var 0d) ∷ All′.map (shiftₛ (T ∷ʳ ⊆-refl)) ⇒-id

  nbe : Trm Γ T → Nf Γ T
  nbe t = reify (eval ⇒-id t)

  -- test : (Γ : Ctx) (T : Typ) → Set
  -- test Γ T = {!nbe {(T ⟶ T) ∷ []} (var 0d)!}


module NBE₂ where

  CPred : Set₁
  CPred = Ctx → Set

  ⟦_⟧ : Typ → CPred
  ⟦ * ⟧ _      = ⊤
  ⟦ S X U ⟧ Γ  = ⟦ S ⟧ Γ × ⟦ U ⟧ Γ
  ⟦ S ⟶ U ⟧ Γ = ∀ {Γ′} → Γ ⊆ Γ′ → ⟦ S ⟧ Γ′ → ⟦ U ⟧ Γ′

  mutual
    reify : ∀ {Γ} T → ⟦ T ⟧ Γ → Nf Γ T
    reify * ⟦T⟧               = *
    reify (S X U) (⟦S⟧ , ⟦U⟧) = pr (reify S ⟦S⟧) (reify U ⟦U⟧)
    reify (S ⟶ U) ⟦T⟧         = Λ (reify U (⟦T⟧ (S ∷ʳ ⊆-refl) (reflect S (var 0d))))

    reflect : ∀ {Γ} T → Ne Γ T → ⟦ T ⟧ Γ
    reflect * t                = tt
    reflect (S X U) t          = reflect S (π₁ t) , reflect U (π₂ t)
    reflect (S ⟶ U) t Γ⊆Γ′ ⟦S⟧ = reflect U (shiftₑ t Γ⊆Γ′ $ (reify S ⟦S⟧))
