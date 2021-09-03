{-# OPTIONS --without-K --safe #-}

module WithNat.NBE where

open import Lib
open import WithNat.Statics

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional
open import Data.Unit using (tt; ⊤)

variable
  s t u : Trm Γ T
  s′ t′ u′ : Trm Γ T

infix 0 _≈_
data _≈_ : (s u : Trm Γ T) → Set where
  reflx    : t ≈ t
  symm     : s ≈ u → u ≈ s
  tran     : s ≈ t → t ≈ u → s ≈ u

  *-η      : t ≈ *
  pr-η     : t ≈ pr (π₁ t) (π₂ t)
  π₁-β     : π₁ (pr s u) ≈ s
  π₂-β     : π₂ (pr s u) ≈ u
  rec-β₁   : rec s u ze ≈ s
  rec-β₂   : rec s u (su t) ≈ (u $ t) $ (rec s u t)
  Λ-η      : t ≈ Λ (shift t (S ∷ʳ ⊆-refl) $ var 0d)
  $-β      : (Λ t) $ s ≈ t ⟦ s ⟧!

  su-cong  : t ≈ t′ → su t ≈ su t′
  rec-cong : s ≈ s′ → u ≈ u′ → t ≈ t′ → rec s u t ≈ rec s′ u′ t′
  pr-cong  : s ≈ s′ → u ≈ u′ → pr s u ≈ pr s′ u′
  π₁-cong  : t ≈ t′ → π₁ t ≈ π₁ t′
  π₂-cong  : t ≈ t′ → π₂ t ≈ π₂ t′
  $-cong   : s ≈ s′ → u ≈ u′ → s $ u ≈ s′ $ u′
  Λ-cong   : t ≈ t′ → Λ t ≈ Λ t′

data Nf : Ctx → Typ → Set
data Ne : Ctx → Typ → Set

data Nf where
  *  : Nf Γ *
  ze : Nf Γ N
  su : Nf Γ N → Nf Γ N
  pr : (s : Nf Γ S) (u : Nf Γ U) → Nf Γ (S X U)
  Λ  : Nf (S ∷ Γ) U → Nf Γ (S ⟶ U)
  ne : (t : Ne Γ T) → Nf Γ T

data Ne where
  var : T ∈ Γ → Ne Γ T
  rec : Nf Γ T → Nf Γ (N ⟶ T ⟶ T) → Ne Γ N → Ne Γ T
  π₁  : Ne Γ (S X U) → Ne Γ S
  π₂  : Ne Γ (S X U) → Ne Γ U
  _$_ : Ne Γ (S ⟶ U) → (s : Nf Γ S) → Ne Γ U

shiftₙ : Nf Γ T → Γ ⊆ Γ′ → Nf Γ′ T
shiftₑ : Ne Γ T → Γ ⊆ Γ′ → Ne Γ′ T

shiftₙ * Γ⊆Γ′        = *
shiftₙ (pr s u) Γ⊆Γ′ = pr (shiftₙ s Γ⊆Γ′) (shiftₙ u Γ⊆Γ′)
shiftₙ ze Γ⊆Γ′       = ze
shiftₙ (su t) Γ⊆Γ′   = su (shiftₙ t Γ⊆Γ′)
shiftₙ (Λ t) Γ⊆Γ′    = Λ (shiftₙ t (refl ∷ Γ⊆Γ′))
shiftₙ (ne t) Γ⊆Γ′   = ne (shiftₑ t Γ⊆Γ′)

shiftₑ (var T∈Γ) Γ⊆Γ′   = var (∈-⊆ T∈Γ Γ⊆Γ′)
shiftₑ (rec b r n) Γ⊆Γ′ = rec (shiftₙ b Γ⊆Γ′) (shiftₙ r Γ⊆Γ′) (shiftₑ n Γ⊆Γ′)
shiftₑ (π₁ t) Γ⊆Γ′      = π₁ (shiftₑ t Γ⊆Γ′)
shiftₑ (π₂ t) Γ⊆Γ′      = π₂ (shiftₑ t Γ⊆Γ′)
shiftₑ (t $ s) Γ⊆Γ′     = shiftₑ t Γ⊆Γ′ $ shiftₙ s Γ⊆Γ′

module NBE1 where

  ⟦_⊢_⟧ : Ctx → Typ → Set
  ⟦ Γ ⊢ * ⟧     = ⊤
  ⟦ Γ ⊢ N ⟧     = Nf Γ N
  ⟦ Γ ⊢ S X U ⟧ = ⟦ Γ ⊢ S ⟧ × ⟦ Γ ⊢ U ⟧
  ⟦ Γ ⊢ S ⟶ U ⟧ = ∀ {Γ′} → Γ ⊆ Γ′ → ⟦ Γ′ ⊢ S ⟧ → ⟦ Γ′ ⊢ U ⟧

  reify : ⟦ Γ ⊢ T ⟧ → Nf Γ T
  reflect : Ne Γ T → ⟦ Γ ⊢ T ⟧

  reify {_} {*} t           = *
  reify {_} {N} t           = t
  reify {_} {S X U} (s , u) = pr (reify s) (reify u)
  reify {_} {S ⟶ U} t       = Λ (reify (t (S ∷ʳ ⊆-refl) (reflect (var 0d))))

  reflect {_} {*} t              = tt
  reflect {_} {N} t              = ne t
  reflect {_} {S X U} t          = reflect (π₁ t) , reflect (π₂ t)
  reflect {_} {S ⟶ U} t Γ⊆Γ′ ⟦S⟧ = reflect (shiftₑ t Γ⊆Γ′ $ reify ⟦S⟧)

  shiftₛ : Γ ⊆ Γ′ → ⟦ Γ ⊢ T ⟧ → ⟦ Γ′ ⊢ T ⟧
  shiftₛ {_} {_} {*} Γ⊆Γ′ ⟦T⟧             = tt
  shiftₛ {_} {_} {N} Γ⊆Γ′ ⟦T⟧             = shiftₙ ⟦T⟧ Γ⊆Γ′
  shiftₛ {_} {_} {S X U} Γ⊆Γ′ (⟦S⟧ , ⟦U⟧) = shiftₛ Γ⊆Γ′ ⟦S⟧ , shiftₛ Γ⊆Γ′ ⟦U⟧
  shiftₛ {_} {_} {S ⟶ U} Γ⊆Γ′ ⟦T⟧ Γ′⊆Γ″   = ⟦T⟧ (⊆-trans Γ⊆Γ′ Γ′⊆Γ″)

  ⟦_⇒_⟧ : Ctx → Ctx → Set
  ⟦_⇒_⟧ Γ = All ⟦ Γ ⊢_⟧

  rec-sem : ⟦ Δ ⇒ Γ ⟧ → ⟦ Δ ⊢ T ⟧ → ⟦ Δ ⊢ N ⟶ T ⟶ T ⟧ → Nf Δ N → ⟦ Δ ⊢ T ⟧
  rec-sem ΔΓ b r ze     = b
  rec-sem ΔΓ b r (su n) = r ⊆-refl n ⊆-refl (rec-sem ΔΓ b r n)
  rec-sem ΔΓ b r (ne t) = reflect (rec (reify b) (reify r) t)

  eval : ⟦ Δ ⇒ Γ ⟧ → Trm Γ T → ⟦ Δ ⊢ T ⟧
  eval ΔΓ *              = tt
  eval ΔΓ (var T∈Γ)      = All′.lookup ΔΓ T∈Γ
  eval ΔΓ ze             = ze
  eval ΔΓ (su t)         = su (eval ΔΓ t)
  eval ΔΓ (rec b r n)    = rec-sem ΔΓ (eval ΔΓ b) (eval ΔΓ r) (eval ΔΓ n)
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

  module Sound (ext : Extensionality 0ℓ 0ℓ) where

    ≈⇒nbe≡ : (σ : ⟦ Δ ⇒ Γ ⟧) → s ≈ u → eval σ s ≡ eval σ u
    ≈⇒nbe≡ σ reflx              = refl
    ≈⇒nbe≡ σ (symm r)           = sym (≈⇒nbe≡ σ r)
    ≈⇒nbe≡ σ (tran r r′)        = trans (≈⇒nbe≡ σ r) (≈⇒nbe≡ σ r′)
    ≈⇒nbe≡ σ *-η                = refl
    ≈⇒nbe≡ σ pr-η               = refl
    ≈⇒nbe≡ σ π₁-β               = refl
    ≈⇒nbe≡ σ π₂-β               = refl
    ≈⇒nbe≡ σ rec-β₁             = refl
    ≈⇒nbe≡ σ rec-β₂             = refl
    ≈⇒nbe≡ σ Λ-η                = implicit-extensionality ext (ext λ Δ⊆Γ′ → ext (λ ⟦S⟧ → {!!}))
    ≈⇒nbe≡ σ $-β                = {!!}
    ≈⇒nbe≡ σ (su-cong r)        = cong su (≈⇒nbe≡ σ r)
    ≈⇒nbe≡ σ (rec-cong r r′ r″) = cong₃ (rec-sem σ) (≈⇒nbe≡ σ r) (≈⇒nbe≡ σ r′) (≈⇒nbe≡ σ r″)
    ≈⇒nbe≡ σ (pr-cong r r′)     = cong₂ _,_ (≈⇒nbe≡ σ r) (≈⇒nbe≡ σ r′)
    ≈⇒nbe≡ σ (π₁-cong r)        = cong proj₁ (≈⇒nbe≡ σ r)
    ≈⇒nbe≡ σ (π₂-cong r)        = cong proj₂ (≈⇒nbe≡ σ r)
    ≈⇒nbe≡ σ ($-cong r r′)      = cong₂ (λ s u → s ⊆-refl u) (≈⇒nbe≡ σ r) (≈⇒nbe≡ σ r′)
    ≈⇒nbe≡ σ (Λ-cong r)         = implicit-extensionality ext (ext λ Δ⊆Γ′ → ext (λ ⟦S⟧ → ≈⇒nbe≡ (⟦S⟧ ∷ All′.map (shiftₛ Δ⊆Γ′) σ) r))

-- module NBE2 where

--   ⟦_⊢_⟧ : Ctx → Typ → Set
--   ⟦ Γ ⊢ * ⟧     = ⊤
--   ⟦ Γ ⊢ N ⟧     = Nf Γ N
--   ⟦ Γ ⊢ S X U ⟧ = ⟦ Γ ⊢ S ⟧ × ⟦ Γ ⊢ U ⟧
--   ⟦ Γ ⊢ S ⟶ U ⟧ = ∀ Γ′ → ⟦ Γ′ ++ Γ ⊢ S ⟧ → ⟦ Γ′ ++ Γ ⊢ U ⟧

--   reify : ⟦ Γ ⊢ T ⟧ → Nf Γ T
--   reflect : Ne Γ T → ⟦ Γ ⊢ T ⟧

--   reify {_} {*} t           = *
--   reify {_} {N} t           = t
--   reify {_} {S X U} (s , u) = pr (reify s) (reify u)
--   reify {_} {S ⟶ U} t       = Λ (reify (t (S ∷ []) (reflect (var 0d))))

--   reflect {_} {*} t          = tt
--   reflect {_} {N} t          = ne t
--   reflect {_} {S X U} t      = (reflect (π₁ t)) , (reflect (π₂ t))
--   reflect {_} {S ⟶ U} t Γ′ s = reflect ((shiftₑ t (Γ′ ++ʳ ⊆-refl)) $ reify s)

--   shiftₛ : ∀ Γ′ → ⟦ Γ ⊢ T ⟧ → ⟦ Γ′ ++ Γ ⊢ T ⟧
--   shiftₛ {_} {*} Γ′ t           = tt
--   shiftₛ {_} {N} Γ′ t           = shiftₙ t (Γ′ ++ʳ ⊆-refl)
--   shiftₛ {_} {S X U} Γ′ (s , u) = shiftₛ Γ′ s , shiftₛ Γ′ u
--   shiftₛ {_} {S ⟶ U} Γ′ t Γ″ s  = {!t (Γ″ ++ Γ′) !}

--   ⟦_⇒_⟧ : Ctx → Ctx → Set
--   ⟦_⇒_⟧ Γ = All ⟦ Γ ⊢_⟧
