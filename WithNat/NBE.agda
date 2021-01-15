{-# OPTIONS --without-K --safe #-}

module WithNat.NBE where

open import Lib
open import WithNat.Statics

open import Data.Unit using (tt; ⊤)

data Nf : Env → Typ → Set
data Ne : Env → Typ → Set

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

⟦_⊢_⟧ : Env → Typ → Set
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

⟦_⇒_⟧ : Env → Env → Set
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
