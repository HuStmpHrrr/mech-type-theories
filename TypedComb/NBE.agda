{-# OPTIONS --without-K --safe #-}

module TypedComb.NBE where

open import Lib
open import TypedComb.Statics

variable
  a b c d : Exp T

infix 0 _≈_
data _≈_ : Exp T → Exp T → Set where
  reflx   : a ≈ a
  symm    : a ≈ b → b ≈ a
  tran    : a ≈ b → b ≈ c → a ≈ c

  K-β     : K $ a $ b ≈ a
  S-β     : S $ a $ b $ c ≈ a $ c $ (b $ c)
  Rec-β₁  : Rec $ a $ b $ Ze ≈ a
  Rec-β₂  : Rec $ a $ b $ Su c ≈ b $ c $ (Rec $ a $ b $ c)

  Su-cong : a ≈ b → Su a ≈ Su b
  $-cong  : a ≈ b → c ≈ d → a $ c ≈ b $ d

data Nf : Typ → Set where
  K     : Nf (T ⟶ U ⟶ T)
  S     : Nf ((T ⟶ T′ ⟶ U) ⟶ (T ⟶ T′) ⟶ T ⟶ U)
  Ze    : Nf N
  Su    : Nf N → Nf N
  Rec   : Nf (T ⟶ (N ⟶ T ⟶ T) ⟶ N ⟶ T)
  K$    : Nf T → Nf (U ⟶ T)
  S$    : Nf (T ⟶ T′ ⟶ U) → Nf ((T ⟶ T′) ⟶ T ⟶ U)
  S$$   : Nf (T ⟶ T′ ⟶ U) → Nf (T ⟶ T′) → Nf (T ⟶ U)
  Rec$  : Nf T → Nf ((N ⟶ T ⟶ T) ⟶ N ⟶ T)
  Rec$$ : Nf T → Nf (N ⟶ T ⟶ T) → Nf (N ⟶ T)

Nf⇒Exp : Nf T → Exp T
Nf⇒Exp K           = K
Nf⇒Exp S           = S
Nf⇒Exp Ze          = Ze
Nf⇒Exp (Su t)      = Su (Nf⇒Exp t)
Nf⇒Exp Rec         = Rec
Nf⇒Exp (K$ t)      = K $ Nf⇒Exp t
Nf⇒Exp (S$ t)      = S $ Nf⇒Exp t
Nf⇒Exp (S$$ t u)   = S $ Nf⇒Exp t $ Nf⇒Exp u
Nf⇒Exp (Rec$ t)    = Rec $ Nf⇒Exp t
Nf⇒Exp (Rec$$ t u) = Rec $ Nf⇒Exp t $ Nf⇒Exp u

⟦_⟧ : Typ → Set
⟦ N ⟧     = Nf N
⟦ T ⟶ U ⟧ = Nf (T ⟶ U) × (⟦ T ⟧ → ⟦ U ⟧)

reify : ⟦ T ⟧ → Nf T
reify {N} ⟦T⟧         = ⟦T⟧
reify {T ⟶ U} (e , _) = e

rec : ⟦ T ⟧ → ⟦ N ⟶ T ⟶ T ⟧ → ⟦ N ⟧ → ⟦ T ⟧
rec t r Ze               = t
rec t r@(_ , ⟦r⟧) (Su n) = proj₂ (⟦r⟧ n) (rec t r n )

⟦_⟧ₑ : Exp T → ⟦ T ⟧
⟦ K ⟧ₑ     = K , λ t → K$ (reify t) , λ _ → t
⟦ S ⟧ₑ     = S , λ f@(fe , ⟦f⟧) → S$ fe , λ g@(ge , ⟦g⟧) → S$$ fe ge , λ t → proj₂ (⟦f⟧ t) (⟦g⟧ t)
⟦ t $ u ⟧ₑ = proj₂ ⟦ t ⟧ₑ ⟦ u ⟧ₑ
⟦ Ze ⟧ₑ    = Ze
⟦ Su e ⟧ₑ  = Su ⟦ e ⟧ₑ
⟦ Rec ⟧ₑ   = Rec , λ t → Rec$ (reify t) , λ r@(re , ⟦r⟧) → Rec$$ (reify t) re , rec t r

nbe : Exp T → Nf T
nbe t = reify ⟦ t ⟧ₑ

≈⇒⟦⟧ : a ≈ b → ⟦ a ⟧ₑ ≡ ⟦ b ⟧ₑ
≈⇒⟦⟧ reflx           = refl
≈⇒⟦⟧ (symm eq)       = sym (≈⇒⟦⟧ eq)
≈⇒⟦⟧ (tran eq eq′)   = trans (≈⇒⟦⟧ eq) (≈⇒⟦⟧ eq′)
≈⇒⟦⟧ K-β             = refl
≈⇒⟦⟧ S-β             = refl
≈⇒⟦⟧ Rec-β₁          = refl
≈⇒⟦⟧ Rec-β₂          = refl
≈⇒⟦⟧ (Su-cong eq)    = cong Su (≈⇒⟦⟧ eq)
≈⇒⟦⟧ ($-cong eq eq′) = cong₂ proj₂ (≈⇒⟦⟧ eq) (≈⇒⟦⟧ eq′)

≈⇒nbe≡ : a ≈ b → nbe a ≡ nbe b
≈⇒nbe≡ eq = cong reify (≈⇒⟦⟧ eq)

