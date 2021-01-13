{-# OPTIONS --without-K --safe #-}

module TypedComb.Statics where

infixr 5 _⟶_

data Typ : Set where
  N   : Typ
  _⟶_ : Typ → Typ → Typ

variable
  T T′ U U′ : Typ

infixl 10 _$_
data Exp : Typ → Set where
  K   : Exp (T ⟶ U ⟶ T)
  S   : Exp ((T ⟶ T′ ⟶ U) ⟶ (T ⟶ T′) ⟶ T ⟶ U)
  _$_ : Exp (T ⟶ U) → Exp T → Exp U
  Ze  : Exp N
  Su  : Exp N → Exp N
  Rec : Exp (T ⟶ (N ⟶ T ⟶ T) ⟶ N ⟶ T)
