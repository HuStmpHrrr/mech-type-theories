{-# OPTIONS --without-K --safe #-}

module Weakening where

open import Lib

import Data.Nat.Properties as ℕₚ


data Wk : Set where
  I   : Wk
  p q : Wk → Wk

infixl 3 _∘w_

_∘w_ : Wk → Wk → Wk
I ∘w γ′     = γ′
p γ ∘w q γ′ = p (γ ∘w γ′)
q γ ∘w q γ′ = q (γ ∘w γ′)
γ ∘w I      = γ
γ ∘w p γ′   = p (γ ∘w γ′)


∘w-I : ∀ γ → (γ ∘w I) ≡ γ
∘w-I I     = refl
∘w-I (p γ) = refl
∘w-I (q γ) = refl

∘w-p : ∀ γ γ′ → (γ ∘w p γ′) ≡ p (γ ∘w γ′)
∘w-p I γ′     = refl
∘w-p (p γ) γ′ = refl
∘w-p (q γ) γ′ = refl

∘w-pI : ∀ γ → (γ ∘w p I) ≡ p γ
∘w-pI I     = refl
∘w-pI (p γ) = refl
∘w-pI (q γ) = refl

pI∘p*I : ∀ n → (p I ∘w repeat p n I) ≡ repeat p (1 + n) I
pI∘p*I zero    = refl
pI∘p*I (suc n) = cong p (pI∘p*I n)

∘w-assoc : ∀ γ γ′ γ″ → ((γ ∘w γ′) ∘w γ″) ≡ (γ ∘w (γ′ ∘w γ″))
∘w-assoc I γ′ γ″          = refl
∘w-assoc γ I γ″
  rewrite ∘w-I γ          = refl
∘w-assoc γ γ′ I
  rewrite ∘w-I (γ ∘w γ′)
        | ∘w-I γ′         = refl
∘w-assoc γ γ′ (p γ″)
  rewrite ∘w-p γ′ γ″
        | ∘w-p (γ ∘w γ′) γ″
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc γ (p γ′) (q γ″)
  rewrite ∘w-p γ γ′
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (p γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (q γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl

wk-x : ℕ → Wk → ℕ
wk-x x I          = x
wk-x x (p γ)       = suc (wk-x x γ)
wk-x 0 (q γ)       = 0
wk-x (suc x) (q γ) = suc (wk-x x γ)

wk-x-repeat-p : ∀ x y → wk-x x (repeat p y I) ≡ y + x
wk-x-repeat-p x zero = refl
wk-x-repeat-p x (suc y) = cong suc (wk-x-repeat-p x y)

wk-x-repeat-p′ : ∀ x y → wk-x x (repeat p y I) ≡ x + y
wk-x-repeat-p′ x y = trans (wk-x-repeat-p x y) (ℕₚ.+-comm y x)

wk-x-comp : ∀ x γ γ′ → wk-x (wk-x x γ) γ′ ≡ wk-x x (γ ∘w γ′)
wk-x-comp x I γ′              = refl
wk-x-comp x (p γ) I           = refl
wk-x-comp x (p γ) (p γ′)
  rewrite wk-x-comp x (p γ) γ′ = refl
wk-x-comp x (p γ) (q γ′)
  rewrite wk-x-comp x γ γ′     = refl
wk-x-comp x (q γ) I           = refl
wk-x-comp x (q γ) (p γ′)
  rewrite wk-x-comp x (q γ) γ′ = refl
wk-x-comp zero (q γ) (q γ′)    = refl
wk-x-comp (suc x) (q γ) (q γ′)
  rewrite wk-x-comp x γ γ′     = refl

wk-I-x : ∀ n x → wk-x x (repeat q n I) ≡ x
wk-I-x n zero        = helper n
  where helper : ∀ n → wk-x zero (repeat q n I) ≡ zero
        helper zero    = refl
        helper (suc n) = refl
wk-I-x zero (suc x)  = refl
wk-I-x (suc n) (suc x)
  rewrite wk-I-x n x = refl
