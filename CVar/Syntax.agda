{-# OPTIONS --without-K --safe #-}

module CVar.Syntax where

open import Level renaming (suc to succ)

open import Lib public

-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public


infixr 5 _⟶_ ctx⇒_

mutual

  -- types
  data Typ : Set where
    N     : Typ
    _⟶_   : Typ → Typ → Typ
    □     : LCtx → Typ → Typ
    ctx⇒_ : Typ → Typ

  -- a local binding
  data LBnd : Set where
    -- either a contextual variable
    cv : ℕ → LBnd
    -- or a normal binding of a type
    ty : Typ → LBnd

  LCtx : Set
  LCtx = List LBnd

-- a global binding
data Bnd : Set where
  ctx : Bnd
  _,_ : LCtx → Typ → Bnd


GCtx : Set
GCtx = List Bnd


data Layer : Set where
  𝟘 𝟙 : Layer


data Gwk : Set where
  id  : Gwk
  p q : Gwk → Gwk


infixl 3 _∘g_

_∘g_ : Gwk → Gwk → Gwk
id ∘g γ′    = γ′
p γ ∘g q γ′ = p (γ ∘g γ′)
q γ ∘g q γ′ = q (γ ∘g γ′)
γ ∘g id     = γ
γ ∘g p γ′   = p (γ ∘g γ′)


gwk-x : ℕ → Gwk → ℕ
gwk-x x id = x
gwk-x x (p γ) = gwk-x (suc x) γ
gwk-x 0 (q γ) = 0
gwk-x (suc x) (q γ) = suc (gwk-x x γ)

mutual

  gwk-t : Typ → Gwk → Typ
  gwk-t N γ        = N
  gwk-t (S ⟶ T) γ  = gwk-t S γ ⟶ gwk-t T γ
  gwk-t (□ Γ T) γ  = □ (gwk-lc Γ γ) (gwk-t T γ)
  gwk-t (ctx⇒ T) γ = ctx⇒ gwk-t T (q γ)

  gwk-lb : LBnd → Gwk → LBnd
  gwk-lb (cv x) γ = cv (gwk-x x γ)
  gwk-lb (ty T) γ = ty (gwk-t T γ)

  gwk-lc : LCtx → Gwk → LCtx
  gwk-lc [] γ        = []
  gwk-lc (lb ∷ lc) γ = gwk-lb lb γ ∷ gwk-lc lc γ

instance
  gwk-t-mon : Monotone Typ Gwk
  gwk-t-mon = record { _[_] = gwk-t }

  gwk-lb-mon : Monotone LBnd Gwk
  gwk-lb-mon = record { _[_] = gwk-lb }

  gwk-lc-mon : Monotone LCtx Gwk
  gwk-lc-mon = record { _[_] = gwk-lc }


variable
  i : Layer
  Ψ Ψ′ Ψ″ : GCtx
  Φ Φ′ Φ″ : GCtx
  Γ Γ′ Γ″ : LCtx
  Δ Δ′ Δ″ : LCtx
  T T′ T″ : Typ
  S S′ S″ : Typ
  x x′ x″ : ℕ


infix 4 ⊢_ _⊢[_]_ _﹔_⊢[_]_

mutual

  -- well-formedness of global contexts
  data ⊢_ : GCtx → Set where
    ⊢[]  : ⊢ []
    ⊢ctx : ⊢ Ψ → ⊢ ctx ∷ Ψ
    ⊢v   : Ψ ﹔ Γ ⊢[ 𝟘 ] T → ⊢ (Γ , T) ∷ Ψ

  -- well-formedness of local contexts
  data _⊢[_]_ : GCtx → Layer → LCtx → Set where
    ⊢[]  : ⊢ Ψ → Ψ ⊢[ i ] []
    ⊢ctx : x ∶ ctx ∈ Ψ → Ψ ⊢[ i ] Γ → Ψ ⊢[ i ] cv x ∷ Γ
    ⊢v   : Ψ ﹔ Γ ⊢[ i ] T → Ψ ⊢[ i ] ty T ∷ Γ

  -- well-formedness of types
  data _﹔_⊢[_]_ : GCtx → LCtx → Layer → Typ → Set where
    ⊢N : Ψ ⊢[ i ] Γ → Ψ ﹔ Γ ⊢[ i ] N
    ⊢⟶ : Ψ ﹔ Γ ⊢[ i ] S → Ψ ﹔ Γ ⊢[ i ] T → Ψ ﹔ Γ ⊢[ i ] S ⟶ T
    ⊢□ : Ψ ⊢[ 𝟙 ] Γ → Ψ ﹔ Δ ⊢[ 𝟘 ] T → Ψ ﹔ Γ ⊢[ 𝟙 ] □ Δ T
    ⊢⇒ : Ψ ⊢[ 𝟙 ] Γ → ctx ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] T → Ψ ﹔ Γ ⊢[ 𝟙 ] ctx⇒ T


-- presupposition

mutual

  presup-l : Ψ ⊢[ i ] Γ → ⊢ Ψ
  presup-l (⊢[] ⊢Ψ)      = ⊢Ψ
  presup-l (⊢ctx x∈Ψ ⊢Γ) = presup-l ⊢Γ
  presup-l (⊢v ⊢T)       = proj₁ (presup-t ⊢T)

  presup-t : Ψ ﹔ Γ ⊢[ i ] T → ⊢ Ψ × Ψ ⊢[ i ] Γ
  presup-t (⊢N ⊢Γ)    = presup-l ⊢Γ , ⊢Γ
  presup-t (⊢⟶ ⊢S ⊢T) = presup-t ⊢T
  presup-t (⊢□ ⊢Γ ⊢T) = presup-l ⊢Γ , ⊢Γ
  presup-t (⊢⇒ ⊢Γ _)  = presup-l ⊢Γ , ⊢Γ
