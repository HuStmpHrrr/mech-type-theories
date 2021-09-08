{-# OPTIONS --without-K --safe #-}

module Idem.Statics where

open import Level using (_⊔_)
open import Data.List.Properties as Lₚ

open import Lib

record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 8 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

record HasTil {i} (A : Set i) : Set i where
  field
    til : A → A

open HasTil {{...}} public

infixr 5 _⟶_

-- types
data Typ : Set where
  B   : Typ
  _⟶_ : Typ → Typ → Typ
  □   : Typ → Typ

Ctx : Set
Ctx = List Typ

variable
  S T U      : Typ
  Γ Γ′ Γ″    : Ctx
  Δ Δ′ Δ″    : Ctx

infixl 10 _$_
infixl 3 _∘_
mutual
  data Exp : Set where
    v     : (x : ℕ) → Exp
    Λ     : Exp → Exp
    _$_   : Exp → Exp → Exp
    box   : Exp → Exp
    unbox : Exp → Exp
    sub   : Exp → Subst → Exp

  data Subst : Set where
    I   : Subst
    p   : Subst → Subst
    _,_ : Subst → Exp → Subst
    hat : Subst → Subst
    _∘_ : Subst → Subst → Subst

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Subst
  δ δ′ δ″ : Subst

instance
  ExpMonotone : Monotone Exp Subst
  ExpMonotone = record { _[_] = sub }

mutual
  s-til : Subst → Subst
  s-til I       = I
  s-til (p σ)   = p (s-til σ)
  s-til (σ , t) = s-til σ , t-til t
  s-til (hat σ) = s-til σ
  s-til (σ ∘ δ) = s-til σ ∘ s-til δ

  t-til : Exp → Exp
  t-til (v x)     = v x
  t-til (Λ t)     = Λ (t-til t)
  t-til (t $ s)   = t-til t $ t-til s
  t-til (box t)   = box t
  t-til (unbox t) = unbox t
  t-til (sub t σ) = sub (t-til t) (s-til σ)

instance
  SubstHasTil : HasTil Subst
  SubstHasTil = record { til = s-til }

  ExpHasTil : HasTil Exp
  ExpHasTil = record { til = t-til }

q : Subst → Subst
q σ = (σ ∘ p I) , v 0

infix 4 _﹔_⊢_∶_ _﹔_⊢s_∶_﹔_
mutual
  data _﹔_⊢_∶_ : Ctx → Ctx → Exp → Typ → Set where
    vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ----------------
              Δ ﹔ Γ ⊢ v x ∶ T
    ⟶-I     : Δ ﹔ S ∷ Γ ⊢ t ∶ T →
              --------------------
              Δ ﹔ Γ ⊢ Λ t ∶ S ⟶ T
    ⟶-E     : Δ ﹔ Γ ⊢ t ∶ S ⟶ T →
              Δ ﹔ Γ ⊢ s ∶ S →
              ------------------
              Δ ﹔ Γ ⊢ t $ s ∶ T
    □-I     : Γ ++ Δ ﹔ [] ⊢ t ∶ T →
              ----------------------
              Δ ﹔ Γ ⊢ box t ∶ □ T
    □-E     : [] ﹔ Γ ++ Δ ⊢ t ∶ □ T →
              ------------------------
              Δ ﹔ Γ ⊢ unbox t ∶ T
    t[σ]    : Δ′ ﹔ Γ′ ⊢ t ∶ T →
              Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
              ------------------------
              Δ ﹔ Γ ⊢ t [ σ ] ∶ T

  data _﹔_⊢s_∶_﹔_ : Ctx → Ctx → Subst → Ctx → Ctx → Set where
    S-I   : ∀ Δ′ →
            Δ ﹔ Γ ++ Δ′ ⊢s I ∶ Δ′ ++ Δ ﹔ Γ
    S-p   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ T ∷ Γ′ →
            ---------------------------
            Δ ﹔ Γ ⊢s p σ ∶ Δ′ ﹔ Γ′
    S-,   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            Δ ﹔ Γ ⊢ t ∶ T →
            ------------------------------
            Δ ﹔ Γ ⊢s σ , t ∶ Δ′ ﹔ T ∷ Γ′
    S-hat : ∀ Γ₁ {Γ₂} →
            Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            Γ ++ Δ ≡ Γ₁ ++ Γ₂ →
            --------------------------------------
            Γ₂ ﹔ Γ₁ ⊢s hat σ ∶ Γ′ ++ Δ′ ﹔ []
    S-∘   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            Δ′ ﹔ Γ′ ⊢s δ ∶ Δ″ ﹔ Γ″ →
            --------------------------
            Δ ﹔ Γ ⊢s δ ∘ σ ∶ Δ″ ﹔ Γ″

S-I′ : Δ ﹔ Γ ⊢s I ∶ Δ ﹔ Γ
S-I′ {Δ} {Γ} = subst (Δ ﹔_⊢s I ∶ Δ ﹔ Γ) (++-identityʳ _) (S-I [])

S-hat′ : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ → Γ ++ Δ ﹔ [] ⊢s hat σ ∶ Γ′ ++ Δ′ ﹔ []
S-hat′ ⊢σ = S-hat [] ⊢σ refl

⊢q : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′  → ∀ T → Δ ﹔ T ∷ Γ ⊢s q σ ∶ Δ′ ﹔ T ∷ Γ′
⊢q {Δ} {Γ} ⊢σ T = S-, (S-∘ (S-p S-I′) ⊢σ) (vlookup here)


mutual
  ⊢-til : Δ ﹔ Γ ⊢ t ∶ T → [] ﹔ Γ ++ Δ ⊢ til t ∶ T
  ⊢-til (vlookup T∈Γ)    = vlookup (∈-++ʳ T∈Γ)
  ⊢-til (⟶-I ⊢t)         = ⟶-I (⊢-til ⊢t)
  ⊢-til (⟶-E ⊢t ⊢s)      = ⟶-E (⊢-til ⊢t) (⊢-til ⊢s)
  ⊢-til (□-I {Γ} {Δ} ⊢t) = □-I (subst (_﹔ _ ⊢ _ ∶ _) (sym (++-identityʳ (Γ ++ Δ))) ⊢t)
  ⊢-til (□-E {Γ} {Δ} ⊢t) = □-E (subst (_ ﹔_⊢ _ ∶ _) (sym (++-identityʳ (Γ ++ Δ))) ⊢t)
  ⊢-til (t[σ] ⊢t ⊢σ)     = t[σ] (⊢-til ⊢t) (⊢s-til ⊢σ)

  ⊢s-til : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ → [] ﹔ Γ ++ Δ ⊢s til σ ∶ [] ﹔ Γ′ ++ Δ′
  ⊢s-til {Δ} {_} {_} {_} {Γ′} (S-I Δ′)
    rewrite ++-assoc Γ′ Δ′ Δ = S-I′
  ⊢s-til (S-p ⊢σ)            = S-p (⊢s-til ⊢σ)
  ⊢s-til (S-, ⊢σ ⊢t)         = S-, (⊢s-til ⊢σ) (⊢-til ⊢t)
  ⊢s-til (S-hat Γ₁ ⊢σ eq)
    rewrite sym eq           = ⊢s-til ⊢σ
  ⊢s-til (S-∘ ⊢σ ⊢δ)         = S-∘ (⊢s-til ⊢σ) (⊢s-til ⊢δ)

mutual
  ⊢-mweaken : ∀ Δ → Δ ++ Δ′ ﹔ Γ ⊢ t ∶ T → Δ′ ﹔ Γ ++ Δ ⊢ t ∶ T
  ⊢-mweaken Δ (vlookup T∈Γ)         = vlookup (∈-++ʳ T∈Γ)
  ⊢-mweaken Δ (⟶-I ⊢t)              = ⟶-I (⊢-mweaken Δ ⊢t)
  ⊢-mweaken Δ (⟶-E ⊢t ⊢s)           = ⟶-E (⊢-mweaken Δ ⊢t) (⊢-mweaken Δ ⊢s)
  ⊢-mweaken {Δ′} {Γ} Δ (□-I ⊢t)
    rewrite sym (++-assoc Γ Δ Δ′) = □-I ⊢t
  ⊢-mweaken {Δ′} {Γ} Δ (□-E ⊢t)
    rewrite sym (++-assoc Γ Δ Δ′) = □-E ⊢t
  ⊢-mweaken Δ (t[σ] ⊢t ⊢σ) = t[σ] ⊢t (⊢s-mweaken Δ ⊢σ)

  ⊢s-mweaken : ∀ Δ → Δ ++ Δ′ ﹔ Γ ⊢s σ ∶ Δ″ ﹔ Γ′ → Δ′ ﹔ Γ ++ Δ ⊢s σ ∶ Δ″ ﹔ Γ′
  ⊢s-mweaken {_} {_} {_} {_} {Γ′} Δ (S-I Δ′) = helper (S-I (Δ′ ++ Δ))
    where helper : Δ″ ﹔ Γ′ ++ Δ′ ++ Δ ⊢s I ∶ (Δ′ ++ Δ) ++ Δ″ ﹔ Γ′ →  Δ″ ﹔ (Γ′ ++ Δ′) ++ Δ ⊢s I ∶ Δ′ ++ Δ ++ Δ″ ﹔ Γ′
          helper {Δ″} ⊢I
            rewrite ++-assoc Γ′ Δ′ Δ
                  | ++-assoc Δ′ Δ Δ″ = ⊢I
  ⊢s-mweaken Δ (S-p ⊢σ)                      = S-p (⊢s-mweaken Δ ⊢σ)
  ⊢s-mweaken Δ (S-, ⊢σ ⊢t)                   = S-, (⊢s-mweaken Δ ⊢σ) (⊢-mweaken Δ ⊢t)
  ⊢s-mweaken Δ (S-hat Γ₁ ⊢σ eq)              = S-hat (Γ₁ ++ Δ) ⊢σ (trans eq (sym (++-assoc Γ₁ Δ _)))
  ⊢s-mweaken Δ (S-∘ ⊢σ ⊢δ)                   = S-∘ (⊢s-mweaken Δ ⊢σ) ⊢δ

infix 4 _﹔_⊢_≈_∶_ _﹔_⊢s_≈_∶_﹔_

mutual
  data _﹔_⊢_≈_∶_ : Ctx → Ctx → Exp → Exp → Typ → Set where
    v-≈        : ∀ {x} →
                 x ∶ T ∈ Γ →
                 ----------------------
                 Δ ﹔ Γ ⊢ v x ≈ v x ∶ T
    Λ-cong     : Δ ﹔ S ∷ Γ ⊢ t ≈ t′ ∶ T →
                 ---------------------------
                 Δ ﹔ Γ ⊢ Λ t ≈ Λ t′ ∶ S ⟶ T
    $-cong     : Δ ﹔ Γ ⊢ t ≈ t′ ∶ S ⟶ T →
                 Δ ﹔ Γ ⊢ s ≈ s′ ∶ S →
                 ----------------------------
                  Δ ﹔ Γ ⊢ t $ s ≈ t′ $ s′ ∶ T
    box-cong   : Γ ++ Δ ﹔ [] ⊢ t ≈ t′ ∶ T →
                 -----------------------------
                 Δ ﹔ Γ ⊢ box t ≈ box t′ ∶ □ T
    unbox-cong : [] ﹔ Γ ++ Δ ⊢ t ≈ t′ ∶ □ T →
                 -------------------------------
                 Δ ﹔ Γ ⊢ unbox t ≈ unbox t′ ∶ T
    []-cong    : Δ′ ﹔ Γ′ ⊢ t ≈ t′ ∶ T →
                 Δ ﹔ Γ ⊢s σ ≈ σ′ ∶ Δ′ ﹔ Γ′ →
                 --------------------------------
                 Δ ﹔ Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T
    Λ-[]       : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Δ′ ﹔ Γ′ ⊢ t ∶ T →
                 ------------------------------------------
                 Δ ﹔ Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ S ⟶ T
    $-[]       : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Δ′ ﹔ Γ′ ⊢ t ∶ S ⟶ T →
                 Δ′ ﹔ Γ′ ⊢ s ∶ S →
                 -------------------------------------------------
                 Δ ﹔ Γ ⊢ t $ s [ σ ] ≈ (t [ σ ]) $ (s [ σ ]) ∶ T
    box-[]     : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Γ′ ++ Δ′ ﹔ [] ⊢ t ∶ T →
                 ----------------------------------------------
                 Δ ﹔ Γ ⊢ box t [ σ ] ≈ box (t [ hat σ ]) ∶ □ T
    unbox-[]   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 [] ﹔ Γ′ ++ Δ′ ⊢ t ∶ □ T →
                 ------------------------------------------------
                 Δ ﹔ Γ ⊢ unbox t [ σ ] ≈ unbox (t [ til σ ]) ∶ T
    ⟶-β        : Δ ﹔ S ∷ Γ ⊢ t ∶ T →
                 Δ ﹔ Γ ⊢ s ∶ S →
                 -----------------------------------
                 Δ ﹔ Γ ⊢ Λ t $ s ≈ t [ I , s ] ∶ T
    □-β        : Γ ++ Δ ﹔ [] ⊢ t ∶ T →
                 -------------------------------
                 Δ ﹔ Γ ⊢ unbox (box t) ≈ t ∶ T
    ⟶-η        : Δ ﹔ Γ ⊢ t ∶ S ⟶ T →
                 ------------------------------------------
                 Δ ﹔ Γ ⊢ t ≈ Λ ((t [ p I ]) $ v 0) ∶ S ⟶ T
    □-η        : Δ ﹔ Γ ⊢ t ∶ □ T →
                 ----------------------------------
                 Δ ﹔ Γ ⊢ t ≈ box (unbox t) ∶ □ T
    [I]        : Δ ﹔ Γ ⊢ t ∶ T →
                 -------------------------
                 Δ ﹔ Γ ⊢ t [ I ] ≈ t ∶ T
    [∘]        : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Δ′ ﹔ Γ′ ⊢s σ′ ∶ Δ″ ﹔ Γ″ →
                 Δ″ ﹔ Γ″ ⊢ t ∶ T →
                 ------------------------------------------
                 Δ ﹔ Γ ⊢ t [ σ′ ∘ σ ] ≈ t [ σ′ ] [ σ ] ∶ T
    v-ze       : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Δ ﹔ Γ ⊢ t ∶ T →
                 ------------------------------
                 Δ ﹔ Γ ⊢ v 0 [ σ , t ] ≈ t ∶ T
    v-su       : ∀ {x} →
                 Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
                 Δ ﹔ Γ ⊢ t ∶ T →
                 x ∶ T ∈ Γ →
                 --------------------------------------------
                 Δ ﹔ Γ ⊢ v (suc x) [ σ , t ] ≈ v x [ σ ] ∶ T
    [p]        : ∀ {x} →
                 Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ T ∷ Γ′ →
                 x ∶ T ∈ Γ →
                 -------------------------------------------
                 Δ ﹔ Γ ⊢ v x [ p σ ] ≈ v (suc x) [ σ ] ∶ T
    ≈-sym      : Δ ﹔ Γ ⊢ t ≈ t′ ∶ T →
                 -----------------------
                 Δ ﹔ Γ ⊢ t′ ≈ t ∶ T
    ≈-trans    : Δ ﹔ Γ ⊢ t ≈ t′ ∶ T →
                 Δ ﹔ Γ ⊢ t′ ≈ t″ ∶ T →
                 ------------------------
                 Δ ﹔ Γ ⊢ t ≈ t″ ∶ T

  data _﹔_⊢s_≈_∶_﹔_ : Ctx → Ctx → Subst → Subst → Ctx → Ctx → Set where
