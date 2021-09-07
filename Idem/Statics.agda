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
    s-I   : Δ ﹔ Γ ⊢s I ∶ Δ ﹔ Γ
    s-p   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ T ∷ Γ′ →
            ---------------------------
            Δ ﹔ Γ ⊢s p σ ∶ Δ′ ﹔ Γ′
    s-,   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            Δ ﹔ Γ ⊢ t ∶ T →
            ------------------------------
            Δ ﹔ Γ ⊢s σ , t ∶ Δ′ ﹔ T ∷ Γ′
    s-hat : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            --------------------------------------
            Γ ++ Δ ﹔ [] ⊢s hat σ ∶ Γ′ ++ Δ′ ﹔ []
    s-∘   : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ →
            Δ′ ﹔ Γ′ ⊢s δ ∶ Δ″ ﹔ Γ″ →
            --------------------------
            Δ ﹔ Γ ⊢s δ ∘ σ ∶ Δ″ ﹔ Γ″

mutual
  ⊢-til : Δ ﹔ Γ ⊢ t ∶ T → [] ﹔ Γ ++ Δ ⊢ til t ∶ T
  ⊢-til (vlookup T∈Γ)    = vlookup (∈-++ʳ T∈Γ)
  ⊢-til (⟶-I ⊢t)         = ⟶-I (⊢-til ⊢t)
  ⊢-til (⟶-E ⊢t ⊢s)      = ⟶-E (⊢-til ⊢t) (⊢-til ⊢s)
  ⊢-til (□-I {Γ} {Δ} ⊢t) = □-I (subst (_﹔ _ ⊢ _ ∶ _) (sym (++-identityʳ (Γ ++ Δ))) ⊢t)
  ⊢-til (□-E {Γ} {Δ} ⊢t) = □-E (subst (_ ﹔_⊢ _ ∶ _) (sym (++-identityʳ (Γ ++ Δ))) ⊢t)
  ⊢-til (t[σ] ⊢t ⊢σ)     = t[σ] (⊢-til ⊢t) (⊢s-til ⊢σ)

  ⊢s-til : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ → [] ﹔ Γ ++ Δ ⊢s til σ ∶ [] ﹔ Γ′ ++ Δ′
  ⊢s-til s-I         = s-I
  ⊢s-til (s-p ⊢σ)    = s-p (⊢s-til ⊢σ)
  ⊢s-til (s-, ⊢σ ⊢t) = s-, (⊢s-til ⊢σ) (⊢-til ⊢t)
  ⊢s-til (s-hat ⊢σ)  = ⊢s-til ⊢σ
  ⊢s-til (s-∘ ⊢σ ⊢δ) = s-∘ (⊢s-til ⊢σ) (⊢s-til ⊢δ)
