{-# OPTIONS --without-K --safe #-}

module Unbox.Statics where

open import Lib

open import Level renaming (suc to succ)
open import Data.List.NonEmpty as List⁺ hiding ([_])
open import Relation.Binary.Definitions

import Data.Nat.ExtraProperties as Nₚ

record HasLength {i} (A : Set i) : Set i where
  field
    len : A → ℕ

open HasLength {{...}} public

instance
  ListLength : ∀ {i} {A : Set i} → HasLength (List A)
  ListLength = record { len = L.length }

  List⁺Length : ∀ {i} {A : Set i} → HasLength (List⁺ A)
  List⁺Length = record { len = List⁺.length }

infixr 5 _⟶_

-- types
data Typ : Set where
  B   : Typ
  _⟶_ : Typ → Typ → Typ
  □   : Typ → Typ

Env : Set
Env = List Typ

Envs : Set
Envs = List⁺ Env

variable
  S T U      : Typ
  Γ Γ′ Γ″    : Env
  Δ Δ′ Δ″    : Env
  Γs Γs′ Γs″ : List Env
  Δs Δs′ Δs″ : List Env
  Ψ Ψ′ Ψ″ Ψ‴ : Envs

infixl 10 _$_
infixl 11 _[_]
infixl 3 _∘_
infixl 5 _；_
mutual
  data Exp : Set where
    v     : (x : ℕ) → Exp
    Λ     : Exp → Exp
    _$_   : Exp → Exp → Exp
    box   : Exp → Exp
    unbox : ℕ → Exp → Exp
    _[_]  : Exp → Substs → Exp

  data Substs : Set where
    I : Substs
    p : Substs → Substs
    _,_ : Substs → Exp → Substs
    _；_ : Substs → ℕ → Substs
    _∘_ : Substs → Substs → Substs

q : Substs → Substs
q σs = (σs ∘ p I) , v 0

L : Substs → ℕ → ℕ
L σs 0              = 0
L I (suc n)         = suc n
L (p σs) (suc n)    = L σs (suc n)
L (σs , t) (suc n)  = L σs (suc n)
L (σs ； m) (suc n) = m + L σs n
L (σs ∘ δs) (suc n) = L δs (L σs (suc n))

Tr : Substs → ℕ → Substs
Tr σs 0              = σs
Tr I (suc n)         = I
Tr (p σs) (suc n)    = Tr σs (suc n)
Tr (σs , t) (suc n)  = Tr σs (suc n)
Tr (σs ； m) (suc n) = Tr σs n
Tr (σs ∘ δs) (suc n) = Tr σs (suc n) ∘ Tr δs (L σs (suc n))

variable
  t t′ t″    : Exp
  r r′ r″    : Exp
  s s′ s″    : Exp
  σs σs′ σs″ : Substs
  δs δs′ δs″ : Substs

infix 4 _⊢_∶_ _⊢s_∶_
mutual
  data _⊢_∶_ : Envs → Exp → Typ → Set where
    vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ----------------
              Γ ∷ Γs ⊢ v x ∶ T
    ⟶-I     : (S ∷ Γ) ∷ Γs ⊢ t ∶ T →
              ----------------------
              Γ ∷ Γs ⊢ Λ t ∶ S ⟶ T
    ⟶-E     : Ψ ⊢ t ∶ S ⟶ T →
              Ψ ⊢ s ∶ S →
              -------------
              Ψ ⊢ t $ s ∶ T
    □-I     : [] ∷⁺ Ψ ⊢ t ∶ T →
              -----------------
              Ψ ⊢ box t ∶ □ T
    □-E     : ∀ {n} →
              Ψ ⊢ t ∶ □ T →
              len Ψ′ ≡ n →
              -------------------------
              Ψ′ ⁺++⁺ Ψ ⊢ unbox n t ∶ T
    t[σ]    : Ψ ⊢ t ∶ T →
              Ψ′ ⊢s σs ∶ Ψ →
              ----------------
              Ψ′ ⊢ t [ σs ] ∶ T

  data _⊢s_∶_ : Envs → Substs → Envs → Set where
    S-I  : Ψ ⊢s I ∶ Ψ
    S-p  : Ψ ⊢s σs ∶ (T ∷ Γ) ∷ Γs →
           ------------------------
           Ψ ⊢s p(σs) ∶ Γ ∷ Γs
    S-,  : Ψ ⊢s σs ∶ Γ ∷ Γs →
           Ψ ⊢ t ∶ T →
           --------------------------
           Ψ ⊢s σs , t ∶ (T ∷ Γ) ∷ Γs
    S-； : ∀ {n} →
           Ψ ⊢s σs ∶ Ψ′ →
           len Ψ″ ≡ n →
           -------------------------------
           Ψ″ ⁺++⁺ Ψ ⊢s σs ； n ∶ [] ∷⁺ Ψ′
    S-∘  : Ψ ⊢s δs ∶ Ψ′ →
           Ψ′ ⊢s σs ∶ Ψ″ →
           -----------------
           Ψ ⊢s σs ∘ δs ∶ Ψ″


infix 4 _⊢_≈_∶_ _⊢s_≈_∶_

mutual
  data _⊢_≈_∶_ : Envs → Exp → Exp → Typ → Set where
    v-≈        : ∀ {x} →
                 x ∶ T ∈ Γ →
                 ----------------------
                 Γ ∷ Γs ⊢ v x ≈ v x ∶ T
    Λ-cong     : (S ∷ Γ) ∷ Γs ⊢ t ≈ t′ ∶ T →
                 ---------------------------
                 Γ ∷ Γs ⊢ Λ t ≈ Λ t′ ∶ S ⟶ T
    $-cong     : Ψ ⊢ t ≈ t′ ∶ S ⟶ T →
                 Ψ ⊢ s ≈ s′ ∶ S →
                 -----------------------
                 Ψ ⊢ t $ s ≈ t′ $ s′ ∶ T
    box-cong   : [] ∷⁺ Ψ ⊢ t ≈ t′ ∶ T →
                 ------------------------
                 Ψ ⊢ box t ≈ box t′ ∶ □ T
    unbox-cong : ∀ {n} →
                 Ψ ⊢ t ≈ t′ ∶ □ T →
                 len Ψ′ ≡ n →
                 --------------------------------------
                 Ψ′ ⁺++⁺ Ψ ⊢ unbox n t ≈ unbox n t′ ∶ T
    []-cong    : Ψ ⊢ t ≈ t′ ∶ T →
                 Ψ′ ⊢s σs ≈ σs′ ∶ Ψ →
                 ------------------------------
                 Ψ′ ⊢ t [ σs ] ≈ t′ [ σs′ ] ∶ T
    v-ze       : Ψ ⊢s σs ∶ Γ ∷ Γs →
                 Ψ ⊢ t ∶ T →
                 --------------------------
                 Ψ ⊢ v 0 [ σs , t ] ≈ t ∶ T
    v-su       : ∀ {x} →
                 Ψ ⊢s σs ∶ Γ ∷ Γs →
                 Ψ ⊢ t ∶ T →
                 x ∶ T ∈ Γ →
                 -----------------------------------------
                 Ψ ⊢ v (suc x) [ σs , t ] ≈ v x [ σs ] ∶ T
    Λ-[]       : Ψ ⊢s σs ∶ Γ ∷ Γs →
                 (S ∷ Γ) ∷ Γs ⊢ t ∶ T →
                 -------------------------------------
                 Ψ ⊢ Λ t [ σs ] ≈ Λ (t [ σs ]) ∶ S ⟶ T
    $-[]       : Ψ ⊢s σs ∶ Ψ′ →
                 Ψ′ ⊢ t ∶ S ⟶ T →
                 Ψ′ ⊢ s ∶ S →
                 ----------------------------------------------
                 Ψ ⊢ t $ s [ σs ] ≈ (t [ σs ]) $ (s [ σs ]) ∶ T
    box-[]     : Ψ ⊢s σs ∶ Ψ′ →
                 [] ∷⁺ Ψ′ ⊢ t ∶ T →
                 ---------------------------------------
                 Ψ ⊢ box t [ σs ] ≈ box (t [ σs ]) ∶ □ T
    unbox-[]   : ∀ {n} →
                 Ψ ⊢s σs ∶ Ψ′ →
                 Ψ′ ⊢ t ∶ □ T →
                 len Ψ″ ≡ n →
                 ---------------------------------------------------------
                 Ψ ⊢ unbox n t [ σs ] ≈ unbox (L σs n) (t [ Tr σs n ]) ∶ T
    ⟶-β        : (S ∷ Γ) ∷ Γs ⊢ t ∶ T →
                 Γ ∷ Γs ⊢ s ∶ S →
                 --------------------------------------
                 Γ ∷ Γs ⊢ Λ t $ s ≈ t [ I , s ] ∶ S ⟶ T
    □-β        : ∀ {n} →
                 [] ∷⁺ Ψ ⊢ t ∶ T →
                 len Ψ′ ≡ n →
                 ------------------------------------------------
                 Ψ′ ⁺++⁺ Ψ ⊢ unbox n (box t) ≈ t [ I ； n ] ∶ □ T
    ⟶-η        : Ψ ⊢ t ∶ S ⟶ T →
                 -----------------------------
                 Ψ ⊢ t ≈ Λ (t [ p I ]) ∶ S ⟶ T
    □-η        : Ψ ⊢ t ∶ □ T →
                 -----------------------------
                 Ψ ⊢ t ≈ box (unbox 1 t) ∶ □ T
    ≈-sym      : Ψ ⊢ t ≈ t′ ∶ T →
                 ----------------
                 Ψ ⊢ t′ ≈ t ∶ T
    ≈-trans    : Ψ ⊢ t ≈ t′ ∶ T →
                 Ψ ⊢ t′ ≈ t″ ∶ T →
                 -----------------
                 Ψ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Envs → Substs → Substs → Envs → Set where
    ∘-I     : Ψ ⊢s σs ∶ Ψ′ →
              ---------------------
              Ψ ⊢s σs ∘ I ≈ σs ∶ Ψ′
    I-∘     : Ψ ⊢s σs ∶ Ψ′ →
              ---------------------
              Ψ ⊢s I ∘ σs ≈ σs ∶ Ψ′
    ∘-assoc : Ψ ⊢s σs ∶ Ψ′ →
              Ψ′ ⊢s σs′ ∶ Ψ″ →
              Ψ″ ⊢s σs″ ∶ Ψ‴ →
              -------------------------------------------
              Ψ ⊢s σs″ ∘ σs′ ∘ σs ≈ σs″ ∘ (σs′ ∘ σs) ∶ Ψ‴
    ,-∘     : Ψ′ ⊢s σs ∶ Γ ∷ Γs →
              Ψ′ ⊢ t ∶ T →
              Ψ ⊢s δs ∶ Ψ′ →
              --------------------------------------------------------
              Ψ ⊢s (σs , t) ∘ δs ≈ (σs ∘ δs) , t [ δs ] ∶ (T ∷ Γ) ∷ Γs
    p-∘     : Ψ′ ⊢s σs ∶ (T ∷ Γ) ∷ Γs →
              Ψ ⊢s δs ∶ Ψ′ →
              -------------------------------------------
              Ψ ⊢s p σs ∘ δs ≈ p (σs ∘ δs) ∶ (T ∷ Γ) ∷ Γs
    ；-∘     : ∀ {Ψ‴ n} →
              Ψ ⊢s σs ∶ Ψ′ →
              len Ψ″ ≡ n →
              Ψ‴ ⊢s δs ∶ Ψ″ ⁺++⁺ Ψ →
              ------------------------------------------------------
              Ψ‴ ⊢s σs ； n ∘ δs ≈ σs ∘ Tr δs n ； L δs n ∶ [] ∷⁺ Ψ′
    p-,     : Ψ ⊢s σs ∶ Γ ∷ Γs →
              Ψ ⊢ t ∶ T →
              -----------------------------
              Ψ ⊢s p (σs , t) ≈ σs ∶ Γ ∷ Γs
    ,-ext   : Ψ ⊢s σs ∶ (T ∷ Γ) ∷ Γs →
              ------------------------------------------
              Ψ ⊢s σs ≈ p σs , v 0 [ σs ] ∶ (T ∷ Γ) ∷ Γs
    ；-ext   : Ψ ⊢s σs ∶ [] ∷ Γ ∷ Γs →
              -----------------------------------------
              Ψ ⊢s σs ≈ Tr σs 1 ； L σs 1 ∶ [] ∷ Γ ∷ Γs
