{-# OPTIONS --without-K --safe #-}

module Unbox.Statics where

open import Lib

open import Level renaming (suc to succ)
open import LibNonEmpty public
open import Unbox.Typ public


record HasL {i} (A : Set i) : Set i where
  field
    L : A → ℕ → ℕ

open HasL {{...}} public

record HasTr {i} (A : Set i) : Set i where
  field
    Tr : A → ℕ → A

open HasTr {{...}} public

record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 8 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public


infixl 10 _$_
infixl 3 _∘_
infixl 5 _；_
mutual
  data Exp : Set where
    v     : (x : ℕ) → Exp
    Λ     : Exp → Exp
    _$_   : Exp → Exp → Exp
    box   : Exp → Exp
    unbox : ℕ → Exp → Exp
    sub   : Exp → Substs → Exp

  data Substs : Set where
    I    : Substs
    p    : Substs → Substs
    _,_  : Substs → Exp → Substs
    _；_ : Substs → ℕ → Substs
    _∘_  : Substs → Substs → Substs

instance
  ExpMonotone : Monotone Exp Substs
  ExpMonotone = record { _[_] = sub }

q : Substs → Substs
q σ = (σ ∘ p I) , v 0

S-L : Substs → ℕ → ℕ
S-L σ 0              = 0
S-L I (suc n)        = suc n
S-L (p σ) (suc n)    = S-L σ (suc n)
S-L (σ , t) (suc n)  = S-L σ (suc n)
S-L (σ ； m) (suc n) = m + S-L σ n
S-L (σ ∘ δ) (suc n)  = S-L δ (S-L σ (suc n))

instance
  SubstsHasL : HasL Substs
  SubstsHasL = record { L = S-L }

S-Tr : Substs → ℕ → Substs
S-Tr σ 0              = σ
S-Tr I (suc n)        = I
S-Tr (p σ) (suc n)    = S-Tr σ (suc n)
S-Tr (σ , t) (suc n)  = S-Tr σ (suc n)
S-Tr (σ ； m) (suc n) = S-Tr σ n
S-Tr (σ ∘ δ) (suc n)  = S-Tr σ (suc n) ∘ S-Tr δ (L σ (suc n))

instance
  SubstsHasTr : HasTr Substs
  SubstsHasTr = record { Tr = S-Tr }

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Substs
  δ δ′ δ″ : Substs

infix 4 _⊢_∶_ _⊢s_∶_
mutual
  data _⊢_∶_ : Ctxs → Exp → Typ → Set where
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
    □-E     : ∀ {n} Γs →
              Ψ ⊢ t ∶ □ T →
              len Γs ≡ n →
              -------------------------
              Γs ++⁺ Ψ ⊢ unbox n t ∶ T
    t[σ]    : Ψ ⊢ t ∶ T →
              Ψ′ ⊢s σ ∶ Ψ →
              ----------------
              Ψ′ ⊢ t [ σ ] ∶ T

  data _⊢s_∶_ : Ctxs → Substs → Ctxs → Set where
    S-I  : Ψ ⊢s I ∶ Ψ
    S-p  : Ψ ⊢s σ ∶ (T ∷ Γ) ∷ Γs →
           ------------------------
           Ψ ⊢s p σ ∶ Γ ∷ Γs
    S-,  : Ψ ⊢s σ ∶ Γ ∷ Γs →
           Ψ ⊢ t ∶ T →
           --------------------------
           Ψ ⊢s σ , t ∶ (T ∷ Γ) ∷ Γs
    S-； : ∀ {n} Γs →
           Ψ ⊢s σ ∶ Ψ′ →
           len Γs ≡ n →
           -------------------------------
           Γs ++⁺ Ψ ⊢s σ ； n ∶ [] ∷⁺ Ψ′
    S-∘  : Ψ ⊢s δ ∶ Ψ′ →
           Ψ′ ⊢s σ ∶ Ψ″ →
           -----------------
           Ψ ⊢s σ ∘ δ ∶ Ψ″

⊢q : Γ ∷ Γs ⊢s σ ∶ Δ ∷ Δs → ∀ T → (T ∷ Γ) ∷ Γs ⊢s q σ ∶ (T ∷ Δ) ∷ Δs
⊢q ⊢σ T = S-, (S-∘ (S-p S-I) ⊢σ) (vlookup here)

infix 4 _⊢_≈_∶_ _⊢s_≈_∶_

mutual
  data _⊢_≈_∶_ : Ctxs → Exp → Exp → Typ → Set where
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
    unbox-cong : ∀ {n} Γs →
                 Ψ ⊢ t ≈ t′ ∶ □ T →
                 len Γs ≡ n →
                 --------------------------------------
                 Γs ++⁺ Ψ ⊢ unbox n t ≈ unbox n t′ ∶ T
    []-cong    : Ψ ⊢ t ≈ t′ ∶ T →
                 Ψ′ ⊢s σ ≈ σ′ ∶ Ψ →
                 ------------------------------
                 Ψ′ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T
    Λ-[]       : Ψ ⊢s σ ∶ Γ ∷ Γs →
                 (S ∷ Γ) ∷ Γs ⊢ t ∶ T →
                 -------------------------------------
                 Ψ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ S ⟶ T
    $-[]       : Ψ ⊢s σ ∶ Ψ′ →
                 Ψ′ ⊢ t ∶ S ⟶ T →
                 Ψ′ ⊢ s ∶ S →
                 ----------------------------------------------
                 Ψ ⊢ t $ s [ σ ] ≈ (t [ σ ]) $ (s [ σ ]) ∶ T
    box-[]     : Ψ ⊢s σ ∶ Ψ′ →
                 [] ∷⁺ Ψ′ ⊢ t ∶ T →
                 ------------------------------------------
                 Ψ ⊢ box t [ σ ] ≈ box (t [ σ ； 1 ]) ∶ □ T
    unbox-[]   : ∀ {n} Γs →
                 Ψ ⊢s σ ∶ Γs ++⁺ Ψ′ →
                 Ψ′ ⊢ t ∶ □ T →
                 len Γs ≡ n →
                 ---------------------------------------------------------
                 Ψ ⊢ unbox n t [ σ ] ≈ unbox (L σ n) (t [ Tr σ n ]) ∶ T
    ⟶-β        : (S ∷ Γ) ∷ Γs ⊢ t ∶ T →
                 Γ ∷ Γs ⊢ s ∶ S →
                 --------------------------------------
                 Γ ∷ Γs ⊢ Λ t $ s ≈ t [ I , s ] ∶ T
    □-β        : ∀ {n} Γs →
                 [] ∷⁺ Ψ ⊢ t ∶ T →
                 len Γs ≡ n →
                 ------------------------------------------------
                 Γs ++⁺ Ψ ⊢ unbox n (box t) ≈ t [ I ； n ] ∶ T
    ⟶-η        : Ψ ⊢ t ∶ S ⟶ T →
                 -------------------------------------
                 Ψ ⊢ t ≈ Λ ((t [ p I ]) $ v 0) ∶ S ⟶ T
    □-η        : Ψ ⊢ t ∶ □ T →
                 -----------------------------
                 Ψ ⊢ t ≈ box (unbox 1 t) ∶ □ T
    [I]        : Ψ ⊢ t ∶ T →
                 -------------------
                 Ψ ⊢ t [ I ] ≈ t ∶ T
    [∘]        : Ψ ⊢s σ ∶ Ψ′ →
                 Ψ′ ⊢s σ′ ∶ Ψ″ →
                 Ψ″ ⊢ t ∶ T →
                 --------------------------------------
                 Ψ ⊢ t [ σ′ ∘ σ ] ≈ t [ σ′ ] [ σ ] ∶ T
    v-ze       : Ψ ⊢s σ ∶ Γ ∷ Γs →
                 Ψ ⊢ t ∶ T →
                 --------------------------
                 Ψ ⊢ v 0 [ σ , t ] ≈ t ∶ T
    v-su       : ∀ {x} →
                 Ψ ⊢s σ ∶ Γ ∷ Γs →
                 Ψ ⊢ t ∶ S →
                 x ∶ T ∈ Γ →
                 -----------------------------------------
                 Ψ ⊢ v (suc x) [ σ , t ] ≈ v x [ σ ] ∶ T
    [p]        : ∀ {x} →
                 Ψ ⊢s σ ∶ (S ∷ Γ) ∷ Γs →
                 x ∶ T ∈ Γ →
                 --------------------------------------
                 Ψ ⊢ v x [ p σ ] ≈ v (suc x) [ σ ] ∶ T
    ≈-sym      : Ψ ⊢ t ≈ t′ ∶ T →
                 ----------------
                 Ψ ⊢ t′ ≈ t ∶ T
    ≈-trans    : Ψ ⊢ t ≈ t′ ∶ T →
                 Ψ ⊢ t′ ≈ t″ ∶ T →
                 -----------------
                 Ψ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set where
    I-≈       : Ψ ⊢s I ≈ I ∶ Ψ
    p-cong    : Ψ ⊢s σ ≈ σ′ ∶ (T ∷ Γ) ∷ Γs →
                ----------------------------
                Ψ ⊢s p σ ≈ p σ′ ∶ Γ ∷ Γs
    ,-cong    : Ψ ⊢s σ ≈ σ′ ∶ Γ ∷ Γs →
                Ψ ⊢ t ≈ t′ ∶ T →
                -----------------------------------
                Ψ ⊢s σ , t ≈ σ′ , t′ ∶ (T ∷ Γ) ∷ Γs
    ；-cong    : ∀ {n} Γs →
                Ψ ⊢s σ ≈ σ′ ∶ Ψ′ →
                len Γs ≡ n →
                --------------------------------------
                Γs ++⁺ Ψ ⊢s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Ψ′
    ∘-cong    : Ψ ⊢s δ ≈ δ′ ∶ Ψ′ →
                Ψ′ ⊢s σ ≈ σ′ ∶ Ψ″ →
                -------------------------
                Ψ ⊢s σ ∘ δ ≈ σ′ ∘ δ′ ∶ Ψ″
    ∘-I       : Ψ ⊢s σ ∶ Ψ′ →
                ---------------------
                Ψ ⊢s σ ∘ I ≈ σ ∶ Ψ′
    I-∘       : Ψ ⊢s σ ∶ Ψ′ →
                ---------------------
                Ψ ⊢s I ∘ σ ≈ σ ∶ Ψ′
    ∘-assoc   : Ψ ⊢s σ ∶ Ψ′ →
                Ψ′ ⊢s σ′ ∶ Ψ″ →
                Ψ″ ⊢s σ″ ∶ Ψ‴ →
                -------------------------------------------
                Ψ ⊢s σ″ ∘ σ′ ∘ σ ≈ σ″ ∘ (σ′ ∘ σ) ∶ Ψ‴
    ,-∘       : Ψ′ ⊢s σ ∶ Γ ∷ Γs →
                Ψ′ ⊢ t ∶ T →
                Ψ ⊢s δ ∶ Ψ′ →
                --------------------------------------------------------
                Ψ ⊢s (σ , t) ∘ δ ≈ (σ ∘ δ) , t [ δ ] ∶ (T ∷ Γ) ∷ Γs
    p-∘       : Ψ′ ⊢s σ ∶ (T ∷ Γ) ∷ Γs →
                Ψ ⊢s δ ∶ Ψ′ →
                -------------------------------------------
                Ψ ⊢s p σ ∘ δ ≈ p (σ ∘ δ) ∶ Γ ∷ Γs
    ；-∘       : ∀ {n} Γs →
                Ψ ⊢s σ ∶ Ψ′ →
                Ψ″ ⊢s δ ∶ Γs ++⁺ Ψ →
                len Γs ≡ n →
                --------------------------------------------------
                Ψ″ ⊢s σ ； n ∘ δ ≈ (σ ∘ Tr δ n) ； L δ n ∶ [] ∷⁺ Ψ′
    p-,       : Ψ ⊢s σ ∶ Γ ∷ Γs →
                Ψ ⊢ t ∶ T →
                -----------------------------
                Ψ ⊢s p (σ , t) ≈ σ ∶ Γ ∷ Γs
    ,-ext     : Ψ ⊢s σ ∶ (T ∷ Γ) ∷ Γs →
                ------------------------------------------
                Ψ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ (T ∷ Γ) ∷ Γs
    ；-ext     : Ψ ⊢s σ ∶ [] ∷ Γ ∷ Γs →
                -----------------------------------------
                Ψ ⊢s σ ≈ Tr σ 1 ； L σ 1 ∶ [] ∷ Γ ∷ Γs
    s-≈-sym   : Ψ ⊢s σ ≈ σ′ ∶ Ψ′ →
                ------------------
                Ψ ⊢s σ′ ≈ σ ∶ Ψ′
    s-≈-trans : Ψ ⊢s σ ≈ σ′ ∶ Ψ′ →
                Ψ ⊢s σ′ ≈ σ″ ∶ Ψ′ →
                --------------------
                Ψ ⊢s σ ≈ σ″ ∶ Ψ′

mutual
  data Ne : Set where
    v     : (x : ℕ) → Ne
    _$_   : Ne → (n : Nf) → Ne
    unbox : ℕ → Ne → Ne

  data Nf : Set where
    ne  : (u : Ne) → Nf
    Λ   : Nf → Nf
    box : Nf → Nf

pattern v′ x = ne (v x)

variable
  u u′ u″ : Ne
  w w′ w″ : Nf

mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)       = v x
  Ne⇒Exp (u $ w)     = Ne⇒Exp u $ Nf⇒Exp w
  Ne⇒Exp (unbox n c) = unbox n (Ne⇒Exp c)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u) = Ne⇒Exp u
  Nf⇒Exp (Λ w)  = Λ (Nf⇒Exp w)
  Nf⇒Exp (box w) = box (Nf⇒Exp w)
