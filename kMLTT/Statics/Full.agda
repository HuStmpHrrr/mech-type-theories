{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Full where

open import Level renaming (suc to succ)

open import Lib
open import LibNonEmpty public

record HasL {i} (A : Set i) : Set i where
  field
    L : A → ℕ → ℕ

open HasL {{...}} public

record HasTr {i} (A : Set i) : Set i where
  infixl 3.5 _∥_
  field
    _∥_ : A → ℕ → A

open HasTr {{...}} public

record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 8 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

infixl 6 _$_
infixl 8 _[|_]

mutual
  Typ = Exp

  data Exp : Set where
    -- type constructors
    N     : Typ
    Π     : Typ → Typ → Typ
    Se    : (i : ℕ) → Typ
    □     : Typ → Typ
    v     : (x : ℕ) → Exp
    -- natural numebrs
    ze    : Exp
    su    : Exp → Exp
    rec   : (T : Typ) (z s t : Exp) → Exp
    -- functions
    Λ     : Exp → Exp
    _$_   : Exp → Exp → Exp
    -- modal terms
    box   : Exp → Exp
    unbox : ℕ → Exp → Exp
    -- explicit substitutions
    sub   : Exp → Substs → Exp

  infixl 3 _∘_
  infixl 5 _；_
  data Substs : Set where
    -- identity
    I    : Substs
    -- weakening
    p    : Substs → Substs
    -- composition
    _∘_  : Substs → Substs → Substs
    -- extension
    _,_  : Substs → Exp → Substs
    -- modal transformation (MoT)
    _；_ : Substs → ℕ → Substs

-- standard contexts
Ctx : Set
Ctx = List Typ

-- context stacks
Ctxs : Set
Ctxs = List⁺ Ctx

-- cons the topmost context
infixr 5 _∺_
_∺_ : Typ → Ctxs → Ctxs
T ∺ (Ψ ∷ Ψs) = (T ∷ Ψ) ∷ Ψs

instance
  ExpMonotone : Monotone Exp Substs
  ExpMonotone = record { _[_] = sub }

-- one step weakening
wk : Substs
wk = p I

-- quick helpers
infixr 5 _⟶_
_⟶_ : Typ → Typ → Typ
S ⟶ T = Π S (T [ wk ])

_[|_] : Exp → Exp → Exp
t [| s ] = t [ I , s ]

q : Substs → Substs
q σ = (σ ∘ p I) , v 0

-- L and truncation for syntactic substitutions
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
  SubstsHasTr = record { _∥_ = S-Tr }

-- neutral and normal forms
mutual
  data Ne : Set where
    v     : (x : ℕ) → Ne
    rec   : (T : Nf) (z s : Nf) → Ne → Ne
    _$_   : Ne → (n : Nf) → Ne
    unbox : ℕ → Ne → Ne

  data Nf : Set where
    ne  : (u : Ne) → Nf
    N   : Nf
    Π   : Nf → Nf → Nf
    Se  : (i : ℕ) → Nf
    □   : Nf → Nf
    ze  : Nf
    su  : Nf → Nf
    Λ   : Nf → Nf
    box : Nf → Nf

variable
  S S′ S″ : Typ
  T T′ T″ : Typ
  Ψ Ψ′ Ψ″ : Ctx
  Ψs Ψs′  : List Ctx
  Γ Γ′ Γ″ : Ctxs
  Δ Δ′ Δ″ : Ctxs
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Substs
  τ τ′ τ″ : Substs
  u u′ u″ : Ne
  w w′ w″ : Nf

-- conversion from neutrals/normals to terms
mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (rec T z s u) = rec (Nf⇒Exp T) (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n
  Ne⇒Exp (unbox n u)   = unbox n (Ne⇒Exp u)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)  = Ne⇒Exp u
  Nf⇒Exp ze      = ze
  Nf⇒Exp (su w)  = su (Nf⇒Exp w)
  Nf⇒Exp (Λ w)   = Λ (Nf⇒Exp w)
  Nf⇒Exp N       = N
  Nf⇒Exp (Π S T) = Π (Nf⇒Exp S) (Nf⇒Exp T)
  Nf⇒Exp (Se i)  = Se i
  Nf⇒Exp (□ w)   = □ (Nf⇒Exp w)
  Nf⇒Exp (box w) = box (Nf⇒Exp w)

-- dependent context lookup
infix 2 _∶_∈!_
data _∶_∈!_ : ℕ → Typ → Ctxs → Set where
  here  : 0 ∶ T [ wk ] ∈! T ∺ Γ
  there : ∀ {n T S} → n ∶ T ∈! Γ → suc n ∶ T [ wk ] ∈! S ∺ Γ

infix 4 ⊢_ _⊢_ _⊢_∶_ _⊢s_∶_ _⊢_≈_∶_ _⊢_≈_ _⊢s_≈_∶_ ⊢_≈_

mutual
  data ⊢_ : Ctxs → Set where
    ⊢[] : ⊢ [] ∷ []
    ⊢κ  : ⊢ Γ →
          ----------
          ⊢ [] ∷⁺ Γ
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶ Se i →
          --------------
          ⊢ T ∺ Γ

  data ⊢_≈_ : Ctxs → Ctxs → Set where
    []-≈   : ⊢ [] ∷ [] ≈ [] ∷ []
    κ-cong : ⊢ Γ ≈ Δ →
             -------------------
             ⊢ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
    ∷-cong : ∀ {i} →
             ⊢ Γ ≈ Δ →
             Γ ⊢ T ∶ Se i →    -- remove after presupposition
             Δ ⊢ T′ ∶ Se i →   -- remove after presupposition
             ----------------
             ⊢ T ∺ Γ ≈ T′ ∺ Δ

  data _⊢_∶_ : Ctxs → Exp → Typ → Set where
    N-wf    : ∀ i →
              ⊢ Γ →
              -------------
              Γ ⊢ N ∶ Se i
    Se-wf   : ∀ i →
              ⊢ Γ →
              ----------------
              Γ ⊢ Se i ∶ Se (1 + i)
    Π-wf    : ∀ {i} →
              Γ ⊢ S ∶ Se i →
              S ∺ Γ ⊢ T ∶ Se i →
              --------------------
              Γ ⊢ Π S T ∶ Se i
    □-wf    : ∀ {i} →
              [] ∷⁺ Γ ⊢ T ∶ Se i →
              --------------------
              Γ ⊢ □ T ∶ Se i
    vlookup : ∀ {x} →
              ⊢ Γ →
              x ∶ T ∈! Γ →
              ------------
              Γ ⊢ v x ∶ T
    ze-I    : ⊢ Γ →
              -----------
              Γ ⊢ ze ∶ N
    su-I    : Γ ⊢ t ∶ N →
              -------------
              Γ ⊢ su t ∶ N
    N-E     : ∀ {i} →
              N ∺ Γ ⊢ T ∶ Se i →
              Γ ⊢ s ∶ T [| ze ] →
              T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              Γ ⊢ t ∶ N →
              --------------------------
              Γ ⊢ rec T s r t ∶ T [| t ]
    Λ-I     : ∀ {i} →
              Γ ⊢ S ∶ Se i →    -- remove after presupposision
              S ∺ Γ ⊢ t ∶ T →
              ------------------
              Γ ⊢ Λ t ∶ Π S T
    Λ-E     : Γ ⊢ r ∶ Π S T →
              Γ ⊢ s ∶ S →
              ---------------------
              Γ ⊢ r $ s ∶ T [| s ]
    □-I     : [] ∷⁺ Γ ⊢ t ∶ T →
              -----------------
              Γ ⊢ box t ∶ □ T
    □-E     : ∀ {n} Ψs →
              Γ ⊢ t ∶ □ T →
              ⊢ Ψs ++⁺ Γ →
              len Ψs ≡ n →
              -----------------------------------
              Ψs ++⁺ Γ ⊢ unbox n t ∶ T [ I ； n ]
    t[σ]    : Δ ⊢ t ∶ T →
              Γ ⊢s σ ∶ Δ →
              ---------------------
              Γ ⊢ t [ σ ] ∶ T [ σ ]
    cumu    : ∀ {i} →
              Γ ⊢ T ∶ Se i →
              ------------------
              Γ ⊢ T ∶ Se (1 + i)
    conv    : ∀ {i} →
              Γ ⊢ t ∶ S →
              Γ ⊢ S ≈ T ∶ Se i →
              ------------------
              Γ ⊢ t ∶ T

  data _⊢s_∶_ : Ctxs → Substs → Ctxs → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-p    : Γ ⊢s σ ∶ T ∺ Δ →
             -----------------
             Γ ⊢s p σ ∶ Δ
    s-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢ t ∶ T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ T ∺ Δ
    s-；    : ∀ {n} Ψs →
             Γ ⊢s σ ∶ Δ →
             ⊢ Ψs ++⁺ Γ →
             len Ψs ≡ n →
             -----------------------------
             Ψs ++⁺ Γ ⊢s σ ； n ∶ [] ∷⁺ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′

  data _⊢_≈_∶_ : Ctxs → Exp → Exp → Typ → Set where
    N-[]       : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 -----------------------
                 Γ ⊢ N [ σ ] ≈ N ∶ Se i
    Se-[]      : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 ----------------------------------
                 Γ ⊢ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
    Π-[]       : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →   -- remove after presupposition
                 S ∺ Δ ⊢ T ∶ Se i →
                 -------------------------------------------------
                 Γ ⊢ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
    □-[]       : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 [] ∷⁺ Δ ⊢ T ∶ Se i →
                 ---------------------------------------
                 Γ ⊢ □ T [ σ ] ≈ □ (T [ σ ； 1 ]) ∶ Se i
    Π-cong     : ∀ {i} →
                 Γ ⊢ S ∶ Se i →   -- remove after presupposition
                 Γ ⊢ S ≈ S′ ∶ Se i →
                 S ∺ Γ ⊢ T ≈ T′ ∶ Se i →
                 --------------------------
                 Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se i
    □-cong     : ∀ {i} →
                 [] ∷⁺ Γ ⊢ T ≈ T′ ∶ Se i →
                 --------------------------
                 Γ ⊢ □ T ≈ □ T′ ∶ Se i
    v-≈        : ∀ {x} →
                 ⊢ Γ →
                 x ∶ T ∈! Γ →
                 -----------------
                 Γ ⊢ v x ≈ v x ∶ T
    ze-≈       : ⊢ Γ →
                 ----------------
                 Γ ⊢ ze ≈ ze ∶ N
    su-cong    : Γ ⊢ t ≈ t′ ∶ N →
                 --------- ------------
                 Γ ⊢ su t ≈ su t′ ∶ N
    rec-cong   : ∀ {i} →
                 N ∺ Γ ⊢ T ≈ T′ ∶ Se i →
                 Γ ⊢ s ≈ s′ ∶ T [ I , ze ] →
                 T ∺ N ∺ Γ ⊢ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ≈ t′ ∶ N →
                 --------------------------------------------
                 Γ ⊢ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
    Λ-cong     : S ∺ Γ ⊢ t ≈ t′ ∶ T →
                 -----------------------
                 Γ ⊢ Λ t ≈ Λ t′ ∶ Π S T
    $-cong     : Γ ⊢ r ≈ r′ ∶ Π S T →
                 Γ ⊢ s ≈ s′ ∶ S →
                 -------------------------------
                 Γ ⊢ r $ s ≈ r′ $ s′ ∶ T [| s ]
    box-cong   : [] ∷⁺ Γ ⊢ t ≈ t′ ∶ T →
                 ------------------------
                 Γ ⊢ box t ≈ box t′ ∶ □ T
    unbox-cong : ∀ {n} Ψs →
                 Γ ⊢ t ≈ t′ ∶ □ T →
                 ⊢ Ψs ++⁺ Γ →
                 len Ψs ≡ n →
                 ------------------------------------------------
                 Ψs ++⁺ Γ ⊢ unbox n t ≈ unbox n t′ ∶ T [ I ； n ]
    []-cong    : Δ ⊢ t ≈ t′ ∶ T →
                 Γ ⊢s σ ≈ σ′ ∶ Δ →
                 ---------------------------------
                 Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T [ σ ]
    ze-[]      : Γ ⊢s σ ∶ Δ →
                 ----------------------
                 Γ ⊢ ze [ σ ] ≈ ze ∶ N
    su-[]      : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ N →
                 ----------------------------------
                 Γ ⊢ su t [ σ ] ≈ su (t [ σ ]) ∶ N
    rec-[]     : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 N ∺ Δ ⊢ T ∶ Se i →
                 Δ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Δ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Δ ⊢ t ∶ N →
                 -----------------------------------------------------------------------------------------------
                 Γ ⊢ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]
    Λ-[]       : Γ ⊢s σ ∶ Δ →
                 S ∺ Δ ⊢ t ∶ T →
                 --------------------------------------------
                 Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
    $-[]       : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ r ∶ Π S T →
                 Δ ⊢ s ∶ S →
                 ---------------------------------------------------------
                 Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
    box-[]     : Γ ⊢s σ ∶ Δ →
                 [] ∷⁺ Δ ⊢ t ∶ T →
                 ------------------------------------------
                 Γ ⊢ box t [ σ ] ≈ box (t [ σ ； 1 ]) ∶ □ T
    unbox-[]   : ∀ {n} Ψs →
                 Δ ⊢ t ∶ □ T →
                 Γ ⊢s σ ∶ Ψs ++⁺ Δ →
                 len Ψs ≡ n →
                 --------------------------------------------------------------------------
                 Γ ⊢ unbox n t [ σ ] ≈ unbox (L σ n) (t [ σ ∥ n ]) ∶ T [ (σ ∥ n) ； L σ n ]
    rec-β-ze   : ∀ {i} →
                 N ∺ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 ---------------------------------------------
                 Γ ⊢ rec T s r ze ≈ s ∶ T [| ze ]
    rec-β-su   : ∀ {i} →
                 N ∺ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ∶ N →
                 -----------------------------------------------------------------
                 Γ ⊢ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
    Λ-β        : ∀ {i} →
                 Γ ⊢ S ∶ Se i →   -- remove after presupposition
                 S ∺ Γ ⊢ t ∶ T →
                 Γ ⊢ s ∶ S →
                 ----------------------------------
                 Γ ⊢ Λ t $ s ≈ t [| s ] ∶ T [| s ]
    Λ-η        : Γ ⊢ t ∶ Π S T →
                 ----------------------------------
                 Γ ⊢ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
    □-β        : ∀ {n} Ψs →
                 [] ∷⁺ Γ ⊢ t ∶ T →
                 ⊢ Ψs ++⁺ Γ →
                 len Ψs ≡ n →
                 --------------------------------------------------------
                 Ψs ++⁺ Γ ⊢ unbox n (box t) ≈ t [ I ； n ] ∶ T [ I ； n ]
    □-η        : Γ ⊢ t ∶ □ T →
                 ------------------------------
                 Γ ⊢ t ≈ box (unbox 1 t) ∶ □ T
    [I]        : Γ ⊢ t ∶ T →
                 --------------------
                 Γ ⊢ t [ I ] ≈ t ∶ T
    [p]        : ∀ {x} →
                 Δ ⊢s σ ∶ T ∺ Γ →
                 x ∶ T ∈! Γ →
                 ---------------------------------------------
                 Δ ⊢ v x [ p σ ] ≈ v (suc x) [ σ ] ∶ T [ p σ ]
    [∘]        : Γ ⊢s τ ∶ Γ′ →
                 Γ′ ⊢s σ ∶ Γ″ →
                 Γ″ ⊢ t ∶ T →
                 ---------------------------------------------
                 Γ ⊢ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T [ σ ∘ τ ]
    [,]-v-ze   : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 Γ ⊢ s ∶ S [ σ ] →
                 --------------------------------
                 Γ ⊢ v 0 [ σ , s ] ≈ s ∶ S [ σ ]
    [,]-v-su   : ∀ {i x} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 Γ ⊢ s ∶ S [ σ ] →
                 x ∶ T ∈! Δ →
                 ---------------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]
    ≈-cumu     : ∀ {i} →
                 Γ ⊢ T ≈ T′ ∶ Se i →
                 -----------------------
                 Γ ⊢ T ≈ T′ ∶ Se (1 + i)
    ≈-conv     : ∀ {i} →
                 Γ ⊢ s ≈ t ∶ S →
                 Γ ⊢ S ≈ T ∶ Se i →
                 --------------------
                 Γ ⊢ s ≈ t ∶ T
    ≈-sym      : Γ ⊢ t ≈ t′ ∶ T →
                 ----------------
                 Γ ⊢ t′ ≈ t ∶ T
    ≈-trans    : Γ ⊢ t ≈ t′ ∶ T →
                 Γ ⊢ t′ ≈ t″ ∶ T →
                 ------ ------------
                 Γ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set where
    I-≈       : ⊢ Γ →
                --------------
                Γ ⊢s I ≈ I ∶ Γ
    p-cong    : Γ ⊢s σ ≈ σ′ ∶ T ∺ Δ →
                ----------------------
                Γ ⊢s p σ ≈ p σ′ ∶ Δ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                ----------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Δ ⊢ T ∶ Se i →
                Γ ⊢ t ≈ t′ ∶ T [ σ ] →
                -----------------------------
                Γ ⊢s σ , t ≈ σ′ , t′ ∶ T ∺ Δ
    ；-cong    : ∀ {n} Ψs →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                ⊢ Ψs ++⁺ Γ →
                len Ψs ≡ n →
                --------------------------------------
                Ψs ++⁺ Γ ⊢s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Δ
    I-∘       : Γ ⊢s σ ∶ Δ →
                -------------------
                Γ ⊢s I ∘ σ ≈ σ ∶ Δ
    ∘-I       : Γ ⊢s σ ∶ Δ →
                -------------------
                Γ ⊢s σ ∘ I ≈ σ ∶ Δ
    ∘-assoc   : ∀ {Γ‴} →
                Γ′ ⊢s σ ∶ Γ →
                Γ″ ⊢s σ′ ∶ Γ′ →
                Γ‴ ⊢s σ″ ∶ Γ″ →
                ---------------------------------------
                Γ‴ ⊢s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
    ,-∘       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ″ →
                Γ″ ⊢ T ∶ Se i →
                Γ′ ⊢ t ∶ T [ σ ] →
                Γ ⊢s τ ∶ Γ′ →
                ---------------------------------------------
                Γ ⊢s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∺ Γ″
    p-∘       : Γ′ ⊢s σ ∶ T ∺ Γ″ →
                Γ ⊢s τ ∶ Γ′ →
                ------------------------------
                Γ ⊢s p σ ∘ τ ≈ p (σ ∘ τ) ∶ Γ″
    ；-∘       : ∀ {n} Ψs →
                Γ′ ⊢s σ ∶ Γ″ →
                Γ ⊢s τ ∶ Ψs ++⁺ Γ′ →
                len Ψs ≡ n →
                ------------------------------
                Γ ⊢s σ ； n ∘ τ ≈ (σ ∘ τ ∥ n) ； L τ n ∶ [] ∷⁺ Γ″
    p-,       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ →
                Γ ⊢ T ∶ Se i →
                Γ′ ⊢ t ∶ T [ σ ] →
                -------------------------
                Γ′ ⊢s p (σ , t) ≈ σ ∶ Γ
    ,-ext     : Γ′ ⊢s σ ∶ T ∺ Γ →
                ----------------------------------
                Γ′ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ T ∺ Γ
    ；-ext     : Γ ⊢s σ ∶ [] ∷⁺ Δ →
                -----------------------------------
                Γ ⊢s σ ≈ (σ ∥ 1) ； L σ 1 ∶ [] ∷⁺ Δ
    s-≈-sym   : Γ ⊢s σ ≈ σ′ ∶ Δ →
                ------------------
                Γ ⊢s σ′ ≈ σ ∶ Δ
    s-≈-trans : Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢s σ′ ≈ σ″ ∶ Δ →
                -------------------
                Γ ⊢s σ ≈ σ″ ∶ Δ
    s-conv    : Γ ⊢s σ ≈ σ′ ∶ Δ →
                ⊢ Δ ≈ Δ′ →
                ------------------
                Γ ⊢s σ ≈ σ′ ∶ Δ′

_⊢_ : Ctxs → Typ → Set
Γ ⊢ T = ∃ λ i → Γ ⊢ T ∶ Se i

_⊢_≈_ : Ctxs → Exp → Exp → Set
Γ ⊢ s ≈ t = ∃ λ i → Γ ⊢ s ≈ t ∶ Se i
