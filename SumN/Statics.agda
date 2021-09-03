{-# OPTIONS --without-K --safe #-}

module SumN.Statics where

open import Lib

infixr 5 _⟶_
infixl 7 _∪_
infixl 9 _X_

-- types
data Typ : Set where
  N   : Typ
  _∪_ : Typ → Typ → Typ
  _X_ : Typ → Typ → Typ
  _⟶_ : Typ → Typ → Typ

Ctx : Set
Ctx = List Typ

variable
  S S′ S″ : Typ
  T T′ T″ : Typ
  U U′ U″ : Typ
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx

data Exp : Set
data Subst : Set

infixl 10 _$_
infixl 11 _[_]
data Exp where
  v    : (x : ℕ) → Exp
  ze   : Exp
  su   : Exp → Exp
  rec  : (T : Typ) (z s t : Exp) → Exp
  p₁   : Exp → Exp
  p₂   : Exp → Exp
  pr   : Exp → Exp → Exp
  i₁   : Exp → Exp
  i₂   : Exp → Exp
  pm   : (T : Typ) → Exp → Exp → Exp → Exp
  Λ    : Exp → Exp
  _$_  : Exp → Exp → Exp
  _[_] : Exp → Subst → Exp

infixl 3 _∘_
data Subst where
  ↑   : Subst
  I   : Subst
  _∘_ : Subst → Subst → Subst
  _,_ : Subst → Exp → Subst

q : Subst → Subst
q σ = (σ ∘ ↑) , v 0

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : Subst
  τ τ′ τ″ : Subst

infix 4 _⊢_∶_ _⊢s_∶_

mutual

  data _⊢_∶_ : Ctx → Exp → Typ → Set where
    vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ------------
              Γ ⊢ v x ∶ T
    ze-I    : Γ ⊢ ze ∶ N
    su-I    : Γ ⊢ t ∶ N →
              -------------
              Γ ⊢ su t ∶ N
    N-E     : Γ ⊢ s ∶ T →
              Γ ⊢ r ∶ N ⟶ T ⟶ T →
              Γ ⊢ t ∶ N →
              ----------------------
              Γ ⊢ rec T s r t ∶ T
    X-I     : Γ ⊢ s ∶ S →
              Γ ⊢ r ∶ U →
              ------------------
              Γ ⊢ pr s r ∶ S X U
    X-E₁    : Γ ⊢ t ∶ S X U →
              -----------------
              Γ ⊢ p₁ t ∶ S
    X-E₂    : Γ ⊢ t ∶ S X U →
              -----------------
              Γ ⊢ p₂ t ∶ U
    ∪-I₁    : Γ ⊢ s ∶ S →
              --------------------
              Γ ⊢ i₁ s ∶ S ∪ U
    ∪-I₂    : Γ ⊢ r ∶ U →
              --------------------
              Γ ⊢ i₂ r ∶ S ∪ U
    ∪-E     : Γ ⊢ t ∶ S ∪ U →
              Γ ⊢ s ∶ S ⟶ T →
              Γ ⊢ r ∶ U ⟶ T →
              --------------------
              Γ ⊢ pm T t s r ∶ T
    Λ-I     : S ∷ Γ ⊢ t ∶ T →
              ------------------
              Γ ⊢ Λ t ∶ S ⟶ T
    Λ-E     : Γ ⊢ r ∶ S ⟶ T →
              Γ ⊢ s ∶ S →
              ------------------
              Γ ⊢ r $ s ∶ T
    t[σ]    : Δ ⊢ t ∶ T →
              Γ ⊢s σ ∶ Δ →
              ----------------
              Γ ⊢ t [ σ ] ∶ T

  data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
    S-↑ : S ∷ Γ ⊢s ↑ ∶ Γ
    S-I : Γ ⊢s I ∶ Γ
    S-∘ : Γ ⊢s τ ∶ Γ′ →
          Γ′ ⊢s σ ∶ Γ″ →
          ----------------
          Γ ⊢s σ ∘ τ ∶ Γ″
    S-, : Γ ⊢s σ ∶ Δ →
          Γ ⊢ s ∶ S →
          -------------------
          Γ ⊢s σ , s ∶ S ∷ Δ

infix 4 _⊢_≈_∶_ _⊢s_≈_∶_

mutual

  data _⊢_≈_∶_ : Ctx → Exp → Exp → Typ → Set where
    v-≈      : ∀ {x} →
               x ∶ T ∈ Γ →
               ------------------
               Γ ⊢ v x  ≈ v x ∶ T
    ze-≈     : Γ ⊢ ze ≈ ze ∶ N
    su-cong  : Γ ⊢ t ≈ t′ ∶ N →
               --------------------
               Γ ⊢ su t ≈ su t′ ∶ N
    rec-cong : Γ ⊢ s ≈ s′ ∶ T →
               Γ ⊢ r ≈ r′ ∶ N ⟶ T ⟶ T →
               Γ ⊢ t ≈ t′ ∶ N →
               ------------------------------------
               Γ ⊢ rec T s r t ≈ rec T s′ r′ t′ ∶ T
    pr-cong  : Γ ⊢ s ≈ s′ ∶ S →
               Γ ⊢ r ≈ r′ ∶ U →
               -----------------------------
               Γ ⊢ pr s r ≈ pr s′ r′ ∶ S X U
    p₁-cong  : Γ ⊢ t ≈ t′ ∶ S X U →
               --------------------
               Γ ⊢ p₁ t ≈ p₁ t′ ∶ S
    p₂-cong  : Γ ⊢ t ≈ t′ ∶ S X U →
               --------------------
               Γ ⊢ p₂ t ≈ p₂ t′ ∶ U
    i₁-cong  : Γ ⊢ s ≈ s′ ∶ S →
               ------------------------
               Γ ⊢ i₁ s ≈ i₁ s′ ∶ S ∪ U
    i₂-cong  : Γ ⊢ r ≈ r′ ∶ U →
               ------------------------
               Γ ⊢ i₂ r ≈ i₂ r′ ∶ S ∪ U
    pm-cong  : Γ ⊢ t ≈ t′ ∶ S ∪ U →
               Γ ⊢ s ≈ s′ ∶ S ⟶ T →
               Γ ⊢ r ≈ r′ ∶ U ⟶ T →
               ----------------------------------
               Γ ⊢ pm T t s r ≈ pm T t′ s′ r′ ∶ T
    Λ-cong   : S ∷ Γ ⊢ t ≈ t′ ∶ T →
               ----------------------
               Γ ⊢ Λ t ≈ Λ t′ ∶ S ⟶ T
    $-cong   : Γ ⊢ r ≈ r′ ∶ S ⟶ T →
               Γ ⊢ s ≈ s′ ∶ S →
               -----------------------
               Γ ⊢ r $ s ≈ r′ $ s′ ∶ T
    []-cong  : Γ ⊢s σ ≈ σ′ ∶ Δ →
               Δ ⊢ t ≈ t′ ∶ T →
               ---------------------------
               Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T
    ze-[]    : Γ ⊢s σ ∶ Δ →
               ----------------------
               Γ ⊢ ze [ σ ] ≈ ze ∶ N
    su-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ t ∶ N →
               ---------------------------------
               Γ ⊢ su t [ σ ] ≈ su (t [ σ ]) ∶ N
    rec-[]   : Γ ⊢s σ ∶ Δ →
               Δ ⊢ s ∶ T →
               Δ ⊢ r ∶ N ⟶ T ⟶ T →
               Δ ⊢ t ∶ N →
               ---------------------------------------------------------------
               Γ ⊢ rec T s r t [ σ ] ≈ rec T (s [ σ ]) (r [ σ ]) (t [ σ ]) ∶ T
    pr-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ s ∶ S →
               Δ ⊢ r ∶ U →
               -------------------------------------------------
               Γ ⊢ pr s r [ σ ] ≈ pr (s [ σ ]) (r [ σ ]) ∶ S X U
    p₁-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ t ∶ S X U →
               ---------------------------------
               Γ ⊢ p₁ t [ σ ] ≈ p₁ (t [ σ ]) ∶ S
    p₂-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ t ∶ S X U →
               ---------------------------------
               Γ ⊢ p₂ t [ σ ] ≈ p₂ (t [ σ ]) ∶ U
    i₁-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ s ∶ S →
               -------------------------------------
               Γ ⊢ i₁ s [ σ ] ≈ i₁ (s [ σ ]) ∶ S ∪ U
    i₂-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ r ∶ U →
               -------------------------------------
               Γ ⊢ i₂ r [ σ ] ≈ i₂ (r [ σ ]) ∶ S ∪ U
    pm-[]    : Γ ⊢s σ ∶ Δ →
               Δ ⊢ t ∶ S ∪ U →
               Δ ⊢ s ∶ S ⟶ T →
               Δ ⊢ r ∶ U ⟶ T →
               -------------------------------------------------------------
               Γ ⊢ pm T t s r [ σ ] ≈ pm T (t [ σ ]) (s [ σ ]) (r [ σ ]) ∶ T
    Λ-[]     : Γ ⊢s σ ∶ Δ →
               S ∷ Δ ⊢ t ∶ T →
               -------------------------------------
               Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ S ⟶ T
    $-[]     : Γ ⊢s σ ∶ Δ →
               Δ ⊢ r ∶ S ⟶ T →
               Δ ⊢ s ∶ S →
               -----------------------------------------
               Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T
    X-β₁     : Γ ⊢ s ∶ S →
               Γ ⊢ r ∶ U →
               -----------------------
               Γ ⊢ p₁ (pr s r) ≈ s ∶ S
    X-β₂     : Γ ⊢ s ∶ S →
               Γ ⊢ r ∶ U →
               -----------------------
               Γ ⊢ p₂ (pr s r) ≈ r ∶ U
    X-η      : Γ ⊢ t ∶ S X U →
               --------------------------------
               Γ ⊢ t ≈ pr (p₁ t) (p₂ t) ∶ S X U
    ∪-β₁     : Γ ⊢ t ∶ S →
               Γ ⊢ s ∶ S ⟶ T →
               Γ ⊢ r ∶ U ⟶ T →
               -------------------------------
               Γ ⊢ pm T (i₁ t) s r ≈ s $ t ∶ T
    ∪-β₂     : Γ ⊢ t ∶ U →
               Γ ⊢ s ∶ S ⟶ T →
               Γ ⊢ r ∶ U ⟶ T →
               -------------------------------
               Γ ⊢ pm T (i₂ t) s r ≈ r $ t ∶ T
    rec-β-ze : Γ ⊢ s ∶ T →
               Γ ⊢ r ∶ N ⟶ T ⟶ T →
               -------------------------
               Γ ⊢ rec T s r ze ≈ s ∶ T
    rec-β-su : Γ ⊢ s ∶ T →
               Γ ⊢ r ∶ N ⟶ T ⟶ T →
               Γ ⊢ t ∶ N →
               --------------------------------------------------
               Γ ⊢ rec T s r (su t) ≈ r $ t $ (rec T s r t) ∶ T
    Λ-β      : S ∷ Γ ⊢ t ∶ T →
               Γ ⊢ s ∶ S →
               -----------------------------------------
               Γ ⊢ Λ t $ s ≈ t [ I , s ] ∶ T
    Λ-η      : Γ ⊢ t ∶ S ⟶ T →
               ---------------------------------------------------
               Γ ⊢ t ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T
    [I]      : Γ ⊢ t ∶ T →
               --------------------
               Γ ⊢ t [ I ] ≈ t ∶ T
    ↑-lookup : ∀ {x} →
               x ∶ T ∈ Γ →
               ---------------------------------------
               S ∷ Γ ⊢ v x [ ↑ ] ≈ v (suc x) ∶ T
    [∘]      : Γ ⊢s τ ∶ Γ′ →
               Γ′ ⊢s σ ∶ Γ″ →
               Γ″ ⊢ t ∶ T →
               -------------------------------------------
               Γ ⊢ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T
    [,]-v-ze : Γ ⊢s σ ∶ Δ →
               Γ ⊢ s ∶ S →
               --------------------------------
               Γ ⊢ v 0 [ σ , s ] ≈ s ∶ S
    [,]-v-su : ∀ {x} →
               Γ ⊢s σ ∶ Δ →
               Γ ⊢ s ∶ S →
               x ∶ T ∈ Δ →
               ---------------------------------------
               Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T
    ≈-sym    : Γ ⊢ t ≈ t′ ∶ T →
               ----------------
               Γ ⊢ t′ ≈ t ∶ T
    ≈-trans  : Γ ⊢ t ≈ t′ ∶ T →
               Γ ⊢ t′ ≈ t″ ∶ T →
               -----------------
               Γ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set where
    ↑-≈       : S ∷ Γ ⊢s ↑ ≈ ↑ ∶ Γ
    I-≈       : Γ ⊢s I ≈ I ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                -------------------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢ s ≈ s′ ∶ S →
                -----------------------------
                Γ ⊢s σ , s ≈ σ′ , s′ ∶ S ∷ Δ
    ↑-∘-,     : Γ ⊢s σ ∶ Δ →
                Γ ⊢ s ∶ S →
                ------------------------
                Γ ⊢s ↑ ∘ (σ , s) ≈ σ ∶ Δ
    I-∘       : Γ ⊢s σ ∶ Δ →
                ------------------
                Γ ⊢s I ∘ σ ≈ σ ∶ Δ
    ∘-I       : Γ ⊢s σ ∶ Δ →
                ------------------
                Γ ⊢s σ ∘ I ≈ σ ∶ Δ
    ∘-assoc   : ∀ {Γ‴} →
                Γ′ ⊢s σ ∶ Γ →
                Γ″ ⊢s σ′ ∶ Γ′ →
                Γ‴ ⊢s σ″ ∶ Γ″ →
                ------------------------------------------
                Γ‴ ⊢s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
    ,-ext     : Γ ⊢s σ ∶ S ∷ Δ →
                ------------------------------------
                Γ ⊢s σ ≈ (↑ ∘ σ) , v 0 [ σ ] ∶ S ∷ Δ
    S-≈-sym   : Γ ⊢s σ ≈ σ′ ∶ Δ →
                -----------------
                Γ ⊢s σ′ ≈ σ ∶ Δ
    S-≈-trans : Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢s σ′ ≈ σ″ ∶ Δ →
                ------------------
                Γ ⊢s σ ≈ σ″ ∶ Δ

mutual

  ≈-refl : Γ ⊢ t ∶ T → Γ ⊢ t ≈ t ∶ T
  ≈-refl (vlookup T∈Γ) = v-≈ T∈Γ
  ≈-refl ze-I          = ze-≈
  ≈-refl (su-I t)      = su-cong (≈-refl t)
  ≈-refl (N-E s r t)   = rec-cong (≈-refl s) (≈-refl r) (≈-refl t)
  ≈-refl (X-I s r)     = pr-cong (≈-refl s) (≈-refl r)
  ≈-refl (X-E₁ t)      = p₁-cong (≈-refl t)
  ≈-refl (X-E₂ t)      = p₂-cong (≈-refl t)
  ≈-refl (∪-I₁ t)      = i₁-cong (≈-refl t)
  ≈-refl (∪-I₂ t)      = i₂-cong (≈-refl t)
  ≈-refl (∪-E t s r)   = pm-cong (≈-refl t) (≈-refl s) (≈-refl r)
  ≈-refl (Λ-I t)       = Λ-cong (≈-refl t)
  ≈-refl (Λ-E r s)     = $-cong (≈-refl r) (≈-refl s)
  ≈-refl (t[σ] t σ)    = []-cong (S-≈-refl σ) (≈-refl t)

  S-≈-refl : Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ ∶ Δ
  S-≈-refl S-↑ = ↑-≈
  S-≈-refl S-I = I-≈
  S-≈-refl (S-∘ σ τ) = ∘-cong (S-≈-refl σ) (S-≈-refl τ)
  S-≈-refl (S-, σ s) = ,-cong (S-≈-refl σ) (≈-refl s)

mutual
  data Ne : Set where
    v   : (x : ℕ) → Ne
    _$_ : Ne → (n : Nf) → Ne
    rec : (T : Typ) (z s : Nf) → Ne → Ne
    p₁  : Ne → Ne
    p₂  : Ne → Ne
    pm  : (T : Typ) → Ne → Nf → Nf → Ne

  data Nf : Set where
    ne : (u : Ne) → Nf
    ze : Nf
    su : Nf → Nf
    pr : Nf → Nf → Nf
    i₁ : Nf → Nf
    i₂ : Nf → Nf
    Λ  : Nf → Nf

pattern v′ x = ne (v x)

variable
  u u′ u″ : Ne
  w w′ w″ : Nf

mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n
  Ne⇒Exp (rec T z s u) = rec T (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (p₁ u)        = p₁ (Ne⇒Exp u)
  Ne⇒Exp (p₂ u)        = p₂ (Ne⇒Exp u)
  Ne⇒Exp (pm T t s r)  = pm T (Ne⇒Exp t) (Nf⇒Exp s) (Nf⇒Exp r)

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u)    = Ne⇒Exp u
  Nf⇒Exp ze        = ze
  Nf⇒Exp (su w)    = su (Nf⇒Exp w)
  Nf⇒Exp (pr w w′) = pr (Nf⇒Exp w) (Nf⇒Exp w′)
  Nf⇒Exp (i₁ w)    = i₁ (Nf⇒Exp w)
  Nf⇒Exp (i₂ w)    = i₂ (Nf⇒Exp w)
  Nf⇒Exp (Λ w)     = Λ (Nf⇒Exp w)
