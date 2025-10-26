{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Definitions where

open import Level renaming (suc to succ)
open import Relation.Nullary.Decidable

open import Lib


infixr 5 _⟶_

-- types
data Typ : Set where
  N   : Typ
  _⟶_ : Typ → Typ → Typ

Ctx : Set
Ctx = List Typ

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx


infixl 10 _$_
data Exp : Set where
  v    : (x : ℕ) → Exp
  ze   : Exp
  su   : Exp → Exp
  rec  : (T : Typ) (z s t : Exp) → Exp
  Λ    : Exp → Exp
  _$_  : Exp → Exp → Exp


variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp


-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public

record Composable {i} (A : Set i) : Set i where
  infixl 4.5 _∙_
  field
    _∙_ : A → A → A

open Composable {{...}} public

record HeadWeaken {i} (A : Set i) : Set i where
  field
    q : A → A

open HeadWeaken {{...}} public

record Extends {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _↦_
  field
    _↦_ : A → B → A

open Extends {{...}} public

record HasIdentity {i} (A : Set i) : Set i where
  field
    id : A

open HasIdentity {{...}} public


Wk : Set
Wk = ℕ → ℕ

Subst : Set
Subst = ℕ → Exp


variable
  ϕ ϕ′ ϕ″ : Wk
  ψ ψ′ ψ″ : Wk
  σ σ′ σ″ : Subst
  τ τ′ τ″ : Subst

conv : Wk → Subst
conv ϕ n = v (ϕ n)

wk : ℕ → Wk
wk n m
  with n ≤? m
...  | yes _ = 1 + m
...  | no _  = m

wk-compose : Wk → Wk → Wk
wk-compose ϕ ψ n = ψ (ϕ n)

wk-q : Wk → Wk
wk-q ϕ 0 = 0
wk-q ϕ (suc n) = 1 + ϕ n

instance
  Wk-Composable : Composable Wk
  Wk-Composable = record { _∙_ = wk-compose }

  Wk-HeadWeaken : HeadWeaken Wk
  Wk-HeadWeaken = record { q = wk-q }

  Wk-HasIdentity : HasIdentity Wk
  Wk-HasIdentity = record { id = λ z → z }

wk-app : Exp → Wk → Exp
wk-app (v x) ϕ         = v (ϕ x)
wk-app ze ϕ            = ze
wk-app (su t) ϕ        = su (wk-app t ϕ)
wk-app (rec T u s t) ϕ = rec T (wk-app u ϕ) (wk-app s (q (q ϕ))) (wk-app t ϕ)
wk-app (Λ t) ϕ         = Λ (wk-app t (q ϕ))
wk-app (t $ s) ϕ       = (wk-app t ϕ) $ (wk-app s ϕ)


instance
  Wk-Monotone : Monotone Exp Wk
  Wk-Monotone = record { _[_] = wk-app }

wk-subst-app : Subst → Wk → Subst
wk-subst-app σ ϕ n = σ n [ ϕ ]


instance
  Wk-Monotone′ : Monotone Subst Wk
  Wk-Monotone′ = record { _[_] = wk-subst-app }


subst-ext : Subst → Exp → Subst
subst-ext σ t 0       = t
subst-ext σ t (suc n) = σ n

subst-q : Subst → Subst
subst-q σ 0 = v 0
subst-q σ (suc n) = (σ [ wk 0 ]) n

instance
  Subst-Extends : Extends Subst Exp
  Subst-Extends = record { _↦_ = subst-ext }

  Subst-HeadWeaken : HeadWeaken Subst
  Subst-HeadWeaken = record { q = subst-q }

  Subst-HasIdentity : HasIdentity Subst
  Subst-HasIdentity = record { id = v }

subst-app : Exp → Subst → Exp
subst-app (v x) σ         = σ x
subst-app ze σ            = ze
subst-app (su t) σ        = su (subst-app t σ)
subst-app (rec T u s t) σ = rec T (subst-app u σ) (subst-app s (q (q σ))) (subst-app t σ)
subst-app (Λ t) σ         = Λ (subst-app t (q σ))
subst-app (t $ s) σ       = (subst-app t σ) $ (subst-app s σ)

instance
  Subst-Monotone : Monotone Exp Subst
  Subst-Monotone = record { _[_] = subst-app }

subst-compose : Subst → Subst → Subst
subst-compose σ σ′ n = σ n [ σ′ ]

instance
  Subst-Composable : Composable Subst
  Subst-Composable = record { _∙_ = subst-compose }

-- infixl 3 _∘_
-- data Subst where
--   ↑   : Subst
--   I   : Subst
--   _∘_ : Subst → Subst → Subst
--   _,_ : Subst → Exp → Subst

-- q : Subst → Subst
-- q σ = (σ ∘ ↑) , v 0

-- data Weaken : Ctx → Ctx → Set where
--   I : Weaken Γ Γ
--   P : ∀ T → Weaken Γ Δ → Weaken (T ∷ Γ) Δ
--   Q : ∀ T → Weaken Γ Δ → Weaken (T ∷ Γ) (T ∷ Δ)

-- _∘∘_ : Weaken Γ′ Δ → Weaken Γ Γ′ → Weaken Γ Δ
-- σ      ∘∘ I     = σ
-- σ      ∘∘ P T δ = P T (σ ∘∘ δ)
-- I      ∘∘ Q T δ = Q T δ
-- P .T σ ∘∘ Q T δ = P T (σ ∘∘ δ)
-- Q .T σ ∘∘ Q T δ = Q T (σ ∘∘ δ)

-- Weaken⇒Subst : Weaken Γ Δ → Subst
-- Weaken⇒Subst I        = I
-- Weaken⇒Subst (P T wk) = Weaken⇒Subst wk ∘ ↑
-- Weaken⇒Subst (Q T wk) = q (Weaken⇒Subst wk)

-- module Typing where

--   infix 4 _⊢_∶_ _⊢s_∶_

--   mutual

--     data _⊢_∶_ : Ctx → Exp → Typ → Set where
--       vlookup : ∀ {x} →
--                 x ∶ T ∈ Γ →
--                 ------------
--                 Γ ⊢ v x ∶ T
--       ze-I    : Γ ⊢ ze ∶ N
--       su-I    : Γ ⊢ t ∶ N →
--                 -------------
--                 Γ ⊢ su t ∶ N
--       N-E     : Γ ⊢ s ∶ T →
--                 Γ ⊢ r ∶ N ⟶ T ⟶ T →
--                 Γ ⊢ t ∶ N →
--                 ----------------------
--                 Γ ⊢ rec T s r t ∶ T
--       Λ-I     : S ∷ Γ ⊢ t ∶ T →
--                 ------------------
--                 Γ ⊢ Λ t ∶ S ⟶ T
--       Λ-E     : Γ ⊢ r ∶ S ⟶ T →
--                 Γ ⊢ s ∶ S →
--                 ------------------
--                 Γ ⊢ r $ s ∶ T
--       t[σ]    : Δ ⊢ t ∶ T →
--                 Γ ⊢s σ ∶ Δ →
--                 ----------------
--                 Γ ⊢ t [ σ ] ∶ T

--     data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
--       S-↑ : S ∷ Γ ⊢s ↑ ∶ Γ
--       S-I : Γ ⊢s I ∶ Γ
--       S-∘ : Γ ⊢s τ ∶ Γ′ →
--             Γ′ ⊢s σ ∶ Γ″ →
--             ----------------
--             Γ ⊢s σ ∘ τ ∶ Γ″
--       S-, : Γ ⊢s σ ∶ Δ →
--             Γ ⊢ s ∶ S →
--             -------------------
--             Γ ⊢s σ , s ∶ S ∷ Δ

--   infix 4 _⊢_≈_∶_ _⊢s_≈_∶_

--   mutual

--     data _⊢_≈_∶_ : Ctx → Exp → Exp → Typ → Set where
--       v-≈      : ∀ {x} →
--                  x ∶ T ∈ Γ →
--                  --------------------------------------
--                  Γ ⊢ v x                 ≈ v x ∶ T
--       ze-≈     : Γ ⊢ ze                  ≈ ze ∶ N
--       su-cong  : Γ ⊢ t                   ≈ t′ ∶ N →
--                  ---------------------------------------
--                  Γ ⊢ su t                ≈ su t′ ∶ N
--       rec-cong : Γ ⊢ s                   ≈ s′ ∶ T →
--                  Γ ⊢ r                   ≈ r′ ∶ N ⟶ T ⟶ T →
--                  Γ ⊢ t                   ≈ t′ ∶ N →
--                  --------------------------------------------
--                  Γ ⊢ rec T s r t         ≈ rec T s′ r′ t′ ∶ T
--       Λ-cong   : S ∷ Γ ⊢ t               ≈ t′ ∶ T →
--                  ----------------------------------------
--                  Γ ⊢ Λ t                 ≈ Λ t′ ∶ S ⟶ T
--       $-cong   : Γ ⊢ r                   ≈ r′ ∶ S ⟶ T →
--                  Γ ⊢ s                   ≈ s′ ∶ S →
--                  ----------------------------------------
--                  Γ ⊢ r $ s               ≈ r′ $ s′ ∶ T
--       []-cong  : Γ ⊢s σ                  ≈ σ′ ∶ Δ →
--                  Δ ⊢ t                   ≈ t′ ∶ T →
--                  -----------------------------------------
--                  Γ ⊢ t [ σ ]             ≈ t′ [ σ′ ] ∶ T
--       ze-[]    : Γ ⊢s σ ∶ Δ →
--                  ---------------------------------
--                  Γ ⊢ ze [ σ ]            ≈ ze ∶ N
--       su-[]    : Γ ⊢s σ ∶ Δ →
--                  Δ ⊢ t ∶ N →
--                  --------------------------------------------
--                  Γ ⊢ su t [ σ ]          ≈ su (t [ σ ]) ∶ N
--       Λ-[]     : Γ ⊢s σ ∶ Δ →
--                  S ∷ Δ ⊢ t ∶ T →
--                  --------------------------------------------
--                  Γ ⊢ Λ t [ σ ]           ≈ Λ (t [ q σ ]) ∶ S ⟶ T
--       $-[]     : Γ ⊢s σ ∶ Δ →
--                  Δ ⊢ r ∶ S ⟶ T →
--                  Δ ⊢ s ∶ S →
--                  ------------------------------------------------
--                  Γ ⊢ (r $ s) [ σ ]       ≈ r [ σ ] $ s [ σ ] ∶ T
--       rec-[]   : Γ ⊢s σ ∶ Δ →
--                  Δ ⊢ s ∶ T →
--                  Δ ⊢ r ∶ N ⟶ T ⟶ T →
--                  Δ ⊢ t ∶ N →
--                  -----------------------------------------------------------------
--                  Γ ⊢ rec T s r t [ σ ]   ≈ rec T (s [ σ ]) (r [ σ ]) (t [ σ ]) ∶ T
--       rec-β-ze : Γ ⊢ s ∶ T →
--                  Γ ⊢ r ∶ N ⟶ T ⟶ T →
--                  --------------------------------
--                  Γ ⊢ rec T s r ze        ≈ s ∶ T
--       rec-β-su : Γ ⊢ s ∶ T →
--                  Γ ⊢ r ∶ N ⟶ T ⟶ T →
--                  Γ ⊢ t ∶ N →
--                  -----------------------------------------------------
--                  Γ ⊢ rec T s r (su t)    ≈ r $ t $ (rec T s r t) ∶ T
--       Λ-β      : S ∷ Γ ⊢ t ∶ T →
--                  Γ ⊢ s ∶ S →
--                  -----------------------------------------
--                  Γ ⊢ Λ t $ s             ≈ t [ I , s ] ∶ T
--       Λ-η      : Γ ⊢ t ∶ S ⟶ T →
--                  ---------------------------------------------------
--                  Γ ⊢ t                   ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T
--       [I]      : Γ ⊢ t ∶ T →
--                  --------------------
--                  Γ ⊢ t [ I ]             ≈ t ∶ T
--       ↑-lookup : ∀ {x} →
--                  x ∶ T ∈ Γ →
--                  ---------------------------------------
--                  S ∷ Γ ⊢ v x [ ↑ ]       ≈ v (suc x) ∶ T
--       [∘]      : Γ ⊢s τ ∶ Γ′ →
--                  Γ′ ⊢s σ ∶ Γ″ →
--                  Γ″ ⊢ t ∶ T →
--                  -------------------------------------------
--                  Γ ⊢ t [ σ ∘ τ ]         ≈ t [ σ ] [ τ ] ∶ T
--       [,]-v-ze : Γ ⊢s σ ∶ Δ →
--                  Γ ⊢ s ∶ S →
--                  --------------------------------
--                  Γ ⊢ v 0 [ σ , s ]       ≈ s ∶ S
--       [,]-v-su : ∀ {x} →
--                  Γ ⊢s σ ∶ Δ →
--                  Γ ⊢ s ∶ S →
--                  x ∶ T ∈ Δ →
--                  ---------------------------------------
--                  Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T
--       ≈-sym    : Γ ⊢ t                   ≈ t′ ∶ T →
--                  ----------------------------------
--                  Γ ⊢ t′                  ≈ t ∶ T
--       ≈-trans  : Γ ⊢ t                   ≈ t′ ∶ T →
--                  Γ ⊢ t′                  ≈ t″ ∶ T →
--                  -----------------------------------
--                  Γ ⊢ t                   ≈ t″ ∶ T

--     data _⊢s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set where
--       ↑-≈       : S ∷ Γ ⊢s ↑           ≈ ↑             ∶ Γ
--       I-≈       : Γ     ⊢s I           ≈ I             ∶ Γ
--       ∘-cong    : Γ     ⊢s τ           ≈ τ′            ∶ Γ′ →
--                   Γ′    ⊢s σ           ≈ σ′            ∶ Γ″ →
--                   --------------------------------------------
--                   Γ     ⊢s σ ∘ τ       ≈ σ′ ∘ τ′       ∶ Γ″
--       ,-cong    : Γ     ⊢s σ           ≈ σ′            ∶ Δ →
--                   Γ     ⊢ s            ≈ s′            ∶ S →
--                   ---------------------------------------------
--                   Γ     ⊢s σ , s       ≈ σ′ , s′       ∶ S ∷ Δ
--       ↑-∘-,     : Γ     ⊢s σ                           ∶ Δ →
--                   Γ     ⊢ s                            ∶ S →
--                   --------------------------------------------
--                   Γ     ⊢s ↑ ∘ (σ , s) ≈ σ             ∶ Δ
--       I-∘       : Γ     ⊢s σ                           ∶ Δ →
--                   -------------------------------------------
--                   Γ     ⊢s I ∘ σ       ≈ σ             ∶ Δ
--       ∘-I       : Γ     ⊢s σ                           ∶ Δ →
--                   --------------------------------------------
--                   Γ     ⊢s σ ∘ I       ≈ σ             ∶ Δ
--       ∘-assoc   : ∀ {Γ‴} →
--                   Γ′    ⊢s σ                           ∶ Γ →
--                   Γ″    ⊢s σ′                          ∶ Γ′ →
--                   Γ‴    ⊢s σ″                          ∶ Γ″ →
--                   ---------------------------------------------
--                   Γ‴    ⊢s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
--       ,-ext     : Γ     ⊢s σ                           ∶ S ∷ Δ →
--                   -----------------------------------------------
--                   Γ     ⊢s σ           ≈ (↑ ∘ σ) , v 0 [ σ ] ∶ S ∷ Δ
--       S-≈-sym   : Γ     ⊢s σ           ≈ σ′            ∶ Δ →
--                   ---------------------------------------------
--                   Γ     ⊢s σ′          ≈ σ             ∶ Δ
--       S-≈-trans : Γ     ⊢s σ           ≈ σ′            ∶ Δ →
--                   Γ     ⊢s σ′          ≈ σ″            ∶ Δ →
--                   --------------------------------------------
--                   Γ     ⊢s σ           ≈ σ″            ∶ Δ

--   mutual

--     ≈-refl : Γ ⊢ t ∶ T → Γ ⊢ t ≈ t ∶ T
--     ≈-refl (vlookup T∈Γ) = v-≈ T∈Γ
--     ≈-refl ze-I          = ze-≈
--     ≈-refl (su-I t)      = su-cong (≈-refl t)
--     ≈-refl (N-E s r t)   = rec-cong (≈-refl s) (≈-refl r) (≈-refl t)
--     ≈-refl (Λ-I t)       = Λ-cong (≈-refl t)
--     ≈-refl (Λ-E r s)     = $-cong (≈-refl r) (≈-refl s)
--     ≈-refl (t[σ] t σ)    = []-cong (S-≈-refl σ) (≈-refl t)

--     S-≈-refl : Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ ∶ Δ
--     S-≈-refl S-↑ = ↑-≈
--     S-≈-refl S-I = I-≈
--     S-≈-refl (S-∘ σ τ) = ∘-cong (S-≈-refl σ) (S-≈-refl τ)
--     S-≈-refl (S-, σ s) = ,-cong (S-≈-refl σ) (≈-refl s)

-- module Intentional where
--   mutual
--     data Ne : Set where
--       v   : (x : ℕ) → Ne
--       rec : (z s : Nf) → Ne → Ne
--       _$_ : Ne → (n : Nf) → Ne

--     data Nf : Set where
--       ne : (u : Ne) → Nf
--       ze : Nf
--       su : Nf → Nf
--       Λ  : Nf → Nf

--   pattern v′ x = ne (v x)

--   variable
--     u u′ u″ : Ne
--     w w′ w″ : Nf

-- module Extensional where
--   mutual
--     data Ne : Set where
--       v   : (x : ℕ) → Ne
--       rec : (T : Typ) (z s : Nf) → Ne → Ne
--       _$_ : Ne → (n : Nf) → Ne

--     data Nf : Set where
--       ne : (u : Ne) → Nf
--       ze : Nf
--       su : Nf → Nf
--       Λ  : Nf → Nf

--   pattern v′ x = ne (v x)

--   variable
--     u u′ u″ : Ne
--     w w′ w″ : Nf

--   mutual
--     Ne⇒Exp : Ne → Exp
--     Ne⇒Exp (v x)         = v x
--     Ne⇒Exp (rec T z s u) = rec T (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
--     Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n

--     Nf⇒Exp : Nf → Exp
--     Nf⇒Exp (ne u) = Ne⇒Exp u
--     Nf⇒Exp ze     = ze
--     Nf⇒Exp (su w) = su (Nf⇒Exp w)
--     Nf⇒Exp (Λ w)  = Λ (Nf⇒Exp w)
