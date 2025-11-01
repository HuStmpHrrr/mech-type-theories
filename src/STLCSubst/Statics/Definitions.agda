{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Definitions where

open import Level renaming (suc to succ)
open import Relation.Nullary.Decidable

open import Lib


infixr 10 _⟶_

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

⇑ : Wk
⇑ = wk 0

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


mutual
  data Ne : Set where
    v   : (x : ℕ) → Ne
    rec : (T : Typ) (z s : Nf) → Ne → Ne
    _$_ : Ne → (n : Nf) → Ne

  data Nf : Set where
    ne : (u : Ne) → Nf
    ze : Nf
    su : Nf → Nf
    Λ  : Nf → Nf

pattern v′ x = ne (v x)

variable
  u u′ u″ : Ne
  w w′ w″ : Nf

mutual
  Ne⇒Exp : Ne → Exp
  Ne⇒Exp (v x)         = v x
  Ne⇒Exp (rec T z s u) = rec T (Nf⇒Exp z) (Nf⇒Exp s) (Ne⇒Exp u)
  Ne⇒Exp (u $ n)       = Ne⇒Exp u $ Nf⇒Exp n

  Nf⇒Exp : Nf → Exp
  Nf⇒Exp (ne u) = Ne⇒Exp u
  Nf⇒Exp ze     = ze
  Nf⇒Exp (su w) = su (Nf⇒Exp w)
  Nf⇒Exp (Λ w)  = Λ (Nf⇒Exp w)
