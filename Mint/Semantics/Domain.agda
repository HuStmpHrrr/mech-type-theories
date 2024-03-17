{-# OPTIONS --without-K --safe #-}

-- Definition of the untyped domain model
--
-- This module defines variables definitions of the untyped domain model and its operations.
module Mint.Semantics.Domain where

open import Relation.Binary using (Rel; REL)

open import Lib hiding (lookup)
open import Mint.Statics.Syntax public


mutual
  -- A local evaluation environment, which models an individual context
  --
  -- It maps de Bruijn indices to a domain value.  One should consider Env as a model
  -- of an infinitely long local substitution. It is convenient to not have to
  -- consider length restriction in an untyped setting and hence ease the
  -- formalization. In reality, we only rely on some finite prefix, as guaranteed by
  -- the completeness and soundness theorems.
  Env : Set
  Env = ℕ → D

  -- A (global) evaluation environment, which models a context stack
  --
  -- It maps the context index to an associated local environment and the modal
  -- offset to the next local environment.
  --
  -- The topmost(current) environment is at index 0.
  --
  -- Similar to Env, an Envs models an infinitely long unified substitution. In
  -- addition to Env which keep tracks of the mapping from de Bruijn indices to values
  -- in each levels, we also keep track of modal offsets, which in unified
  -- substitutions keeps track of how many contexts to add to the codomain stack
  -- before going into the next world in Kripke semantics' sense.
  Envs : Set
  Envs = ℕ → ℕ × Env

  -- Domain values
  --
  -- D models values in the untyped domain, both representing types and terms.
  --
  -- Morally, D models β normal forms of Mint so it contains no β redices. To make D
  -- a "real" normal form, we must annotate it with another D representing the type
  -- value as done in Df.
  data D : Set where
    N   : D
    □   : D → D
    Π   : D → (t : Exp) → (ρ : Envs) → D -- t has 1 open var
    U   : ℕ → D
    ze  : D
    su  : D → D
    Λ   : (t : Exp) → (ρ : Envs) → D
    box : D → D
    ↑   : D → (c : Dn) → D

  -- Domain neutral values
  data Dn : Set where
    -- Variables in the domain model
    --
    -- Notice that the number x here is not a de Bruijn index but an absolute
    -- representation of names.  That is, this number does not change relative to the
    -- binding structure it currently exists in.
    l     : (x : ℕ) → Dn
    rec   : (T : Typ) → D → (t : Exp) → (ρ : Envs) → Dn → Dn -- T has 1 open var and t has 2 open vars
    _$_   : Dn → (d : Df) → Dn
    unbox : ℕ → Dn → Dn

  -- Domain normal values
  --
  -- It is just D but we annotate it with another value representing its type, i.e. ↓
  -- A b is a value b of type A.
  data Df : Set where
    ↓ : D → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ A x        = ↑ A (l x)
pattern unbox′ A n c  = ↑ A (unbox n c)
pattern [_]_$′_ A x y = ↑ A (_$_ x y)

-- Untyped modal transformations
--
-- A stream of natural numbers models an infinitely long modal transformation. All
-- these numbers are modal offsets.
UMoT : Set
UMoT = ℕ → ℕ

variable
  a a′ a″    : D
  b b′ b″    : D
  A A′ A″    : D
  B B′ B″    : D
  f f′ f″    : D
  c c′ c″    : Dn
  C C′ C″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Envs
  κ κ′ κ″    : UMoT

-- Empty local evaluation environment
--
-- Its right hand side is arbitrary as a well-typed term can never go out of bound.
emp : Env
emp n = ↑ N (l 0)

-- Empty global evaluation environment
--
-- An empty global evaluation environment can be considered as a substitution where no
-- variable maps to a sensible value.
empty : Envs
empty n = 1 , emp

infixl 4.3 _↦_ _↦′_
_↦′_ : Env → D → Env
(ρ ↦′ d) zero    = d
(ρ ↦′ d) (suc x) = ρ x

-- Push a value to the current local evaluation environment
_↦_ : Envs → D → Envs
(ρ ↦ d) 0       = proj₁ (ρ 0) , proj₂ (ρ 0) ↦′ d
(ρ ↦ d) (suc n) = ρ (suc n)

-- Grow the evaluation environment with a specified modal offset
ext : Envs → ℕ → Envs
ext ρ n zero    = n , emp
ext ρ n (suc m) = ρ m

-- Truncation operation of evaluation environments
C-Tr : Envs → ℕ → Envs
C-Tr ρ n m = ρ (n + m)

-- Drop the topmost value in the current local evaluation envrionment
drop : Envs → Envs
drop ρ zero    = proj₁ (ρ 0) , λ m → proj₂ (ρ 0) (1 + m)
drop ρ (suc n) = ρ (suc n)

-- Look up the current local evaluation environment
lookup : Envs → ℕ → D
lookup ρ n = proj₂ (ρ 0) n

-- Grow a UMoT by a modal offset
ins : UMoT → ℕ → UMoT
ins κ n zero    = n
ins κ n (suc m) = κ m

-- Truncation of UMoTs
instance
  UMoTHasTr : HasTr UMoT
  UMoTHasTr = record { _∥_ = λ κ n m → κ (n + m) }

-- Truncation offsets of UMoTs
M-O : UMoT → ℕ → ℕ
M-O κ zero    = 0
M-O κ (suc n) = κ 0 + M-O (κ ∥ 1) n

instance
  MTransHasO : HasO UMoT
  MTransHasO = record { O = M-O }

toUMoT : Envs → UMoT
toUMoT ρ n = proj₁ (ρ n)

instance
  -- Truncation offsets of evaluation environments are essentially the same
  EnvsHasO : HasO Envs
  EnvsHasO = record { O = λ ρ → M-O (toUMoT ρ) }

  EnvHasTr : HasTr Envs
  EnvHasTr = record { _∥_ = C-Tr }

-- Composition of UMoTs
infixl 3 _ø_
_ø_ : UMoT → UMoT → UMoT
(κ ø κ′) zero    = O κ′ (κ 0)
(κ ø κ′) (suc n) = (κ ∥ 1 ø κ′ ∥ κ 0) n

-- Monotonicity of the domain model / Application of UMoTs to the domain model
mutual
  mtran : D → UMoT → D
  mtran N κ         = N
  mtran (□ A) κ     = □ (mtran A (ins κ 1))
  mtran (Π A t ρ) κ = Π (mtran A κ) t (mtran-Envs ρ κ)
  mtran (U i) κ     = U i
  mtran ze κ        = ze
  mtran (su a) κ    = su (mtran a κ)
  mtran (Λ t ρ) κ   = Λ t (mtran-Envs ρ κ)
  mtran (box a) κ   = box (mtran a (ins κ 1))
  mtran (↑ A c) κ   = ↑ (mtran A κ) (mtran-c c κ)

  mtran-c : Dn → UMoT → Dn
  mtran-c (l x) κ           = l x
  mtran-c (rec T a t ρ c) κ = rec T (mtran a κ) t (mtran-Envs ρ κ) (mtran-c c κ)
  mtran-c (c $ d) κ         = mtran-c c κ $ mtran-d d κ
  mtran-c (unbox n c) κ     = unbox (O κ n) (mtran-c c (κ ∥ n))

  mtran-d : Df → UMoT → Df
  mtran-d (↓ A a) κ = ↓ (mtran A κ) (mtran a κ)

  mtran-Envs : Envs → UMoT → Envs
  mtran-Envs ρ κ n = O (κ ∥ O ρ n) (proj₁ (ρ n)) , λ m → mtran (proj₂ (ρ n) m) (κ ∥ O ρ n)

instance
  DMonotone : Monotone D UMoT
  DMonotone = record { _[_] = mtran }

  DnMonotone : Monotone Dn UMoT
  DnMonotone = record { _[_] = mtran-c }

  DfMonotone : Monotone Df UMoT
  DfMonotone = record { _[_] = mtran-d }

  EnvsMonotone : Monotone Envs UMoT
  EnvsMonotone = record { _[_] = mtran-Envs }

-- Identity UMoT
vone : UMoT
vone _ = 1

-- Relational syntax
infix 1 _≈_∈_ _∈′_ _∼_∈_
_≈_∈_ : ∀ {i} {A : Set i} → A → A → Rel A i → Set i
a ≈ b ∈ P = P a b

_∈′_ : ∀ {i} {A : Set i} → A → Rel A i → Set i
a ∈′ P = P a a

_∼_∈_ : ∀ {i} {A B : Set i} → A → B → REL A B i → Set i
a ∼ b ∈ P = P a b
