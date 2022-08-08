{-# OPTIONS --without-K --safe #-}

-- Definition of the untyped domain model
--
-- This module defines variables definitions of the untyped domain model and its operations.
module NonCumulative.Semantics.Domain where

open import Relation.Binary using (Rel; REL)

open import Lib
open import NonCumulative.Statics.Ascribed.Syntax public


mutual
  -- An evaluation environment, which models a context
  --
  -- It maps de Bruijn indices to a domain value.  One should consider Env as a model
  -- of an infinitely long substitution. It is convenient to not have to
  -- consider length restriction in an untyped setting and hence ease the
  -- formalization. In reality, we only rely on some finite prefix, as guaranteed by
  -- the completeness and soundness theorems.
  Env : Set
  Env = ℕ → D

  -- Domain values
  --
  -- D models values in the untyped domain, both representing types and terms.
  --
  -- Morally, D models β normal forms of NonCumulative so it contains no β redices. To make D
  -- a "real" normal form, we must annotate it with another D representing the type
  -- value as done in Df.
  data D : Set where
    N   : D
    Π   : ℕ → D → (T : lTyp) → (ρ : Env) → D -- t has 1 open var
    U   : ℕ → D
    Li  : ℕ → ℕ → D → D         -- type lifting of universe level
    ze  : D
    su  : D → D
    Λ   : (t : Exp) → (ρ : Env) → D
    li  : ℕ → D → D             -- constructor for type lifting
    ↑   : ℕ → D → (c : Dn) → D

  -- Domain neutral values
  data Dn : Set where
    -- Variables in the domain model
    --
    -- Notice that the number x here is not a de Bruijn index but an absolute
    -- representation of names.  That is, this number does not change relative to the
    -- binding structure it currently exists in.
    l     : (x : ℕ) → Dn
    rec   : (T : lTyp) → D → (t : Exp) → (ρ : Env) → Dn → Dn -- T has 1 open var and t has 2 open vars
    _$_   : Dn → (d : Df) → Dn
    unli  : Dn → Dn             -- destructor for type lifting

  -- Domain normal values
  --
  -- It is just D but we annotate it with another value representing its type at some
  -- level i, i.e. ↓ i A b is a value b of type A at level i.
  data Df : Set where
    ↓ : ℕ → D → (a : D) → Df

infixl 10 [_↙_]_$′_
pattern l′ i A x      = ↑ i A (l x)
pattern [_↙_]_$′_ A i x y = ↑ i A (_$_ x y)


variable
  a a′ a″    : D
  b b′ b″    : D
  A A′ A″    : D
  B B′ B″    : D
  f f′ f″    : D
  c c′ c″    : Dn
  C C′ C″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Env

-- Empty evaluation environment
--
-- Its right hand side is arbitrary as a well-typed term can never go out of bound.
emp : Env
emp n = ze

infixl 4.3 _↦_
-- Push a value to the evaluation environment
_↦_ : Env → D → Env
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x

-- Drop the topmost value in the current evaluation envrionment
drop : Env → Env
drop ρ n = ρ (1 + n)

-- Look up the evaluation environment
lookup : Env → ℕ → D
lookup ρ n = ρ n


-- Relational syntax
infix 1 _≈_∈_ _∈′_ _∼_∈_
_≈_∈_ : ∀ {i} {A : Set i} → A → A → Rel A i → Set i
a ≈ b ∈ P = P a b

_∈′_ : ∀ {i} {A : Set i} → A → Rel A i → Set i
a ∈′ P = P a a

_∼_∈_ : ∀ {i} {A B : Set i} → A → B → REL A B i → Set i
a ∼ b ∈ P = P a b
