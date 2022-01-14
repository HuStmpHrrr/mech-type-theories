{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.Domain where

open import Relation.Binary using (Rel; REL)

open import Lib
open import kMLTT.Statics.Syntax public


mutual
  Env : Set
  Env = ℕ → D

  Envs : Set
  Envs = ℕ → ℕ × Env

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

  data Dn : Set where
    l     : (x : ℕ) → Dn
    rec   : (T : Typ) → D → (t : Exp) → (ρ : Envs) → Dn → Dn -- T has 1 open var and t has 2 open vars
    _$_   : Dn → (d : Df) → Dn
    unbox : ℕ → Dn → Dn

  data Df : Set where
    ↓ : D → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ A x        = ↑ A (l x)
pattern unbox′ A n c  = ↑ A (unbox n c)
pattern [_]_$′_ A x y = ↑ A (_$_ x y)

-- untyped modal transformations
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

emp : Env
emp n = ↑ N (l 0)

empty : Envs
empty n = 1 , emp

infixl 4.3 _↦_ _↦′_
_↦′_ : Env → D → Env
(ρ ↦′ d) zero    = d
(ρ ↦′ d) (suc x) = ρ x

_↦_ : Envs → D → Envs
(ρ ↦ d) 0       = proj₁ (ρ 0) , proj₂ (ρ 0) ↦′ d
(ρ ↦ d) (suc n) = ρ (suc n)

ext : Envs → ℕ → Envs
ext ρ n zero    = n , emp
ext ρ n (suc m) = ρ m

C-Tr : Envs → ℕ → Envs
C-Tr ρ n m = ρ (n + m)

drop : Envs → Envs
drop ρ zero    = proj₁ (ρ 0) , λ m → proj₂ (ρ 0) (1 + m)
drop ρ (suc n) = ρ (suc n)

lookup : Envs → ℕ → D
lookup ρ n = proj₂ (ρ 0) n

ins : UMoT → ℕ → UMoT
ins κ n zero    = n
ins κ n (suc m) = κ m

instance
  UMoTHasTr : HasTr UMoT
  UMoTHasTr = record { _∥_ = λ κ n m → κ (n + m) }

M-O : UMoT → ℕ → ℕ
M-O κ zero    = 0
M-O κ (suc n) = κ 0 + M-O (κ ∥ 1) n

instance
  MTransHasO : HasO UMoT
  MTransHasO = record { O = M-O }

toUMoT : Envs → UMoT
toUMoT ρ n = proj₁ (ρ n)

instance
  EnvsHasO : HasO Envs
  EnvsHasO = record { O = λ ρ → M-O (toUMoT ρ) }

  EnvHasTr : HasTr Envs
  EnvHasTr = record { _∥_ = C-Tr }

infixl 3 _ø_
_ø_ : UMoT → UMoT → UMoT
(κ ø κ′) zero    = O κ′ (κ 0)
(κ ø κ′) (suc n) = (κ ∥ 1 ø κ′ ∥ κ 0) n

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

vone : UMoT
vone _ = 1

infix 1 _≈_∈_ _∈′_ _∼_∈_
_≈_∈_ : ∀ {i} {A : Set i} → A → A → Rel A i → Set i
a ≈ b ∈ P = P a b

_∈′_ : ∀ {i} {A : Set i} → A → Rel A i → Set i
a ∈′ P = P a a

_∼_∈_ : ∀ {i} {A B : Set i} → A → B → REL A B i → Set i
a ∼ b ∈ P = P a b
