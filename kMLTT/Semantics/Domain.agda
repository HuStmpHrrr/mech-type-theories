{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.Domain where

open import Lib
open import kMLTT.Statics.Syntax

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
UnMoT : Set
UnMoT = ℕ → ℕ

variable
  a a′ a″    : D
  b b′ b″    : D
  A A′ A″    : D
  B B′ B″    : D
  f f′ f″    : D
  c c′ c″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Envs
  κ κ′ κ″    : UnMoT

emp : Env
emp n = ↑ N (l 0)

empty : Envs
empty n = 1 , emp

infixl 7 _↦_ _↦′_
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

ins : UnMoT → ℕ → UnMoT
ins κ n zero    = n
ins κ n (suc m) = κ m

instance
  UnMoTHasTr : HasTr UnMoT
  UnMoTHasTr = record { _∥_ = λ κ n m → κ (n + m) }

M-L : UnMoT → ℕ → ℕ
M-L κ zero    = 0
M-L κ (suc n) = κ 0 + M-L (κ ∥ 1) n

instance
  MTransHasL : HasL UnMoT
  MTransHasL = record { L = M-L }

toUnMoT : Envs → UnMoT
toUnMoT ρ n = proj₁ (ρ n)

instance
  EnvsHasL : HasL Envs
  EnvsHasL = record { L = λ ρ → M-L (toUnMoT ρ) }

  EnvHasTr : HasTr Envs
  EnvHasTr = record { _∥_ = C-Tr }

infixl 3 _ø_
_ø_ : UnMoT → UnMoT → UnMoT
(κ ø κ′) zero    = L κ′ (κ 0)
(κ ø κ′) (suc n) = (κ ∥ 1 ø κ′ ∥ κ 0) n

mutual
  mtran : D → UnMoT → D
  mtran N κ         = N
  mtran (□ A) κ     = □ (mtran A κ)
  mtran (Π A t ρ) κ = Π (mtran A κ) t (mtran-Envs ρ κ)
  mtran (U i) κ     = U i
  mtran ze κ        = ze
  mtran (su a) κ    = su (mtran a κ)
  mtran (Λ t ρ) κ   = Λ t (mtran-Envs ρ κ)
  mtran (box a) κ   = box (mtran a (ins κ 1))
  mtran (↑ A c) κ   = ↑ (mtran A κ) (mtran-c c κ)

  mtran-c : Dn → UnMoT → Dn
  mtran-c (l x) κ           = l x
  mtran-c (rec T a t ρ c) κ = rec T (mtran a κ) t (mtran-Envs ρ κ) (mtran-c c κ)
  mtran-c (c $ d) κ         = mtran-c c κ $ mtran-d d κ
  mtran-c (unbox n c) κ     = unbox (L κ n) (mtran-c c κ)

  mtran-d : Df → UnMoT → Df
  mtran-d (↓ A a) κ = ↓ (mtran A κ) (mtran a κ)

  mtran-Envs : Envs → UnMoT → Envs
  mtran-Envs ρ κ n = L (κ ∥ L ρ n) (proj₁ (ρ n)) , λ m → mtran (proj₂ (ρ n) m) (κ ∥ L ρ n)

instance
  DMonotone : Monotone D UnMoT
  DMonotone = record { _[_] = mtran }

  DnMonotone : Monotone Dn UnMoT
  DnMonotone = record { _[_] = mtran-c }

  DfMonotone : Monotone Df UnMoT
  DfMonotone = record { _[_] = mtran-d }

  EnvsMonotone : Monotone Envs UnMoT
  EnvsMonotone = record { _[_] = mtran-Envs }

vone : UnMoT
vone _ = 1
