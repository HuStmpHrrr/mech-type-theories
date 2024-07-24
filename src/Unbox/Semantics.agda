{-# OPTIONS --without-K --safe #-}

module Unbox.Semantics where

open import Lib hiding (lookup)
open import Unbox.Statics

open import Relation.Binary using (Rel; REL)

mutual
  Env : Set
  Env = ℕ → D

  Envs : Set
  Envs = ℕ → ℕ × Env

  data D : Set where
    Λ   : (t : Exp) → (ρ : Envs) → D
    box : D → D
    ↑   : (T : Typ) → (c : Dn) → D

  data Dn : Set where
    l     : (x : ℕ) → Dn
    _$_   : Dn → (d : Df) → Dn
    unbox : ℕ → Dn → Dn

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ T x        = ↑ T (l x)
pattern unbox′ T n c  = ↑ T (unbox n c)
pattern [_]_$′_ T x y = ↑ T (_$_ x y)

UMoT : Set
UMoT = ℕ → ℕ

variable
  a a′ a″    : D
  b b′ b″    : D
  f f′ f″    : D
  c c′ c″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Envs
  κ κ′ κ″    : UMoT

emp : Env
emp n = ↑ B (l 0)

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

ins : UMoT → ℕ → UMoT
ins κ n zero = n
ins κ n (suc m) = κ m

instance
  UMoTHasTr : HasTr UMoT
  UMoTHasTr = record { Tr = λ κ n m → κ (n + m) }

M-O : UMoT → ℕ → ℕ
M-O κ zero    = 0
M-O κ (suc n) = κ 0 + M-O (Tr κ 1) n

instance
  UMoTHasO : HasO UMoT
  UMoTHasO = record { O = M-O }

toUMoT : Envs → UMoT
toUMoT ρ n = proj₁ (ρ n)

instance
  EnvsHasO : HasO Envs
  EnvsHasO = record { O = λ ρ → M-O (toUMoT ρ) }

  EnvHasTr : HasTr Envs
  EnvHasTr = record { Tr = C-Tr }

infixl 3 _ø_
_ø_ : UMoT → UMoT → UMoT
(κ ø κ′) zero    = O κ′ (κ 0)
(κ ø κ′) (suc n) = (Tr κ 1 ø Tr κ′ (κ 0)) n

mutual
  mtran : D → UMoT → D
  mtran (Λ t ρ) κ = Λ t (mtran-Cs ρ κ)
  mtran (box a) κ = box (mtran a (ins κ 1))
  mtran (↑ T e) κ = ↑ T (mtran-c e κ)

  mtran-c : Dn → UMoT → Dn
  mtran-c (l x) κ = l x
  mtran-c (c $ d) κ = (mtran-c c κ) $ mtran-d d κ
  mtran-c (unbox n c) κ = unbox (O κ n) (mtran-c c (Tr κ n))

  mtran-d : Df → UMoT → Df
  mtran-d (↓ T a) κ = ↓ T (mtran a κ)

  mtran-Cs : Envs → UMoT → Envs
  mtran-Cs ρ κ n = O (Tr κ (O ρ n)) (proj₁ (ρ n)) , λ m → mtran (proj₂ (ρ n) m) (Tr κ (O ρ n))

instance
  DMonotone : Monotone D UMoT
  DMonotone = record { _[_] = mtran }

  DnMonotone : Monotone Dn UMoT
  DnMonotone = record { _[_] = mtran-c }

  DfMonotone : Monotone Df UMoT
  DfMonotone = record { _[_] = mtran-d }

  EnvsMonotone : Monotone Envs UMoT
  EnvsMonotone = record { _[_] = mtran-Cs }

vone : UMoT
vone _ = 1

infix 4 _∙_↘_ unbox∙_,_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ S T c a → ↑ (S ⟶ T) c ∙ a ↘ ↑ T (c $ ↓ S a)

  data unbox∙_,_↘_ : ℕ → D → D → Set where
    box↘   : ∀ n →
             unbox∙ n , box a ↘ a [ ins vone n ]
    unbox∙ : ∀ n →
             unbox∙ n , ↑ (□ T) c ↘ ↑ T (unbox n c)

  data ⟦_⟧_↘_ : Exp → Envs → D → Set where
    ⟦v⟧     : ∀ n →
              ⟦ v n ⟧ ρ ↘ lookup ρ n
    ⟦Λ⟧     : ∀ t →
              ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧     : ⟦ r ⟧ ρ ↘ f →
              ⟦ s ⟧ ρ ↘ a →
              f ∙ a ↘ b →
              ---------------------
              ⟦ r $ s ⟧ ρ ↘ b
    ⟦box⟧   : ⟦ t ⟧ ext ρ 1 ↘ a →
              ---------------------
              ⟦ box t ⟧ ρ ↘ box a
    ⟦unbox⟧ : ∀ n →
              ⟦ t ⟧ Tr ρ n ↘ a →
              unbox∙ O ρ n , a ↘ b →
              ----------------------
              ⟦ unbox n t ⟧ ρ ↘ b
    ⟦[]⟧    : ⟦ σ ⟧s ρ ↘ ρ′ →
              ⟦ t ⟧ ρ′ ↘ a →
              ---------------------
              ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Substs → Envs → Envs → Set where
    ⟦I⟧ : ⟦ I ⟧s ρ ↘ ρ
    ⟦p⟧ : ⟦ p ⟧s ρ ↘ drop ρ
    ⟦,⟧ : ⟦ σ ⟧s ρ ↘ ρ′ →
          ⟦ t ⟧ ρ ↘ a →
          ---------------------
          ⟦ σ , t ⟧s ρ ↘ ρ′ ↦ a
    ⟦；⟧ : ∀ {n} →
          ⟦ σ ⟧s Tr ρ n ↘ ρ′ →
          -----------------------------
          ⟦ σ ； n ⟧s ρ ↘ ext ρ′ (O ρ n)
    ⟦∘⟧ : ⟦ δ ⟧s ρ ↘ ρ′ →
          ⟦ σ ⟧s ρ′ ↘ ρ″ →
          -----------------
          ⟦ σ ∘ δ ⟧s ρ ↘ ρ″


mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′)             = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ S T e _) ($∙ .S .T .e _) = refl

  unbox-det : ∀ {n} → unbox∙ n , a ↘ b → unbox∙ n , a ↘ b′ → b ≡ b′
  unbox-det (box↘ _) (box↘ _)     = refl
  unbox-det (unbox∙ _) (unbox∙ _) = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n) = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t) = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′ = refl
  ⟦⟧-det (⟦box⟧ ↘a) (⟦box⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b  = refl
  ⟦⟧-det (⟦unbox⟧ n ↘a ↘a′) (⟦unbox⟧ .n ↘b ↘b′)
    rewrite ⟦⟧-det ↘a ↘b
          | unbox-det ↘a′ ↘b′ = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b  = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦I⟧ ⟦I⟧             = refl
  ⟦⟧s-det ⟦p⟧ ⟦p⟧             = refl
  ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b      = refl
  ⟦⟧s-det (⟦；⟧ ↘ρ′) (⟦；⟧ ↘ρ″)
      rewrite ⟦⟧s-det ↘ρ′ ↘ρ″ = refl
  ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
          | ⟦⟧s-det ↘ρ″ ↘ρ⁗   = refl

instance
  ℕsHasTr : HasTr (List⁺ ℕ)
  ℕsHasTr = record { Tr = λ ns n → drop+ n ns }

inc : List⁺ ℕ → List⁺ ℕ
inc (n ∷ ns) = (suc n ∷ ns)

-- Readback functions
infix 4 Rf_-_↘_ Re_-_↘_

mutual

  data Rf_-_↘_ : List⁺ ℕ → Df → Nf → Set where
    RΛ  : ∀ ns →
          f ∙ l′ S (head ns) ↘ a →
          Rf inc ns - ↓ T a ↘ w →
          ---------------------
          Rf ns - ↓ (S ⟶ T) f ↘ Λ w
    R□  : ∀ ns →
          unbox∙ 1 , a ↘ b →
          Rf 0 ∷⁺ ns - ↓ T b ↘ w →
          --------------------------
          Rf ns - ↓ (□ T) a ↘ box w
    Rne : ∀ n →
          Re n - c ↘ u →
          ---------------------
          Rf n - ↓ B (↑ B c) ↘ ne u

  data Re_-_↘_ : List⁺ ℕ → Dn → Ne → Set where
    Rl : ∀ ns x →
         Re ns - l x ↘ v (head ns ∸ x ∸ 1)
    R$ : ∀ ns →
         Re ns - c ↘ u →
         Rf ns - d ↘ w →
         ---------------------
         Re ns - c $ d ↘ u $ w
    Ru : ∀ ns k →
         Re Tr ns k - c ↘ u →
         -------------------------
         Re ns - unbox k c ↘ unbox k u

mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (RΛ _ ↘a ↘w) (RΛ _ ↘a′ ↘w′)
    rewrite ap-det ↘a ↘a′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (R□ _ ↘a ↘w) (R□ _ ↘b ↘w′)
    rewrite unbox-det ↘a ↘b
          | Rf-det ↘w ↘w′       = refl
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - c ↘ u → Re n - c ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x) = refl
  Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)
    rewrite Re-det ↘u ↘u′
          | Rf-det ↘w ↘w′   = refl
  Re-det (Ru _ k ↘u) (Ru _ .k ↘u′) = cong (unbox k) (Re-det ↘u ↘u′)

record Nbe ns ρ t T w : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↓⟦t⟧ : Rf ns - ↓ T ⟦t⟧ ↘ w

InitialEnv : Ctx → Env
InitialEnv []      i       = ↑ B (l 0)
InitialEnv (T ∷ Γ) zero    = l′ T (L.length Γ)
InitialEnv (T ∷ Γ) (suc i) = InitialEnv Γ i

InitialEnvs : List Ctx → Envs
InitialEnvs [] n             = 1 , emp
InitialEnvs (Γ ∷ Γs) zero    = 1 , InitialEnv Γ
InitialEnvs (Γ ∷ Γs) (suc n) = InitialEnvs Γs n

infix 1 _≈_∈_ _∼_∈_
_≈_∈_ : ∀ {i} {A : Set i} → A → A → Rel A i → Set i
a ≈ b ∈ P = P a b

_∼_∈_ : ∀ {i} {A B : Set i} → A → B → REL A B i → Set i
a ∼ b ∈ P = P a b
