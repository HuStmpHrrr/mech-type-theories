{-# OPTIONS --without-K --safe #-}

module Unbox.Presheaf where

open import Lib
open import LibNonEmpty
open import Unbox.Typ

open import Level using (0ℓ)
open import Function using (flip)
open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as Nₚ
open import Data.Nat.Induction
import Induction.WellFounded as Wf

record HasO (A : Ctxs → Ctxs → Set) : Set where
  field
    O : ∀ Γs → A Ψ (Γs ++⁺ Ψ′) → List Ctx

open HasO {{...}} public

record HasR (A : Ctxs → Ctxs → Set) : Set where
  field
    R : ∀ Γs → A Ψ (Γs ++⁺ Ψ′) → Ctxs

open HasR {{...}} public

record HasTr (A : Ctxs → Ctxs → Set) {{hasR : HasR A}} : Set where
  field
    Tr : ∀ Γs (σ : A Ψ (Γs ++⁺ Ψ′)) → A (R Γs σ) Ψ′

open HasTr {{...}} public


infixl 10 _$_
data Exp : Typ → Ctxs → Set where
  v     : (T∈Γ : T ∈ Γ) →
          ---------------
          Exp T (Γ ∷ Γs)
  Λ     : Exp T ((S ∷ Γ) ∷ Γs) →
          ----------------------
          Exp (S ⟶ T) (Γ ∷ Γs)
  _$_   : Exp (S ⟶ T) Ψ →
          Exp S Ψ →
          ---------------
          Exp T Ψ
  box   : Exp T ([] ∷ toList Ψ) →
          -----------------------
          Exp (□ T) Ψ
  unbox : ∀ Γs →
          Exp (□ T) Ψ →
          Ψ′ ≡ Γs ++⁺ Ψ →
          ----------------
          Exp T Ψ′

mutual
  data Ne : Typ → Ctxs → Set where
    v     : (T∈Γ : T ∈ Γ) →
            ---------------
            Ne T (Γ ∷ Γs)
    _$_   : Ne (S ⟶ T) Ψ →
            Nf S Ψ →
            ---------------
            Ne T Ψ
    unbox : ∀ Γs →
            Ne (□ T) Ψ →
            Ψ′ ≡ Γs ++⁺ Ψ →
            ----------------
            Ne T Ψ′

  data Nf : Typ → Ctxs → Set where
    ne  : Ne T Ψ → Nf T Ψ
    Λ   : Nf T ((S ∷ Γ) ∷ Γs) →
          ----------------------
          Nf (S ⟶ T) (Γ ∷ Γs)
    box : Nf T ([] ∷ toList Ψ) →
          -----------------------
          Nf (□ T) Ψ

pattern
  unbox′ Γs t = unbox Γs t refl

variable
  t t′ t″ : Exp T Ψ
  r r′ r″ : Exp T Ψ
  s s′ s″ : Exp T Ψ
  u u′ u″ : Ne T Ψ
  w w′ w″ : Nf T Ψ

infix 3 _⇒_
data _⇒_ : Ctxs → Ctxs → Set where
  ε  : [] ∷ [] ⇒ [] ∷ []
  p  : Γ ∷ Γs ⇒ Ψ →
       ----------------
       (T ∷ Γ) ∷ Γs ⇒ Ψ
  q  : Γ ∷ Γs ⇒ Δ ∷ Δs →
       ---------------------------
       (T ∷ Γ) ∷ Γs ⇒ (T ∷ Δ) ∷ Δs
  ex : ∀ Γs →
       Ψ ⇒ Ψ′ →
       Ψ″ ≡ Γs ++⁺ Ψ →
       -------------------------
       Ψ″ ⇒ [] ∷ toList Ψ′

pattern
  ex′ Γs σ = ex Γs σ refl

variable
  σ σ′ σ″ : Ψ ⇒ Ψ′
  δ δ′ δ″ : Ψ ⇒ Ψ′

record Monotone {I : Set} (A : I → Ctxs → Set) (R : Ctxs → Ctxs → Set) : Set where
  infixl 8 _[_]
  field
    _[_] : ∀ {i} → A i Ψ′ → R Ψ Ψ′ → A i Ψ

open Monotone {{...}} public

id′ : ∀ Γs Γ → Γ ∷ Γs ⇒ Γ ∷ Γs
id′ [] []       = ε
id′ (Γ ∷ Γs) [] = ex′ ([] ∷ []) (id′ Γs Γ)
id′ Γs (T ∷ Γ)  = q (id′ Γs Γ)

id : ∀ Ψ → Ψ ⇒ Ψ
id Ψ = id′ (tail Ψ) (head Ψ)


M-O : ∀ Γs → Ψ ⇒ Γs ++⁺ Ψ′ → List Ctx
M-O [] σ                 = []
M-O (Γ ∷ Γs) (p {T = T} σ)
  with M-O (Γ ∷ Γs) σ
... | []                 = []
... | Δ ∷ Δs             = (T ∷ Δ) ∷ Δs
M-O ((_ ∷ Γ) ∷ Γs) (q {T = T} σ)
  with M-O (Γ ∷ Γs) σ
... | []                 = []
... | Δ ∷ Δs             = (T ∷ Δ) ∷ Δs
M-O (Γ ∷ Γs) (ex Δs σ eq) = Δs ++ M-O Γs σ

instance
  MHasO : HasO _⇒_
  MHasO = record { O = M-O }

M-R : ∀ Γs → Ψ ⇒ Γs ++⁺ Ψ′ → Ctxs
M-R {Ψ} [] σ                 = Ψ
M-R {Ψ} (Γ ∷ Γs) (p σ)
  with O (Γ ∷ Γs) σ
... | []                     = Ψ
... | _ ∷ _                  = M-R (Γ ∷ Γs) σ
M-R {Ψ} ((_ ∷ Γ) ∷ Γs) (q σ)
  with O (Γ ∷ Γs) σ
... | []                     = Ψ
... | _ ∷ _                  = M-R (Γ ∷ Γs) σ
M-R (.[] ∷ Γs) (ex Δs σ eq) = M-R Γs σ

instance
  MHasR : HasR _⇒_
  MHasR = record { R = M-R }

M-O+R : ∀ Γs (σ : Ψ ⇒ Γs ++⁺ Ψ′) → Ψ ≡ O Γs σ ++⁺ R Γs σ
M-O+R {Ψ} [] σ                 = refl
M-O+R {(_ ∷ Δ) ∷ Δs} (Γ ∷ Γs) (p σ)
  with O (Γ ∷ Γs) σ | M-O+R (Γ ∷ Γs) σ
... | []       | eq            = refl
... | Γ′ ∷ Γs′ | eq
    with ∷-injective (cong toList eq)
...    | eq′ , eq″ rewrite eq′ = cong (_ ∷_) eq″
M-O+R {(_ ∷ Δ) ∷ Δs} ((_ ∷ Γ) ∷ Γs) (q σ)
  with O (Γ ∷ Γs) σ | M-O+R (Γ ∷ Γs) σ
... | [] | eq                  = refl
... | Γ′ ∷ Γs′ | eq
    with ∷-injective (cong toList eq)
...    | eq′ , eq″ rewrite eq′ = cong (_ ∷_) eq″
M-O+R (.[] ∷ Γs) (ex Δs σ eq)  = trans eq
                                 (trans (cong (Δs ++⁺_) (M-O+R Γs σ))
                                        (sym (++-++⁺ Δs)))

M-Tr : ∀ Γs (σ : Ψ ⇒ Γs ++⁺ Ψ′) → R Γs σ ⇒ Ψ′
M-Tr [] σ                    = σ
M-Tr (Γ ∷ Γs) δ@(p σ)
  with O (Γ ∷ Γs) σ | M-O+R (Γ ∷ Γs) σ
... | []     | eq           = p (subst (_⇒ _) (sym eq) (M-Tr (Γ ∷ Γs) σ))
... | Δ ∷ Δs | _            = M-Tr (Γ ∷ Γs) σ
M-Tr ((_ ∷ Γ) ∷ Γs) (q σ)
  with O (Γ ∷ Γs) σ | M-O+R (Γ ∷ Γs) σ
... | []     | eq           = p (subst (_⇒ _) (sym eq) (M-Tr (Γ ∷ Γs) σ))
... | Δ ∷ Δs | _            = M-Tr (Γ ∷ Γs) σ
M-Tr (.[] ∷ Γs) (ex Δs σ eq) = M-Tr Γs σ

instance
  MHasTr : HasTr _⇒_
  MHasTr = record { Tr = M-Tr }

infixl 3 _∘_
_∘_ : Ψ′ ⇒ Ψ″ → Ψ ⇒ Ψ′ → Ψ ⇒ Ψ″
ε        ∘ ε   = ε
p σ      ∘ q δ = p (σ ∘ δ)
q σ      ∘ q δ = q (σ ∘ δ)
ex′ Γs σ ∘ δ   = ex (O Γs δ) (σ ∘ Tr Γs δ) (M-O+R Γs δ)
σ        ∘ p δ = p (σ ∘ δ)

-- interpreting a type to a presheaf
⟦_⟧T : Typ → Ctxs → Set
⟦ B ⟧T       = Ne B
⟦ S ⟶ T ⟧T Ψ = ∀ {Ψ′} → Ψ′ ⇒ Ψ → ⟦ S ⟧T Ψ′ → ⟦ T ⟧T Ψ′
⟦ □ T ⟧T Ψ   = ⟦ T ⟧T ([] ∷ toList Ψ)

-- interpreting a context to a presheaf
⟦_⟧Γ : Ctx → Ctxs → Set
⟦ [] ⟧Γ _    = ⊤
⟦ T ∷ Γ ⟧Γ Ψ = ⟦ T ⟧T Ψ × ⟦ Γ ⟧Γ Ψ

-- interpreting a context stack to a presheaf
⟦_⟧Γs : List Ctx → Ctxs → Set
⟦ [] ⟧Γs _     = ⊤
⟦ Γ ∷ Γs ⟧Γs Ψ = ∃₂ λ Δs Ψ′ → Ψ ≡ Δs ++⁺ Ψ′ × ⟦ Γ ⟧Γ Ψ′ × ⟦ Γs ⟧Γs Ψ′

-- interpreting a context stack to a presheaf
⟦_⟧Es : Ctxs → Ctxs → Set
⟦ Γ ∷ Γs ⟧Es Ψ = ⟦ Γ ⟧Γ Ψ × ⟦ Γs ⟧Γs Ψ

lookup-mon : T ∈ Γ → Δ ∷ Δs ⇒ Γ ∷ Γs → T ∈ Δ
lookup-mon T∈Γ (p σ)      = there (lookup-mon T∈Γ σ)
lookup-mon 0d (q σ)       = 0d
lookup-mon (1+ T∈Γ) (q σ) = there (lookup-mon T∈Γ σ)

mutual
  Nf-mon : Nf T Ψ → Ψ′ ⇒ Ψ → Nf T Ψ′
  Nf-mon (ne u) σ = ne (Ne-mon u σ)
  Nf-mon (Λ w) σ = Λ (Nf-mon w (q σ))
  Nf-mon (box w) σ = box (Nf-mon w (ex ([] ∷ []) σ refl))

  Ne-mon : Ne T Ψ → Ψ′ ⇒ Ψ → Ne T Ψ′
  Ne-mon (v T∈Γ) σ = v (lookup-mon T∈Γ σ)
  Ne-mon (u $ w) σ = Ne-mon u σ $ (Nf-mon w σ)
  Ne-mon (unbox′ Γs u) σ = unbox (O Γs σ) (Ne-mon u (Tr Γs σ)) (M-O+R Γs σ)

Exp-mon : Exp T Ψ → Ψ′ ⇒ Ψ → Exp T Ψ′
Exp-mon (v T∈Γ) σ       = v (lookup-mon T∈Γ σ)
Exp-mon (Λ t) σ         = Λ (Exp-mon t (q σ))
Exp-mon (t $ s) σ       = Exp-mon t σ $ Exp-mon s σ
Exp-mon (box t) σ       = box (Exp-mon t (ex ([] ∷ []) σ refl))
Exp-mon (unbox′ Γs t) σ = unbox (O Γs σ) (Exp-mon t (Tr Γs σ)) (M-O+R Γs σ)

instance
  NfMonotone : Monotone Nf _⇒_
  NfMonotone = record { _[_] = Nf-mon }

  NeMonotone : Monotone Ne _⇒_
  NeMonotone = record { _[_] = Ne-mon }

  ExpMonotone : Monotone Exp _⇒_
  ExpMonotone = record { _[_] = Exp-mon }

T-mon : ∀ T → ⟦ T ⟧T Ψ → Ψ′ ⇒ Ψ → ⟦ T ⟧T Ψ′
T-mon B                   = _[_]
T-mon (S ⟶ T) ⟦t⟧ σ δ ⟦s⟧ = ⟦t⟧ (σ ∘ δ) ⟦s⟧
T-mon (□ T) ⟦t⟧ σ         = T-mon T ⟦t⟧ (ex′ ([] ∷ []) σ)

instance
  TMonotone : Monotone ⟦_⟧T _⇒_
  TMonotone = record { _[_] = λ {_} {_} {T} → T-mon T }

Γ-mon : ∀ Γ → ⟦ Γ ⟧Γ Ψ → Ψ′ ⇒ Ψ → ⟦ Γ ⟧Γ Ψ′
Γ-mon []      ρ σ         = _
Γ-mon (T ∷ Γ) (⟦t⟧ , ρ) σ = T-mon T ⟦t⟧ σ , Γ-mon Γ ρ σ

instance
  ΓMonotone : Monotone ⟦_⟧Γ _⇒_
  ΓMonotone = record { _[_] = Γ-mon _ }

Γs-mon : ∀ Γs → ⟦ Γs ⟧Γs Ψ → Ψ′ ⇒ Ψ → ⟦ Γs ⟧Γs Ψ′
Γs-mon [] _ σ                               = _
Γs-mon (Γ ∷ Γs) (Δs , Ψ″ , refl , ρ , ρs) σ = O Δs σ , R Δs σ , M-O+R Δs σ , Γ-mon Γ ρ (Tr Δs σ) , Γs-mon Γs ρs (Tr Δs σ)

Es-mon : ⟦ Ψ ⟧Es Ψ′ → Ψ″ ⇒ Ψ′ → ⟦ Ψ ⟧Es Ψ″
Es-mon (ρ , e) σ = Γ-mon _ ρ σ , Γs-mon _ e σ

instance
  ΓsMonotone : Monotone ⟦_⟧Γs _⇒_
  ΓsMonotone = record { _[_] = Γs-mon _ }

  CtxsMonotone : Monotone ⟦_⟧Es _⇒_
  CtxsMonotone = record { _[_] = Es-mon }


S-O : ∀ Γs → ⟦ Γs ++⁺ Ψ′ ⟧Es Ψ → List Ctx
S-O [] ρs                          = []
S-O (_ ∷ Γs) (_ , Δs , _ , _ , ρs) = Δs ++ S-O Γs ρs

instance
  IntpHasO : HasO (flip ⟦_⟧Es)
  IntpHasO = record { O = S-O }

S-R : ∀ Γs → ⟦ Γs ++⁺ Ψ′ ⟧Es Ψ → Ctxs
S-R {_} {Ψ} [] ρs                 = Ψ
S-R (_ ∷ Γs) (_ , _ , _ , _ , ρs) = S-R Γs ρs

instance
  IntpHasR : HasR (flip ⟦_⟧Es)
  IntpHasR = record { R = S-R }

S-O+R : ∀ Γs (ρs : ⟦ Γs ++⁺ Ψ′ ⟧Es Ψ) → Ψ ≡ O Γs ρs ++⁺ R Γs ρs
S-O+R [] ρs                              = refl
S-O+R (_ ∷ Γs) (_ , Δs , Ψ″ , refl , ρs) = trans (cong (Δs ++⁺_) (S-O+R Γs ρs))
                                                 (sym (++-++⁺ Δs))

S-Tr : ∀ Γs (ρs : ⟦ Γs ++⁺ Ψ′ ⟧Es Ψ) → ⟦ Ψ′ ⟧Es (R Γs ρs)
S-Tr [] ρs                         = ρs
S-Tr (Γ ∷ Γs) (_ , _ , _ , _ , ρs) = S-Tr Γs ρs

instance
  IntpHasTr : HasTr (flip ⟦_⟧Es)
  IntpHasTr = record { Tr = S-Tr }


sem-lookup : T ∈ Γ → ⟦ Γ ⟧Γ Ψ → ⟦ T ⟧T Ψ
sem-lookup 0d (⟦T⟧ , _)     = ⟦T⟧
sem-lookup (1+ T∈Γ) (_ , ρ) = sem-lookup T∈Γ ρ

⟦_⟧ : Exp T Ψ → ∀ {Ψ′} → ⟦ Ψ ⟧Es Ψ′ → ⟦ T ⟧T Ψ′
⟦ v T∈Γ ⟧ (ρ , _)          = sem-lookup T∈Γ ρ
⟦ Λ t ⟧ (ρ , e) σ ⟦s⟧      = let (ρ′ , e′) = Es-mon (ρ , e) σ in ⟦ t ⟧ ((⟦s⟧ , ρ′) , e′)
⟦ t $ s ⟧ ρs               = ⟦ t ⟧ ρs (id _) (⟦ s ⟧ ρs)
⟦ box t ⟧ ρs               = ⟦ t ⟧ (_ , ([] ∷ [] , _ , refl , ρs))
⟦ unbox {T} Γs t refl ⟧ ρs = T-mon T (⟦ t ⟧ (Tr Γs ρs)) (ex (O Γs ρs) (id _) (S-O+R Γs ρs))

mutual
  ↓ : ∀ T → ⟦ T ⟧T Ψ → Nf T Ψ
  ↓ B           = ne
  ↓ (S ⟶ T) ⟦t⟧ = Λ (↓ T (⟦t⟧ (p (id _)) (↑ S (v 0d))))
  ↓ (□ T) ⟦t⟧   = box (↓ T ⟦t⟧)

  ↑ : ∀ T → Ne T Ψ → ⟦ T ⟧T Ψ
  ↑ B ⟦t⟧             = ⟦t⟧
  ↑ (S ⟶ T) ⟦t⟧ σ ⟦s⟧ = ↑ T (Ne-mon ⟦t⟧ σ $ ↓ S ⟦s⟧)
  ↑ (□ T) ⟦t⟧         = ↑ T (unbox′ ([] ∷ []) ⟦t⟧)

↑Γ : ∀ Γ → ⟦ Γ ⟧Γ (Γ ∷ Γs)
↑Γ []      = _
↑Γ (T ∷ Γ) = ↑ T (v 0d) , Γ-mon _ (↑Γ Γ) (p (id _))

↑Ψ : ∀ Ψ → ⟦ Ψ ⟧Es Ψ
↑Ψ Ψ = Ind.wfRec (λ Ψ → ⟦ Ψ ⟧Es Ψ) helper Ψ
  where module Wflen = Wf.InverseImage {_<_ = Lib._<_} (length {A = Ctx})
        module Ind   = Wf.All (Wflen.wellFounded <-wellFounded) 0ℓ
        helper : ∀ Ψ → (∀ Ψ′ → len Ψ′ < len Ψ → ⟦ Ψ′ ⟧Es Ψ′) → ⟦ Ψ ⟧Es Ψ
        helper (Γ ∷ []) rec      = ↑Γ Γ , _
        helper (Γ ∷ Γ′ ∷ Γs) rec = ↑Γ Γ , Γ ∷ [] , Γ′ ∷ Γs , refl , rec (Γ′ ∷ Γs) Nₚ.≤-refl

nbe : Exp T Ψ → Nf T Ψ
nbe {T} {Ψ} t = ↓ T (⟦ t ⟧ (↑Ψ Ψ))
