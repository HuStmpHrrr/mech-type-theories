{-# OPTIONS --without-K --safe #-}

module CLayered.Statics where

open import Level hiding (zero; suc)

open import Lib public
open import Weakening public
open import CLayered.Typ public

import Data.Nat.Properties as ℕₚ


-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[[_]]
  field
    _[[_]] : A → B → A

open Monotone {{...}} public


mutual
  data Exp : Set where
    v      : ℕ → Exp
    gv     : ℕ → LSubst → Exp
    ze     : Exp
    su     : Exp → Exp
    Λ      : Exp → Exp
    _$_    : Exp → Exp → Exp
    box    : Exp → Exp
    letbox : Exp → Exp → Exp
    case   : Exp → Branches → Exp
    _[_]   : Exp → LSubst → Exp

  data LSubst : Set where
    ↑      : LSubst
    I      : LSubst
    _∘_    : LSubst → LSubst → LSubst
    _,_    : LSubst → Exp → LSubst

  Branch = ℕ × Exp

  Branches = List Branch


GSubst = List Exp

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : GSubst
  τ τ′ τ″ : GSubst
  δ δ′ δ″ : LSubst


Gwk = Wk

variable
  γ γ′ γ″ : Gwk

infix 4 _⊢gw_∶_

data _⊢gw_∶_ : GCtx → Gwk → GCtx → Set where
  I-wf : gwfs? Ψ →
         Ψ ⊢gw I ∶ Ψ
  p-wf : Ψ ⊢gw γ ∶ Φ →
         gwf? (Γ , T) →
         (Γ , T) ∷ Ψ ⊢gw p γ ∶ Φ
  q-wf  : Ψ ⊢gw γ ∶ Φ →
          gwf? (Γ , T) →
          (Γ , T) ∷ Ψ ⊢gw q γ ∶ (Γ , T) ∷ Φ

mutual
  gwk : Exp → Gwk → Exp
  gwk (v x) γ        = v x
  gwk (gv x δ) γ     = gv (wk-x x γ) (gwk-lsubst δ γ)
  gwk ze γ           = ze
  gwk (su t) γ       = su (gwk t γ)
  gwk (Λ t) γ        = Λ (gwk t (q γ))
  gwk (t $ s) γ      = gwk t γ $ gwk s γ
  gwk (box t) γ      = box (gwk t γ)
  gwk (letbox t s) γ = letbox (gwk t γ) (gwk s (q γ))
  gwk (case t bs) γ  = case (gwk t γ) (gwk-branches bs γ)
  gwk (t [ δ ]) γ    = gwk t γ [ gwk-lsubst δ γ ]

  gwk-lsubst : LSubst → Gwk → LSubst
  gwk-lsubst ↑ γ           = ↑
  gwk-lsubst I γ           = I
  gwk-lsubst (δ ∘ δ′) γ    = gwk-lsubst δ γ ∘ gwk-lsubst δ′ γ
  gwk-lsubst (δ , t) γ     = gwk-lsubst δ γ , gwk t γ

  gwk-branches : Branches → Gwk → Branches
  gwk-branches [] γ = []
  gwk-branches ((n , t) ∷ bs) γ = (n , gwk t (repeat q n γ)) ∷ gwk-branches bs γ


gwk-gsubst : GSubst → Gwk → GSubst
gwk-gsubst σ γ = L.map (λ t → gwk t γ) σ

instance
  ExpMonotone : Monotone Exp Gwk
  ExpMonotone = record { _[[_]] = gwk }

  LSubstMonotone : Monotone LSubst Gwk
  LSubstMonotone = record { _[[_]] = gwk-lsubst }

  BranchesMonotone : Monotone Branches Gwk
  BranchesMonotone = record { _[[_]] = gwk-branches }

  GSubstMonotone : Monotone GSubst Gwk
  GSubstMonotone = record { _[[_]] = gwk-gsubst }

gsub-x : ℕ → GSubst → Exp
gsub-x x []            = ze
gsub-x zero (t ∷ σ)    = t
gsub-x (suc x) (_ ∷ σ) = gsub-x x σ


qg : GSubst → GSubst
qg σ = gv 0 I ∷ gwk-gsubst σ (p I)

mutual
  gsub : Exp → GSubst → Exp
  gsub (v x) σ        = v x
  gsub (gv x δ) σ     = gsub-x x σ [ gsub-lsubst δ σ ]
  gsub ze σ           = ze
  gsub (su t) σ       = su (gsub t σ)
  gsub (Λ t) σ        = Λ (gsub t σ)
  gsub (t $ s) σ      = gsub t σ $ gsub s σ
  gsub (box t) σ      = box (gsub t σ)
  gsub (letbox t s) σ = letbox (gsub t σ) (gsub s (qg σ))
  gsub (case t bs) σ  = case (gsub t σ) (gsub-branches bs σ)
  gsub (t [ δ ]) σ    = gsub t σ [ gsub-lsubst δ σ ]

  gsub-lsubst : LSubst → GSubst → LSubst
  gsub-lsubst ↑ σ        = ↑
  gsub-lsubst I σ        = I
  gsub-lsubst (δ ∘ δ′) σ = gsub-lsubst δ σ ∘ gsub-lsubst δ′ σ
  gsub-lsubst (δ , t) σ  = gsub-lsubst δ σ , gsub t σ

  gsub-branches : Branches → GSubst → Branches
  gsub-branches [] σ             = []
  gsub-branches ((n , t) ∷ bs) σ = (n , gsub t (repeat qg n σ)) ∷ gsub-branches bs σ

instance
  ExpGSubMono : Monotone Exp GSubst
  ExpGSubMono = record { _[[_]] = gsub }

  LSubstGSubMono : Monotone LSubst GSubst
  LSubstGSubMono = record { _[[_]] = gsub-lsubst }

  BranchesGSubMono : Monotone Branches GSubst
  BranchesGSubMono = record { _[[_]] = gsub-branches }


ql : LSubst → LSubst
ql δ = (δ ∘ ↑) , v 0


infixr 5 _∷′_
data vbranches {a} {A : Set a} : LCtx → Typ → List A → Set a where
  []   : vbranches [] T []
  _∷_  : ∀ {xs} →
         ¬ (S ≡ T) →
         vbranches Γ T xs →
         vbranches (S ∷ Γ) T xs
  _∷′_ : ∀ {x xs} →
         S ≡ T →
         vbranches Γ T xs →
         vbranches (S ∷ Γ) T (x ∷ xs)

infix 4 _⊢s_∶_ _﹔_⊢[_]_∶_ _﹔_⊢[_⇒_]_∶_ _﹔_⊢s[_]_∶_

mutual

  data _﹔_⊢[_]_∶_ : GCtx → LCtx → Layer → Exp → Typ → Set where
    vlkup  : ∀ {x} →
             gwfs? Ψ →
             wfs? i Γ →
             x ∶ T ∈ Γ →
             ---------------------
             Ψ ﹔ Γ ⊢[ i ] v x ∶ T
    gvlkup : ∀ {x} →
             Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             x ∶ Δ , T ∈ Ψ →
             ------------------------
             Ψ ﹔ Γ ⊢[ i ] gv x δ ∶ T
    ze-I   : gwfs? Ψ →
             wfs? i Γ →
             --------------------
             Ψ ﹔ Γ ⊢[ i ] ze ∶ N
    su-I   : Ψ ﹔ Γ ⊢[ i ] t ∶ N →
             ----------------------
             Ψ ﹔ Γ ⊢[ i ] su t ∶ N
    Λ-I    : Ψ ﹔ S ∷ Γ ⊢[ i ] t ∶ T →
             -------------------------
             Ψ ﹔ Γ ⊢[ i ] Λ t ∶ S ⟶ T
    Λ-E    : Ψ ﹔ Γ ⊢[ i ] r ∶ S ⟶ T →
             Ψ ﹔ Γ ⊢[ i ] s ∶ S →
             -----------------------
             Ψ ﹔ Γ ⊢[ i ] r $ s ∶ T
    □-I    : wfs? one Γ →
             Ψ ﹔ Δ ⊢[ zer ] t ∶ T →
             -----------------------------
             Ψ ﹔ Γ ⊢[ one ] box t ∶ □ Δ T
    □-E    : Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
             (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ∶ S →
             ---------------------------------
             Ψ ﹔ Γ ⊢[ one ] letbox t s ∶ S
    □-E′   : ∀ {bs} →
             Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
             Ψ ﹔ Γ ⊢[ Δ ⇒ T ] bs ∶ S →
             ---------------------------------
             Ψ ﹔ Γ ⊢[ one ] case t bs ∶ S
    t[δ]   : Ψ ﹔ Δ ⊢[ i ] t ∶ T →
             Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             -------------------------
             Ψ ﹔ Γ ⊢[ i ] t [ δ ] ∶ T

  data _﹔_⊢[_⇒_]_∶_ : GCtx → LCtx → LCtx → Typ → Branches → Typ → Set where
    bs-N : ∀ {tz tsu t$ tvs} →
           vbranches Δ N tvs →
           Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
           (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
           (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
           (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
           -----------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ N ] (0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs ∶ T
    bs-⟶ : ∀ {tΛ t$ tvs} →
           vbranches Δ N tvs →
           (S ∷ Δ , S′) ∷ Ψ ﹔ Γ ⊢[ one ] tΛ ∶ T →
           (∀ {S″} → wf? zer S″ → (Δ , S″) ∷ (Δ , S″ ⟶ S ⟶ S′) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
           (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
           ----------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ S ⟶ S′ ] (1 , tΛ) ∷ (2 , t$) ∷ L.map (0 ,_) tvs ∶ T

  data _﹔_⊢s[_]_∶_ : GCtx → LCtx → Layer → LSubst → LCtx → Set where
    s-↑    : gwfs? Ψ →
             wfs? i Γ →
             wf? i T →
             ------------------------
             Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
    s-I    : gwfs? Ψ →
             wfs? i Γ →
             --------------------
             Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
    s-∘    : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
             Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
             --------------------------
             Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
    s-,    : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             Ψ ﹔ Γ ⊢[ i ] s ∶ S →
             ----------------------------
             Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ


data _⊢s_∶_ : GCtx → GSubst → GCtx → Set where
  S-[] : gwfs? Ψ →
         ----------
         Ψ ⊢s [] ∶ []
  S-∷  : Ψ ⊢s σ ∶ Φ →
         Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
         --------------------
         Ψ ⊢s t ∷ σ ∶ (Γ , T) ∷ Ψ


-- infix 4 _⊢s_≈_∶_ _﹔_⊢[_]_≈_∶_ _﹔_⊢[_⇒_]_≈_∶_ _﹔_⊢s[_]_≈_∶_

-- mutual

--   data _﹔_⊢[_]_≈_∶_ : GCtx → LCtx → Layer → Exp → Exp → Typ → Set where
--     -- congruence rules
--     v-≈         : ∀ {x} →
--                   gwfs? Ψ →
--                   wfs? i Γ →
--                   x ∶ T ∈ Γ →
--                   --------------------------
--                   Ψ ﹔ Γ ⊢[ i ] v x ≈ v x ∶ T
--     gv-cong     : ∀ {x} →
--                   Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
--                   x ∶ Δ , T ∈ Ψ →
--                   ----------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] gv x δ ≈ gv x δ′ ∶ T
--     ze-≈        : gwfs? Ψ →
--                   wfs? i Γ →
--                   -------------------------
--                   Ψ ﹔ Γ ⊢[ i ] ze ≈ ze ∶ N
--     su-cong     : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ N →
--                   ------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] su t ≈ su t′ ∶ N
--     Λ-cong      : Ψ ﹔ S ∷ Γ ⊢[ i ] t ≈ t′ ∶ T →
--                   --------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] Λ t ≈ Λ t′ ∶ S ⟶ T
--     $-cong      : Ψ ﹔ Γ ⊢[ i ] r ≈ r′ ∶ S ⟶ T →
--                   Ψ ﹔ Γ ⊢[ i ] s ≈ s′ ∶ S →
--                   ---------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] r $ s ≈ r′ $ s′ ∶ T
--     box-cong    : wfs? one Γ →
--                   Ψ ﹔ Δ ⊢[ zer ] t ≈ t′ ∶ T →
--                   --------------------------------------
--                   Ψ ﹔ Γ ⊢[ one ] box t ≈ box t′ ∶ □ Δ T
--     letbox-cong : Ψ ﹔ Γ ⊢[ one ] t ≈ t′ ∶ □ Δ T →
--                   (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ≈ s′ ∶ S →
--                   -------------------------------------------
--                   Ψ ﹔ Γ ⊢[ one ] letbox t s ≈ letbox t s ∶ S
--     -- □-E′    : ∀ {ts} →
--     --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
--     --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
--     --           ---------------------------------
--     --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
--     []-cong     : Ψ ﹔ Δ ⊢[ i ] t ≈ t′ ∶ T →
--                   Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
--                   -------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] t [ δ ] ≈ t′ [ δ′ ] ∶ T
--     [[]]-cong   : Φ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
--                   Ψ ⊢s σ ≈ σ′ ∶ Φ →
--                   -----------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ≈ t′ [[ σ′ ]] ∶ T

--     -- local substitution rules
--     v-[,]-ze    : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ Γ ⊢[ i ] s ∶ S →
--                   -----------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] v 0 [ δ , s ] ≈ s ∶ S
--     v-[,]-su    : ∀ {x} →
--                   Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ Γ ⊢[ i ] s ∶ S →
--                   x ∶ T ∈ Δ →
--                   -------------------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] v (1 + x) [ δ , s ] ≈ v x [ δ ] ∶ T
--     v-↑         : ∀ {x} →
--                   gwfs? Ψ →
--                   wfs? i Γ →
--                   x ∶ T ∈ Γ →
--                   -------------------------------------------
--                   Ψ ﹔ S ∷ Γ ⊢[ i ] v x [ ↑ ] ≈ v (1 + x) ∶ T
--     gv-[]       : ∀ {x} →
--                   Ψ ﹔ Γ ⊢s[ i ] δ′ ∶ Δ′ →
--                   Ψ ﹔ Δ′ ⊢s[ i ] δ ∶ Δ →
--                   x ∶ Δ , T ∈ Ψ →
--                   -----------------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] gv x δ [ δ′ ] ≈ gv x (δ ∘ δ′) ∶ T
--     ze-[]       : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   -------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] ze [ δ ] ≈ ze ∶ N
--     su-[]       : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ Δ ⊢[ i ] t ∶ N →
--                   -------------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] su t [ δ ] ≈ su (t [ δ ]) ∶ N
--     Λ-[]        : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ S ∷ Δ ⊢[ i ] t ∶ T →
--                   --------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] Λ t [ δ ] ≈ Λ (t [ ql δ ]) ∶ S ⟶ T
--     $-[]        : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ Δ ⊢[ i ] r ∶ S ⟶ T →
--                   Ψ ﹔ Δ ⊢[ i ] s ∶ S →
--                   ---------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] (r $ s) [ δ ] ≈ (r′ [ δ ]) $ (s′ [ δ ]) ∶ T
--     box-[]      : wfs? one Δ′ →
--                   Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ′ →
--                   Ψ ﹔ Δ ⊢[ zer ] t ∶ T →
--                   -------------------------------------------
--                   Ψ ﹔ Γ ⊢[ one ] box t [ δ ] ≈ box t ∶ □ Δ T
--     letbox-[]   : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   Ψ ﹔ Δ ⊢[ one ] t ∶ □ Δ′ T →
--                   (Δ′ , T) ∷ Ψ ﹔ Δ ⊢[ one ] s ∶ S →
--                   -------------------------------------------
--                   Ψ ﹔ Γ ⊢[ one ] letbox t s [ δ ] ≈ letbox (t [ δ ]) (s [ δ ]) ∶ S
--     -- □-E′    : ∀ {ts} →
--     --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
--     --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
--     --           ---------------------------------
--     --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
--     [∘]         : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ′ →
--                   Ψ ﹔ Δ ⊢[ i ] t ∶ T →
--                   Ψ ﹔ Δ′ ⊢s[ i ] δ′ ∶ Δ →
--                   -------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] t [ δ ] [ δ′ ] ≈ t′ [ δ ∘ δ′ ] ∶ T
--     [I]        : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
--                   -----------------------------
--                   Ψ ﹔ Δ ⊢[ i ] t [ I ] ≈ t ∶ T

--     -- global substitution rules
--     v-[[]]      : ∀ {x} →
--                   wfs? i Γ →
--                   Ψ ⊢s σ ∶ Φ →
--                   x ∶ T ∈ Γ →
--                   -----------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] v x [[ σ ]] ≈ v x ∶ T
--     gv-[[∷]]    : ∀ {x} →
--                   Ψ ⊢s σ ∶ Φ →
--                   Φ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--                   x ∶ Δ , T ∈ Φ →
--                   x ∶ t ∈ σ →
--                   --------------------------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] gv x δ [[ σ ]] ≈ t [ δ [[ σ ]] ] ∶ T
--     ze-[[]]     : Ψ ⊢s σ ∶ Φ →
--                   wfs? i Γ →
--                   ---------------------------------
--                   Ψ ﹔ Γ ⊢[ i ] ze [[ σ ]] ≈ ze ∶ N
--     -- su-cong     : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ N →
--     --               ------------------------------
--     --               Ψ ﹔ Γ ⊢[ i ] su t ≈ su t′ ∶ N
--     -- Λ-cong      : Ψ ﹔ S ∷ Γ ⊢[ i ] t ≈ t′ ∶ T →
--     --               --------------------------------
--     --               Ψ ﹔ Γ ⊢[ i ] Λ t ≈ Λ t′ ∶ S ⟶ T
--     -- $-cong      : Ψ ﹔ Γ ⊢[ i ] r ≈ r′ ∶ S ⟶ T →
--     --               Ψ ﹔ Γ ⊢[ i ] s ≈ s′ ∶ S →
--     --               ---------------------------------
--     --               Ψ ﹔ Γ ⊢[ i ] r $ s ≈ r′ $ s′ ∶ T
--     -- box-cong    : wfs? one Γ →
--     --               Ψ ﹔ Δ ⊢[ zer ] t ≈ t′ ∶ T →
--     --               --------------------------------------
--     --               Ψ ﹔ Γ ⊢[ one ] box t ≈ box t′ ∶ □ Δ T
--     -- letbox-cong : Ψ ﹔ Γ ⊢[ one ] t ≈ t′ ∶ □ Δ T →
--     --               (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ≈ s′ ∶ S →
--     --               -------------------------------------------
--     --               Ψ ﹔ Γ ⊢[ one ] letbox t s ≈ letbox t s ∶ S
--     -- -- □-E′    : ∀ {ts} →
--     -- --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
--     -- --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
--     -- --           ---------------------------------
--     -- --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
--     -- []-cong     : Ψ ﹔ Δ ⊢[ i ] t ≈ t′ ∶ T →
--     --               Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
--     --               -------------------------------------
--     --               Ψ ﹔ Γ ⊢[ i ] t [ δ ] ≈ t′ [ δ′ ] ∶ T
--     -- [[]]-cong   : Φ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
--     --               Ψ ⊢s σ ≈ σ′ ∶ Φ →
--     --               -----------------------------------------
--     --               Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ≈ t′ [[ σ′ ]] ∶ T


--   data _﹔_⊢[_⇒_]_≈_∶_ : GCtx → LCtx → LCtx → Typ → List Exp → List Exp → Typ → Set where
--     bs-≈ : ∀ {tz tsu t$ tvs tz′ tsu′ t$′ tvs′ tvp} →
--            vbranches Δ N tvp →
--            unzip tvp ≡ (tvs , tvs′) →
--            Ψ ﹔ Γ ⊢[ one ] tz ≈ tz′ ∶ T →
--            (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ≈ tsu′ ∶ T →
--            (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
--            (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
--            ------------------------------------------------------------------
--            Ψ ﹔ Γ ⊢[ Δ ⇒ N ] tz ∷ tsu ∷ t$ ∷ tvs ≈ tz′ ∷ tsu′ ∷ t$′ ∷ tvs′ ∶ T
--     bs-⟶ : ∀ {tΛ t$ tvs tΛ′ t$′ tvs′ tvp} →
--            vbranches Δ N tvp →
--            unzip tvp ≡ (tvs , tvs′) →
--            (S ∷ Δ , S′) ∷ Ψ ﹔ Γ ⊢[ one ] tΛ ≈ tΛ′ ∶ T →
--            (∀ {S″} → wf? zer S″ → (Δ , S″) ∷ (Δ , S″ ⟶ S ⟶ S′) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
--            (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
--            -----------------------------------------------------------
--            Ψ ﹔ Γ ⊢[ Δ ⇒ S ⟶ S′ ] tΛ ∷ t$ ∷ tvs ≈ tΛ′ ∷ t$′ ∷ tvs′ ∶ T

--   data _﹔_⊢s[_]_≈_∶_ : GCtx → LCtx → Layer → LSubst → LSubst → LCtx → Set where
--     -- s-↑ : gwfs? Ψ →
--     --       wfs? i Γ →
--     --       wf? i T →
--     --       ------------------------
--     --       Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
--     -- s-I : gwfs? Ψ →
--     --       wfs? i Γ →
--     --       --------------------
--     --       Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
--     -- s-∘ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
--     --       Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
--     --       --------------------------
--     --       Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
--     -- s-, : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
--     --       Ψ ﹔ Γ ⊢[ i ] s ∶ S →
--     --       ----------------------------
--     --       Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ

--   data _⊢s_≈_∶_ : GCtx → GSubst → GSubst → GCtx → Set where
--     -- S-I : gwfs? Ψ →
--     --       ----------
--     --       Ψ ⊢s I ∶ Ψ
--     -- S-↑ : gwfs? Ψ →
--     --       gwf? (Γ , T) →
--     --       --------------------
--     --       (Γ , T) ∷ Ψ ⊢s ↑ ∶ Ψ
--     -- S-, : Ψ ⊢s σ ∶ Φ →
--     --       Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
--     --       ------------------------
--     --       Ψ ⊢s σ , t ∶ (Γ , T) ∷ Φ
--     -- S-∘ : Ψ ⊢s σ ∶ Ψ′ →
--     --       Ψ′ ⊢s σ′ ∶ Ψ″ →
--     --       ----------------
--     --       Ψ ⊢s σ′ ∘ σ ∶ Ψ″
