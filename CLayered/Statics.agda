{-# OPTIONS --without-K --safe #-}

module CLayered.Statics where

open import CLayered.Typ public
open import Lib

import Data.Nat.Properties as ℕₚ


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
    _[[_]] : Exp → GSubst → Exp
    _[_]   : Exp → LSubst → Exp

  data LSubst : Set where
    ↑      : LSubst
    I      : LSubst
    _∘_    : LSubst → LSubst → LSubst
    _,_    : LSubst → Exp → LSubst
    _[[_]] : LSubst → GSubst → LSubst

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


data Wk : Set where
  id  : Wk
  p q : Wk → Wk

infixl 3 _∘w_

_∘w_ : Wk → Wk → Wk
id ∘w γ′    = γ′
p γ ∘w q γ′ = p (γ ∘w γ′)
q γ ∘w q γ′ = q (γ ∘w γ′)
γ ∘w id     = γ
γ ∘w p γ′   = p (γ ∘w γ′)


∘w-id : ∀ γ → (γ ∘w id) ≡ γ
∘w-id id    = refl
∘w-id (p γ) = refl
∘w-id (q γ) = refl

∘w-p : ∀ γ γ′ → (γ ∘w p γ′) ≡ p (γ ∘w γ′)
∘w-p id γ′    = refl
∘w-p (p γ) γ′ = refl
∘w-p (q γ) γ′ = refl

∘w-pid : ∀ γ → (γ ∘w p id) ≡ p γ
∘w-pid id    = refl
∘w-pid (p γ) = refl
∘w-pid (q γ) = refl

pid∘p*id : ∀ n → (p id ∘w repeat p n id) ≡ repeat p (1 + n) id
pid∘p*id zero    = refl
pid∘p*id (suc n) = cong p (pid∘p*id n)

∘w-assoc : ∀ γ γ′ γ″ → ((γ ∘w γ′) ∘w γ″) ≡ (γ ∘w (γ′ ∘w γ″))
∘w-assoc id γ′ γ″          = refl
∘w-assoc γ id γ″
  rewrite ∘w-id γ          = refl
∘w-assoc γ γ′ id
  rewrite ∘w-id (γ ∘w γ′)
        | ∘w-id γ′         = refl
∘w-assoc γ γ′ (p γ″)
  rewrite ∘w-p γ′ γ″
        | ∘w-p (γ ∘w γ′) γ″
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc γ (p γ′) (q γ″)
  rewrite ∘w-p γ γ′
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (p γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (q γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl

wk-x : ℕ → Wk → ℕ
wk-x x id          = x
wk-x x (p γ)       = suc (wk-x x γ)
wk-x 0 (q γ)       = 0
wk-x (suc x) (q γ) = suc (wk-x x γ)

wk-x-repeat-p : ∀ x y → wk-x x (repeat p y id) ≡ y + x
wk-x-repeat-p x zero = refl
wk-x-repeat-p x (suc y) = cong suc (wk-x-repeat-p x y)

wk-x-repeat-p′ : ∀ x y → wk-x x (repeat p y id) ≡ x + y
wk-x-repeat-p′ x y = trans (wk-x-repeat-p x y) (ℕₚ.+-comm y x)

wk-x-comp : ∀ x γ γ′ → wk-x (wk-x x γ) γ′ ≡ wk-x x (γ ∘w γ′)
wk-x-comp x id γ′              = refl
wk-x-comp x (p γ) id           = refl
wk-x-comp x (p γ) (p γ′)
  rewrite wk-x-comp x (p γ) γ′ = refl
wk-x-comp x (p γ) (q γ′)
  rewrite wk-x-comp x γ γ′     = refl
wk-x-comp x (q γ) id           = refl
wk-x-comp x (q γ) (p γ′)
  rewrite wk-x-comp x (q γ) γ′ = refl
wk-x-comp zero (q γ) (q γ′)    = refl
wk-x-comp (suc x) (q γ) (q γ′)
  rewrite wk-x-comp x γ γ′     = refl

mutual
  gwk : Exp → Wk → Exp
  gwk (v x) γ        = v x
  gwk (gv x δ) γ     = gv (wk-x x γ) (gwk-lsubst δ γ)
  gwk ze γ           = ze
  gwk (su t) γ       = su (gwk t γ)
  gwk (Λ t) γ        = Λ (gwk t (q γ))
  gwk (t $ s) γ      = gwk t γ $ gwk s γ
  gwk (box t) γ      = box (gwk t γ)
  gwk (letbox t s) γ = letbox (gwk t γ) (gwk s (q γ))
  gwk (case t bs) γ  = case (gwk t γ) (gwk-branches bs γ)
  gwk (t [[ σ ]]) γ  = t [[ gwk-gsubst σ γ ]]
  gwk (t [ δ ]) γ    = gwk t γ [ gwk-lsubst δ γ ]

  gwk-lsubst : LSubst → Wk → LSubst
  gwk-lsubst ↑ γ           = ↑
  gwk-lsubst I γ           = I
  gwk-lsubst (δ ∘ δ′) γ    = gwk-lsubst δ γ ∘ gwk-lsubst δ′ γ
  gwk-lsubst (δ , t) γ     = gwk-lsubst δ γ , gwk t γ
  gwk-lsubst (δ [[ σ ]]) γ = δ [[ gwk-gsubst σ γ ]]

  gwk-gsubst : GSubst → Wk → GSubst
  gwk-gsubst [] γ      = []
  gwk-gsubst (t ∷ σ) γ = gwk t γ ∷ gwk-gsubst σ γ

  gwk-branches : Branches → Wk → Branches
  gwk-branches [] γ = []
  gwk-branches ((n , t) ∷ bs) γ = (n , gwk t (repeat q n γ)) ∷ gwk-branches bs γ


  -- gwk-gsubst : GSubst → Wk → GSubst
  -- gwk-gsubst σ γ = L.map (λ t → gwk t γ) σ

-- qg : GSubst → GSubst
-- qg σ = (σ ∘ ↑) , v 0

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
    t[σ]   : Φ ﹔ Γ ⊢[ i ] t ∶ T →
             Ψ ⊢s σ ∶ Φ →
             ---------------------------
             Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ∶ T

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
    s-[[]] : Φ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             Ψ ⊢s σ ∶ Φ →
             --------------------------
             Ψ ﹔ Γ ⊢s[ i ] δ [[ σ ]] ∶ Δ

  data _⊢s_∶_ : GCtx → GSubst → GCtx → Set where
    S-[] : gwfs? Ψ →
           ----------
           Ψ ⊢s [] ∶ []
    S-∷  : Ψ ⊢s σ ∶ Φ →
           Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
           --------------------
           Ψ ⊢s t ∷ σ ∶ (Γ , T) ∷ Ψ

infix 4 _⊢s_≈_∶_ _﹔_⊢[_]_≈_∶_ _﹔_⊢[_⇒_]_≈_∶_ _﹔_⊢s[_]_≈_∶_

mutual

  data _﹔_⊢[_]_≈_∶_ : GCtx → LCtx → Layer → Exp → Exp → Typ → Set where
    -- congruence rules
    v-≈         : ∀ {x} →
                  gwfs? Ψ →
                  wfs? i Γ →
                  x ∶ T ∈ Γ →
                  --------------------------
                  Ψ ﹔ Γ ⊢[ i ] v x ≈ v x ∶ T
    gv-cong     : ∀ {x} →
                  Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
                  x ∶ Δ , T ∈ Ψ →
                  ----------------------------------
                  Ψ ﹔ Γ ⊢[ i ] gv x δ ≈ gv x δ′ ∶ T
    ze-≈        : gwfs? Ψ →
                  wfs? i Γ →
                  -------------------------
                  Ψ ﹔ Γ ⊢[ i ] ze ≈ ze ∶ N
    su-cong     : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ N →
                  ------------------------------
                  Ψ ﹔ Γ ⊢[ i ] su t ≈ su t′ ∶ N
    Λ-cong      : Ψ ﹔ S ∷ Γ ⊢[ i ] t ≈ t′ ∶ T →
                  --------------------------------
                  Ψ ﹔ Γ ⊢[ i ] Λ t ≈ Λ t′ ∶ S ⟶ T
    $-cong      : Ψ ﹔ Γ ⊢[ i ] r ≈ r′ ∶ S ⟶ T →
                  Ψ ﹔ Γ ⊢[ i ] s ≈ s′ ∶ S →
                  ---------------------------------
                  Ψ ﹔ Γ ⊢[ i ] r $ s ≈ r′ $ s′ ∶ T
    box-cong    : wfs? one Γ →
                  Ψ ﹔ Δ ⊢[ zer ] t ≈ t′ ∶ T →
                  --------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] box t ≈ box t′ ∶ □ Δ T
    letbox-cong : Ψ ﹔ Γ ⊢[ one ] t ≈ t′ ∶ □ Δ T →
                  (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ≈ s′ ∶ S →
                  -------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] letbox t s ≈ letbox t s ∶ S
    -- □-E′    : ∀ {ts} →
    --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
    --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
    --           ---------------------------------
    --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
    []-cong     : Ψ ﹔ Δ ⊢[ i ] t ≈ t′ ∶ T →
                  Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
                  -------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [ δ ] ≈ t′ [ δ′ ] ∶ T
    [[]]-cong   : Φ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
                  Ψ ⊢s σ ≈ σ′ ∶ Φ →
                  -----------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ≈ t′ [[ σ′ ]] ∶ T

    -- local substitution rules
    v-[,]-ze    : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Γ ⊢[ i ] s ∶ S →
                  -----------------------------------
                  Ψ ﹔ Γ ⊢[ i ] v 0 [ δ , s ] ≈ s ∶ S
    v-[,]-su    : ∀ {x} →
                  Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Γ ⊢[ i ] s ∶ S →
                  x ∶ T ∈ Δ →
                  -------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] v (1 + x) [ δ , s ] ≈ v x [ δ ] ∶ T
    v-↑         : ∀ {x} →
                  gwfs? Ψ →
                  wfs? i Γ →
                  x ∶ T ∈ Γ →
                  -------------------------------------------
                  Ψ ﹔ S ∷ Γ ⊢[ i ] v x [ ↑ ] ≈ v (1 + x) ∶ T
    gv-[]       : ∀ {x} →
                  Ψ ﹔ Γ ⊢s[ i ] δ′ ∶ Δ′ →
                  Ψ ﹔ Δ′ ⊢s[ i ] δ ∶ Δ →
                  x ∶ Δ , T ∈ Ψ →
                  -----------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] gv x δ [ δ′ ] ≈ gv x (δ ∘ δ′) ∶ T
    ze-[]       : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  -------------------------------
                  Ψ ﹔ Γ ⊢[ i ] ze [ δ ] ≈ ze ∶ N
    su-[]       : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Δ ⊢[ i ] t ∶ N →
                  -------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] su t [ δ ] ≈ su (t [ δ ]) ∶ N
    Λ-[]        : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ S ∷ Δ ⊢[ i ] t ∶ T →
                  --------------------------------
                  Ψ ﹔ Γ ⊢[ i ] Λ t [ δ ] ≈ Λ (t [ ql δ ]) ∶ S ⟶ T
    $-[]        : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Δ ⊢[ i ] r ∶ S ⟶ T →
                  Ψ ﹔ Δ ⊢[ i ] s ∶ S →
                  ---------------------------------
                  Ψ ﹔ Γ ⊢[ i ] (r $ s) [ δ ] ≈ (r′ [ δ ]) $ (s′ [ δ ]) ∶ T
    box-[]      : wfs? one Δ′ →
                  Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ′ →
                  Ψ ﹔ Δ ⊢[ zer ] t ∶ T →
                  -------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] box t [ δ ] ≈ box t ∶ □ Δ T
    letbox-[]   : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Δ ⊢[ one ] t ∶ □ Δ′ T →
                  (Δ′ , T) ∷ Ψ ﹔ Δ ⊢[ one ] s ∶ S →
                  -------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] letbox t s [ δ ] ≈ letbox (t [ δ ]) (s [ δ ]) ∶ S
    -- □-E′    : ∀ {ts} →
    --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
    --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
    --           ---------------------------------
    --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
    [∘]         : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ′ →
                  Ψ ﹔ Δ ⊢[ i ] t ∶ T →
                  Ψ ﹔ Δ′ ⊢s[ i ] δ′ ∶ Δ →
                  -------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [ δ ] [ δ′ ] ≈ t′ [ δ ∘ δ′ ] ∶ T
    [id]        : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
                  -----------------------------
                  Ψ ﹔ Δ ⊢[ i ] t [ I ] ≈ t ∶ T

    -- global substitution rules
    v-[[]]      : ∀ {x} →
                  wfs? i Γ →
                  Ψ ⊢s σ ∶ Φ →
                  x ∶ T ∈ Γ →
                  -----------------------------------
                  Ψ ﹔ Γ ⊢[ i ] v x [[ σ ]] ≈ v x ∶ T
    gv-[[∷]]    : ∀ {x} →
                  Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  x ∶ Δ , T ∈ Φ →
                  x ∶ t ∈ σ →
                  --------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] gv x δ [[ σ ]] ≈ t [ δ [[ σ ]] ] ∶ T
    ze-[[]]     : Ψ ⊢s σ ∶ Φ →
                  wfs? i Γ →
                  ---------------------------------
                  Ψ ﹔ Γ ⊢[ i ] ze [[ σ ]] ≈ ze ∶ N
    -- su-cong     : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ N →
    --               ------------------------------
    --               Ψ ﹔ Γ ⊢[ i ] su t ≈ su t′ ∶ N
    -- Λ-cong      : Ψ ﹔ S ∷ Γ ⊢[ i ] t ≈ t′ ∶ T →
    --               --------------------------------
    --               Ψ ﹔ Γ ⊢[ i ] Λ t ≈ Λ t′ ∶ S ⟶ T
    -- $-cong      : Ψ ﹔ Γ ⊢[ i ] r ≈ r′ ∶ S ⟶ T →
    --               Ψ ﹔ Γ ⊢[ i ] s ≈ s′ ∶ S →
    --               ---------------------------------
    --               Ψ ﹔ Γ ⊢[ i ] r $ s ≈ r′ $ s′ ∶ T
    -- box-cong    : wfs? one Γ →
    --               Ψ ﹔ Δ ⊢[ zer ] t ≈ t′ ∶ T →
    --               --------------------------------------
    --               Ψ ﹔ Γ ⊢[ one ] box t ≈ box t′ ∶ □ Δ T
    -- letbox-cong : Ψ ﹔ Γ ⊢[ one ] t ≈ t′ ∶ □ Δ T →
    --               (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ≈ s′ ∶ S →
    --               -------------------------------------------
    --               Ψ ﹔ Γ ⊢[ one ] letbox t s ≈ letbox t s ∶ S
    -- -- □-E′    : ∀ {ts} →
    -- --           Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
    -- --           Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
    -- --           ---------------------------------
    -- --           Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
    -- []-cong     : Ψ ﹔ Δ ⊢[ i ] t ≈ t′ ∶ T →
    --               Ψ ﹔ Γ ⊢s[ i ] δ ≈ δ′ ∶ Δ →
    --               -------------------------------------
    --               Ψ ﹔ Γ ⊢[ i ] t [ δ ] ≈ t′ [ δ′ ] ∶ T
    -- [[]]-cong   : Φ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
    --               Ψ ⊢s σ ≈ σ′ ∶ Φ →
    --               -----------------------------------------
    --               Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ≈ t′ [[ σ′ ]] ∶ T


  data _﹔_⊢[_⇒_]_≈_∶_ : GCtx → LCtx → LCtx → Typ → List Exp → List Exp → Typ → Set where
    bs-≈ : ∀ {tz tsu t$ tvs tz′ tsu′ t$′ tvs′ tvp} →
           vbranches Δ N tvp →
           unzip tvp ≡ (tvs , tvs′) →
           Ψ ﹔ Γ ⊢[ one ] tz ≈ tz′ ∶ T →
           (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ≈ tsu′ ∶ T →
           (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
           (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
           ------------------------------------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ N ] tz ∷ tsu ∷ t$ ∷ tvs ≈ tz′ ∷ tsu′ ∷ t$′ ∷ tvs′ ∶ T
    bs-⟶ : ∀ {tΛ t$ tvs tΛ′ t$′ tvs′ tvp} →
           vbranches Δ N tvp →
           unzip tvp ≡ (tvs , tvs′) →
           (S ∷ Δ , S′) ∷ Ψ ﹔ Γ ⊢[ one ] tΛ ≈ tΛ′ ∶ T →
           (∀ {S″} → wf? zer S″ → (Δ , S″) ∷ (Δ , S″ ⟶ S ⟶ S′) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
           (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
           -----------------------------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ S ⟶ S′ ] tΛ ∷ t$ ∷ tvs ≈ tΛ′ ∷ t$′ ∷ tvs′ ∶ T

  data _﹔_⊢s[_]_≈_∶_ : GCtx → LCtx → Layer → LSubst → LSubst → LCtx → Set where
    -- s-↑ : gwfs? Ψ →
    --       wfs? i Γ →
    --       wf? i T →
    --       ------------------------
    --       Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
    -- s-I : gwfs? Ψ →
    --       wfs? i Γ →
    --       --------------------
    --       Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
    -- s-∘ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
    --       Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
    --       --------------------------
    --       Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
    -- s-, : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
    --       Ψ ﹔ Γ ⊢[ i ] s ∶ S →
    --       ----------------------------
    --       Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ

  data _⊢s_≈_∶_ : GCtx → GSubst → GSubst → GCtx → Set where
    -- S-I : gwfs? Ψ →
    --       ----------
    --       Ψ ⊢s I ∶ Ψ
    -- S-↑ : gwfs? Ψ →
    --       gwf? (Γ , T) →
    --       --------------------
    --       (Γ , T) ∷ Ψ ⊢s ↑ ∶ Ψ
    -- S-, : Ψ ⊢s σ ∶ Φ →
    --       Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
    --       ------------------------
    --       Ψ ⊢s σ , t ∶ (Γ , T) ∷ Φ
    -- S-∘ : Ψ ⊢s σ ∶ Ψ′ →
    --       Ψ′ ⊢s σ′ ∶ Ψ″ →
    --       ----------------
    --       Ψ ⊢s σ′ ∘ σ ∶ Ψ″
