{-# OPTIONS --without-K --safe #-}

module CLayered.Statics where

open import Level hiding (zero; suc)

open import Lib public
open import Weakening public
open import CLayered.Typ public

import Data.Nat.Properties as ℕₚ


infixl 10 _$_
infixl 11 _[_] _[[_]]
infixl 3 _∘_

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
    []     : LSubst
    ↑      : LSubst
    I      : LSubst
    _∘_    : LSubst → LSubst → LSubst
    _,_    : LSubst → Exp → LSubst
    _[[_]] : LSubst → GSubst → LSubst

  data GSubst : Set where
    ↑    : GSubst
    I    : GSubst
    _∘_  : GSubst → GSubst → GSubst
    _,_  : GSubst → Exp → GSubst

  Branch = ℕ × Exp

  Branches = List Branch


variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : GSubst
  τ τ′ τ″ : GSubst
  δ δ′ δ″ : LSubst


qg : GSubst → GSubst
qg σ = (σ ∘ ↑) , gv 0 I


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

infix 2 _∶_∈[_⇒_]_
data _∶_∈[_⇒_]_ : ℕ → Exp → LCtx → Typ → List Exp → Set where
  here   : ∀ {ts} →
           vbranches Γ T ts →
           0 ∶ t ∈[ T ∷ Γ ⇒ T ] t ∷ ts
  there  : ∀ {x ts} →
           ¬ (S ≡ T) →
           x ∶ t ∈[ Γ ⇒ T ] ts →
           suc x ∶ t ∈[ S ∷ Γ ⇒ T ] ts
  there′ : ∀ {x ts} →
           S ≡ T →
           x ∶ t ∈[ Γ ⇒ T ] ts →
           suc x ∶ t ∈[ S ∷ Γ ⇒ T ] s ∷ ts


bnd⇒vbranches : ∀ {x ts} → x ∶ t ∈[ Γ ⇒ T ] ts → vbranches Γ T ts
bnd⇒vbranches (here vb)       = refl ∷′ vb
bnd⇒vbranches (there S≠T x∶t) = S≠T ∷ bnd⇒vbranches x∶t
bnd⇒vbranches (there′ eq x∶t) = eq ∷′ bnd⇒vbranches x∶t


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
    s-[] : gwfs? Ψ →
           wfs? i Γ →
           ----------------------
           Ψ ﹔ Γ ⊢s[ i ] [] ∶ []
    s-↑  : gwfs? Ψ →
           wfs? i Γ →
           wf? i T →
           ------------------------
           Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
    s-I  : gwfs? Ψ →
           wfs? i Γ →
           --------------------
           Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
    s-∘  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
           Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
           --------------------------
           Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
    s-,  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
           Ψ ﹔ Γ ⊢[ i ] s ∶ S →
           ----------------------------
           Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ


  data _⊢s_∶_ : GCtx → GSubst → GCtx → Set where
    S-I : gwfs? Ψ →
          ----------
          Ψ ⊢s I ∶ Ψ
    S-↑ : gwfs? Ψ →
          gwf? (Γ , T) →
          --------------------
          (Γ , T) ∷ Ψ ⊢s ↑ ∶ Ψ
    S-, : Ψ ⊢s σ ∶ Φ →
          Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
          ------------------------
          Ψ ⊢s σ , t ∶ (Γ , T) ∷ Φ
    S-∘ : Ψ ⊢s σ ∶ Ψ′ →
          Ψ′ ⊢s σ′ ∶ Ψ″ →
          ----------------
          Ψ ⊢s σ′ ∘ σ ∶ Ψ″


infix 2 _/_∈_
data _/_∈_ : Exp → ℕ → GSubst → Set where
  here : t / 0 ∈ σ , t
  there : ∀ {x} → t / x ∈ σ → t / suc x ∈ σ , s


infix 4 _⊢s_≈_∶_ _﹔_⊢[_]_≈_∶_ _﹔_⊢[_⇒_]_≈_∶_ _﹔_⊢s[_]_≈_∶_

mutual

  data _﹔_⊢[_]_≈_∶_ : GCtx → LCtx → Layer → Exp → Exp → Typ → Set where
    -- PER rules
    ≈-sym    : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
               --------------------------
               Ψ ﹔ Γ ⊢[ i ] t′ ≈ t ∶ T
    ≈-trans  : Ψ ﹔ Γ ⊢[ i ] t ≈ t′ ∶ T →
               Ψ ﹔ Γ ⊢[ i ] t′ ≈ t″ ∶ T →
               ---------------------------
               Ψ ﹔ Γ ⊢[ i ] t ≈ t″ ∶ T

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
    case-cong   : ∀ {bs bs′} →
                  Ψ ﹔ Γ ⊢[ one ] t ≈ t′ ∶ □ Δ T →
                  Ψ ﹔ Γ ⊢[ Δ ⇒ T ] bs ≈ bs′ ∶ S →
                  ---------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case t bs ≈ case t′ bs′ ∶ S
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
                  -------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] (r $ s) [ δ ] ≈ r′ [ δ ] $ (s′ [ δ ]) ∶ T
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
    case-[]     : ∀ {bs} →
                  Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  Ψ ﹔ Δ ⊢[ one ] t ∶ □ Δ T →
                  Ψ ﹔ Δ ⊢[ Δ ⇒ T ] bs ∶ S →
                  -----------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case t bs [ δ ] ≈ case (t [ δ ]) (L.map (λ (n , t) → n , t [ δ ]) bs) ∶ S
    [∘]         : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ′ →
                  Ψ ﹔ Δ ⊢[ i ] t ∶ T →
                  Ψ ﹔ Δ′ ⊢s[ i ] δ′ ∶ Δ →
                  -------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [ δ ] [ δ′ ] ≈ t′ [ δ ∘ δ′ ] ∶ T
    [I]         : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
                  -----------------------------
                  Ψ ﹔ Δ ⊢[ i ] t [ I ] ≈ t ∶ T
    [*]         : wfs? i Γ →
                  Ψ ﹔ [] ⊢[ i ] t ∶ T →
                  ------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [ [] ] ≈ t ∶ T

    -- global substitution rules
    v-[[]]      : ∀ {x} →
                  wfs? i Γ →
                  Ψ ⊢s σ ∶ Φ →
                  x ∶ T ∈ Γ →
                  -----------------------------------
                  Ψ ﹔ Γ ⊢[ i ] v x [[ σ ]] ≈ v x ∶ T
    gv-[[]]     : ∀ {x} →
                  Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  x ∶ Δ , T ∈ Φ →
                  t / x ∈ σ →
                  --------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] gv x δ [[ σ ]] ≈ t [ δ [[ σ ]] ] ∶ T
    gv-↑        : ∀ {x} →
                  gwf? (Γ′ , T′) →
                  Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  x ∶ Δ , T ∈ Ψ →
                  ---------------------------------------------------------------------
                  (Γ′ , T′) ∷ Ψ ﹔ Γ ⊢[ i ] gv x δ [[ ↑ ]] ≈ gv (suc x) (δ [[ ↑ ]]) ∶ T
    ze-[[]]     : Ψ ⊢s σ ∶ Φ →
                  wfs? i Γ →
                  ---------------------------------
                  Ψ ﹔ Γ ⊢[ i ] ze [[ σ ]] ≈ ze ∶ N
    su-[[]]     : Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢[ i ] t ∶ N →
                  -----------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] su t [[ σ ]] ≈ su (t [[ σ ]]) ∶ N
    Λ-[[]]      : Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ S ∷ Γ ⊢[ i ] t ∶ T →
                  --------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] Λ t [[ σ ]] ≈ Λ (t [[ σ ]]) ∶ S ⟶ T
    $-[[]]      : Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢[ i ] r ∶ S ⟶ T →
                  Φ ﹔ Γ ⊢[ i ] s ∶ S →
                  -----------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] (r $ s) [[ σ ]] ≈ r [[ σ ]] $ (s [[ σ ]]) ∶ T
    box-[[]]    : wfs? one Γ →
                  Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Δ ⊢[ zer ] t ∶ T →
                  --------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] box t [[ σ ]] ≈ box (t [[ σ ]]) ∶ □ Δ T
    letbox-[[]] : Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
                  (Δ , T) ∷ Φ ﹔ Γ ⊢[ one ] s ∶ S →
                  --------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] letbox t s [[ σ ]] ≈ letbox (t [[ σ ]]) (s [[ qg σ ]]) ∶ S
    case-[[]]   : ∀ {bs} →
                  Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
                  Φ ﹔ Γ ⊢[ Δ ⇒ T ] bs ∶ S →
                  -----------------------------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case t bs [[ σ ]] ≈ case (t [[ σ ]]) (L.map (λ (n , t) → n , t [[ repeat qg n σ ]]) bs) ∶ S
    []-[[]]     : Ψ ⊢s σ ∶ Φ →
                  Φ ﹔ Δ ⊢[ i ] t ∶ T →
                  Φ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                  -----------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [ δ ] [[ σ ]] ≈ t [[ σ ]] [ δ [[ σ ]] ] ∶ T
    [[∘]]       : Ψ ⊢s σ ∶ Φ →
                  Φ ⊢s σ′ ∶ Φ′ →
                  Φ′ ﹔ Γ ⊢[ i ] t ∶ T →
                  -----------------------------------------------------
                  Ψ ﹔ Γ ⊢[ i ] t [[ σ′ ]] [[ σ ]] ≈ t [[ σ′ ∘ σ ]] ∶ T
    [[I]]       : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
                  -------------------------------
                  Ψ ﹔ Δ ⊢[ i ] t [[ I ]] ≈ t ∶ T

    -- computation rules
    Λ-β         : Ψ ﹔ S ∷ Γ ⊢[ one ] t ∶ T →
                  Ψ ﹔ Γ ⊢[ one ] s ∶ S →
                  -----------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] Λ t $ s ≈ t [ I , s ] ∶ T
    Λ-η         : Ψ ﹔ Γ ⊢[ one ] t ∶ S ⟶ T →
                  ---------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] t ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T

    case-ze     : ∀ {tz tsu t$ tvs} →
                  vbranches Δ N tvs →
                  Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
                  (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
                  (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
                  (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
                  -------------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case (box ze) ((0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs) ≈ tz ∶ T
    case-su     : ∀ {tz tsu t$ tvs} →
                  vbranches Δ N tvs →
                  Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
                  (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
                  (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
                  (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
                  Ψ ﹔ Δ ⊢[ zer ] t ∶ N →
                  ------------------------------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case (box (su t)) ((0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs) ≈ tsu [[ I , t ]] ∶ T
    case-$N     : ∀ {tz tsu t$ tvs} →
                  vbranches Δ N tvs →
                  Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
                  (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
                  (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
                  (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
                  Ψ ﹔ Δ ⊢[ zer ] t ∶ S ⟶ N →
                  Ψ ﹔ Δ ⊢[ zer ] s ∶ S →
                  -----------------------------------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case (box (su t)) ((0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs) ≈ t$ [[ (I , t) , s ]] ∶ T
    case-vN     : ∀ {tz tsu t$ tvs tv x} →
                  Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
                  (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
                  (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
                  (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
                  x ∶ tv ∈[ Δ ⇒ N ] tvs →
                  ----------------------------------------------------------------------------------------------
                  Ψ ﹔ Γ ⊢[ one ] case (box (v x)) ((0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs) ≈ tv ∶ T


  data _﹔_⊢[_⇒_]_≈_∶_ : GCtx → LCtx → LCtx → Typ → Branches → Branches → Typ → Set where
    bs-≈ : ∀ {tz tsu t$ tvs tz′ tsu′ t$′ tvs′ tvp} →
           vbranches Δ N tvp →
           unzip tvp ≡ (tvs , tvs′) →
           Ψ ﹔ Γ ⊢[ one ] tz ≈ tz′ ∶ T →
           (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ≈ tsu′ ∶ T →
           (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
           (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
           ------------------------------------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ N ] (0 , tz) ∷ (1 , tsu) ∷ (2 , t$) ∷ L.map (0 ,_) tvs ≈
                            (0 , tz′) ∷ (1 , tsu′) ∷ (2 , t$′) ∷ L.map (0 ,_) tvs′ ∶ T
    bs-⟶ : ∀ {tΛ t$ tvs tΛ′ t$′ tvs′ tvp} →
           vbranches Δ N tvp →
           unzip tvp ≡ (tvs , tvs′) →
           (S ∷ Δ , S′) ∷ Ψ ﹔ Γ ⊢[ one ] tΛ ≈ tΛ′ ∶ T →
           (∀ {S″} → wf? zer S″ → (Δ , S″) ∷ (Δ , S″ ⟶ S ⟶ S′) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ≈ t$′ ∶ T) →
           (∀ {tv tv′} → (tv , tv′) ∈ tvp → Ψ ﹔ Γ ⊢[ one ] tv ≈ tv′ ∶ T) →
           -----------------------------------------------------------
           Ψ ﹔ Γ ⊢[ Δ ⇒ S ⟶ S′ ] (1 , tΛ) ∷ (2 , t$) ∷ L.map (0 ,_) tvs ≈
                                 (1 , tΛ′) ∷ (2 , t$′) ∷ L.map (0 ,_) tvs′ ∶ T

  data _﹔_⊢s[_]_≈_∶_ : GCtx → LCtx → Layer → LSubst → LSubst → LCtx → Set where
    -- s-[] : gwfs? Ψ →
    --        wfs? i Γ →
    --        ----------------------
    --        Ψ ﹔ Γ ⊢s[ i ] [] ∶ []
    -- s-↑  : gwfs? Ψ →
    --        wfs? i Γ →
    --        wf? i T →
    --        ------------------------
    --        Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
    -- s-I  : gwfs? Ψ →
    --        wfs? i Γ →
    --        --------------------
    --        Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
    -- s-∘  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
    --        Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
    --        --------------------------
    --        Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
    -- s-,  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
    --        Ψ ﹔ Γ ⊢[ i ] s ∶ S →
    --        ----------------------------
    --        Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ

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
