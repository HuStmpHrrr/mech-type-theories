{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Unascribed.Anno where

open import Lib

open import NonCumulative.Statics.Unascribed.Syntax public

variable
  Γ Γ′ Γ″ : lCtx
  Δ Δ′ Δ″ : lCtx

infix 4 ⊢_ _⊢_∶[_]_ _⊢s_∶_ _⊢_≈_∶[_]_ _⊢s_≈_∶_ ⊢_≈_ _∶[_]_∈_

mutual
  data ⊢_ : lCtx → Set where
    ⊢[] : ⊢ []
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶[ 1 + i ] Se i →
          -----------------------
          ⊢ (i , T) ∷ Γ

  data ⊢_≈_ : lCtx → lCtx → Set where
    []-≈   : ⊢ [] ≈ []
    ∷-cong : ∀ {i} →
             ⊢ Γ ≈ Δ →
             Γ ⊢ T ∶[ 1 + i ] Se i →      -- remove after presupposition
             Δ ⊢ T′ ∶[ 1 + i ] Se i →     -- remove after presupposition
             Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
             Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → -- remove after presupposition
             ----------------
             ⊢ (i , T) ∷ Γ ≈ (i , T′) ∷ Δ

  data _∶[_]_∈_ : ∀ {Γ} → ℕ → ℕ → Typ → ⊢ Γ → Set where
    here  : ∀ {i} (⊢Γ : ⊢ Γ) (⊢T : Γ ⊢ T ∶[ 1 + i ] Se i) →
            0 ∶[ i ] T [ wk ] ∈ ⊢∷ ⊢Γ ⊢T
    there : ∀ {i j n} (⊢Γ : ⊢ Γ) (⊢T : Γ ⊢ T ∶[ 1 + i ] Se i) →
            n ∶[ j ] S ∈ ⊢Γ →
            suc n ∶[ j ] S [ wk ] ∈ ⊢∷ ⊢Γ ⊢T

  data _⊢_∶[_]_ : lCtx → Exp → ℕ → Typ → Set where
    N-wf     : ⊢ Γ →
               -------------
               Γ ⊢ N ∶[ 1 ] Se 0
    Se-wf    : ∀ i →
               ⊢ Γ →
               ----------------
               Γ ⊢ Se i ∶[ 2 + i ] Se (1 + i)
    Liftt-wf : ∀ {i} n →
               Γ ⊢ T ∶[ 1 + i ] Se i →
               -------------------------
               Γ ⊢ Liftt n T ∶[ 1 + n + i ] Se (n + i)
    Π-wf     : ∀ {i j k} →
               Γ ⊢ S ∶[ 1 + i ] Se i →
               (i , S) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
               k ≡ max i j →
               --------------------
               Γ ⊢ Π S T ∶[ 1 + k ] Se k
    vlookup  : ∀ {x i} (⊢Γ : ⊢ Γ) →
               x ∶[ i ] T ∈ ⊢Γ →
               --------------------
               Γ ⊢ v x ∶[ i ] T
    ze-I     : ⊢ Γ →
               -----------
               Γ ⊢ ze ∶[ 0 ] N
    su-I     : Γ ⊢ t ∶[ 0 ] N →
               -------------
               Γ ⊢ su t ∶[ 0 ] N
    N-E      : ∀ {i} →
               (0 , N) ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
               Γ ⊢ s ∶[ i ] T [| ze ] →
               (i , T) ∷ (0 , N) ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ] →
               Γ ⊢ t ∶[ 0 ] N →
               --------------------------
               Γ ⊢ rec T s r t ∶[ i ] T [| t ]
    Λ-I      : ∀ {i j k} →
               Γ ⊢ S ∶[ 1 + i ] Se i →    -- remove after presupposition
               (i , S) ∷ Γ ⊢ t ∶[ j ] T →
               k ≡ max i j →
               ------------------
               Γ ⊢ Λ t ∶[ k ] Π S T
    Λ-E      : ∀ {i j k} →
               -- expose typing judgments for soundness proof
               Γ ⊢ S ∶[ 1 + i ] Se i →
               (i , S) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
               Γ ⊢ r ∶[ k ] Π S T →
               Γ ⊢ s ∶[ i ] S →
               k ≡ max i j →
               ---------------------
               Γ ⊢ r $ s ∶[ j ] T [| s ]
    L-I      : ∀ {i} n →
               Γ ⊢ t ∶[ i ] T →
               -------------------------
               Γ ⊢ liftt n t ∶[ n + i ] Liftt n T
    L-E      : ∀ {i} n →
               Γ ⊢ T ∶[ suc i ] Se i →
               Γ ⊢ t ∶[ n + i ] Liftt n T →
               --------------------
               Γ ⊢ unlift t ∶[ i ] T
    t[σ]     : ∀ {i} →
               Δ ⊢ t ∶[ i ] T →
               Γ ⊢s σ ∶ Δ →
               ---------------------
               Γ ⊢ t [ σ ] ∶[ i ] T [ σ ]
    conv     : ∀ {i} →
               Γ ⊢ t ∶[ i ] S →
               Γ ⊢ S ≈ T ∶[ 1 + i ] Se i →
               ------------------
               Γ ⊢ t ∶[ i ] T

  data _⊢s_∶_ : lCtx → Subst → lCtx → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-wk   : ∀ {i} →
             ⊢ (i , T) ∷ Γ →
             ------------------
             (i , T) ∷ Γ ⊢s wk ∶ Γ
    s-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶[ 1 + i ] Se i →
             Γ ⊢ t ∶[ i ] T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ (i , T) ∷ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′

  data _⊢_≈_∶[_]_ : lCtx → Exp → Exp → ℕ → Typ → Set where
    N-[]       : Γ ⊢s σ ∶ Δ →
                 -----------------------
                 Γ ⊢ N [ σ ] ≈ N ∶[ 1 ] Se 0
    Se-[]      : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 ----------------------------------
                 Γ ⊢ Se i [ σ ] ≈ Se i ∶[ 2 + i ] Se (1 + i)
    Liftt-[]   : ∀ {i} n →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ T ∶[ 1 + i ] Se i →
                 ----------------------------------------------------
                 Γ ⊢ Liftt n T [ σ ] ≈ Liftt n (T [ σ ]) ∶[ 1 + n + i ] Se (n + i)
    Π-[]       : ∀ {i j k} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (i , S) ∷ Δ ⊢ T ∶[ 1 + j ] Se j →
                 k ≡ max i j →
                 -------------------------------------------------
                 Γ ⊢ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶[ 1 + k ] Se k
    Π-cong     : ∀ {i j k} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →   -- remove after presupposition
                 Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i →
                 (i , S) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + j ] Se j →
                 k ≡ max i j →
                 --------------------------
                 Γ ⊢ Π S T ≈ Π S′ T′ ∶[ 1 + k ] Se k
    Liftt-cong : ∀ {i} n →
                 Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                 ----------------------------------------------------
                 Γ ⊢ Liftt n T ≈ Liftt n T′ ∶[ 1 + n + i ] Se (n + i)
    v-≈        : ∀ {x i} (⊢Γ : ⊢ Γ) →
                 x ∶[ i ] T ∈ ⊢Γ →
                 -----------------
                 Γ ⊢ v x ≈ v x ∶[ i ] T
    ze-≈       : ⊢ Γ →
                 ----------------
                 Γ ⊢ ze ≈ ze ∶[ 0 ] N
    su-cong    : Γ ⊢ t ≈ t′ ∶[ 0 ] N →
                 --------- ------------
                 Γ ⊢ su t ≈ su t′ ∶[ 0 ] N
    rec-cong   : ∀ {i} →
                 (0 , N) ∷ Γ ⊢ T ∶[ 1 + i ] Se i → -- remove after presupposition
                 (0 , N) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                 Γ ⊢ s ≈ s′ ∶[ i ] T [ I , ze ] →
                 (i , T) ∷ (0 , N) ∷ Γ ⊢ r ≈ r′ ∶[ i ] T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ≈ t′ ∶[ 0 ] N →
                 --------------------------------------------
                 Γ ⊢ rec T s r t ≈ rec T′ s′ r′ t′ ∶[ i ] T [| t ]
    Λ-cong     : ∀ {i j k} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →   -- remove after presupposition
                 (i , S) ∷ Γ ⊢ t ≈ t′ ∶[ j ] T →
                 k ≡ max i j →
                 -----------------------
                 Γ ⊢ Λ t ≈ Λ t′ ∶[ k ] Π S T
    $-cong     : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶[ 1 + i ] Se i →
                 (i , S) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢ r ≈ r′ ∶[ k ] Π S T →
                 Γ ⊢ s ≈ s′ ∶[ i ] S →
                 k ≡ max i j →
                 -------------------------------
                 Γ ⊢ r $ s ≈ r′ $ s′ ∶[ j ] T [| s ]
    liftt-cong : ∀ {i} n →
                 Γ ⊢ t ≈ t′ ∶[ i ] T →
                 ------------------------------------
                 Γ ⊢ liftt n t ≈ liftt n t′ ∶[ n + i ] Liftt n T
    unlift-cong : ∀ {i} n →
                 Γ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢ t ≈ t′ ∶[ n + i ] Liftt n T →
                 --------------------
                 Γ ⊢ unlift t ≈ unlift t′ ∶[ i ] T
    []-cong    : ∀ {i} →
                 Δ ⊢ t ≈ t′ ∶[ i ] T →
                 Γ ⊢s σ ≈ σ′ ∶ Δ →
                 ---------------------------------
                 Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶[ i ] T [ σ ]
    ze-[]      : Γ ⊢s σ ∶ Δ →
                 ----------------------
                 Γ ⊢ ze [ σ ] ≈ ze ∶[ 0 ] N
    su-[]      : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶[ 0 ] N →
                 ----------------------------------
                 Γ ⊢ su t [ σ ] ≈ su (t [ σ ]) ∶[ 0 ] N
    rec-[]     : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 (0 , N) ∷ Δ ⊢ T ∶[ 1 + i ] Se i →
                 Δ ⊢ s ∶[ i ] T [| ze ] →
                 (i , T) ∷ (0 , N) ∷ Δ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ] →
                 Δ ⊢ t ∶[ 0 ] N →
                 -----------------------------------------------------------------------------------------------
                 Γ ⊢ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶[ i ] T [ σ , t [ σ ] ]
    Λ-[]       : ∀ {i j k} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (i , S) ∷ Δ ⊢ t ∶[ j ] T →
                 k ≡ max i j →
                 --------------------------------------------
                 Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶[ k ] Π S T [ σ ]
    $-[]       : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (i , S) ∷ Δ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ r ∶[ k ] Π S T →
                 Δ ⊢ s ∶[ i ] S →
                 k ≡ max i j →
                 ---------------------------------------------------------
                 Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶[ j ] T [ σ , s [ σ ] ]
    liftt-[]   : ∀ {i} n →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ T ∶[ suc i ] Se i →
                 Δ ⊢ t ∶[ i ] T →
                 --------------------------------------
                 Γ ⊢ liftt n t [ σ ] ≈ liftt n (t [ σ ]) ∶[ n + i ] Liftt n T [ σ ]
    unlift-[]  : ∀ {i} n →
                 Δ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶[ n + i ] Liftt n T →
                 ---------------------------------------
                 Γ ⊢ unlift t [ σ ] ≈ unlift (t [ σ ]) ∶[ i ] T [ σ ]
    rec-β-ze   : ∀ {i} →
                 (0 , N) ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] T [| ze ] →
                 (i , T) ∷ (0 , N) ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ] →
                 ---------------------------------------------
                 Γ ⊢ rec T s r ze ≈ s ∶[ i ] T [| ze ]
    rec-β-su   : ∀ {i} →
                 (0 , N) ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] T [| ze ] →
                 (i , T) ∷ (0 , N) ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ∶[ 0 ] N →
                 -----------------------------------------------------------------
                 Γ ⊢ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶[ i ] T [| su t ]
    Λ-β        : ∀ {i j} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →   -- remove after presupposition
                 -- expose typing judgments for soundness proof
                 (i , S) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 (i , S) ∷ Γ ⊢ t ∶[ j ] T →
                 Γ ⊢ s ∶[ i ] S →
                 ----------------------------------
                 Γ ⊢ Λ t $ s ≈ t [| s ] ∶[ j ] T [| s ]
    Λ-η        : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶[ 1 + i ] Se i →
                 (i , S) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢ t ∶[ k ] Π S T →
                 k ≡ max i j →
                 ----------------------------------
                 Γ ⊢ t ≈ Λ (t [ wk ] $ v 0) ∶[ k ] Π S T
    L-β        : ∀ {i} n →
                 Γ ⊢ t ∶[ i ] T →
                 -----------------------------
                 Γ ⊢ unlift (liftt n t) ≈ t ∶[ i ] T
    L-η        : ∀ {i} n →
                 Γ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢ t ∶[ n + i ] Liftt n T →
                 -----------------------------
                 Γ ⊢ t ≈ liftt n (unlift t) ∶[ n + i ] Liftt n T
    [I]        : ∀ {i} →
                 Γ ⊢ t ∶[ i ] T →
                 --------------------
                 Γ ⊢ t [ I ] ≈ t ∶[ i ] T
    [wk]       : ∀ {i j x} (⊢Γ : ⊢ Γ) →
                 Γ ⊢ S ∶[ 1 + j ] Se j →
                 x ∶[ i ] T ∈ ⊢Γ →
                 ---------------------------------------------------
                 (j , S) ∷ Γ ⊢ v x [ wk ] ≈ v (suc x) ∶[ i ] T [ wk ]
    [∘]        : ∀ {i} →
                 Γ ⊢s τ ∶ Γ′ →
                 Γ′ ⊢s σ ∶ Γ″ →
                 Γ″ ⊢ t ∶[ i ] T →
                 ---------------------------------------------
                 Γ ⊢ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶[ i ] T [ σ ∘ τ ]
    [,]-v-ze   : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] S [ σ ] →
                 --------------------------------
                 Γ ⊢ v 0 [ σ , s ] ≈ s ∶[ i ] S [ σ ]
    [,]-v-su   : ∀ {i j x} (⊢Δ : ⊢ Δ) →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] S [ σ ] →
                 x ∶[ j ] T ∈ ⊢Δ →
                 ---------------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶[ j ] T [ σ ]
    ≈-conv     : ∀ {i} →
                 Γ ⊢ s ≈ t ∶[ i ] S →
                 Γ ⊢ S ≈ T ∶[ 1 + i ] Se i →
                 --------------------
                 Γ ⊢ s ≈ t ∶[ i ] T
    ≈-sym      : ∀ {i} →
                 Γ ⊢ t ≈ t′ ∶[ i ] T →
                 ----------------
                 Γ ⊢ t′ ≈ t ∶[ i ] T
    ≈-trans    : ∀ {i} →
                 Γ ⊢ t ≈ t′ ∶[ i ] T →
                 Γ ⊢ t′ ≈ t″ ∶[ i ] T →
                 ------ ------------
                 Γ ⊢ t ≈ t″ ∶[ i ] T

  data _⊢s_≈_∶_ : lCtx → Subst → Subst → lCtx → Set where
    I-≈       : ⊢ Γ →
                --------------
                Γ ⊢s I ≈ I ∶ Γ
    wk-≈      : ∀ {i} →
                ⊢ (i , T) ∷ Γ →
                --------------------------
                (i , T) ∷ Γ ⊢s wk ≈ wk ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                ----------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Δ ⊢ T ∶[ 1 + i ] Se i →
                Γ ⊢ t ≈ t′ ∶[ i ] T [ σ ] →
                -----------------------------
                Γ ⊢s σ , t ≈ σ′ , t′ ∶ (i , T) ∷ Δ
    I-∘       : Γ ⊢s σ ∶ Δ →
                -------------------
                Γ ⊢s I ∘ σ ≈ σ ∶ Δ
    ∘-I       : Γ ⊢s σ ∶ Δ →
                -------------------
                Γ ⊢s σ ∘ I ≈ σ ∶ Δ
    ∘-assoc   : ∀ {Γ‴} →
                Γ′ ⊢s σ ∶ Γ →
                Γ″ ⊢s σ′ ∶ Γ′ →
                Γ‴ ⊢s σ″ ∶ Γ″ →
                ---------------------------------------
                Γ‴ ⊢s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
    ,-∘       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ″ →
                Γ″ ⊢ T ∶[ 1 + i ] Se i →
                Γ′ ⊢ t ∶[ i ] T [ σ ] →
                Γ ⊢s τ ∶ Γ′ →
                ---------------------------------------------
                Γ ⊢s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ (i , T) ∷ Γ″
    p-,       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ →
                Γ ⊢ T ∶[ 1 + i ] Se i →
                Γ′ ⊢ t ∶[ i ] T [ σ ] →
                -------------------------
                Γ′ ⊢s p (σ , t) ≈ σ ∶ Γ
    ,-ext     : ∀ {i} →
                Γ′ ⊢s σ ∶ (i , T) ∷ Γ →
                ----------------------------------
                Γ′ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ (i , T) ∷ Γ
    s-≈-sym   : Γ ⊢s σ ≈ σ′ ∶ Δ →
                ------------------
                Γ ⊢s σ′ ≈ σ ∶ Δ
    s-≈-trans : Γ ⊢s σ ≈ σ′ ∶ Δ →
                Γ ⊢s σ′ ≈ σ″ ∶ Δ →
                -------------------
                Γ ⊢s σ ≈ σ″ ∶ Δ
    s-≈-conv  : Γ ⊢s σ ≈ σ′ ∶ Δ →
                ⊢ Δ ≈ Δ′ →
                ------------------
                Γ ⊢s σ ≈ σ′ ∶ Δ′

⊢p : ∀ {i} → ⊢ (i , T) ∷ Δ → Γ ⊢s σ ∶ (i , T) ∷ Δ → Γ ⊢s p σ ∶ Δ
⊢p ⊢TΔ ⊢σ = s-∘ ⊢σ (s-wk ⊢TΔ)
