{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Full where

open import Lib

open import NonCumulative.Statics.Ascribed.Syntax public

infix 4 ⊢_ _⊢_∶[_]_ _⊢s_∶_ _⊢_≈_∶[_]_ _⊢s_≈_∶_ ⊢_≈_

mutual
  data ⊢_ : Ctx → Set where
    ⊢[] : ⊢ []
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶[ 1 + i ] Se i →
          -----------------------
          ⊢ (T ↙ i) ∷ Γ

  data ⊢_≈_ : Ctx → Ctx → Set where
    []-≈   : ⊢ [] ≈ []
    ∷-cong : ∀ {i} →
             ⊢ Γ ≈ Δ →
             Γ ⊢ T ∶[ 1 + i ] Se i →      -- remove after presupposition
             Δ ⊢ T′ ∶[ 1 + i ] Se i →     -- remove after presupposition
             Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
             Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → -- remove after presupposition
             ----------------
             ⊢ (T ↙ i) ∷ Γ ≈ (T′ ↙ i) ∷ Δ

  data _⊢_∶[_]_ : Ctx → Exp → ℕ → Typ → Set where
    N-wf     : ⊢ Γ →
               -------------
               Γ ⊢ N ∶[ 1 ] Se 0
    Se-wf    : ∀ i →
               ⊢ Γ →
               ----------------
               Γ ⊢ Se i ∶[ 2 + i ] Se (1 + i)
    Liftt-wf : ∀ {i} n →
               Γ ⊢ S ∶[ 1 + i ] Se i →
               -------------------------
               Γ ⊢ Liftt n (S ↙ i) ∶[ 1 + n + i ] Se (n + i)
    Π-wf     : ∀ {i j k} →
               Γ ⊢ S ∶[ 1 + i ] Se i →
               (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
               k ≡ max i j →
               ---------------------------
               Γ ⊢ Π (S ↙ i) (T ↙ j) ∶[ 1 + k ] Se k
    vlookup  : ∀ {x i} →
               ⊢ Γ →
               x ∶[ i ] T ∈! Γ →
               --------------------
               Γ ⊢ v x ∶[ i ] T
    ze-I     : ⊢ Γ →
               -----------
               Γ ⊢ ze ∶[ 0 ] N
    su-I     : Γ ⊢ t ∶[ 0 ] N →
               -------------
               Γ ⊢ su t ∶[ 0 ] N
    N-E      : ∀ {i} →
               N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
               Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
               (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
               Γ ⊢ t ∶[ 0 ] N →
               --------------------------
               Γ ⊢ rec (T ↙ i) s r t ∶[ i ] T [| t ∶ N₀ ]
    Λ-I      : ∀ {i j k} →
               Γ ⊢ S ∶[ 1 + i ] Se i →    -- remove after presupposition
               (S ↙ i) ∷ Γ ⊢ t ∶[ j ] T →
               k ≡ max i j →
               ---------------------------------
               Γ ⊢ Λ (S ↙ i) t ∶[ k ] Π (S ↙ i) (T ↙ j)
    Λ-E      : ∀ {i j k} →
               -- expose typing judgments for soundness proof
               Γ ⊢ S ∶[ 1 + i ] Se i →
               (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
               Γ ⊢ r ∶[ k ] Π (S ↙ i) (T ↙ j) →
               Γ ⊢ s ∶[ i ] S →
               k ≡ max i j →
               ---------------------
               Γ ⊢ r $ s ∶[ j ] T [| s ∶ S ↙ i ]
    L-I      : ∀ {i} n →
               Γ ⊢ t ∶[ i ] T →
               -------------------------
               Γ ⊢ liftt n t ∶[ n + i ] Liftt n (T ↙ i)
    L-E      : ∀ {i} n →
               Γ ⊢ T ∶[ suc i ] Se i →
               Γ ⊢ t ∶[ n + i ] Liftt n (T ↙ i) →
               ---------------------------
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

  data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-wk   : ∀ {i} →
             ⊢ (T ↙ i) ∷ Γ →
             ------------------
             (T ↙ i) ∷ Γ ⊢s wk ∶ Γ
    s-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶[ 1 + i ] Se i →
             Γ ⊢ t ∶[ i ] T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ T ↙ i ∶ (T ↙ i) ∷ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′

  data _⊢_≈_∶[_]_ : Ctx → Exp → Exp → ℕ → Typ → Set where
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
                 Γ ⊢ Liftt n (T ↙ i) [ σ ] ≈ Liftt n (T [ σ ] ↙ i) ∶[ 1 + n + i ] Se (n + i)
    Π-[]       : ∀ {i j k} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Δ ⊢ T ∶[ 1 + j ] Se j →
                 k ≡ max i j →
                 -------------------------------------------------
                 Γ ⊢ Π (S ↙ i) (T ↙ j) [ σ ] ≈ Π (S [ σ ] ↙ i) (T [ q (S ↙ i) σ ] ↙ j) ∶[ 1 + k ] Se k
    Π-cong     : ∀ {i j k} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →   -- remove after presupposition
                 Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + j ] Se j →
                 k ≡ max i j →
                 ------------------------------------------
                 Γ ⊢ Π (S ↙ i) (T ↙ j) ≈ Π (S′ ↙ i) (T′ ↙ j) ∶[ 1 + k ] Se k
    Liftt-cong : ∀ {i} n →
                 Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                 ----------------------------------------------------
                 Γ ⊢ Liftt n (T ↙ i) ≈ Liftt n (T′ ↙ i) ∶[ 1 + n + i ] Se (n + i)
    v-≈        : ∀ {x i} →
                 ⊢ Γ →
                 x ∶[ i ] T ∈! Γ →
                 -----------------
                 Γ ⊢ v x ≈ v x ∶[ i ] T
    ze-≈       : ⊢ Γ →
                 ----------------
                 Γ ⊢ ze ≈ ze ∶[ 0 ] N
    su-cong    : Γ ⊢ t ≈ t′ ∶[ 0 ] N →
                 --------- ------------
                 Γ ⊢ su t ≈ su t′ ∶[ 0 ] N
    rec-cong   : ∀ {i} →
                 N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i → -- remove after presupposition
                 N₀ ∷ Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                 Γ ⊢ s ≈ s′ ∶[ i ] T [| ze ∶ N₀ ] →
                 (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ≈ r′ ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
                 Γ ⊢ t ≈ t′ ∶[ 0 ] N →
                 --------------------------------------------
                 Γ ⊢ rec (T ↙ i) s r t ≈ rec (T′ ↙ i) s′ r′ t′ ∶[ i ] T [| t ∶ N₀ ]
    Λ-cong     : ∀ {i j k} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →
                 Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Γ ⊢ t ≈ t′ ∶[ j ] T →
                 k ≡ max i j →
                 -----------------------
                 Γ ⊢ Λ (S ↙ i) t ≈ Λ (S′ ↙ i) t′ ∶[ k ] Π (S ↙ i) (T ↙ j)
    $-cong     : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢ r ≈ r′ ∶[ k ] Π (S ↙ i) (T ↙ j) →
                 Γ ⊢ s ≈ s′ ∶[ i ] S →
                 k ≡ max i j →
                 -------------------------------
                 Γ ⊢ r $ s ≈ r′ $ s′ ∶[ j ] T [| s ∶ S ↙ i ]
    liftt-cong : ∀ {i} n →
                 Γ ⊢ t ≈ t′ ∶[ i ] T →
                 ------------------------------------
                 Γ ⊢ liftt n t ≈ liftt n t′ ∶[ n + i ] Liftt n (T ↙ i)
    unlift-cong : ∀ {i} n →
                 Γ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢ t ≈ t′ ∶[ n + i ] Liftt n (T ↙ i) →
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
                 N₀ ∷ Δ ⊢ T ∶[ 1 + i ] Se i →
                 Δ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
                 (T ↙ i) ∷ N₀ ∷ Δ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
                 Δ ⊢ t ∶[ 0 ] N →
                 -----------------------------------------------------------------------------------------------
                 Γ ⊢ rec (T ↙ i) s r t [ σ ] ≈ rec (T [ q N₀ σ ] ↙ i) (s [ σ ]) (r [ q (T ↙ i) (q N₀ σ) ]) (t [ σ ]) ∶[ i ] T [ σ , t [ σ ] ∶ N₀ ]
    Λ-[]       : ∀ {i j k} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Δ ⊢ t ∶[ j ] T →
                 k ≡ max i j →
                 --------------------------------------------
                 Γ ⊢ Λ (S ↙ i) t [ σ ] ≈ Λ (S [ σ ] ↙ i) (t [ q (S ↙ i) σ ]) ∶[ k ] Π (S ↙ i) (T ↙ j) [ σ ]
    $-[]       : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Δ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ r ∶[ k ] Π (S ↙ i) (T ↙ j) →
                 Δ ⊢ s ∶[ i ] S →
                 k ≡ max i j →
                 ---------------------------------------------------------
                 Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶[ j ] T [ σ , s [ σ ] ∶ S ↙ i ]
    liftt-[]   : ∀ {i} n →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ T ∶[ suc i ] Se i →
                 Δ ⊢ t ∶[ i ] T →
                 --------------------------------------
                 Γ ⊢ liftt n t [ σ ] ≈ liftt n (t [ σ ]) ∶[ n + i ] Liftt n (T ↙ i) [ σ ]
    unlift-[]  : ∀ {i} n →
                 Δ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶[ n + i ] Liftt n (T ↙ i) →
                 ---------------------------------------
                 Γ ⊢ unlift t [ σ ] ≈ unlift (t [ σ ]) ∶[ i ] T [ σ ]
    rec-β-ze   : ∀ {i} →
                 N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
                 (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
                 ---------------------------------------------
                 Γ ⊢ rec (T ↙ i) s r ze ≈ s ∶[ i ] T [| ze ∶ N₀ ]
    rec-β-su   : ∀ {i} →
                 N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
                 (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
                 Γ ⊢ t ∶[ 0 ] N →
                 -----------------------------------------------------------------
                 Γ ⊢ rec (T ↙ i) s r (su t) ≈ r [ (I , t ∶ N₀) , rec (T ↙ i) s r t ∶ T ↙ i ] ∶[ i ] T [| su t ∶ N₀ ]
    Λ-β        : ∀ {i j} →
                 Γ ⊢ S ∶[ 1 + i ] Se i →   -- remove after presupposition
                 -- expose typing judgments for soundness proof
                 (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 (S ↙ i) ∷ Γ ⊢ t ∶[ j ] T →
                 Γ ⊢ s ∶[ i ] S →
                 ----------------------------------
                 Γ ⊢ Λ (S ↙ i) t $ s ≈ (t [| s ∶ S ↙ i ]) ∶[ j ] T [| s ∶ S ↙ i ]
    Λ-η        : ∀ {i j k} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶[ 1 + i ] Se i →
                 (S ↙ i) ∷ Γ ⊢ T ∶[ 1 + j ] Se j →
                 Γ ⊢ t ∶[ k ] Π (S ↙ i) (T ↙ j) →
                 k ≡ max i j →
                 ----------------------------------
                 Γ ⊢ t ≈ Λ (S ↙ i) (t [ wk ] $ v 0) ∶[ k ] Π (S ↙ i) (T ↙ j)
    L-β        : ∀ {i} n →
                 Γ ⊢ t ∶[ i ] T →
                 -----------------------------
                 Γ ⊢ unlift (liftt n t) ≈ t ∶[ i ] T
    L-η        : ∀ {i} n →
                 Γ ⊢ T ∶[ suc i ] Se i →
                 Γ ⊢ t ∶[ n + i ] Liftt n (T ↙ i) →
                 -----------------------------
                 Γ ⊢ t ≈ liftt n (unlift t) ∶[ n + i ] Liftt n (T ↙ i)
    [I]        : ∀ {i} →
                 Γ ⊢ t ∶[ i ] T →
                 --------------------
                 Γ ⊢ t [ I ] ≈ t ∶[ i ] T
    [wk]       : ∀ {i j x} →
                 ⊢ Γ →
                 Γ ⊢ S ∶[ 1 + j ] Se j →
                 x ∶[ i ] T ∈! Γ →
                 ---------------------------------------------------
                 (S ↙ j) ∷ Γ ⊢ v x [ wk ] ≈ v (suc x) ∶[ i ] T [ wk ]
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
                 Γ ⊢ v 0 [ σ , s ∶ S ↙ i ] ≈ s ∶[ i ] S [ σ ]
    [,]-v-su   : ∀ {i j x} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶[ 1 + i ] Se i →
                 Γ ⊢ s ∶[ i ] S [ σ ] →
                 x ∶[ j ] T ∈! Δ →
                 ---------------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ∶ S ↙ i ] ≈ v x [ σ ] ∶[ j ] T [ σ ]
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

  data _⊢s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set where
    I-≈       : ⊢ Γ →
                --------------
                Γ ⊢s I ≈ I ∶ Γ
    wk-≈      : ∀ {i} →
                ⊢ (T ↙ i) ∷ Γ →
                --------------------------
                (T ↙ i) ∷ Γ ⊢s wk ≈ wk ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                ----------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Δ ⊢ T ∶[ 1 + i ] Se i →
                Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
                Γ ⊢ t ≈ t′ ∶[ i ] T [ σ ] →
                -----------------------------
                Γ ⊢s σ , t ∶ T ↙ i ≈ σ′ , t′ ∶ T′ ↙ i ∶ (T ↙ i) ∷ Δ
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
                Γ ⊢s (σ , t ∶ T ↙ i) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ↙ i ∶ (T ↙ i) ∷ Γ″
    p-,       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ →
                Γ ⊢ T ∶[ 1 + i ] Se i →
                Γ′ ⊢ t ∶[ i ] T [ σ ] →
                -------------------------
                Γ′ ⊢s p (σ , t ∶ T ↙ i) ≈ σ ∶ Γ
    ,-ext     : ∀ {i} →
                Γ′ ⊢s σ ∶ (T ↙ i) ∷ Γ →
                ----------------------------------
                Γ′ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ T ↙ i ∶ (T ↙ i) ∷ Γ
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

⊢p : ∀ {i} → ⊢ (T ↙ i) ∷ Δ → Γ ⊢s σ ∶ (T ↙ i) ∷ Δ → Γ ⊢s p σ ∶ Δ
⊢p ⊢TΔ ⊢σ = s-∘ ⊢σ (s-wk ⊢TΔ)
