{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Unascribed.Full where

open import Lib

open import NonCumulative.Statics.Unascribed.Syntax public

infix 4 ⊢_ _⊢_ _⊢_∶_ _⊢s_∶_ _⊢_≈_∶_ _⊢_≈_ _⊢s_≈_∶_ ⊢_≈_

variable
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx
  Ψ Ψ′ Ψ″ : Ctx

mutual
  data ⊢_ : Ctx → Set where
    ⊢[] : ⊢ []
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶ Se i →
          --------------
          ⊢ T ∷ Γ

  data ⊢_≈_ : Ctx → Ctx → Set where
    []-≈   : ⊢ [] ≈ []
    ∷-cong : ∀ {i} →
             ⊢ Γ ≈ Δ →
             Γ ⊢ T ∶ Se i →      -- remove after presupposition
             Δ ⊢ T′ ∶ Se i →     -- remove after presupposition
             Γ ⊢ T ≈ T′ ∶ Se i →
             Δ ⊢ T ≈ T′ ∶ Se i → -- remove after presupposition
             ----------------
             ⊢ T ∷ Γ ≈ T′ ∷ Δ

  data _⊢_∶_ : Ctx → Exp → Typ → Set where
    N-wf     : ⊢ Γ →
               -------------
               Γ ⊢ N ∶ Se 0
    Se-wf    : ∀ i →
               ⊢ Γ →
               ----------------
               Γ ⊢ Se i ∶ Se (1 + i)
    Liftt-wf : ∀ {i} n →
               Γ ⊢ T ∶ Se i →
               -------------------------
               Γ ⊢ Liftt n T ∶ Se (n + i)
    Π-wf     : ∀ {i j k} →
               ⊢ Γ → 
               Γ ⊢ S ∶ Se i →
               S ∷ Γ ⊢ T ∶ Se j →
               k ≡ max i j →
               --------------------
               Γ ⊢ Π S T ∶ Se k
    vlookup  : ∀ {x} →
               ⊢ Γ →
               x ∶ T ∈! Γ →
               ------------
               Γ ⊢ v x ∶ T
    ze-I     : ⊢ Γ →
               -----------
               Γ ⊢ ze ∶ N
    su-I     : Γ ⊢ t ∶ N →
               -------------
               Γ ⊢ su t ∶ N
    N-E      : ∀ {i} →
               ⊢ Γ →
               N ∷ Γ ⊢ T ∶ Se i →
               Γ ⊢ s ∶ T [| ze ∶ N ] →
               T ∷ N ∷ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ∶ N ] →
               Γ ⊢ t ∶ N →
               --------------------------
               Γ ⊢ rec T s r t ∶ T [| t ∶ N ]
    Λ-I      : ∀ {i} →
               ⊢ Γ →   -- ** new
               Γ ⊢ S ∶ Se i →    -- remove after presupposition
               S ∷ Γ ⊢ t ∶ T →
               ------------------
               Γ ⊢ Λ S t ∶ Π S T
    Λ-E      : ∀ {i j} →
               -- expose typing judgments for soundness proof
               ⊢ Γ →
               Γ ⊢ S ∶ Se i →
               S ∷ Γ ⊢ T ∶ Se j →
               Γ ⊢ r ∶ Π S T →
               Γ ⊢ s ∶ S →
               ---------------------
               Γ ⊢ r $ s ∶ T [| s ∶ S ]
    L-I      : ∀ n →
               Γ ⊢ t ∶ T →
               -------------------------
               Γ ⊢ liftt n t ∶ Liftt n T
    L-E      : ∀ {i} n →
               ⊢ Γ → 
               Γ ⊢ T ∶ Se i →
               Γ ⊢ t ∶ Liftt n T →
               --------------------
               Γ ⊢ unlift t ∶ T
    t[σ]     : ⊢ Δ →
               Δ ⊢ t ∶ T →
               Γ ⊢s σ ∶ Δ →
               ---------------------
               Γ ⊢ t [ σ ] ∶ T [ σ ]
    conv     : ∀ {i} →
               ⊢ Γ →
               Γ ⊢ t ∶ S →
               Γ ⊢ S ∶ Se i → 
               Γ ⊢ S ≈ T ∶ Se i →
               ------------------
               Γ ⊢ t ∶ T

  data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-wk   : ⊢ T ∷ Γ →
             ------------------
             T ∷ Γ ⊢s wk ∶ Γ
    s-∘    : ⊢ Γ′ → 
             Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             ⊢ Γ →
             ⊢ Δ →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢ t ∶ T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ T  ∶ T ∷ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′

  data _⊢_≈_∶_ : Ctx → Exp → Exp → Typ → Set where
    N-[]       : Γ ⊢s σ ∶ Δ →
                 -----------------------
                 Γ ⊢ N [ σ ] ≈ N ∶ Se 0
    Se-[]      : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 ----------------------------------
                 Γ ⊢ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
    Liftt-[]   : ∀ {i} n →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ T ∶ Se i →
                 ----------------------------------------------------
                 Γ ⊢ Liftt n T [ σ ] ≈ Liftt n (T [ σ ]) ∶ Se (n + i)
    Π-[]       : ∀ {i j k} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 S ∷ Δ ⊢ T ∶ Se j →
                 k ≡ max i j →
                 -------------------------------------------------
                 Γ ⊢ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q S σ ]) ∶ Se k
    Π-cong     : ∀ {i j k} →
                 Γ ⊢ S ∶ Se i →   -- remove after presupposition
                 Γ ⊢ S ≈ S′ ∶ Se i →
                 S ∷ Γ ⊢ T ≈ T′ ∶ Se j →
                 k ≡ max i j →
                 --------------------------
                 Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se k
    Liftt-cong : ∀ {i} n →
                 Γ ⊢ T ≈ T′ ∶ Se i →
                 ----------------------------------------------------
                 Γ ⊢ Liftt n T ≈ Liftt n T′ ∶ Se (n + i)
    v-≈        : ∀ {x} →
                 ⊢ Γ →
                 x ∶ T ∈! Γ →
                 -----------------
                 Γ ⊢ v x ≈ v x ∶ T
    ze-≈       : ⊢ Γ →
                 ----------------
                 Γ ⊢ ze ≈ ze ∶ N
    su-cong    : Γ ⊢ t ≈ t′ ∶ N →
                 --------- ------------
                 Γ ⊢ su t ≈ su t′ ∶ N
    rec-cong   : ∀ {i} →
                 N ∷ Γ ⊢ T ∶ Se i → -- remove after presupposition
                 N ∷ Γ ⊢ T ≈ T′ ∶ Se i →
                 Γ ⊢ s ≈ s′ ∶ T [ I , ze ∶ N ] →
                 T ∷ N ∷ Γ ⊢ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ∶ N ] →
                 Γ ⊢ t ≈ t′ ∶ N →
                 --------------------------------------------
                 Γ ⊢ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ∶ N ]
    Λ-cong     : ∀ {i} →
                 ⊢ Γ →
                 Γ ⊢ S ∶ Se i →   -- remove after presupposition
                 Γ ⊢ S ≈ S′ ∶ Se i →
                 S ∷ Γ ⊢ t ≈ t′ ∶ T →
                 -----------------------
                 Γ ⊢ Λ S t ≈ Λ S′ t′ ∶ Π S T
    $-cong     : ∀ {i j} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶ Se i →
                 S ∷ Γ ⊢ T ∶ Se j →
                 Γ ⊢ r ≈ r′ ∶ Π S T →
                 Γ ⊢ s ≈ s′ ∶ S →
                 -------------------------------
                 Γ ⊢ r $ s ≈ r′ $ s′ ∶ T [| s ∶ S ]
    liftt-cong : ∀ n →
                 Γ ⊢ t ≈ t′ ∶ T →
                 ------------------------------------
                 Γ ⊢ liftt n t ≈ liftt n t′ ∶ Liftt n T
    unlift-cong : ∀ {i} n →
                 Γ ⊢ T ∶ Se i →
                 Γ ⊢ t ≈ t′ ∶ Liftt n T →
                 --------------------
                 Γ ⊢ unlift t ≈ unlift t′ ∶ T
    []-cong    : Δ ⊢ t ≈ t′ ∶ T →
                 Γ ⊢s σ ≈ σ′ ∶ Δ →
                 ---------------------------------
                 Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ T [ σ ]
    ze-[]      : Γ ⊢s σ ∶ Δ →
                 ----------------------
                 Γ ⊢ ze [ σ ] ≈ ze ∶ N
    su-[]      : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ N →
                 ----------------------------------
                 Γ ⊢ su t [ σ ] ≈ su (t [ σ ]) ∶ N
    rec-[]     : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 N ∷ Δ ⊢ T ∶ Se i →
                 Δ ⊢ s ∶ T [| ze ∶ N ] →
                 T ∷ N ∷ Δ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ∶ N ] →
                 Δ ⊢ t ∶ N →
                 -----------------------------------------------------------------------------------------------
                 Γ ⊢ rec T s r t [ σ ] ≈ rec (T [ q N σ ]) (s [ σ ]) (r [ q T (q N σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ∶ N ]
    Λ-[]       : ∀ {i} → 
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 S ∷ Δ ⊢ t ∶ T →
                 --------------------------------------------
                 Γ ⊢ Λ S t [ σ ] ≈ Λ (S [ σ ]) (t [ q S σ ]) ∶ Π S T [ σ ]
    $-[]       : ∀ {i j} →
                 -- expose typing judgments for soundness proof
                 Δ ⊢ S ∶ Se i →
                 S ∷ Δ ⊢ T ∶ Se j →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ r ∶ Π S T →
                 Δ ⊢ s ∶ S →
                 ---------------------------------------------------------
                 Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ∶ S ]
    liftt-[]   : ∀ {i} n →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ T ∶ Se i →
                 Δ ⊢ t ∶ T →
                 --------------------------------------
                 Γ ⊢ liftt n t [ σ ] ≈ liftt n (t [ σ ]) ∶ Liftt n T [ σ ]
    unlift-[]  : ∀ {i} n →
                 Δ ⊢ T ∶ Se i →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ Liftt n T →
                 ---------------------------------------
                 Γ ⊢ unlift t [ σ ] ≈ unlift (t [ σ ]) ∶ T [ σ ]
    rec-β-ze   : ∀ {i} →
                 N ∷ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ∶ N ] →
                 T ∷ N ∷ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ∶ N ] →
                 ---------------------------------------------
                 Γ ⊢ rec T s r ze ≈ s ∶ T [| ze ∶ N ]
    rec-β-su   : ∀ {i} →
                 N ∷ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ∶ N ] →
                 T ∷ N ∷ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ∶ N ] →
                 Γ ⊢ t ∶ N →
                 -----------------------------------------------------------------
                 Γ ⊢ rec T s r (su t) ≈ r [ (I , t ∶ N ) , rec T s r t ∶ T  ] ∶ T [| su t ∶ N ]
    Λ-β        : ∀ {i j} →
                 Γ ⊢ S ∶ Se i →   -- remove after presupposition
                 -- expose typing judgments for soundness proof
                 S ∷ Γ ⊢ T ∶ Se j →
                 S ∷ Γ ⊢ t ∶ T →
                 Γ ⊢ s ∶ S →
                 ----------------------------------
                 Γ ⊢ Λ S t $ s ≈ t [| s ∶ S ] ∶ T [| s ∶ S ]
    Λ-η        : ∀ {i j} →
                 -- expose typing judgments for soundness proof
                 Γ ⊢ S ∶ Se i →
                 S ∷ Γ ⊢ T ∶ Se j →
                 Γ ⊢ t ∶ Π S T →
                 ----------------------------------
                 Γ ⊢ t ≈ Λ S (t [ wk ] $ v 0) ∶ Π S T
    L-β        : ∀ n →
                 Γ ⊢ t ∶ T →
                 -----------------------------
                 Γ ⊢ unlift (liftt n t) ≈ t ∶ T
    L-η        : ∀ {i} n →
                 Γ ⊢ T ∶ Se i →
                 Γ ⊢ t ∶ Liftt n T →
                 -----------------------------
                 Γ ⊢ t ≈ liftt n (unlift t) ∶ Liftt n T
    [I]        : Γ ⊢ t ∶ T →
                 --------------------
                 Γ ⊢ t [ I ] ≈ t ∶ T
    [wk]       : ∀ {x} →
                 ⊢ S ∷ Γ →
                 x ∶ T ∈! Γ →
                 ---------------------------------------------------
                 S ∷ Γ ⊢ v x [ wk ] ≈ v (suc x) ∶ T [ wk ]
    [∘]        : Γ ⊢s τ ∶ Γ′ →
                 Γ′ ⊢s σ ∶ Γ″ →
                 Γ″ ⊢ t ∶ T →
                 ---------------------------------------------
                 Γ ⊢ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T [ σ ∘ τ ]
    [,]-v-ze   : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 Γ ⊢ s ∶ S [ σ ] →
                 --------------------------------
                 Γ ⊢ v 0 [ σ , s ∶ S ] ≈ s ∶ S [ σ ]
    [,]-v-su   : ∀ {i x} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 Γ ⊢ s ∶ S [ σ ] →
                 x ∶ T ∈! Δ →
                 ---------------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ∶ S ] ≈ v x [ σ ] ∶ T [ σ ]
    ≈-conv     : ∀ {i} →
                 Γ ⊢ s ≈ t ∶ S →
                 Γ ⊢ S ≈ T ∶ Se i →
                 --------------------
                 Γ ⊢ s ≈ t ∶ T
    ≈-sym      : Γ ⊢ t ≈ t′ ∶ T →
                 ----------------
                 Γ ⊢ t′ ≈ t ∶ T
    ≈-trans    : Γ ⊢ t ≈ t′ ∶ T →
                 Γ ⊢ t′ ≈ t″ ∶ T →
                 ------ ------------
                 Γ ⊢ t ≈ t″ ∶ T

  data _⊢s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set where
    I-≈       : ⊢ Γ →
                --------------
                Γ ⊢s I ≈ I ∶ Γ
    wk-≈      : ⊢ T ∷ Γ →
                --------------------------
                T ∷ Γ ⊢s wk ≈ wk ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                ----------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Δ ⊢ T ∶ Se i →
                Δ ⊢ T ≈ T′ ∶ Se i →
                Γ ⊢ t ≈ t′ ∶ T [ σ ] →
                -----------------------------
                Γ ⊢s σ , t ∶ T ≈ σ′ , t′ ∶ T′ ∶ T ∷ Δ
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
                Γ″ ⊢ T ∶ Se i →
                Γ′ ⊢ t ∶ T [ σ ] →
                Γ ⊢s τ ∶ Γ′ →
                ---------------------------------------------
                Γ ⊢s (σ , t ∶ T) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∶ T ∷ Γ″
    p-,       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ →
                Γ ⊢ T ∶ Se i →
                Γ′ ⊢ t ∶ T [ σ ] →
                -------------------------
                Γ′ ⊢s p (σ , t ∶ T) ≈ σ ∶ Γ
    ,-ext     : Γ′ ⊢s σ ∶ T ∷ Γ →
                ----------------------------------
                Γ′ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ T ∶ T ∷ Γ
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

_⊢_ : Ctx → Typ → Set
Γ ⊢ T = ∃ λ i → Γ ⊢ T ∶ Se i

_⊢_≈_ : Ctx → Exp → Exp → Set
Γ ⊢ S ≈ T = ∃ λ i → Γ ⊢ S ≈ T ∶ Se i

-- ⊢p : ⊢ T ∷ Δ → Γ ⊢s σ ∶ T ∷ Δ → Γ ⊢s p σ ∶ Δ
-- ⊢p ⊢TΔ ⊢σ = s-∘ (proj₂ {! presup-s  !}) ⊢σ (s-wk ⊢TΔ)
