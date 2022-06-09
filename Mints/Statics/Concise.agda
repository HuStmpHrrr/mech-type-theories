{-# OPTIONS --without-K --safe #-}

-- A formulation after removing certain redundant rules from the Full formulation
--
-- This formulation is the true and golden formulation of the type theory.
--
-- Once their equivalence is established, all properties of the full formulation will
-- also hold for this formulation.
module Mints.Statics.Concise where

open import Lib

open import Mints.Statics.Syntax public

infix 4 ⊢_ _⊢_ _⊢_∶_ _⊢s_∶_ _⊢_≈_∶_ _⊢_≈_ _⊢s_≈_∶_ ⊢_≈_

mutual
  -- well-formedness of context stacks
  data ⊢_ : Ctxs → Set where
    ⊢[] : ⊢ [] ∷ []
    ⊢κ  : ⊢ Γ →
          ----------
          ⊢ [] ∷⁺ Γ
    ⊢∺  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶ Se i →
          --------------
          ⊢ T ∺ Γ

  -- equivalence of context stacks
  --
  -- needed due to explicit substitutions
  data ⊢_≈_ : Ctxs → Ctxs → Set where
    []-≈   : ⊢ [] ∷ [] ≈ [] ∷ []
    κ-cong : ⊢ Γ ≈ Δ →
             -------------------
             ⊢ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
    ∺-cong : ∀ {i} →
             ⊢ Γ ≈ Δ →
             Γ ⊢ T ≈ T′ ∶ Se i →
             ----------------
             ⊢ T ∺ Γ ≈ T′ ∺ Δ

  -- typing judgment of terms
  data _⊢_∶_ : Ctxs → Exp → Typ → Set where
    N-wf    : ∀ i →
              ⊢ Γ →
              -------------
              Γ ⊢ N ∶ Se i
    Se-wf   : ∀ i →
              ⊢ Γ →
              ----------------
              Γ ⊢ Se i ∶ Se (1 + i)
    Π-wf    : ∀ {i} →
              Γ ⊢ S ∶ Se i →
              S ∺ Γ ⊢ T ∶ Se i →
              --------------------
              Γ ⊢ Π S T ∶ Se i
    □-wf    : ∀ {i} →
              [] ∷⁺ Γ ⊢ T ∶ Se i →
              --------------------
              Γ ⊢ □ T ∶ Se i
    vlookup : ∀ {x} →
              ⊢ Γ →
              x ∶ T ∈! Γ →
              ------------
              Γ ⊢ v x ∶ T
    ze-I    : ⊢ Γ →
              -----------
              Γ ⊢ ze ∶ N
    su-I    : Γ ⊢ t ∶ N →
              -------------
              Γ ⊢ su t ∶ N
    N-E     : ∀ {i} →
              N ∺ Γ ⊢ T ∶ Se i →
              Γ ⊢ s ∶ T [| ze ] →
              T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              Γ ⊢ t ∶ N →
              --------------------------
              Γ ⊢ rec T s r t ∶ T [| t ]
    Λ-I     : S ∺ Γ ⊢ t ∶ T →
              ------------------
              Γ ⊢ Λ t ∶ Π S T
    Λ-E     : Γ ⊢ r ∶ Π S T →
              Γ ⊢ s ∶ S →
              ---------------------
              Γ ⊢ r $ s ∶ T [| s ]
    □-I     : [] ∷⁺ Γ ⊢ t ∶ T →
              -----------------
              Γ ⊢ box t ∶ □ T
    □-E     : ∀ {n} Ψs →
              Γ ⊢ t ∶ □ T →
              ⊢ Ψs ++⁺ Γ →
              len Ψs ≡ n →
              -----------------------------------
              Ψs ++⁺ Γ ⊢ unbox n t ∶ T [ I ； n ]
    t[σ]    : Δ ⊢ t ∶ T →
              Γ ⊢s σ ∶ Δ →
              ---------------------
              Γ ⊢ t [ σ ] ∶ T [ σ ]
    cumu    : ∀ {i} →
              Γ ⊢ T ∶ Se i →
              ------------------
              Γ ⊢ T ∶ Se (1 + i)
    conv    : ∀ {i} →
              Γ ⊢ t ∶ S →
              Γ ⊢ S ≈ T ∶ Se i →
              ------------------
              Γ ⊢ t ∶ T

  -- typing judgments of (unified) substitutions
  data _⊢s_∶_ : Ctxs → Substs → Ctxs → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-wk   : ⊢ T ∺ Γ →
             ------------------
             T ∺ Γ ⊢s wk ∶ Γ
    s-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢ t ∶ T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ T ∺ Δ
    s-；    : ∀ {n} Ψs →
             Γ ⊢s σ ∶ Δ →
             ⊢ Ψs ++⁺ Γ →
             len Ψs ≡ n →
             -----------------------------
             Ψs ++⁺ Γ ⊢s σ ； n ∶ [] ∷⁺ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′

  -- equivalence of terms
  data _⊢_≈_∶_ : Ctxs → Exp → Exp → Typ → Set where
    N-[]       : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 -----------------------
                 Γ ⊢ N [ σ ] ≈ N ∶ Se i
    Se-[]      : ∀ i →
                 Γ ⊢s σ ∶ Δ →
                 ----------------------------------
                 Γ ⊢ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
    Π-[]       : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 S ∺ Δ ⊢ T ∶ Se i →
                 -------------------------------------------------
                 Γ ⊢ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
    □-[]       : ∀ {i} →
                 Γ ⊢s σ ∶ Δ →
                 [] ∷⁺ Δ ⊢ T ∶ Se i →
                 ---------------------------------------
                 Γ ⊢ □ T [ σ ] ≈ □ (T [ σ ； 1 ]) ∶ Se i
    Π-cong     : ∀ {i} →
                 Γ ⊢ S ≈ S′ ∶ Se i →
                 S ∺ Γ ⊢ T ≈ T′ ∶ Se i →
                 --------------------------
                 Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se i
    □-cong     : ∀ {i} →
                 [] ∷⁺ Γ ⊢ T ≈ T′ ∶ Se i →
                 --------------------------
                 Γ ⊢ □ T ≈ □ T′ ∶ Se i
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
                 N ∺ Γ ⊢ T ≈ T′ ∶ Se i →
                 Γ ⊢ s ≈ s′ ∶ T [ I , ze ] →
                 T ∺ N ∺ Γ ⊢ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ≈ t′ ∶ N →
                 --------------------------------------------
                 Γ ⊢ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
    Λ-cong     : S ∺ Γ ⊢ t ≈ t′ ∶ T →
                 -----------------------
                 Γ ⊢ Λ t ≈ Λ t′ ∶ Π S T
    $-cong     : Γ ⊢ r ≈ r′ ∶ Π S T →
                 Γ ⊢ s ≈ s′ ∶ S →
                 -------------------------------
                 Γ ⊢ r $ s ≈ r′ $ s′ ∶ T [| s ]
    box-cong   : [] ∷⁺ Γ ⊢ t ≈ t′ ∶ T →
                 ------------------------
                 Γ ⊢ box t ≈ box t′ ∶ □ T
    unbox-cong : ∀ {n} Ψs →
                 Γ ⊢ t ≈ t′ ∶ □ T →
                 ⊢ Ψs ++⁺ Γ →
                 len Ψs ≡ n →
                 ------------------------------------------------
                 Ψs ++⁺ Γ ⊢ unbox n t ≈ unbox n t′ ∶ T [ I ； n ]
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
                 N ∺ Δ ⊢ T ∶ Se i →
                 Δ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Δ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Δ ⊢ t ∶ N →
                 -----------------------------------------------------------------------------------------------
                 Γ ⊢ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]
    Λ-[]       : Γ ⊢s σ ∶ Δ →
                 S ∺ Δ ⊢ t ∶ T →
                 --------------------------------------------
                 Γ ⊢ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
    $-[]       : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ r ∶ Π S T →
                 Δ ⊢ s ∶ S →
                 ---------------------------------------------------------
                 Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
    box-[]     : Γ ⊢s σ ∶ Δ →
                 [] ∷⁺ Δ ⊢ t ∶ T →
                 ------------------------------------------------
                 Γ ⊢ box t [ σ ] ≈ box (t [ σ ； 1 ]) ∶ □ T [ σ ]
    unbox-[]   : ∀ {n} Ψs →
                 Δ ⊢ t ∶ □ T →
                 Γ ⊢s σ ∶ Ψs ++⁺ Δ →
                 len Ψs ≡ n →
                 --------------------------------------------------------------------------
                 Γ ⊢ unbox n t [ σ ] ≈ unbox (O σ n) (t [ σ ∥ n ]) ∶ T [ (σ ∥ n) ； O σ n ]
    rec-β-ze   : ∀ {i} →
                 N ∺ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 ---------------------------------------------
                 Γ ⊢ rec T s r ze ≈ s ∶ T [| ze ]
    rec-β-su   : ∀ {i} →
                 N ∺ Γ ⊢ T ∶ Se i →
                 Γ ⊢ s ∶ T [| ze ] →
                 T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
                 Γ ⊢ t ∶ N →
                 -----------------------------------------------------------------
                 Γ ⊢ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
    Λ-β        : S ∺ Γ ⊢ t ∶ T →
                 Γ ⊢ s ∶ S →
                 ----------------------------------
                 Γ ⊢ Λ t $ s ≈ t [| s ] ∶ T [| s ]
    Λ-η        : Γ ⊢ t ∶ Π S T →
                 ----------------------------------
                 Γ ⊢ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
    □-β        : ∀ {n} Ψs →
                 [] ∷⁺ Γ ⊢ t ∶ T →
                 ⊢ Ψs ++⁺ Γ →
                 len Ψs ≡ n →
                 --------------------------------------------------------
                 Ψs ++⁺ Γ ⊢ unbox n (box t) ≈ t [ I ； n ] ∶ T [ I ； n ]
    □-η        : Γ ⊢ t ∶ □ T →
                 ------------------------------
                 Γ ⊢ t ≈ box (unbox 1 t) ∶ □ T
    [I]        : Γ ⊢ t ∶ T →
                 --------------------
                 Γ ⊢ t [ I ] ≈ t ∶ T
    [wk]       : ∀ {x} →
                 ⊢ S ∺ Γ →
                 x ∶ T ∈! Γ →
                 ---------------------------------------------------
                 S ∺ Γ ⊢ v x [ wk ] ≈ v (suc x) ∶ T [ wk ]
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
                 Γ ⊢ v 0 [ σ , s ] ≈ s ∶ S [ σ ]
    [,]-v-su   : ∀ {i x} →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ S ∶ Se i →
                 Γ ⊢ s ∶ S [ σ ] →
                 x ∶ T ∈! Δ →
                 ---------------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]
    ≈-cumu     : ∀ {i} →
                 Γ ⊢ T ≈ T′ ∶ Se i →
                 -----------------------
                 Γ ⊢ T ≈ T′ ∶ Se (1 + i)
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

  -- equivalence of types
  data _⊢s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set where
    I-≈       : ⊢ Γ →
                --------------
                Γ ⊢s I ≈ I ∶ Γ
    wk-≈      : ⊢ T ∺ Γ →
                --------------------------
                T ∺ Γ ⊢s wk ≈ wk ∶ Γ
    ∘-cong    : Γ ⊢s τ ≈ τ′ ∶ Γ′ →
                Γ′ ⊢s σ ≈ σ′ ∶ Γ″ →
                ----------------
                Γ ⊢s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
    ,-cong    : ∀ {i} →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                Δ ⊢ T ∶ Se i →
                Γ ⊢ t ≈ t′ ∶ T [ σ ] →
                -----------------------------
                Γ ⊢s σ , t ≈ σ′ , t′ ∶ T ∺ Δ
    ；-cong    : ∀ {n} Ψs →
                Γ ⊢s σ ≈ σ′ ∶ Δ →
                ⊢ Ψs ++⁺ Γ →
                len Ψs ≡ n →
                --------------------------------------
                Ψs ++⁺ Γ ⊢s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Δ
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
                Γ ⊢s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∺ Γ″
    ；-∘       : ∀ {n} Ψs →
                Γ′ ⊢s σ ∶ Γ″ →
                Γ ⊢s τ ∶ Ψs ++⁺ Γ′ →
                len Ψs ≡ n →
                ------------------------------
                Γ ⊢s σ ； n ∘ τ ≈ (σ ∘ τ ∥ n) ； O τ n ∶ [] ∷⁺ Γ″
    p-,       : ∀ {i} →
                Γ′ ⊢s σ ∶ Γ →
                Γ ⊢ T ∶ Se i →
                Γ′ ⊢ t ∶ T [ σ ] →
                -------------------------
                Γ′ ⊢s p (σ , t) ≈ σ ∶ Γ
    ,-ext     : Γ′ ⊢s σ ∶ T ∺ Γ →
                ----------------------------------
                Γ′ ⊢s σ ≈ p σ , v 0 [ σ ] ∶ T ∺ Γ
    ；-ext     : Γ ⊢s σ ∶ [] ∷⁺ Δ →
                -----------------------------------
                Γ ⊢s σ ≈ (σ ∥ 1) ； O σ 1 ∶ [] ∷⁺ Δ
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

_⊢_ : Ctxs → Typ → Set
Γ ⊢ T = ∃ λ i → Γ ⊢ T ∶ Se i

_⊢_≈_ : Ctxs → Exp → Exp → Set
Γ ⊢ S ≈ T = ∃ λ i → Γ ⊢ S ≈ T ∶ Se i

⊢p : ⊢ T ∺ Δ → Γ ⊢s σ ∶ T ∺ Δ → Γ ⊢s p σ ∶ Δ
⊢p ⊢TΔ ⊢σ = s-∘ ⊢σ (s-wk ⊢TΔ)

p-cong : ⊢ T ∺ Δ → Γ ⊢s σ ≈ σ′ ∶ T ∺ Δ → Γ ⊢s p σ ≈ p σ′ ∶ Δ
p-cong ⊢TΔ σ≈σ′ = ∘-cong σ≈σ′ (wk-≈ ⊢TΔ)