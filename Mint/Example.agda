{-# OPTIONS --without-K --guardedness #-}

-- This module is meant to be executed after compiled into Haskell by agda.
-- How To Execute:
--   1. run `agda -c Example.agda --compile-dir=out --ghc-flag="-Wno-overlapping-patterns"`
--   2. run `out/Example`
--
module Mint.Example where

open import Axiom.Extensionality.Propositional

postulate
  fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

open import Lib
open import LibNonEmpty
open import Mint.Statics
open import Mint.Statics.Properties
open import Mint.Completeness fext

------------------------------------------------------------
-- Type of Examples : Triple of a term, type, and
-- typing derivation for the term under a given well-formed context

Example = ∀ {Γ} → ⊢ Γ → ∃ λ t → ∃ λ T → Γ ⊢ t ∶ T

------------------------------------------------------------
-- Helper functions to define examples

ε : Ctxs
ε = List⁺.[ [] ]

⊢ε : ⊢ ε
⊢ε = ⊢[]

[N⟶N][]≈N⟶N : ∀ {i} →
              Γ ⊢s σ ∶ Δ →
              Γ ⊢ (N ⟶ N) [ σ ] ≈ N ⟶ N ∶ Se i
[N⟶N][]≈N⟶N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ≈-trans
                                 (Π-[]
                                   ⊢σ
                                   (N-wf _ ⊢Δ)
                                   (t[σ]-Se (N-wf _ ⊢Δ) (s-wk ⊢NΔ)))
                                 (Π-cong
                                   (N-[] _ ⊢σ)
                                   (≈-trans
                                     ([]-cong-Se′ (N-[] _ (s-wk ⊢NΔ)) (⊢q ⊢σ (N-wf 0 ⊢Δ)))
                                     (≈-trans (N-[] _ (⊢q ⊢σ (N-wf 0 ⊢Δ))) (≈-sym (N-[] _ (s-wk ⊢N[σ]Γ))))))
  where
    ⊢NΔ = ⊢∺ ⊢Δ (N-wf 0 ⊢Δ)
    ⊢N[σ]Γ = ⊢∺ ⊢Γ (t[σ]-Se (N-wf 0 ⊢Δ) ⊢σ)

N⟶N≈ΠNN : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ N ⟶ N ≈ Π N N ∶ Se i
N⟶N≈ΠNN ⊢Γ = Π-cong (≈-refl (N-wf _ ⊢Γ)) (N-[] _ (s-wk (⊢∺ ⊢Γ (N-wf 0 ⊢Γ))))

[□N][]≈□N : ∀ {i} →
            Γ ⊢s σ ∶ Δ →
            Γ ⊢ (□ N) [ σ ] ≈ □ N ∶ Se i
[□N][]≈□N ⊢σ
  with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ≈-trans (□-[] ⊢σ (N-wf _ (⊢κ ⊢Δ))) (□-cong (N-[] _ (s-； ([] ∷ []) ⊢σ (⊢κ ⊢Γ) refl)))

T[wk][|s]≈T : ∀ {i} →
              Γ ⊢ T ∶ Se i →
              Γ ⊢ s ∶ S →
              Γ ⊢ T [ wk ] [| s ] ≈ T ∶ Se i
T[wk][|s]≈T {T = T} {s} {S} ⊢T ⊢s
  with ⊢Γ , _ , ⊢S ← presup-tm ⊢s = ER.begin
    T [ wk ] [| s ]                 ER.≈⟨ [∘]-Se ⊢T (s-wk (⊢∺ ⊢Γ ⊢S)) (⊢I,t ⊢s) ⟩
    T [ wk ∘ (I , s) ]              ER.≈⟨ []-cong-Se″ ⊢T (p-, (s-I ⊢Γ) ⊢S (conv ⊢s (≈-sym ([I] ⊢S)))) ⟩
    T [ I ]                         ER.≈⟨ [I] ⊢T ⟩
    T                               ER.∎

Λ-E-⟶ : ∀ {i} →
        Γ ⊢ T ∶ Se i →
        Γ ⊢ r ∶ S ⟶ T →
        Γ ⊢ s ∶ S →
        Γ ⊢ r $ s ∶ T
Λ-E-⟶ ⊢T ⊢r ⊢s = conv (Λ-E ⊢r ⊢s) (T[wk][|s]≈T ⊢T ⊢s)

$-[]-⟶ : ∀ {i} →
         Γ ⊢s σ ∶ Δ →
         Δ ⊢ T ∶ Se i →
         Δ ⊢ r ∶ S ⟶ T →
         Δ ⊢ s ∶ S →
         Γ ⊢ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ ]
$-[]-⟶ {σ = σ} {T = T} {r} {s = s} ⊢σ ⊢T ⊢r ⊢s
  with ⊢Δ , _ , ⊢S ← presup-tm ⊢s = ≈-conv ($-[] ⊢σ ⊢r ⊢s) (ER.begin
    T [ wk ] [ σ , s [ σ ] ] ER.≈˘⟨ []-I,-∘ (t[σ]-Se ⊢T (s-wk (⊢∺ ⊢Δ ⊢S))) ⊢σ ⊢s ⟩
    T [ wk ] [| s ] [ σ ] ER.≈⟨ []-cong-Se′ (T[wk][|s]≈T ⊢T ⊢s) ⊢σ ⟩
    T [ σ ] ER.∎)

$-cong-⟶ : ∀ {i} →
           Γ ⊢ T ∶ Se i →
           Γ ⊢ r ≈ r′ ∶ S ⟶ T →
           Γ ⊢ s ≈ s′ ∶ S →
           -------------------------------
           Γ ⊢ r $ s ≈ r′ $ s′ ∶ T
$-cong-⟶ ⊢T r≈ s≈
  with _ , ⊢s , _ ← presup-≈ s≈ = ≈-conv ($-cong r≈ s≈) (T[wk][|s]≈T ⊢T ⊢s)

of-n : ℕ → Exp
of-n 0       = ze
of-n (suc n) = su (of-n n)

⊢of-n : (n : ℕ) → ⊢ Γ → Γ ⊢ of-n n ∶ N
⊢of-n 0       ⊢Γ = ze-I ⊢Γ
⊢of-n (suc n) ⊢Γ = su-I (⊢of-n n ⊢Γ)

------------------------------------------------------------
-- Examples

-- In a more readable syntax, this corresponds to
--
--   example0 : Nat
--   example0 = (λ x → succ x) zero
--
example0 : Example
example0 ⊢Γ = (Λ (su (v 0))) $ ze
            , N
            , conv
                (Λ-E
                  (Λ-I (su-I (⊢vn∶N [] (⊢∺ ⊢Γ (N-wf 0 ⊢Γ)) refl)))
                  (ze-I ⊢Γ))
                (N-[] 0 (⊢I,ze ⊢Γ))

-- In a more readable syntax, this corresponds to
--
--   lift : Nat → □ Nat
--   lift zero     = box (zero)
--   lift (succ n) = box (succ (unbox1 (lift n)))
--
mints-lift : Example
mints-lift ⊢Γ = Λ (rec (□ N) (box ze) (box (su (unbox 1 (v 0)))) (v 0))
              , N ⟶ □ N
              , Λ-I
                  (conv
                    (N-E
                      (□-wf (N-wf 0 ⊢；NNΓ))
                      (conv (□-I (ze-I ⊢；NΓ)) (≈-sym ([□N][]≈□N {i = 0} (⊢I,ze ⊢NΓ))))
                      (conv
                        (□-I
                          (su-I
                            (conv
                              (□-E ([] ∷ []) (conv (vlookup ⊢□NNNΓ here) ([□N][]≈□N {i = 0} □NNNΓ⊢wk)) ⊢；□NNNΓ refl)
                              ([I；1] (N-wf 0 ⊢；□NNNΓ)))))
                        (≈-sym ([□N][]≈□N {i = 0} (⊢[wk∘wk],su[v1] ⊢□NNNΓ))))
                      NΓ⊢v0)
                    (≈-trans ([□N][]≈□N {i = 0} (⊢I,t NΓ⊢v0)) (≈-sym ([□N][]≈□N NΓ⊢wk))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢；NΓ = ⊢κ ⊢NΓ
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢；NNΓ = ⊢κ ⊢NNΓ
    ⊢□NNNΓ = ⊢∺ ⊢NNΓ (□-wf (N-wf 0 ⊢；NNΓ))
    ⊢；□NNNΓ = ⊢κ ⊢□NNNΓ

    NΓ⊢v0 = ⊢vn∶N [] ⊢NΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    □NNNΓ⊢wk = s-wk ⊢□NNNΓ

-- In a more readable syntax, this corresponds to
--
--   _+_ : Nat → Nat → Nat
--   _+_ zero     m = m
--   _+_ (succ n) m = succ (n + m)
--
mints-+ : Example
mints-+ ⊢Γ = Λ
               (Λ
                 (rec
                   N
                   (v 0)
                   (su (v 0))
                   (v 1)))
           , N ⟶ N ⟶ N
           , Λ-I
               (conv
                 (Λ-I
                   (conv
                     (N-E
                       (N-wf 0 ⊢NNNΓ)
                       (conv (⊢vn∶N [] ⊢NNΓ refl) (≈-sym (N-[] 0 (⊢I,ze ⊢NNΓ))))
                       (conv
                         (su-I (⊢vn∶N [] ⊢NNNNΓ refl))
                         (≈-sym (N-[] 0 (⊢[wk∘wk],su[v1] ⊢NNNNΓ))))
                       (⊢vn∶N (N ∷ []) ⊢NNΓ refl))
                     (N-[] 0 (⊢I,t (⊢vn∶N (N ∷ []) ⊢NNΓ refl)))))
                 (≈-sym (≈-trans ([N⟶N][]≈N⟶N {i = 0} NΓ⊢wk) (N⟶N≈ΠNN ⊢NΓ))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢NNNΓ = ⊢∺ ⊢NNΓ (N-wf 0 ⊢NNΓ)
    ⊢NNNNΓ = ⊢∺ ⊢NNNΓ (N-wf 0 ⊢NNNΓ)

    NΓ⊢wk = s-wk ⊢NΓ

-- In a more readable syntax, this corresponds to
--
--   _*_ : Nat → Nat → Nat
--   _*_ zero     m = zero
--   _*_ (succ n) m = m + (n * m)
--
mints-* : Example
mints-* ⊢Γ = Λ
               (Λ
                 (rec
                   N
                   ze
                   ((proj₁ (mints-+ ⊢NNNNΓ) $ v 0) $ v 2)
                   (v 1)))
           , N ⟶ N ⟶ N
           , Λ-I
               (conv
                 (Λ-I
                   (conv
                     (N-E
                       (N-wf 0 ⊢NNNΓ)
                       (conv (ze-I ⊢NNΓ) (≈-sym (N-[] 0 (⊢I,ze ⊢NNΓ))))
                       (conv
                         (Λ-E-⟶
                           (N-wf 0 ⊢NNNNΓ)
                           (Λ-E-⟶ NNNNΓ⊢N⟶N (proj₂ (proj₂ (mints-+ ⊢NNNNΓ))) NNNNΓ⊢v0)
                           NNNNΓ⊢v2)
                         (≈-sym (N-[] 0 (⊢[wk∘wk],su[v1] ⊢NNNNΓ))))
                       (⊢vn∶N (N ∷ []) ⊢NNΓ refl))
                     (N-[] 0 (⊢I,t (⊢vn∶N (N ∷ []) ⊢NNΓ refl)))))
                 (≈-sym (≈-trans ([N⟶N][]≈N⟶N {i = 0} NΓ⊢wk) (N⟶N≈ΠNN ⊢NΓ))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢NNNΓ = ⊢∺ ⊢NNΓ (N-wf 0 ⊢NNΓ)
    ⊢NNNNΓ = ⊢∺ ⊢NNNΓ (N-wf 0 ⊢NNNΓ)
    ⊢NNNNNΓ = ⊢∺ ⊢NNNNΓ (N-wf 0 ⊢NNNNΓ)

    NNNNΓ⊢v0 = ⊢vn∶N [] ⊢NNNNΓ refl
    NNNNΓ⊢v2 = ⊢vn∶N (N ∷ N ∷ []) ⊢NNNNΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNNNNΓ⊢wk = s-wk ⊢NNNNNΓ

    NNNNΓ⊢N⟶N = Π-wf (N-wf 0 ⊢NNNNΓ) (t[σ]-Se (N-wf 0 ⊢NNNNΓ) NNNNNΓ⊢wk)

-- In a more readable syntax, this corresponds to
--
--   pow : Nat → □ (Nat → Nat)
--   pow zero     = box (λ x → succ zero)
--   pow (succ n) = box (λ x → ((unbox1 (pow n)) x) * x)
--
mints-pow : Example
mints-pow ⊢Γ = Λ
                 (rec
                   (□ (N ⟶ N))
                   (box (Λ (su ze)))
                   (box (Λ ((proj₁ (mints-* ⊢N；□[N⟶N]NNΓ) $ (unbox 1 (v 0) $ v 0)) $ v 0)))
                   (v 0))
             , N ⟶ □ (N ⟶ N)
             , Λ-I
                 (conv
                   (N-E
                     (□-wf ；NNΓ⊢N⟶N)
                     (conv
                       (□-I (Λ-I (su-I (ze-I (⊢∺ ⊢；NΓ (N-wf 0 ⊢；NΓ))))))
                       (≈-sym
                         (≈-trans
                           (□-[] (⊢I,ze ⊢NΓ) ；NNΓ⊢N⟶N)
                           (□-cong
                             (≈-trans
                               ([N⟶N][]≈N⟶N (s-； ([] ∷ []) (⊢I,ze ⊢NΓ) ⊢；NΓ refl))
                               (N⟶N≈ΠNN ⊢；NΓ))))))
                     (conv
                       (□-I
                         (Λ-I
                           (Λ-E-⟶
                             (N-wf 0 ⊢N；□[N⟶N]NNΓ)
                             (Λ-E-⟶ N；□[N⟶N]NNΓ⊢N⟶N (proj₂ (proj₂ (mints-* ⊢N；□[N⟶N]NNΓ))) ；□[N⟶N]NNΓ⊢unbox1[v0]$v0)
                             N；□[N⟶N]NNΓ⊢v0)))
                       (≈-sym
                         (≈-trans
                           (□-[] □[N⟶N]NNΓ⊢[wk∘wk],su[v1] ；NNΓ⊢N⟶N)
                           (□-cong
                             (≈-trans
                               ([N⟶N][]≈N⟶N ；□[N⟶N]NNΓ⊢[wk∘wk],su[v1]；1)
                               (N⟶N≈ΠNN ⊢；□[N⟶N]NNΓ))))))
                     NΓ⊢v0)
                   (ER.begin
                    □ (N ⟶ N) [| v 0 ]            ER.≈⟨ □-[] (⊢I,t NΓ⊢v0) ；NNΓ⊢N⟶N ⟩
                    □ ((N ⟶ N) [ (I , v 0) ； 1 ]) ER.≈⟨ □-cong
                                                          (ER.begin
                                                           _     ER.≈⟨ [N⟶N][]≈N⟶N (s-； ([] ∷ []) (⊢I,t NΓ⊢v0) ⊢；NΓ refl) ⟩
                                                           N ⟶ N ER.≈˘⟨ [N⟶N][]≈N⟶N (s-； ([] ∷ []) NΓ⊢wk ⊢；NΓ refl) ⟩
                                                           _     ER.∎) ⟩
                    □ ((N ⟶ N) [ wk ； 1 ])        ER.≈˘⟨ □-[] NΓ⊢wk ；Γ⊢N⟶N ⟩
                    □ (N ⟶ N) [ wk ]              ER.∎))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢；Γ = ⊢κ ⊢Γ
    ⊢；NΓ = ⊢κ ⊢NΓ
    ⊢；NNΓ = ⊢κ ⊢NNΓ
    ⊢N；NNΓ = ⊢∺ ⊢；NNΓ (N-wf 0 ⊢；NNΓ)

    NΓ⊢v0 = ⊢vn∶N [] ⊢NΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNΓ⊢wk = s-wk ⊢NNΓ
    N；Γ⊢wk = s-wk (⊢∺ ⊢；Γ (N-wf 0 ⊢；Γ))
    N；NNΓ⊢wk = s-wk ⊢N；NNΓ

    ；Γ⊢N⟶N = Π-wf (N-wf 0 ⊢；Γ) (t[σ]-Se (N-wf 0 ⊢；Γ) N；Γ⊢wk)
    ；NNΓ⊢N⟶N = Π-wf (N-wf 0 ⊢；NNΓ) (t[σ]-Se (N-wf 0 ⊢；NNΓ) N；NNΓ⊢wk)

    ⊢□[N⟶N]NNΓ = ⊢∺ ⊢NNΓ (□-wf ；NNΓ⊢N⟶N)
    ⊢；□[N⟶N]NNΓ = ⊢κ ⊢□[N⟶N]NNΓ
    ⊢N；□[N⟶N]NNΓ = ⊢∺ ⊢；□[N⟶N]NNΓ (N-wf 0 ⊢；□[N⟶N]NNΓ)
    ⊢NN；□[N⟶N]NNΓ = ⊢∺ ⊢N；□[N⟶N]NNΓ (N-wf 0 ⊢N；□[N⟶N]NNΓ)

    N；□[N⟶N]NNΓ⊢v0 = ⊢vn∶N [] ⊢N；□[N⟶N]NNΓ refl

    □[N⟶N]NNΓ⊢wk = s-wk ⊢□[N⟶N]NNΓ
    □[N⟶N]NNΓ⊢[wk∘wk],su[v1] = ⊢[wk∘wk],su[v1] ⊢□[N⟶N]NNΓ
    ；□[N⟶N]NNΓ⊢[wk∘wk],su[v1]；1 = s-； ([] ∷ []) □[N⟶N]NNΓ⊢[wk∘wk],su[v1] ⊢；□[N⟶N]NNΓ refl
    N；□[N⟶N]NNΓ⊢I；1 = s-； ((N ∷ []) ∷ []) (s-I ⊢□[N⟶N]NNΓ) ⊢N；□[N⟶N]NNΓ refl
    NN；□[N⟶N]NNΓ⊢wk = s-wk ⊢NN；□[N⟶N]NNΓ

    N；□[N⟶N]NNΓ⊢N⟶N = Π-wf (N-wf 0 ⊢N；□[N⟶N]NNΓ) (t[σ]-Se (N-wf 0 ⊢N；□[N⟶N]NNΓ) NN；□[N⟶N]NNΓ⊢wk)

    ；□[N⟶N]NNΓ⊢unbox1[v0]$v0 = Λ-E-⟶
                                 (N-wf 0 ⊢N；□[N⟶N]NNΓ)
                                 (conv
                                   (□-E
                                     ((N ∷ []) ∷ [])
                                     (conv
                                       (vlookup ⊢□[N⟶N]NNΓ here)
                                       (□-[] □[N⟶N]NNΓ⊢wk ；NNΓ⊢N⟶N))
                                     ⊢N；□[N⟶N]NNΓ
                                     refl)
                                   (≈-trans
                                     ([]-cong-Se′
                                       ([N⟶N][]≈N⟶N {i = 0} (s-； ([] ∷ []) □[N⟶N]NNΓ⊢wk ⊢；□[N⟶N]NNΓ refl))
                                       N；□[N⟶N]NNΓ⊢I；1)
                                     ([N⟶N][]≈N⟶N N；□[N⟶N]NNΓ⊢I；1)))
                                 N；□[N⟶N]NNΓ⊢v0

mints-pow-n : ℕ → Example
mints-pow-n n ⊢Γ = proj₁ (mints-pow ⊢Γ) $ of-n n
                 , □ (N ⟶ N)
                 , Λ-E-⟶
                     Γ⊢□[N⟶N]
                     (proj₂ (proj₂ (mints-pow ⊢Γ)))
                     (⊢of-n n ⊢Γ)
  where
    ⊢；Γ = ⊢κ ⊢Γ
    ⊢N；Γ = ⊢∺ ⊢；Γ (N-wf 0 ⊢；Γ)

    N；Γ⊢wk = s-wk ⊢N；Γ

    ；Γ⊢N⟶N = Π-wf (N-wf 0 ⊢；Γ) (t[σ]-Se (N-wf 0 ⊢；Γ) N；Γ⊢wk)
    Γ⊢□[N⟶N] = □-wf ；Γ⊢N⟶N

mints-pow-2 : Example
mints-pow-2 = mints-pow-n 2

nbe-of-example : Example → Nf
nbe-of-example ex = proj₁ (completeness (≈-refl (proj₂ (proj₂ (ex ⊢ε)))))

open import Data.Nat
open import Data.Nat.Show
open import Data.Char hiding (show)
open import Data.Maybe as M hiding (_>>=_)
open import Data.String as S hiding (show)

Exp-to-ℕ : Exp → Maybe ℕ
Exp-to-ℕ ze     = just 0
Exp-to-ℕ (su t) = M.map suc (Exp-to-ℕ t)
Exp-to-ℕ _      = nothing

Exp-to-string : ℕ → Exp → String
Substs-to-string : ℕ → Substs -> String

wrap≥ : ℕ → ℕ → String → String
wrap≥ x y s
  with x ≥? y
...  | yes _ = "(" S.++ s S.++ ")"
...  | no  _ = s

Exp-to-string p N = "N"
Exp-to-string p (Π T t) = wrap≥ p 2 ("Π" S.<+> Exp-to-string 4 T S.<+> "." S.<+> Exp-to-string 0 t)
Exp-to-string p (Se i) = "Se" S.++ show i
Exp-to-string p (□ t) = wrap≥ p 5 ("□" S.<+> Exp-to-string 5 t)
Exp-to-string p (v x) = "v" S.++ show x
Exp-to-string p ze = "0"
Exp-to-string p (su t) = M.maybe′ show (wrap≥ p 2 ("1+" S.<+> Exp-to-string 2 t)) (Exp-to-ℕ (su t))
-- Sugar for easier read
Exp-to-string p (rec N s (su (v 0)) t) = wrap≥ p 2 (Exp-to-string 2 t S.<+> "+" S.<+> Exp-to-string 2 s)
Exp-to-string p (rec T s r t) = wrap≥ p 2 ("elim" S.<+> Exp-to-string 4 T S.<+> Exp-to-string 4 s S.<+> Exp-to-string 4 r S.<+> Exp-to-string 4 t)
Exp-to-string p (Λ t) = wrap≥ p 2 ("Λ" S.<+> Exp-to-string 4 t)
Exp-to-string p (t $ s) = wrap≥ p 3 (Exp-to-string 2 t S.<+> Exp-to-string 3 s)
Exp-to-string p (box t) = wrap≥ p 1 ("box" S.<+> Exp-to-string 4 t S.++ "")
Exp-to-string p (unbox n t) = wrap≥ p 1 ("unbox" S.++ show n S.<+> Exp-to-string 4 t)
Exp-to-string p (sub t σ) = Exp-to-string 5 t S.++ "[" S.++ Substs-to-string 0 σ S.++ "]"

Substs-to-string p I = "I"
Substs-to-string p wk = "wk"
Substs-to-string p (σ ∘ τ) = wrap≥ p 1 (Substs-to-string 0 σ S.<+> "." S.<+> Substs-to-string 0 τ)
Substs-to-string p (σ , t) = wrap≥ p 2 (Substs-to-string 1 σ S.<+> "," S.<+> Exp-to-string 0 t)
Substs-to-string p (σ ； n) = wrap≥ p 3 (Substs-to-string 2 σ S.<+> ";" S.<+> show n)

Nf-to-string : ℕ → Nf → String
Nf-to-string p w = Exp-to-string p (Nf⇒Exp w)

Ne-to-string : ℕ → Ne → String
Ne-to-string p u = Exp-to-string p (Ne⇒Exp u)

open import IO

{-# NON_TERMINATING #-}
main : Main
main = run main′
  where
    main′ : IO _
    process : Maybe ℕ → IO _

    minOption = 0
    maxOption = 2

    main′ = do
      putStrLn "Following examples are given:"
      putStrLn "  0 - pow 2"
      putStrLn "  1 - pow n"
      putStrLn "  2 - quit"
      putStrLn ("Choose an example [" S.++ show minOption S.++ "-" S.++ show maxOption S.++ "]: ")
      s ← getLine
      process (readMaybe 10 s)

    process (just 0) = do
      putStr ("Exp        of pow 2: ")
      putStrLn (Exp-to-string 0 (proj₁ (mints-pow-2 ⊢ε)))
      putStr ("NbE result of pow 2: ")
      putStrLn (Nf-to-string 0 (nbe-of-example mints-pow-2))
      main′
    process (just 1) = helper
      where
        helper : IO _
        helper′ : Maybe ℕ → IO _

        helper = do
          putStrLn "Input the argument to pow: "
          s ← getLine
          helper′ (readMaybe 10 s)

        helper′ (just n) = do
          putStr ("Exp        of pow" S.<+> show n <+> ": ")
          putStrLn (Exp-to-string 0 (proj₁ (mints-pow-n n ⊢ε)))
          putStr ("NbE result of pow" S.<+> show n <+> ": ")
          putStrLn (Nf-to-string 0 (nbe-of-example (mints-pow-n n)))
          main′
        helper′ nothing = do
          putStrLn "Invalid argument; Please input a non-negative decimal integer without a sign."
          helper
    process (just 2) = putStrLn "quit"
    process _        = do
      putStrLn ("Invalid example; Please input a non-negative decimal integer between" S.<+> show minOption S.<+> "and" S.<+> show maxOption)
      main′
