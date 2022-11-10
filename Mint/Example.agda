{-# OPTIONS --without-K #-}

-- This module is meant to be executed in GHCi, after compiled into Haskell.
module Mint.Example where

open import Axiom.Extensionality.Propositional

postulate
  fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

open import Lib
open import LibNonEmpty
open import Mints.Statics
open import Mints.Statics.Properties
open import Mints.Completeness fext

------------------------------------------------------------
-- Type of Examples : Triple of a term, type, and
-- typing derivation for the term under a given well-formed context

Example = (c : ∃ λ Γ → ⊢ Γ) → ∃ λ t → ∃ λ T → proj₁ c ⊢ t ∶ T

------------------------------------------------------------
-- Helper functions to define examples

ε : ∃ λ Γ → ⊢ Γ
ε = List⁺.[ [] ] , ⊢[]

exp-of-example : Example → (∃ λ Γ → ⊢ Γ) → Exp
exp-of-example ex c = proj₁ (ex c)

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

------------------------------------------------------------
-- Examples

example0 : Example
example0 (Γ , ⊢Γ) = (Λ (su (v 0))) $ ze
                  , N
                  , conv (Λ-E (Λ-I (su-I (conv (vlookup (⊢∺ ⊢Γ (N-wf 0 ⊢Γ)) here) (N-[] 0 (s-wk (⊢∺ ⊢Γ (N-wf 0 ⊢Γ))))))) (ze-I ⊢Γ)) (N-[] 0 (s-, (s-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (ze-I ⊢Γ) (≈-sym (N-[] 0 (s-I ⊢Γ))))))

-- In a more readable syntax, this corresponds to
--
--   _+_ : Nat → Nat → Nat
--   _+_ zero     m = m
--   _+_ (succ n) m = succ (n + m)
--
mints-+ : Example
mints-+ (Γ , ⊢Γ) = Λ (Λ (rec N (v 0) (su (v 0)) (v 1)))
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
    NNΓ⊢wk = s-wk ⊢NNΓ
    NNNΓ⊢wk = s-wk ⊢NNNΓ
    NNNNΓ⊢wk = s-wk ⊢NNNNΓ

-- In a more readable syntax, this corresponds to
--
--   _*_ : Nat → Nat → Nat
--   _*_ zero     m = zero
--   _*_ (succ n) m = m + (n * m)
--
mints-* : Example
mints-* (Γ , ⊢Γ) = Λ (Λ (rec N ze ((proj₁ (mints-+ ε) $ v 2) $ v 0) (v 1)))
                 , N ⟶ N ⟶ N
                 , Λ-I
                     (conv
                       (Λ-I
                         (conv
                           (N-E
                             (N-wf 0 ⊢NNNΓ)
                             (conv (ze-I ⊢NNΓ) (≈-sym (N-[] 0 (⊢I,ze ⊢NNΓ))))
                             (conv
                               (Λ-E
                                 (conv
                                   (Λ-E
                                     (proj₂ (proj₂ (mints-+ (_ , ⊢NNNNΓ))))
                                     NNNNΓ⊢v2)
                                   (≈-trans
                                     ([]-cong-Se′
                                       ([N⟶N][]≈N⟶N {i = 0} NNNNNΓ⊢wk)
                                       (⊢I,t NNNNΓ⊢v2))
                                     (≈-trans
                                       ([N⟶N][]≈N⟶N (⊢I,t NNNNΓ⊢v2))
                                       (N⟶N≈ΠNN ⊢NNNNΓ))))
                                 (⊢vn∶N [] ⊢NNNNΓ refl))
                               (≈-trans
                                 (N-[] 0 (⊢I,t (⊢vn∶N [] ⊢NNNNΓ refl)))
                                 (≈-sym (N-[] 0 (⊢[wk∘wk],su[v1] ⊢NNNNΓ)))))
                             (⊢vn∶N (N ∷ []) ⊢NNΓ refl))
                           (N-[] 0 (⊢I,t (⊢vn∶N (N ∷ []) ⊢NNΓ refl)))))
                       (≈-sym
                         (≈-trans ([N⟶N][]≈N⟶N {i = 0} NΓ⊢wk) (N⟶N≈ΠNN ⊢NΓ))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢NNNΓ = ⊢∺ ⊢NNΓ (N-wf 0 ⊢NNΓ)
    ⊢NNNNΓ = ⊢∺ ⊢NNNΓ (N-wf 0 ⊢NNNΓ)
    ⊢NNNNNΓ = ⊢∺ ⊢NNNNΓ (N-wf 0 ⊢NNNNΓ)
    ⊢NNNNNNΓ = ⊢∺ ⊢NNNNNΓ (N-wf 0 ⊢NNNNNΓ)

    NNNNΓ⊢v2 = ⊢vn∶N (N ∷ N ∷ []) ⊢NNNNΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNΓ⊢wk = s-wk ⊢NNΓ
    NNNΓ⊢wk = s-wk ⊢NNNΓ
    NNNNΓ⊢wk = s-wk ⊢NNNNΓ
    NNNNNΓ⊢wk = s-wk ⊢NNNNNΓ
    NNNNNNΓ⊢wk = s-wk ⊢NNNNNNΓ

-- In a more readable syntax, this corresponds to
--
--   pow : Nat → □ (Nat → Nat)
--   pow zero     = box (λ x → succ zero)
--   pow (succ n) = box (λ x → ((unbox1 (pow n)) x) * x)
--
mints-pow : Example
mints-pow (Γ , ⊢Γ) = Λ (rec (□ (N ⟶ N)) (box (Λ (su ze))) (box (Λ ((proj₁ (mints-* ε) $ (unbox 1 (v 0) $ v 0)) $ v 0))) (v 0))
                   , N ⟶ □ (N ⟶ N)
                   , Λ-I
                       (conv
                         (N-E
                           (□-wf []NNΓ⊢N⟶N)
                           (conv
                             (□-I (Λ-I (su-I (ze-I ⊢N[]NΓ))))
                             (≈-sym
                               (≈-trans
                                 (□-[] (⊢I,ze ⊢NΓ) []NNΓ⊢N⟶N)
                                 (□-cong
                                   (≈-trans
                                     ([N⟶N][]≈N⟶N (s-； ([] ∷ []) (⊢I,ze ⊢NΓ) ⊢[]NΓ refl))
                                     (N⟶N≈ΠNN ⊢[]NΓ))))))
                           (conv
                             {!!}
                             {!!})
                           (⊢vn∶N [] ⊢NΓ refl))
                         (≈-trans
                           (□-[] (⊢I,t (⊢vn∶N [] ⊢NΓ refl)) []NNΓ⊢N⟶N)
                           (≈-trans
                             (□-cong
                               (≈-trans
                                 ([N⟶N][]≈N⟶N
                                   (s-； ([] ∷ []) (⊢I,t (⊢vn∶N [] ⊢NΓ refl)) ⊢[]NΓ refl))
                                 (≈-sym
                                   ([N⟶N][]≈N⟶N
                                     (s-； ([] ∷ []) NΓ⊢wk ⊢[]NΓ refl)))))
                             (≈-sym
                               (□-[] NΓ⊢wk []Γ⊢N⟶N)))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢NNNΓ = ⊢∺ ⊢NNΓ (N-wf 0 ⊢NNΓ)
    ⊢NNNNΓ = ⊢∺ ⊢NNNΓ (N-wf 0 ⊢NNNΓ)
    ⊢NNNNNΓ = ⊢∺ ⊢NNNNΓ (N-wf 0 ⊢NNNNΓ)
    ⊢NNNNNNΓ = ⊢∺ ⊢NNNNNΓ (N-wf 0 ⊢NNNNNΓ)
    ⊢[]Γ = ⊢κ ⊢Γ
    ⊢N[]Γ = ⊢∺ ⊢[]Γ (N-wf 0 ⊢[]Γ)
    ⊢[]NΓ = ⊢κ ⊢NΓ
    ⊢N[]NΓ = ⊢∺ ⊢[]NΓ (N-wf 0 ⊢[]NΓ)
    ⊢[]NNΓ = ⊢κ ⊢NNΓ
    ⊢N[]NNΓ = ⊢∺ ⊢[]NNΓ (N-wf 0 ⊢[]NNΓ)

    NNNNΓ⊢v2 = ⊢vn∶N (N ∷ N ∷ []) ⊢NNNNΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNΓ⊢wk = s-wk ⊢NNΓ
    NNNΓ⊢wk = s-wk ⊢NNNΓ
    NNNNΓ⊢wk = s-wk ⊢NNNNΓ
    NNNNNΓ⊢wk = s-wk ⊢NNNNNΓ
    NNNNNNΓ⊢wk = s-wk ⊢NNNNNNΓ
    N[]Γ⊢wk = s-wk ⊢N[]Γ
    N[]NNΓ⊢wk = s-wk ⊢N[]NNΓ

    []Γ⊢N⟶N = Π-wf (N-wf 0 ⊢[]Γ) (t[σ]-Se (N-wf 0 ⊢[]Γ) N[]Γ⊢wk)
    []NNΓ⊢N⟶N = Π-wf (N-wf 0 ⊢[]NNΓ) (t[σ]-Se (N-wf 0 ⊢[]NNΓ) N[]NNΓ⊢wk)

nbe-of-example : Example → Nf
nbe-of-example ex
  with (_ , _ , ⊢t) ← ex ε = proj₁ (completeness (≈-refl ⊢t))
