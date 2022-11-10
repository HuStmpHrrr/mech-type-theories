{-# OPTIONS --without-K --guardedness #-}

-- This module is meant to be executed with runghc, after compiled into Haskell by agda.
-- How To Execute:
--   1. run `agda -c Example.agda --compile-dir=out --ghc-dont-call-ghc`
--   2. run `runghc -iout --ghc-arg="-Wno-overlapping-patterns" --ghc-arg="-XStandaloneDeriving" out/MAlonzo/Code/Mint/Example.hs`
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

-- These names are ad-hoc
{-# FOREIGN GHC
  import qualified MAlonzo.Code.Mint.Statics.Syntax as Syntax

  deriving instance Show Syntax.T_Ne_220
  deriving instance Show Syntax.T_Nf_222
#-}

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

of-n : ℕ → (c : ∃ λ Γ → ⊢ Γ) → ∃ λ t → proj₁ c ⊢ t ∶ N
of-n 0       (_ , ⊢Γ) = ze
                      , ze-I ⊢Γ
of-n (suc n) (_ , ⊢Γ) = su (proj₁ (of-n n (_ , ⊢Γ)))
                      , su-I (proj₂ (of-n n (_ , ⊢Γ)))

------------------------------------------------------------
-- Examples

example0 : Example
example0 (_ , ⊢Γ) = (Λ (su (v 0))) $ ze
                  , N
                  , conv (Λ-E (Λ-I (su-I (conv (vlookup (⊢∺ ⊢Γ (N-wf 0 ⊢Γ)) here) (N-[] 0 (s-wk (⊢∺ ⊢Γ (N-wf 0 ⊢Γ))))))) (ze-I ⊢Γ)) (N-[] 0 (s-, (s-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (ze-I ⊢Γ) (≈-sym (N-[] 0 (s-I ⊢Γ))))))

-- In a more readable syntax, this corresponds to
--
--   _+_ : Nat → Nat → Nat
--   _+_ zero     m = m
--   _+_ (succ n) m = succ (n + m)
--
mints-+ : Example
mints-+ (_ , ⊢Γ) = Λ
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
mints-* (_ , ⊢Γ) = Λ
                     (Λ
                       (rec
                         N
                         ze
                         ((proj₁ (mints-+ (_ , ⊢NNNNΓ)) $ v 2) $ v 0)
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

    NNNNΓ⊢v2 = ⊢vn∶N (N ∷ N ∷ []) ⊢NNNNΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNΓ⊢wk = s-wk ⊢NNΓ
    NNNΓ⊢wk = s-wk ⊢NNNΓ
    NNNNΓ⊢wk = s-wk ⊢NNNNΓ
    NNNNNΓ⊢wk = s-wk ⊢NNNNNΓ

-- In a more readable syntax, this corresponds to
--
--   pow : Nat → □ (Nat → Nat)
--   pow zero     = box (λ x → succ zero)
--   pow (succ n) = box (λ x → ((unbox1 (pow n)) x) * x)
--
mints-pow : Example
mints-pow (_ , ⊢Γ) = Λ
                       (rec
                         (□ (N ⟶ N))
                         (box (Λ (su ze)))
                         (box (Λ ((proj₁ (mints-* (_ , ⊢N；□[N⟶N]NNΓ)) $ (unbox 1 (v 0) $ v 0)) $ v 0)))
                         (v 0))
                   , N ⟶ □ (N ⟶ N)
                   , Λ-I
                       (conv
                         (N-E
                           (□-wf ；NNΓ⊢N⟶N)
                           (conv
                             (□-I (Λ-I (su-I (ze-I ⊢N；NΓ))))
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
                                 (conv
                                   (Λ-E
                                     (conv
                                       (Λ-E
                                         (proj₂ (proj₂ (mints-* (_ , ⊢N；□[N⟶N]NNΓ))))
                                         ；□[N⟶N]NNΓ⊢unbox1[v0]$v0)
                                       (≈-trans
                                         ([]-cong-Se′
                                           ([N⟶N][]≈N⟶N {i = 0} NN；□[N⟶N]NNΓ⊢wk)
                                           (⊢I,t ；□[N⟶N]NNΓ⊢unbox1[v0]$v0))
                                         ([N⟶N][]≈N⟶N (⊢I,t ；□[N⟶N]NNΓ⊢unbox1[v0]$v0))))
                                     N；□[N⟶N]NNΓ⊢v0)
                                   (≈-trans
                                     ([]-cong-Se′ (N-[] 0 NN；□[N⟶N]NNΓ⊢wk) (⊢I,t N；□[N⟶N]NNΓ⊢v0))
                                     (N-[] 0 (⊢I,t N；□[N⟶N]NNΓ⊢v0))))))
                             (≈-sym
                               (≈-trans
                                 (□-[] □[N⟶N]NNΓ⊢[wk∘wk],su[v1] ；NNΓ⊢N⟶N)
                                 (□-cong
                                   (≈-trans
                                     ([N⟶N][]≈N⟶N ；□[N⟶N]NNΓ⊢[wk∘wk],su[v1]；1)
                                     (N⟶N≈ΠNN ⊢；□[N⟶N]NNΓ))))))
                           NΓ⊢v0)
                         (≈-trans
                           (□-[] (⊢I,t NΓ⊢v0) ；NNΓ⊢N⟶N)
                           (≈-trans
                             (□-cong
                               (≈-trans
                                 ([N⟶N][]≈N⟶N
                                   (s-； ([] ∷ []) (⊢I,t NΓ⊢v0) ⊢；NΓ refl))
                                 (≈-sym
                                   ([N⟶N][]≈N⟶N
                                     (s-； ([] ∷ []) NΓ⊢wk ⊢；NΓ refl)))))
                             (≈-sym
                               (□-[] NΓ⊢wk ；Γ⊢N⟶N)))))
  where
    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢NNΓ = ⊢∺ ⊢NΓ (N-wf 0 ⊢NΓ)
    ⊢；Γ = ⊢κ ⊢Γ
    ⊢N；Γ = ⊢∺ ⊢；Γ (N-wf 0 ⊢；Γ)
    ⊢；NΓ = ⊢κ ⊢NΓ
    ⊢N；NΓ = ⊢∺ ⊢；NΓ (N-wf 0 ⊢；NΓ)
    ⊢；NNΓ = ⊢κ ⊢NNΓ
    ⊢N；NNΓ = ⊢∺ ⊢；NNΓ (N-wf 0 ⊢；NNΓ)

    NΓ⊢v0 = ⊢vn∶N [] ⊢NΓ refl

    NΓ⊢wk = s-wk ⊢NΓ
    NNΓ⊢wk = s-wk ⊢NNΓ
    N；Γ⊢wk = s-wk ⊢N；Γ
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

    ；□[N⟶N]NNΓ⊢unbox1[v0]$v0 = conv
                                 (Λ-E
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
                                   N；□[N⟶N]NNΓ⊢v0)
                                 (≈-trans
                                   ([]-cong-Se′
                                     (N-[] 0 NN；□[N⟶N]NNΓ⊢wk)
                                     (⊢I,t N；□[N⟶N]NNΓ⊢v0))
                                   (N-[] 0 (⊢I,t N；□[N⟶N]NNΓ⊢v0)))

mints-pow-2 : Example
mints-pow-2 (_ , ⊢Γ) = proj₁ (mints-pow (_ , ⊢Γ)) $ su (su ze)
                     , □ (N ⟶ N)
                     , conv
                         (Λ-E (proj₂ (proj₂ (mints-pow (_ , ⊢Γ)))) ⊢su[su[ze]])
                         (≈-trans
                           ([]-cong-Se′
                             (≈-trans
                               (□-[] NΓ⊢wk ；Γ⊢N⟶N)
                               (□-cong ([N⟶N][]≈N⟶N (s-； ([] ∷ []) NΓ⊢wk ⊢；NΓ refl))))
                             (⊢I,t ⊢su[su[ze]]))
                           (≈-trans
                             (□-[]
                               (⊢I,t ⊢su[su[ze]])
                               ；NΓ⊢N⟶N)
                             (□-cong ([N⟶N][]≈N⟶N (s-； ([] ∷ []) (⊢I,t ⊢su[su[ze]]) ⊢；Γ refl)))))
  where
    ⊢su[su[ze]] = su-I (su-I (ze-I ⊢Γ))

    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢；Γ = ⊢κ ⊢Γ
    ⊢N；Γ = ⊢∺ ⊢；Γ (N-wf 0 ⊢；Γ)
    ⊢；NΓ = ⊢κ ⊢NΓ
    ⊢N；NΓ = ⊢∺ ⊢；NΓ (N-wf 0 ⊢；NΓ)

    NΓ⊢wk = s-wk ⊢NΓ
    N；Γ⊢wk = s-wk ⊢N；Γ
    N；NΓ⊢wk = s-wk ⊢N；NΓ

    ；Γ⊢N⟶N = Π-wf (N-wf 0 ⊢；Γ) (t[σ]-Se (N-wf 0 ⊢；Γ) N；Γ⊢wk)
    ；NΓ⊢N⟶N = Π-wf (N-wf 0 ⊢；NΓ) (t[σ]-Se (N-wf 0 ⊢；NΓ) N；NΓ⊢wk)

mints-pow-n : ℕ → Example
mints-pow-n n (_ , ⊢Γ) = proj₁ (mints-pow (_ , ⊢Γ)) $ proj₁ (of-n n (_ , ⊢Γ))
                       , □ (N ⟶ N)
                       , conv
                           (Λ-E (proj₂ (proj₂ (mints-pow (_ , ⊢Γ)))) ⊢n)
                           (≈-trans
                             ([]-cong-Se′
                               (≈-trans
                                 (□-[] NΓ⊢wk ；Γ⊢N⟶N)
                                 (□-cong ([N⟶N][]≈N⟶N (s-； ([] ∷ []) NΓ⊢wk ⊢；NΓ refl))))
                               (⊢I,t ⊢n))
                             (≈-trans
                               (□-[]
                                 (⊢I,t ⊢n)
                                 ；NΓ⊢N⟶N)
                               (□-cong ([N⟶N][]≈N⟶N (s-； ([] ∷ []) (⊢I,t ⊢n) ⊢；Γ refl)))))
  where
    ⊢n = proj₂ (of-n n (_ , ⊢Γ))

    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢；Γ = ⊢κ ⊢Γ
    ⊢N；Γ = ⊢∺ ⊢；Γ (N-wf 0 ⊢；Γ)
    ⊢；NΓ = ⊢κ ⊢NΓ
    ⊢N；NΓ = ⊢∺ ⊢；NΓ (N-wf 0 ⊢；NΓ)

    NΓ⊢wk = s-wk ⊢NΓ
    N；Γ⊢wk = s-wk ⊢N；Γ
    N；NΓ⊢wk = s-wk ⊢N；NΓ

    ；Γ⊢N⟶N = Π-wf (N-wf 0 ⊢；Γ) (t[σ]-Se (N-wf 0 ⊢；Γ) N；Γ⊢wk)
    ；NΓ⊢N⟶N = Π-wf (N-wf 0 ⊢；NΓ) (t[σ]-Se (N-wf 0 ⊢；NΓ) N；NΓ⊢wk)

nbe-of-example : Example → Nf
nbe-of-example ex
  with (_ , _ , ⊢t) ← ex ε = proj₁ (completeness (≈-refl ⊢t))

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Char hiding (show)
open import Data.Maybe hiding (_>>=_)
open import Data.String as S hiding (show)
open import IO hiding (_>>=_)

Nf-to-string : Nf → String
Ne-to-string : Ne → String

Nf-to-string (ne u)   = Ne-to-string u
Nf-to-string N        = "N"
Nf-to-string (Π w w′) = "(Π" S.<+> Nf-to-string w S.<+> Nf-to-string w′ S.++ ")"
Nf-to-string (Se i)   = "(Se" S.<+> show i S.++ ")"
Nf-to-string (□ w)    = "(□" S.<+> Nf-to-string w S.++ ")"
Nf-to-string ze       = "0"
Nf-to-string (su w)   = "(1+" S.<+> Nf-to-string w S.++ ")"
Nf-to-string (Λ w)    = "(Λ" S.<+> Nf-to-string w S.++ ")"
Nf-to-string (box w)  = "(box" S.<+> Nf-to-string w S.++ ")"

Ne-to-string (v x)         = "v" S.++ show x
Ne-to-string (rec T z s u) = "(rec" S.<+> Nf-to-string T S.<+> Nf-to-string z S.<+> Nf-to-string s S.<+> Ne-to-string u S.++ ")"
Ne-to-string (u $ n)       = "(" S.++ Ne-to-string u S.<+> Nf-to-string n S.++ ")"
Ne-to-string (unbox x u)   = "(unbox" S.++ show x S.<+> Ne-to-string u S.++ ")"

{-# NON_TERMINATING #-}
main : Main
main = run main′
  where
    main′ : IO _
    process : Maybe ℕ → IO _

    open import IO using (_>>=_)

    minOption = 0
    maxOption = 2

    main′ = do
      putStrLn "Following examples are given:"
      putStrLn "  0 - pow 2"
      putStrLn "  1 - pow n"
      putStrLn "  2 - quit"
      putStr ("Choose an example [" S.++ show minOption S.++ "-" S.++ show maxOption S.++ "]: ")
      s ← getLine
      process (readMaybe 10 s)

    process (just 0) = do
      putStrLn (Nf-to-string (nbe-of-example mints-pow-2))
      main′
    process (just 1) = helper
      where
        helper : IO _
        helper′ : Maybe ℕ → IO _

        helper = do
          putStr "Input the argument to pow: "
          s ← getLine
          helper′ (readMaybe 10 s)

        helper′ (just n) = do
          putStr ("NbE result of pow" S.<+> show n <+> "is: ")
          putStrLn (Nf-to-string (nbe-of-example (mints-pow-n n)))
          main′
        helper′ nothing = do
          putStrLn "Invalid argument; Please input a non-negative decimal integer without a sign."
          helper
    process (just 2) = putStrLn "quit"
    process _        = do
      putStrLn ("Invalid example; Please input a non-negative decimal integer between" S.<+> show minOption S.<+> "and" S.<+> show maxOption)
      main′
