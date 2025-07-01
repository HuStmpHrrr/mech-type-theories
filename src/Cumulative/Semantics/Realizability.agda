{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Realizability of the PER model
--
-- Fundamentally, realizability states that if two values are related, then their
-- corresponding syntactic normal forms are equal. More precisely, realizability
-- states that the following subsumption relations:
--
--       Bot ⊆ El i A ⊆ Top
--             𝕌 i    ⊆ TopT
--
-- Due to these subsumptions, we can always derive Top or TopT from El or 𝕌 and thus
-- obtain the equality we want.
module Cumulative.Semantics.Realizability (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Induction
open import Lib

open import Cumulative.Semantics.Domain
open import Cumulative.Semantics.Evaluation
open import Cumulative.Semantics.PER
open import Cumulative.Semantics.Properties.PER.Core fext
open import Cumulative.Semantics.Readback


private
  module Real i (rec : ∀ {j} → j < i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 j) → A ≈ A′ ∈ TopT) where
    mutual

      Bot⊆El : (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
               c ≈ c′ ∈ Bot →
               ↑ A c ≈ ↑ A′ c′ ∈ El i A≈A′
      Bot⊆El (ne C≈C′) c≈c′             = ne c≈c′
      Bot⊆El N c≈c′                     = ne c≈c′
      Bot⊆El (U′ j<i) c≈c′
        rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = ne c≈c′
      Bot⊆El {Π A _ _} {Π A′ _ _} {c} {c′} (Π iA RT) c≈c′ {b} {b′} b≈b′
        with RT b≈b′
      ...  | record
             { ⟦T⟧   = ⟦T⟧
             ; ⟦T′⟧  = ⟦T′⟧
             ; ↘⟦T⟧  = ↘⟦T⟧
             ; ↘⟦T′⟧ = ↘⟦T′⟧
             ; T≈T′  = T≈T′
             } = record
             { fa = [ ⟦T⟧ ] c $′ ↓ A b
             ; fa′ = [ ⟦T′⟧ ] c′ $′ ↓ A′ b′
             ; ↘fa = $∙ A c ↘⟦T⟧
             ; ↘fa′ = $∙ A′ c′ ↘⟦T′⟧
             ; fa≈fa′ = Bot⊆El T≈T′ helper
             }
        where helper : (c $ ↓ A b) ≈ c′ $ ↓ A′ b′ ∈ Bot
              helper n
                with c≈c′ n | El⊆Top iA b≈b′ n
              ...  | u , ↘u , ↘u′
                   | w , ↘w , ↘w′ = u $ w , R$ n ↘u ↘w , R$ n ↘u′ ↘w′


      El⊆Top : (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
               a ≈ a′ ∈ El i A≈A′ →
               ↓ A a ≈ ↓ A′ a′ ∈ Top
      El⊆Top (ne C≈C′) (ne c≈c′) n
        with c≈c′ n
      ...  | u , ↘u , ↘u′     = ne u , Rne n ↘u , Rne n ↘u′
      El⊆Top N ze n           = ze , Rze n , Rze n
      El⊆Top N (su a≈b) n
        with El⊆Top N a≈b n
      ...  | w , ↘w , ↘w′     = su w , Rsu n ↘w , Rsu n ↘w′
      El⊆Top N (ne c≈c′) n
        with c≈c′ n
      ...  | u , ↘u , ↘u′     = ne u , RN n ↘u , RN n ↘u′
      El⊆Top (U′ j<i) A≈A′ n
        rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
        with rec j<i A≈A′ n
      ...  | W , ↘W , ↘W′     = W , RU n ↘W , RU n ↘W′
      El⊆Top (Π iA RT) a≈a′ n
        with Bot⊆El iA (Bot-l n)
      ...  | z≈z′
           with RT z≈z′ | a≈a′ z≈z′
      ...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
              | record { fa = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
              with El⊆Top T≈T′ fa≈fa′ (1 + n)
      ...        | w , ↘w , ↘w′ = Λ w , RΛ n ↘fa ↘⟦T⟧ ↘w , RΛ n ↘fa′ ↘⟦T′⟧ ↘w′


    𝕌⊆TopT : (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT
    𝕌⊆TopT (ne C≈C′) n
      with C≈C′ n
    ...  | V , ↘V , ↘V′          = ne V , Rne n ↘V , Rne n ↘V′
    𝕌⊆TopT N n                   = N , RN n , RN n
    𝕌⊆TopT (U′ j<i) n            = Se _ , RU n , RU n
    𝕌⊆TopT (Π iA RT) n
      with Bot⊆El iA (Bot-l n)
    ...  | z≈z′
         with RT z≈z′
    ...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            with 𝕌⊆TopT iA n | 𝕌⊆TopT T≈T′ (1 + n)
    ...        | W , ↘W , ↘W′
               | W₁ , ↘W₁ , ↘W₁′ = Π W W₁ , RΠ n ↘W ↘⟦T⟧ ↘W₁ , RΠ n ↘W′ ↘⟦T′⟧ ↘W₁′



𝕌⊆TopT : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT
𝕌⊆TopT A≈A′ = <-Measure.wfRec ((λ i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT))
                              Real.𝕌⊆TopT _ A≈A′

Bot⊆El : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
         c ≈ c′ ∈ Bot →
         ↑ A c ≈ ↑ A′ c′ ∈ El i A≈A′
Bot⊆El {i = i} = Real.Bot⊆El i λ _ → 𝕌⊆TopT

El⊆Top : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
         a ≈ a′ ∈ El i A≈A′ →
         ↓ A a ≈ ↓ A′ a′ ∈ Top
El⊆Top {i = i} = Real.El⊆Top i (λ _ → 𝕌⊆TopT)
