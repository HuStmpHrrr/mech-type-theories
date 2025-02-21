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
module NonCumulative.Ascribed.Semantics.Realizability (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties
open import Data.Nat.Induction
open import Lib

open import NonCumulative.Ascribed.Semantics.Domain
open import NonCumulative.Ascribed.Semantics.Evaluation
open import NonCumulative.Ascribed.Semantics.PER
open import NonCumulative.Ascribed.Semantics.Properties.PER.Core fext
open import NonCumulative.Ascribed.Semantics.Readback


private
  module Real where
    mutual

      Bot⊆El : ∀ i
               (real : ∀ {j} → j < i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 j) → A ≈ A′ ∈ TopT j)
               (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
               c ≈ c′ ∈ Bot →
               ↑ i A c ≈ ↑ i A′ c′ ∈ El i A≈A′
      Bot⊆El i real (ne′ C≈C′) c≈c′        = ne′ c≈c′
      Bot⊆El i real N′ c≈c′                = ne c≈c′
      Bot⊆El i real U′ c≈c′                = ne′ c≈c′
      Bot⊆El {Π _ A _ _} {Π _ A′ _ _} {c} {c′} i real (Π′ {j} {k} iA RT) c≈c′ {a} {b} a≈b
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
        rewrite 𝕌-wf-gen k (ΠO≤′ j k refl)
        with RT a≈b
      ...  |  record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
        = record
        { fa     = [ ⟦T⟧ ↙ k ] c $′ ↓ j A a
        ; fa′    = [ ⟦T′⟧ ↙ k ] c′ $′ ↓ j A′ b
        ; ↘fa    = $∙ A c ↘⟦T⟧
        ; ↘fa′   = $∙ A′ c′ ↘⟦T′⟧
        ; fa≈fa′ = Bot⊆El k (λ j′<i → real (≤-trans j′<i (m≤n⊔m j k))) T≈T′ helper
        }
        where helper : (c $ ↓ j A a) ≈ c′ $ ↓ j A′ b ∈ Bot
              helper n
                with c≈c′ n | El⊆Top j (λ j′<i → real (≤-trans j′<i (m≤m⊔n j k))) iA a≈b n
              ...  | u , ↘u , ↘u′
                   | w , ↘w , ↘w′ = u $ w , R$ n ↘u ↘w , R$ n ↘u′ ↘w′
      Bot⊆El {Li _ _ A} {Li _ _ A′} {c} {c′} i real (L′ {j} {k} A≈A′) c≈c′
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
        = record
        { ua    = ↑ k A (unli c)
        ; ub    = ↑ k A′ (unli c′)
        ; ↘ua   = unli↘
        ; ↘ub   = unli↘
        ; ua≈ub = Bot⊆El k (λ l<k → real (≤-trans l<k (m≤n+m k j))) A≈A′ helper
        }
        where helper : unli c ≈ unli c′ ∈ Bot
              helper n
                with c≈c′ n
              ...  | u , ↘u , ↘u′ = unlift u , Runli n ↘u , Runli n ↘u′

      El⊆Top : ∀ i
               (real : ∀ { j } → j < i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 j) → A ≈ A′ ∈ TopT j)
               (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
               a ≈ a′ ∈ El i A≈A′ →
               ↓ i A a ≈ ↓ i A′ a′ ∈ Top
      El⊆Top i real (ne′ C≈C′) (ne′ c≈c′) n
        with c≈c′ n
      ...  | u , ↘u , ↘u′                     = ne u , Rne′ n ↘u , Rne′ n ↘u′
      El⊆Top .0 real N′ ze n                  = ze , Rze n , Rze n
      El⊆Top .0 real N′ (su a≈a′) n
        with El⊆Top _ real N′ a≈a′ n
      ...  | w , ↘w , ↘w′                     = su w , Rsu n ↘w , Rsu n ↘w′
      El⊆Top .0 real N′ (ne c≈c′) n
        with c≈c′ n
      ...  | u , ↘u , ↘u′                     = ne u , RN n ↘u , RN n ↘u′
      El⊆Top i real (U′ {j}) a≈a′ n
        rewrite 𝕌-wf-gen j λ l<j → (≤-trans l<j (≤-reflexive refl))
        with real (≤-reflexive refl) a≈a′ n
      ...  | W , ↘W , ↘W′                     = W , RU′ n ↘W , RU′ n ↘W′
      El⊆Top i real (Π′ {j} {k} iA RT) a≈a′ n
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
        rewrite 𝕌-wf-gen k (ΠO≤′ j k refl)
        with Bot⊆El _ (λ l<j → real (≤-trans l<j (m≤m⊔n j k))) iA (Bot-l n)
      ...  | z≈z′
           with RT z≈z′ | a≈a′ z≈z′
      ...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
              | record { fa = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
              with El⊆Top _ (λ l<k → real (≤-trans l<k (m≤n⊔m j k))) T≈T′ fa≈fa′ (1 + n)
                 | 𝕌⊆TopT _ (λ l<j → real (≤-trans l<j (m≤m⊔n j k))) iA n
      ...        | w , ↘w , ↘w′
                 | W , ↘W , ↘W′ = Λ (W ↙ j) w , RΛ n ↘W ↘fa ↘⟦T⟧ ↘w , RΛ n ↘W′ ↘fa′ ↘⟦T′⟧ ↘w′
      El⊆Top i real (L′ {j} {k} A≈A′) a≈a′ n
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
        with a≈a′
      ...  | record { ua = ua ; ub = ub ; ↘ua = ↘ua ; ↘ub = ↘ub ; ua≈ub = ua≈ub }
           with El⊆Top _ (λ l<k → real (≤-trans l<k (m≤n+m k j))) A≈A′ ua≈ub n
      ...     | w , ↘w , ↘w′                  = liftt j w , Rli n ↘ua ↘w , Rli n ↘ub ↘w′

      𝕌⊆TopT : ∀ i
               (real : ∀ {j} → j < i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 j) → A ≈ A′ ∈ TopT j)
               (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT i
      𝕌⊆TopT i real (ne′ C≈C′) n
        with C≈C′ n
      ...  | V , ↘V , ↘V′        = ne V , Rne n ↘V , Rne n ↘V′
      𝕌⊆TopT i real N′ n         = N , RN n , RN n
      𝕌⊆TopT i real (U′ {j}) n   = Se j , RU n , RU n
      𝕌⊆TopT i real (Π′ {j} {k} iA RT) n
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
        rewrite 𝕌-wf-gen k (ΠO≤′ j k refl)
        with Bot⊆El _ (λ l<j → real (≤-trans l<j (m≤m⊔n j k))) iA (Bot-l n)
      ...  | z≈z′
           with RT z≈z′
      ...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
              with 𝕌⊆TopT _ (λ l<j → real (≤-trans l<j (m≤m⊔n j k))) iA n
                 | 𝕌⊆TopT _ (λ l<k → real (≤-trans l<k (m≤n⊔m j k))) T≈T′ (1 + n)
      ...        | W , ↘W , ↘W′
                 | W₁ , ↘W₁ , ↘W₁′ = Π (W ↙ j) (W₁ ↙ k) , RΠ n ↘W ↘⟦T⟧ ↘W₁ , RΠ n ↘W′ ↘⟦T′⟧ ↘W₁′
      𝕌⊆TopT i real (L′ {j} {k} A≈A′) n
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
        with 𝕌⊆TopT _ (λ l<k → real (≤-trans l<k (m≤n+m k j))) A≈A′ n
      ...  | W , ↘W , ↘W′        = Liftt j (W ↙ k) , RL n ↘W , RL n ↘W′



𝕌⊆TopT : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT i
𝕌⊆TopT {i = i} A≈A′ = <-Measure.wfRec (λ i → ∀ {A A′} (A≈A′ : A ≈ A′ ∈ 𝕌 i) → A ≈ A′ ∈ TopT i)
                                      (λ i real → Real.𝕌⊆TopT i real)
                                      i A≈A′

Bot⊆El : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
         c ≈ c′ ∈ Bot →
         ↑ i A c ≈ ↑ i A′ c′ ∈ El i A≈A′
Bot⊆El {i = i} = Real.Bot⊆El i λ _ → 𝕌⊆TopT

El⊆Top : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
         a ≈ a′ ∈ El i A≈A′ →
         ↓ i A a ≈ ↓ i A′ a′ ∈ Top
El⊆Top {i = i} = Real.El⊆Top i (λ _ → 𝕌⊆TopT)
