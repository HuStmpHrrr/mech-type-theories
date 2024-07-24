{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Various properties of the PER model
module MLTT.Semantics.Properties.PER (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties as ℕₚ
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib hiding (lookup)

open import MLTT.Statics.Syntax
open import MLTT.Semantics.Domain
open import MLTT.Semantics.Evaluation
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Realizability fext
open import MLTT.Semantics.PER

open import MLTT.Semantics.Properties.PER.Core fext public


-- Top and Bot are PERs.
Top-sym : d ≈ d′ ∈ Top → d′ ≈ d ∈ Top
Top-sym d≈d′ n
  with d≈d′ n
...  | w , ↘w , ↘w′ = w , ↘w′ , ↘w

Bot-sym : c ≈ c′ ∈ Bot → c′ ≈ c ∈ Bot
Bot-sym c≈c′ n
  with c≈c′ n
...  | u , ↘u , ↘u′ = u , ↘u′ , ↘u

Top-trans : d ≈ d′ ∈ Top → d′ ≈ d″ ∈ Top → d ≈ d″ ∈ Top
Top-trans d≈d′ d′≈d″ n
  with d≈d′ n | d′≈d″ n
...  | w  , ↘w₁  , ↘w₂
     | w′ , ↘w′₁ , ↘w′₂ = w , ↘w₁ , subst (Rf n - _ ↘_) (sym (Rf-det ↘w₂ ↘w′₁)) ↘w′₂

Bot-trans : c ≈ c′ ∈ Bot → c′ ≈ c″ ∈ Bot → c ≈ c″ ∈ Bot
Bot-trans c≈c′ c′≈c″ n
  with c≈c′ n | c′≈c″ n
...  | u  , ↘u₁  , ↘u₂
     | u′ , ↘u′₁ , ↘u′₂ = u , ↘u₁ , subst (Re n - _ ↘_) (sym (Re-det ↘u₂ ↘u′₁)) ↘u′₂

Top-isPER : IsPartialEquivalence Top
Top-isPER = record
  { sym   = Top-sym
  ; trans = Top-trans
  }

Top-PER : PartialSetoid _ _
Top-PER = record
  { Carrier              = Df
  ; _≈_                  = Top
  ; isPartialEquivalence = Top-isPER
  }

module TopR = PS Top-PER


Bot-isPER : IsPartialEquivalence Bot
Bot-isPER = record
  { sym   = Bot-sym
  ; trans = Bot-trans
  }

Bot-PER : PartialSetoid _ _
Bot-PER = record
  { Carrier              = Dn
  ; _≈_                  = Bot
  ; isPartialEquivalence = Bot-isPER
  }

module BotR = PS Bot-PER

-- Bot is subsumed by Top.
Bot⊆Top : c ≈ c′ ∈ Bot → ↓ (↑ A C) (↑ B c) ≈ ↓ (↑ A′ C′) (↑ B′ c′) ∈ Top
Bot⊆Top c≈c′ n
  with c≈c′ n
...  | u , ↘u , ↘u′ = ne u , Rne n ↘u , Rne n ↘u′

$-Bot : c ≈ c′ ∈ Bot → d ≈ d′ ∈ Top → c $ d ≈ c′ $ d′ ∈ Bot
$-Bot c≈c′ d≈d′ n
  with c≈c′ n | d≈d′ n
...  | u , ↘u , ↘u′
     | w , ↘w , ↘w′ = u $ w , R$ n ↘u ↘w , R$ n ↘u′ ↘w′

-- The model for natural numbers Nat is a PER.
Nat-sym : a ≈ b ∈ Nat → b ≈ a ∈ Nat
Nat-sym ze        = ze
Nat-sym (su a≈b)  = su (Nat-sym a≈b)
Nat-sym (ne c≈c′) = ne (Bot-sym c≈c′)

Nat-trans : a ≈ a′ ∈ Nat → a′ ≈ a″ ∈ Nat → a ≈ a″ ∈ Nat
Nat-trans ze ze                = ze
Nat-trans (su a≈a′) (su a′≈a″) = su (Nat-trans a≈a′ a′≈a″)
Nat-trans (ne c≈c′) (ne c′≈c″) = ne (Bot-trans c≈c′ c′≈c″)

Nat-isPER : IsPartialEquivalence Nat
Nat-isPER = record
  { sym   = Nat-sym
  ; trans = Nat-trans
  }

Nat-PER : PartialSetoid _ _
Nat-PER = record
  { Carrier              = D
  ; _≈_                  = Nat
  ; isPartialEquivalence = Nat-isPER
  }


-- Symmetry of 𝕌 and El
--
-- They must be proved mutually.
private
  module Sym i (rc : ∀ {j} → j < i → ∀ {A′ B′} → A′ ≈ B′ ∈ 𝕌 j → B′ ≈ A′ ∈ 𝕌 j) where

    mutual

      𝕌-sym : A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
      𝕌-sym (ne C≈C′)                           = ne (Bot-sym C≈C′)
      𝕌-sym N                                   = N
      𝕌-sym (U′ j<i)                            = U′ j<i
      𝕌-sym (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (𝕌-sym iA) helper
        where helper : a ≈ a′ ∈ El i (𝕌-sym iA) → ΠRT T′ (ρ′ ↦ a) T (ρ ↦ a′) (𝕌 i)
              helper a≈a′ = record
                { ⟦T⟧   = ⟦T′⟧
                ; ⟦T′⟧  = ⟦T⟧
                ; ↘⟦T⟧  = ↘⟦T′⟧
                ; ↘⟦T′⟧ = ↘⟦T⟧
                ; T≈T′  = 𝕌-sym T≈T′
                }
                where open ΠRT (RT (El-sym (𝕌-sym iA) iA a≈a′))

      -- Watch the type here. Due to proof relevance, we must supply two symmetric
      -- witnesses, one for the premise and the other for the conclusion. This
      -- duplication of arguments can be taken away later once we establish the
      -- irrelevance lemma. But it cannot be done at this point it cannot be done yet.
      El-sym : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
      El-sym (ne _) (ne _) (ne c≈c′)      = ne (Bot-sym c≈c′)
      El-sym N N a≈b                      = Nat-sym a≈b
      El-sym (U′ j<i) (U j<i′ eq) a≈b
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<i′ = rc j<i′ a≈b
      El-sym (Π iA RT) (Π iA′ RT′) f≈f′ a≈a′
        with El-sym iA′ iA a≈a′
      ...  | a≈a′₁
           with RT a≈a′₁ | RT′ a≈a′ | f≈f′ a≈a′₁
      ... | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
          | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁
                | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁      = record
        { fa     = _
        ; fa′    = _
        ; ↘fa    = ↘fa′
        ; ↘fa′   = ↘fa
        ; fa≈fa′ = El-sym T≈T′₁ T≈T′ fa≈fa′
        }

-- wrap up symmetry by well-founded induction
𝕌-sym : ∀ {i} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
𝕌-sym {i = i} = <-Measure.wfRec (λ i → ∀ {A B} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i) Sym.𝕌-sym i

El-sym : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
El-sym {i = i} = Sym.El-sym i (λ _ → 𝕌-sym)

-- El only focuses on one side (left) of relation of 𝕌.
El-one-sided : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B′ ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j A≈B′
El-one-sided (ne _) (ne _) a≈b        = a≈b
El-one-sided N N a≈b                  = a≈b
El-one-sided (U′ k<i) (U′ k<j) a≈b
  rewrite 𝕌-wellfounded-≡-𝕌 _ k<i
        | 𝕌-wellfounded-≡-𝕌 _ k<j     = a≈b
El-one-sided (Π iA RT) (Π iA′ RT′) f≈f′ a≈a′
  with El-one-sided iA′ iA a≈a′
...  | a≈a′₁
     with RT a≈a′₁ | RT′ a≈a′ | f≈f′ a≈a′₁
...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; T≈T′ = T≈T′ }
        | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T≈T′ = T≈T′₁ }
        | record { fa = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
        rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁     = record
  { fa     = fa
  ; fa′    = fa′
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = El-one-sided T≈T′ T≈T′₁ fa≈fa′
  }


-- In other words, the witness of 𝕌 is irrelevant in El.
𝕌-irrel : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j A≈B′
𝕌-irrel = El-one-sided


-- Combined with symmetry, we can see that El can also focus on the right side of 𝕌.
El-one-sided′ : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B : A′ ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j A′≈B
El-one-sided′ A≈B A′≈B a≈b = El-sym (𝕌-sym A′≈B) A′≈B
                                      (El-one-sided (𝕌-sym A≈B) (𝕌-sym A′≈B) (El-sym A≈B (𝕌-sym A≈B) a≈b))

-- 𝕌 and El are transitive.
private

  module Trans i (rc : ∀ {j} → j < i → ∀ {A A′ A″ k} → A ≈ A′ ∈ 𝕌 j → A′ ≈ A″ ∈ 𝕌 k → A ≈ A″ ∈ 𝕌 j) where

    mutual

      𝕌-trans : ∀ {k} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 k → A ≈ A″ ∈ 𝕌 i
      𝕌-trans (ne C≈C′) (ne C′≈C″)  = ne (Bot-trans C≈C′ C′≈C″)
      𝕌-trans N N                   = N
      𝕌-trans (U′ j<i) (U′ j<k)     = U′ j<i
      𝕌-trans (Π {_} {_} {T} {ρ} iA RT) (Π {_} {_} {T′} {ρ′} {T″} {ρ″} iA′ RT′) = Π (𝕌-trans iA iA′) helper
        where helper : a ≈ a′ ∈ El i (𝕌-trans iA iA′) → ΠRT T (ρ ↦ a) T″ (ρ″ ↦ a′) (𝕌 i)
              helper a≈a′
                with 𝕌-refl iA | 𝕌-trans iA iA′
              ...  | A≈A | A≈A″
                   with RT (El-one-sided A≈A iA (El-refl A≈A″ A≈A a≈a′))
                      | RT′ (El-one-sided′ A≈A″ iA′ a≈a′)
              ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                      rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
                { ⟦T⟧   = _
                ; ⟦T′⟧  = _
                ; ↘⟦T⟧  = ↘⟦T⟧
                ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                ; T≈T′  = 𝕌-trans T≈T′ T≈T′₁
                }


      -- Again, similar to symmetry, we have the same problem here. We must supply
      -- three premises in tranitivity and remove this duplication later.
      El-trans : ∀ {k} (A≈A′ : A ≈ A′ ∈ 𝕌 i) (A′≈A″ : A′ ≈ A″ ∈ 𝕌 k) (A≈A″ : A ≈ A″ ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) →
                   a ≈ a′ ∈ El i A≈A′ → a′ ≈ a″ ∈ El k A′≈A″ → a ≈ a″ ∈ El i A≈A″
      El-trans (ne C≈C′) (ne C′≈C″) (ne C≈C″) _ (ne c≈c′) (ne c′≈c″) = ne (Bot-trans c≈c′ c′≈c″)
      El-trans N N N _ a≈a′ a′≈a″                                    = Nat-trans a≈a′ a′≈a″
      El-trans (U′ j<i) (U′ j<k) (U j<i′ eq) _ a≈a′ a′≈a″
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<i
              | 𝕌-wellfounded-≡-𝕌 _ j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<k                              = rc j<i a≈a′ a′≈a″
      El-trans (Π iA RT) (Π iA′ RT′) (Π iA″ RT″) (Π iA‴ RT‴) f≈f′ f′≈f″ a≈a′
        with El-one-sided iA″ iA a≈a′ | El-one-sided′ iA″ iA′ a≈a′
      ...  | a≈a′₁ | a≈a′₂
           with El-refl′ iA iA‴ a≈a′₁ | El-refl iA iA‴ a≈a′₁
      ...     | a≈a | a≈a₁
              with RT a≈a | RT′ a≈a′₂ | RT″ a≈a′ | RT‴ a≈a₁ | f≈f′ a≈a | f′≈f″ a≈a′₂
      ...        | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
                 | record { ↘fa = ↘fa  ; ↘fa′ = ↘fa′  ; fa≈fa′ = fa≈fa′ }
                 | record { ↘fa = ↘fa₁ ; ↘fa′ = ↘fa′₁ ; fa≈fa′ = fa≈fa′₁ }
                 rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁
                       | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₂
                       | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧₂
                       | ⟦⟧-det ↘⟦T⟧₂ ↘⟦T⟧₃
                       | ⟦⟧-det ↘⟦T⟧₃ ↘⟦T′⟧₃
                       | ap-det ↘fa′ ↘fa₁ = record
        { fa     = _
        ; fa′    = _
        ; ↘fa    = ↘fa
        ; ↘fa′   = ↘fa′₁
        ; fa≈fa′ = El-trans T≈T′ T≈T′₁ T≈T′₂ T≈T′₃ fa≈fa′ fa≈fa′₁
        }


      𝕌-refl : A ≈ B ∈ 𝕌 i → A ≈ A ∈ 𝕌 i
      𝕌-refl A≈B = 𝕌-trans A≈B (𝕌-sym A≈B)

      El-refl : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈A
      El-refl A≈B A≈A a≈b = El-trans A≈B (𝕌-sym A≈B) A≈A A≈A a≈b (El-sym A≈B (𝕌-sym A≈B) a≈b)

      El-refl′ : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈B
      El-refl′ A≈B A≈A a≈b = El-one-sided A≈A A≈B (El-refl A≈B A≈A a≈b)


𝕌-trans : ∀ {i j} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 j → A ≈ A″ ∈ 𝕌 i
𝕌-trans {i = i} = <-Measure.wfRec (λ i → ∀ {A A′ A″ k} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 k → A ≈ A″ ∈ 𝕌 i) Trans.𝕌-trans i

𝕌-refl : ∀ {i} → A ≈ B ∈ 𝕌 i → A ≈ A ∈ 𝕌 i
𝕌-refl A≈B = 𝕌-trans A≈B (𝕌-sym A≈B)

El-trans : ∀ {i j} (A≈A′ : A ≈ A′ ∈ 𝕌 i) (A′≈A″ : A′ ≈ A″ ∈ 𝕌 j) (A≈A″ : A ≈ A″ ∈ 𝕌 i) →
           a ≈ a′ ∈ El i A≈A′ → a′ ≈ a″ ∈ El j A′≈A″ → a ≈ a″ ∈ El i A≈A″
El-trans {i = i} A≈A′ A′≈A″ A≈A″ = Trans.El-trans i (λ j<i → 𝕌-trans) A≈A′ A′≈A″ A≈A″ (𝕌-refl A≈A″)

El-refl : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈B
El-refl {i = i} A≈B = Trans.El-refl′ i (λ j<i → 𝕌-trans) A≈B (𝕌-refl A≈B)


-- With symmetry and tranitivity, we can concldue 𝕌 and El are PERs, so our claim
-- that it is a PER model is justified.
𝕌-isPER : ∀ i → IsPartialEquivalence (𝕌 i)
𝕌-isPER i = record
  { sym   = 𝕌-sym
  ; trans = 𝕌-trans
  }

𝕌-PER : ℕ → PartialSetoid _ _
𝕌-PER i = record
  { Carrier              = D
  ; _≈_                  = 𝕌 i
  ; isPartialEquivalence = 𝕌-isPER i
  }

module 𝕌R i = PS (𝕌-PER i)

El-swap : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j B≈A
El-swap A≈B B≈A a≈b = El-one-sided′ A≈A B≈A (El-one-sided A≈B A≈A a≈b)
  where A≈A = 𝕌-refl A≈B

El-sym′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i A≈B
El-sym′ A≈B a≈b = El-swap (𝕌-sym A≈B) A≈B b≈a
  where b≈a = El-sym A≈B (𝕌-sym A≈B) a≈b

El-trans′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ a′ ∈ El i A≈B → a′ ≈ a″ ∈ El i A≈B → a ≈ a″ ∈ El i A≈B
El-trans′ A≈B a≈a′ a′≈a″ = El-one-sided (𝕌-refl A≈B) A≈B a≈a″
  where a≈a″ = El-trans A≈B (𝕌-sym A≈B) (𝕌-refl A≈B) a≈a′ (El-swap A≈B (𝕌-sym A≈B) a′≈a″)


El-isPER : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → IsPartialEquivalence (El i A≈B)
El-isPER i A≈B = record
  { sym   = El-sym′ A≈B
  ; trans = El-trans′ A≈B
  }

El-PER : ∀ i → A ≈ B ∈ 𝕌 i → PartialSetoid _ _
El-PER i A≈B = record
  { Carrier              = D
  ; _≈_                  = El i A≈B
  ; isPartialEquivalence = El-isPER i A≈B
  }

module ElR {A B} i (A≈B : A ≈ B ∈ 𝕌 i) = PS (El-PER i A≈B)

-- El respects 𝕌.
El-tranport : ∀ {i j k} (A≈A : A ≈ A ∈ 𝕌 i) (B≈B : B ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈A → A ≈ B ∈ 𝕌 k → a ≈ b ∈ El j B≈B
El-tranport A≈A B≈B a≈b A≈B = El-one-sided′ A≈B B≈B (El-one-sided A≈A A≈B a≈b)

-- 𝕌 and El are cumulative.
mutual

  𝕌-cumu-step : ∀ i → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌 (1 + i)
  𝕌-cumu-step i (ne C≈C′) = ne C≈C′
  𝕌-cumu-step i N         = N
  𝕌-cumu-step i (U′ j<i)  = U′ (m≤n⇒m≤1+n j<i)
  𝕌-cumu-step i (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (𝕌-cumu-step i iA) helper
    where helper : a ≈ a′ ∈ El (1 + i) (𝕌-cumu-step i iA) → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 (1 + i))
          helper a≈a′ = record
            { ⟦T⟧   = ⟦T⟧
            ; ⟦T′⟧  = ⟦T′⟧
            ; ↘⟦T⟧  = ↘⟦T⟧
            ; ↘⟦T′⟧ = ↘⟦T′⟧
            ; T≈T′  = 𝕌-cumu-step i T≈T′
            }
            where open ΠRT (RT (El-lower i iA a≈a′))

  -- Interestingly, in order to prove cumulativity, we must because to show levels can be lowered.
  --
  -- This is very often a blind spot for paper proof because so far we have not seen
  -- another work which has made this lowering operation explicit.
  El-lower : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El (1 + i) (𝕌-cumu-step i A≈B) → a ≈ b ∈ El i A≈B
  El-lower i (ne C≈C′) (ne c≈c′)             = ne c≈c′
  El-lower i N a≈b                           = a≈b
  El-lower i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (m≤n⇒m≤1+n j<i) = a≈b
  El-lower i (Π iA RT) f≈f′ a≈a′
    with El-cumu-step i iA a≈a′
  ...  | a≈a′₁
       with RT a≈a′ | RT (El-lower i iA a≈a′₁) | f≈f′ a≈a′₁
  ...     | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
          | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = record
    { fa     = _
    ; fa′    = _
    ; ↘fa    = ↘fa
    ; ↘fa′   = ↘fa′
    ; fa≈fa′ = 𝕌-irrel T≈T′₁ T≈T′ (El-lower i T≈T′₁ fa≈fa′)
    }

  El-cumu-step : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El (1 + i) (𝕌-cumu-step i A≈B)
  El-cumu-step i (ne C≈C′) (ne c≈c′)         = ne c≈c′
  El-cumu-step i N a≈b                       = a≈b
  El-cumu-step i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (m≤n⇒m≤1+n j<i) = a≈b
  El-cumu-step i (Π iA RT) f≈f′ a≈a′
    with El-lower i iA a≈a′
  ...  | a≈a′₁ = record
    { fa     = fa
    ; fa′    = fa′
    ; ↘fa    = ↘fa
    ; ↘fa′   = ↘fa′
    ; fa≈fa′ = El-cumu-step i T≈T′ fa≈fa′
    }
    where open ΠRT (RT a≈a′₁)
          open Π̂ (f≈f′ a≈a′₁)

𝕌-cumu-steps : ∀ i j → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌 (j + i)
𝕌-cumu-steps i zero A≈B    = A≈B
𝕌-cumu-steps i (suc j) A≈B = 𝕌-cumu-step (j + i) (𝕌-cumu-steps i j A≈B)

𝕌-cumu : ∀ {i j} → i ≤ j → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌 j
𝕌-cumu {_} {_} {i} i≤j A≈B
  rewrite sym (≤-diff-+ i≤j)
        | sym (ℕₚ.+-comm (≤-diff i≤j) i) = 𝕌-cumu-steps i _ A≈B

El-cumu-steps : ∀ i j (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El (j + i) (𝕌-cumu-steps i j A≈B)
El-cumu-steps i zero A≈B a≈b    = a≈b
El-cumu-steps i (suc j) A≈B a≈b = El-cumu-step (j + i) (𝕌-cumu-steps i j A≈B) (El-cumu-steps i j A≈B a≈b)

El-cumu : ∀ {i j} (i≤j : i ≤ j) (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j (𝕌-cumu i≤j A≈B)
El-cumu {i = i} {j} i≤j A≈B a≈b = helper (𝕌-cumu-steps i (≤-diff i≤j) A≈B) (𝕌-cumu i≤j A≈B) a≈b′ eq
  where a≈b′ : _ ≈ _ ∈ El (≤-diff i≤j + i) (𝕌-cumu-steps i (≤-diff i≤j) A≈B)
        a≈b′ = El-cumu-steps i (≤-diff i≤j) A≈B a≈b
        eq = trans (ℕₚ.+-comm (≤-diff i≤j) i) (≤-diff-+ i≤j)
        helper : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → i ≡ j → a ≈ b ∈ El j A≈B′
        helper A≈B A≈B′ a≈b refl = 𝕌-irrel A≈B A≈B′ a≈b

El-transp : ∀ {j k} (A≈B : A ≈ B ∈ 𝕌 j) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 k) → a ≈ b ∈ El j A≈B → A ≡ A′ → a ≈ b ∈ El k A′≈B′
El-transp A≈B A′≈B′ a≈b refl = El-one-sided A≈B A′≈B′ a≈b


-- Properties for the PER models of context stacks and evaluation environments
--
-- These properties essentially just replay the proofs above but just simpler.

-- Symmetry
mutual

  ⊨-sym : ⊨ Γ ≈ Δ → ⊨ Δ ≈ Γ
  ⊨-sym []-≈                              = []-≈
  ⊨-sym (∷-cong {Γ} {Δ} {T} {T′} Γ≈Δ rel) = ∷-cong (⊨-sym Γ≈Δ) helper
    where helper : ρ ≈ ρ′ ∈ ⟦ ⊨-sym Γ≈Δ ⟧ρ → RelTyp _ T′ ρ T ρ′
          helper ρ≈ρ′ = record
            { ⟦T⟧   = ⟦T′⟧
            ; ⟦T′⟧  = ⟦T⟧
            ; ↘⟦T⟧  = ↘⟦T′⟧
            ; ↘⟦T′⟧ = ↘⟦T⟧
            ; T≈T′  = 𝕌-sym T≈T′
            }
            where open RelTyp (rel (⟦⟧ρ-sym (⊨-sym Γ≈Δ) Γ≈Δ ρ≈ρ′))

  ⟦⟧ρ-sym : (Γ≈Δ : ⊨ Γ ≈ Δ) (Δ≈Γ : ⊨ Δ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ′ ≈ ρ ∈ ⟦ Δ≈Γ ⟧ρ
  ⟦⟧ρ-sym []-≈ []-≈ ρ≈ρ′                        = tt
  ⟦⟧ρ-sym {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT) (∷-cong Δ≈Γ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
    with ⟦⟧ρ-sym Γ≈Δ Δ≈Γ ρ≈ρ′
  ...  | ρ′≈ρ                                   = ρ′≈ρ , helper
    where helper : lookup ρ′ 0 ≈ lookup ρ 0 ∈ El _ (RelTyp.T≈T′ (RT′ ρ′≈ρ))
          helper
            with RT ρ≈ρ′ | RT′ ρ′≈ρ
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
               rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁
                     | ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁ = 𝕌-irrel (𝕌-sym T≈T′) T≈T′₁ (El-sym T≈T′ (𝕌-sym T≈T′) ρ0≈ρ′0)


-- ⟦⟧ρ only cares about one side of the relation between context stacks.
⟦⟧ρ-one-sided : (Γ≈Δ : ⊨ Γ ≈ Δ) (Γ≈Δ′ : ⊨ Γ ≈ Δ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ′ ⟧ρ
⟦⟧ρ-one-sided []-≈ []-≈ ρ≈ρ′                                    = tt
⟦⟧ρ-one-sided {_} {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT) (∷-cong Γ≈Δ′ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
  with ⟦⟧ρ-one-sided Γ≈Δ Γ≈Δ′ ρ≈ρ′
...  | ρ≈ρ′₁ = ρ≈ρ′₁ , helper
    where helper : lookup ρ 0 ≈ lookup ρ′ 0 ∈ El _ (RelTyp.T≈T′ (RT′ ρ≈ρ′₁))
          helper
            with RT ρ≈ρ′ | RT′ ρ≈ρ′₁
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
               rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁ = El-one-sided T≈T′ T≈T′₁ ρ0≈ρ′0


⊨-irrel : (Γ≈Δ Γ≈Δ′ : ⊨ Γ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ′ ⟧ρ
⊨-irrel = ⟦⟧ρ-one-sided


⟦⟧ρ-one-sided′ : (Γ≈Δ : ⊨ Γ ≈ Δ) (Γ′≈Δ : ⊨ Γ′ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ′≈Δ ⟧ρ
⟦⟧ρ-one-sided′ Γ≈Δ Γ′≈Δ ρ≈ρ′ = ⟦⟧ρ-sym (⊨-sym Γ′≈Δ) Γ′≈Δ (⟦⟧ρ-one-sided (⊨-sym Γ≈Δ) (⊨-sym Γ′≈Δ) (⟦⟧ρ-sym Γ≈Δ (⊨-sym Γ≈Δ) ρ≈ρ′))

-- Tranitivity
mutual

  ⊨-trans : ⊨ Γ ≈ Γ′ → ⊨ Γ′ ≈ Γ″ → ⊨ Γ ≈ Γ″
  ⊨-trans []-≈ []-≈                                                             = []-≈
  ⊨-trans (∷-cong {_} {_} {T} {T′} Γ≈Γ′ RT) (∷-cong {_} {_} {_} {T″} Γ′≈Γ″ RT′) = ∷-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″) helper
    where helper : ρ ≈ ρ′ ∈ ⟦ ⊨-trans Γ≈Γ′ Γ′≈Γ″ ⟧ρ → RelTyp _ T ρ T″ ρ′
          helper ρ≈ρ′
            with ⊨-refl Γ≈Γ′
          ...  | Γ≈Γ
               with RT (⟦⟧ρ-one-sided Γ≈Γ Γ≈Γ′ (⟦⟧ρ-refl (⊨-trans Γ≈Γ′ Γ′≈Γ″) Γ≈Γ ρ≈ρ′))
                  | RT′ (⟦⟧ρ-one-sided′ (⊨-trans Γ≈Γ′ Γ′≈Γ″) Γ′≈Γ″ ρ≈ρ′)
          ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                  rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
            { ⟦T⟧   = _
            ; ⟦T′⟧  = _
            ; ↘⟦T⟧  = ↘⟦T⟧
            ; ↘⟦T′⟧ = ↘⟦T′⟧₁
            ; T≈T′  = 𝕌-trans T≈T′ T≈T′₁
            }

  ⟦⟧ρ-trans : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ′≈Γ″ : ⊨ Γ′ ≈ Γ″) (Γ≈Γ″ : ⊨ Γ ≈ Γ″) →
              ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ″ ∈ ⟦ Γ′≈Γ″ ⟧ρ → ρ ≈ ρ″ ∈ ⟦ Γ≈Γ″ ⟧ρ
  ⟦⟧ρ-trans []-≈ []-≈ []-≈ ρ≈ρ′ ρ′≈ρ″                                            = tt
  ⟦⟧ρ-trans {_} {_} {_} {ρ} {ρ′} {ρ″} (∷-cong Γ≈Γ′ RT) (∷-cong Γ′≈Γ″ RT′) (∷-cong Γ≈Γ″ RT″) (ρ≈ρ′ , ρ0≈ρ′0) (ρ′≈ρ″ , ρ′0≈ρ″0)
    with ⟦⟧ρ-trans Γ≈Γ′ Γ′≈Γ″ Γ≈Γ″ ρ≈ρ′ ρ′≈ρ″
  ...  | ρ≈ρ″                                                                    = ρ≈ρ″ , helper
    where helper : lookup ρ 0 ≈ lookup ρ″ 0 ∈ El _ (RelTyp.T≈T′ (RT″ ρ≈ρ″))
          helper
            with RT ρ≈ρ′ | RT′ ρ′≈ρ″ | RT″ ρ≈ρ″
          ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
               | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
               rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁
                     | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₂
                     | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧₂ = 𝕌-irrel (𝕌-trans T≈T′ T≈T′₁) T≈T′₂
                                                      (El-trans T≈T′ T≈T′₁ (𝕌-trans T≈T′ T≈T′₁) ρ0≈ρ′0 ρ′0≈ρ″0)

  ⊨-refl : ⊨ Γ ≈ Γ′ → ⊨ Γ ≈ Γ
  ⊨-refl Γ≈Γ′ = ⊨-trans Γ≈Γ′ (⊨-sym Γ≈Γ′)

  ⟦⟧ρ-refl : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ≈Γ : ⊨ Γ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ ∈ ⟦ Γ≈Γ ⟧ρ
  ⟦⟧ρ-refl Γ≈Γ′ Γ≈Γ ρ≈ρ′ = ⟦⟧ρ-trans Γ≈Γ′ (⊨-sym Γ≈Γ′) Γ≈Γ ρ≈ρ′ (⟦⟧ρ-sym Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ≈ρ′)


-- Show that ⊨ and ⟦⟧ρ are PERs.
⊨-isPER : IsPartialEquivalence ⊨_≈_
⊨-isPER = record
  { sym   = ⊨-sym
  ; trans = ⊨-trans
  }

⊨-PER : PartialSetoid _ _
⊨-PER = record
  { Carrier              = Ctx
  ; _≈_                  = ⊨_≈_
  ; isPartialEquivalence = ⊨-isPER
  }

module ⊨R = PS ⊨-PER

⟦⟧ρ-swap : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) (Γ′≈Γ : ⊨ Γ′ ≈ Γ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ′ ∈ ⟦ Γ′≈Γ ⟧ρ
⟦⟧ρ-swap Γ≈Γ′ Γ′≈Γ ρ≈ρ′ = ⟦⟧ρ-one-sided′ (⊨-refl Γ≈Γ′) Γ′≈Γ (⟦⟧ρ-one-sided Γ≈Γ′ (⊨-refl Γ≈Γ′) ρ≈ρ′)

⟦⟧ρ-sym′ : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ ∈ ⟦ Γ≈Γ′ ⟧ρ
⟦⟧ρ-sym′ Γ≈Γ′ ρ≈ρ′ = ⟦⟧ρ-swap (⊨-sym Γ≈Γ′) Γ≈Γ′ (⟦⟧ρ-sym Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ≈ρ′)

⟦⟧ρ-trans′ : (Γ≈Γ′ : ⊨ Γ ≈ Γ′) → ρ ≈ ρ′ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ′ ≈ ρ″ ∈ ⟦ Γ≈Γ′ ⟧ρ → ρ ≈ ρ″ ∈ ⟦ Γ≈Γ′ ⟧ρ
⟦⟧ρ-trans′ Γ≈Γ′ ρ≈ρ′ ρ′≈ρ″ = ⟦⟧ρ-one-sided (⊨-refl Γ≈Γ′) Γ≈Γ′
                                           (⟦⟧ρ-trans Γ≈Γ′ (⊨-sym Γ≈Γ′) (⊨-refl Γ≈Γ′)
                                                      ρ≈ρ′ (⟦⟧ρ-swap Γ≈Γ′ (⊨-sym Γ≈Γ′) ρ′≈ρ″))

⟦⟧ρ-isPER : (Γ≈Δ : ⊨ Γ ≈ Δ) → IsPartialEquivalence ⟦ Γ≈Δ ⟧ρ
⟦⟧ρ-isPER Γ≈Δ = record
  { sym   = ⟦⟧ρ-sym′ Γ≈Δ
  ; trans = ⟦⟧ρ-trans′ Γ≈Δ
  }

⟦⟧ρ-PER : ⊨ Γ ≈ Δ → PartialSetoid _ _
⟦⟧ρ-PER Γ≈Δ = record
  { Carrier              = Env
  ; _≈_                  = ⟦ Γ≈Δ ⟧ρ

  ; isPartialEquivalence = ⟦⟧ρ-isPER Γ≈Δ
  }

module ⟦⟧ρR {Γ Δ} (Γ≈Δ : ⊨ Γ ≈ Δ) = PS (⟦⟧ρ-PER Γ≈Δ)


⟦⟧ρ-transport : (⊨Γ : ⊨ Γ) (⊨Δ : ⊨ Δ) → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → ⊨ Γ ≈ Δ → ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ
⟦⟧ρ-transport ⊨Γ ⊨Δ ρ≈ρ′ Γ≈Δ = ⟦⟧ρ-one-sided′ Γ≈Δ ⊨Δ (⟦⟧ρ-one-sided ⊨Γ Γ≈Δ ρ≈ρ′)


⊨-resp-len : ⊨ Γ ≈ Δ → len Γ ≡ len Δ
⊨-resp-len []-≈           = refl
⊨-resp-len (∷-cong Γ≈Δ _) = cong ℕ.suc (⊨-resp-len Γ≈Δ)


-- If two context stacks are related, then they can both generate initial evaluation
-- environments, and the generated environments are related.
InitEnvs-related : (Γ≈Δ : ⊨ Γ ≈ Δ) → ∃₂ λ ρ ρ′ → InitEnvs Γ ρ × InitEnvs Δ ρ′ × (ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ)
InitEnvs-related []-≈           = emp , emp , base , base , tt
InitEnvs-related {_ ∷ Γ} {_ ∷ Δ} (∷-cong Γ≈Δ rel)
  with InitEnvs-related Γ≈Δ
...  | ρ , ρ′ , ↘ρ , ↘ρ′ , ρ≈ρ′  = ρ ↦ l′ ⟦T⟧ (len Γ) , ρ′ ↦ l′ ⟦T′⟧ (len Δ)
                                 , s-∷ ↘ρ ↘⟦T⟧ , s-∷ ↘ρ′ ↘⟦T′⟧
                                 , ρ↦⟦T⟧≈ρ′↦⟦T′⟧
  where
    open RelTyp (rel ρ≈ρ′)

    ρ↦⟦T⟧≈ρ′↦⟦T′⟧ : ρ ↦ l′ ⟦T⟧ (len Γ) ≈ ρ′ ↦ l′ ⟦T′⟧ (len Δ) ∈ ⟦ ∷-cong Γ≈Δ rel ⟧ρ
    ρ↦⟦T⟧≈ρ′↦⟦T′⟧ = ρ≈ρ′ , Bot⊆El T≈T′ (subst (λ n → l (len Γ) ≈ l n ∈ Bot) (⊨-resp-len Γ≈Δ) (Bot-l _))
