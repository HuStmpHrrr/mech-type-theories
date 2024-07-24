{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Various properties of the PER model
module Mint.Semantics.Properties.PER (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties as ℕₚ
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib hiding (lookup)

open import Mint.Statics.Syntax
open import Mint.Semantics.Domain
open import Mint.Semantics.Evaluation
open import Mint.Semantics.Readback
open import Mint.Semantics.Realizability fext
open import Mint.Semantics.PER

open import Mint.Semantics.Properties.PER.Core fext public
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Properties.Evaluation fext

-- Monotonicity of Top and Bot relative to UMoTs
Top-mon : ∀ (κ : UMoT) → d ≈ d′ ∈ Top → d [ κ ] ≈ d′ [ κ ] ∈ Top
Top-mon {d} {d′} κ d≈d′ ns κ′
  with d≈d′ ns (κ ø κ′)
...  | w , ↘w , ↘w′ = w , subst (Rf ns -_↘ w) (sym (Df-comp d κ κ′)) ↘w , subst (Rf ns -_↘ w) (sym (Df-comp d′ κ κ′)) ↘w′

Bot-mon : ∀ (κ : UMoT) → c ≈ c′ ∈ Bot → c [ κ ] ≈ c′ [ κ ] ∈ Bot
Bot-mon {c} {c′} κ c≈c′ ns κ′
  with c≈c′ ns (κ ø κ′)
...  | u , ↘u , ↘u′ = u , subst (Re ns -_↘ u) (sym (Dn-comp c κ κ′)) ↘u , subst (Re ns -_↘ u) (sym (Dn-comp c′ κ κ′)) ↘u′

-- Top and Bot are PERs.
Top-sym : d ≈ d′ ∈ Top → d′ ≈ d ∈ Top
Top-sym d≈d′ ns κ
  with d≈d′ ns κ
...  | w , ↘w , ↘w′ = w , ↘w′ , ↘w

Bot-sym : c ≈ c′ ∈ Bot → c′ ≈ c ∈ Bot
Bot-sym c≈c′ ns κ
  with c≈c′ ns κ
...  | u , ↘u , ↘u′ = u , ↘u′ , ↘u

Top-trans : d ≈ d′ ∈ Top → d′ ≈ d″ ∈ Top → d ≈ d″ ∈ Top
Top-trans d≈d′ d′≈d″ ns κ
  with d≈d′ ns κ | d′≈d″ ns κ
...  | w  , ↘w₁  , ↘w₂
     | w′ , ↘w′₁ , ↘w′₂ = w , ↘w₁ , subst (Rf ns - _ ↘_) (sym (Rf-det ↘w₂ ↘w′₁)) ↘w′₂

Bot-trans : c ≈ c′ ∈ Bot → c′ ≈ c″ ∈ Bot → c ≈ c″ ∈ Bot
Bot-trans c≈c′ c′≈c″ ns κ
  with c≈c′ ns κ | c′≈c″ ns κ
...  | u  , ↘u₁  , ↘u₂
     | u′ , ↘u′₁ , ↘u′₂ = u , ↘u₁ , subst (Re ns - _ ↘_) (sym (Re-det ↘u₂ ↘u′₁)) ↘u′₂

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
Bot⊆Top c≈c′ ns κ
  with c≈c′ ns κ
...  | u , ↘u , ↘u′ = ne u , Rne ns ↘u , Rne ns ↘u′

unbox-Bot : ∀ n → c ≈ c′ ∈ Bot → unbox n c ≈ unbox n c′ ∈ Bot
unbox-Bot n c≈c′ ns κ
  with c≈c′ (ns ∥ (O κ n)) (κ ∥ n)
...  | u , ↘u , ↘u′ = unbox (O κ n) u , Ru ns (O κ n) ↘u , Ru ns (O κ n) ↘u′

$-Bot : c ≈ c′ ∈ Bot → d ≈ d′ ∈ Top → c $ d ≈ c′ $ d′ ∈ Bot
$-Bot c≈c′ d≈d′ ns κ
  with c≈c′ ns κ | d≈d′ ns κ
...  | u , ↘u , ↘u′
     | w , ↘w , ↘w′ = u $ w , R$ ns ↘u ↘w , R$ ns ↘u′ ↘w′

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

-- Nat is also monotonic.
Nat-mon : (κ : UMoT) → a ≈ b ∈ Nat → a [ κ ] ≈ b [ κ ] ∈ Nat
Nat-mon κ ze        = ze
Nat-mon κ (su a≈b)  = su (Nat-mon κ a≈b)
Nat-mon κ (ne c≈c′) = ne (Bot-mon κ c≈c′)


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
      𝕌-sym (□ A≈A′)                            = □ λ κ → 𝕌-sym (A≈A′ κ)
      𝕌-sym (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (λ κ → 𝕌-sym (iA κ)) helper
        where helper : ∀ κ → a ≈ a′ ∈ El i (𝕌-sym (iA κ)) → ΠRT T′ (ρ′ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 i)
              helper κ a≈a′ = record
                { ⟦T⟧   = ⟦T′⟧
                ; ⟦T′⟧  = ⟦T⟧
                ; ↘⟦T⟧  = ↘⟦T′⟧
                ; ↘⟦T′⟧ = ↘⟦T⟧
                ; T≈T′  = 𝕌-sym T≈T′
                }
                where open ΠRT (RT κ (El-sym (𝕌-sym (iA κ)) (iA κ) a≈a′))

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
      El-sym (□ A≈A′) (□ A≈A′₁) a≈b n κ   = record
        { ua    = ub
        ; ub    = ua
        ; ↘ua   = ↘ub
        ; ↘ub   = ↘ua
        ; ua≈ub = El-sym (A≈A′ (ins κ n)) (A≈A′₁ (ins κ n)) ua≈ub
        }
        where open □̂ (a≈b n κ)
      El-sym (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈a′
        with El-sym (iA′ κ) (iA κ) a≈a′
      ...  | a≈a′₁
           with RT κ a≈a′₁ | RT′ κ a≈a′ | f≈f′ κ a≈a′₁
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
El-one-sided (□ A≈B) (□ A≈B′) a≈b n κ = record
  { ua    = ua
  ; ub    = ub
  ; ↘ua   = ↘ua
  ; ↘ub   = ↘ub
  ; ua≈ub = El-one-sided (A≈B (ins κ n)) (A≈B′ (ins κ n)) ua≈ub
  }
  where open □̂ (a≈b n κ)
El-one-sided (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈a′
  with El-one-sided (iA′ κ) (iA κ) a≈a′
...  | a≈a′₁
     with RT κ a≈a′₁ | RT′ κ a≈a′ | f≈f′ κ a≈a′₁
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
      𝕌-trans (□ A≈A′) (□ A′≈A″)    = □ (λ κ → 𝕌-trans (A≈A′ κ) (A′≈A″ κ))
      𝕌-trans (Π {_} {_} {T} {ρ} iA RT) (Π {_} {_} {T′} {ρ′} {T″} {ρ″} iA′ RT′) = Π (λ κ → 𝕌-trans (iA κ) (iA′ κ)) helper
        where helper : ∀ κ → a ≈ a′ ∈ El i (𝕌-trans (iA κ) (iA′ κ)) → ΠRT T (ρ [ κ ] ↦ a) T″ (ρ″ [ κ ] ↦ a′) (𝕌 i)
              helper κ a≈a′
                with 𝕌-refl (iA κ) | 𝕌-trans (iA κ) (iA′ κ)
              ...  | A≈A | A≈A″
                   with RT κ (El-one-sided A≈A (iA κ) (El-refl A≈A″ A≈A a≈a′))
                      | RT′ κ (El-one-sided′ A≈A″ (iA′ κ) a≈a′)
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
      -- three premises in transitivity and remove this duplication later.
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
      El-trans (□ A≈A′) (□ A′≈A″) (□ A≈A″) (□ A≈A) a≈a′ a′≈a″ n κ    = record
        { ua    = □̂₁.ua
        ; ub    = □̂₂.ub
        ; ↘ua   = □̂₁.↘ua
        ; ↘ub   = □̂₂.↘ub
        ; ua≈ub = El-trans (A≈A′ (ins κ n)) (A′≈A″ (ins κ n)) (A≈A″ (ins κ n)) (A≈A (ins κ n))
                           □̂₁.ua≈ub
                           (subst (_≈ _ ∈ El _ (A′≈A″ (ins κ n))) (unbox-det □̂₂.↘ua □̂₁.↘ub) □̂₂.ua≈ub)
        }
        where module □̂₁ = □̂ (a≈a′ n κ)
              module □̂₂ = □̂ (a′≈a″ n κ)
      El-trans (Π iA RT) (Π iA′ RT′) (Π iA″ RT″) (Π iA‴ RT‴) f≈f′ f′≈f″ κ a≈a′
        with El-one-sided (iA″ κ) (iA κ) a≈a′ | El-one-sided′ (iA″ κ) (iA′ κ) a≈a′
      ...  | a≈a′₁ | a≈a′₂
           with El-refl′ (iA κ) (iA‴ κ) a≈a′₁ | El-refl (iA κ) (iA‴ κ) a≈a′₁
      ...     | a≈a | a≈a₁
              with RT κ a≈a | RT′ κ a≈a′₂ | RT″ κ a≈a′ | RT‴ κ a≈a₁ | f≈f′ κ a≈a | f′≈f″ κ a≈a′₂
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


-- With symmetry and transitivity, we can concldue 𝕌 and El are PERs, so our claim
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
El-transport : ∀ {i j k} (A≈A : A ≈ A ∈ 𝕌 i) (B≈B : B ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈A → A ≈ B ∈ 𝕌 k → a ≈ b ∈ El j B≈B
El-transport A≈A B≈B a≈b A≈B = El-one-sided′ A≈B B≈B (El-one-sided A≈A A≈B a≈b)


-- 𝕌 and El are monotonic.
--
-- This is THE property which we target to ensure the Kripke structure of □ is
-- internalized, so our proof technique is largely the same as regular MLTT.
𝕌-mon : ∀ {i} (κ : UMoT) → A ≈ B ∈ 𝕌 i → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i
𝕌-mon κ (ne C≈C′)                            = ne (Bot-mon κ C≈C′)
𝕌-mon κ N                                    = N
𝕌-mon κ (U′ j<i)                             = U′ j<i
𝕌-mon κ (□ {A} {B} A≈B)                      = □ λ κ′ → helper κ κ′
  where helper : ∀ κ κ′ → A [ ins κ 1 ] [ κ′ ] ≈ B [ ins κ 1 ] [ κ′ ] ∈ 𝕌 _
        helper κ κ′
          with A≈B (ins κ 1 ø κ′)
        ...  | rel
             rewrite D-comp A (ins κ 1) κ′
                   | D-comp B (ins κ 1) κ′   = rel
𝕌-mon κ (Π {A} {B} {T} {ρ} {T′} {ρ′} A≈B RT) = Π (λ κ′ → helper κ κ′) helper′
  where helper : ∀ κ κ′ → A [ κ ] [ κ′ ] ≈ B [ κ ] [ κ′ ] ∈ 𝕌 _
        helper κ κ′
          rewrite D-comp A κ κ′
                | D-comp B κ κ′              = A≈B (κ ø κ′)
        helper′ : ∀ κ′ → a ≈ b ∈ El _ (helper κ κ′) → ΠRT T (ρ [ κ ] [ κ′ ] ↦ a) T′ (ρ′ [ κ ] [ κ′ ] ↦ b) (𝕌 _)
        helper′ κ′ a≈b
          rewrite D-comp A κ κ′
                | D-comp B κ κ′
                | ρ-comp ρ κ κ′
                | ρ-comp ρ′ κ κ′             = RT (κ ø κ′) a≈b


El-mon : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (κ : UMoT) (A≈B′ : A [ κ ] ≈ B [ κ ] ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a [ κ ] ≈ b [ κ ] ∈ El j A≈B′
El-mon (ne C≈C′) κ (ne C≈C′₁) (ne c≈c′) = ne (Bot-mon κ c≈c′)
El-mon N κ N a≈b                        = Nat-mon κ a≈b
El-mon (U′ k<i) κ (U k<j eq) a≈b
  rewrite ≡-irrelevant eq refl
        | 𝕌-wellfounded-≡-𝕌 _ k<i
        | 𝕌-wellfounded-≡-𝕌 _ k<j       = 𝕌-mon κ a≈b
El-mon {□ A} {□ B} {a} {b} (□ A≈B) κ (□ A≈B′) a≈b n κ′
  with A≈B′ (ins κ′ n)
... | rel
  rewrite D-comp a κ κ′
        | D-comp b κ κ′
        | D-comp A (ins κ 1) (ins κ′ n)
        | D-comp B (ins κ 1) (ins κ′ n)
        | ins-1-ø-ins-n κ κ′ n          = record
  { ua    = ua
  ; ub    = ub
  ; ↘ua   = ↘ua
  ; ↘ub   = ↘ub
  ; ua≈ub = 𝕌-irrel (A≈B (ins (κ ø κ′) n)) rel ua≈ub
  }
  where open □̂ (a≈b n (κ ø κ′))
El-mon {Π A _ ρ} {Π A′ _ ρ′} {f} {f′} (Π iA RT) κ (Π iA′ RT′) f≈f′ {a} {a′} κ′ a≈a′
  rewrite D-comp f κ κ′
        | D-comp f′ κ κ′                = record
  { fa     = fa
  ; fa′    = fa′
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = helper fa≈fa′
  }
  where transp : a ≈ a′ ∈ El _ (iA′ κ′) → a ≈ a′ ∈ El _ (iA (κ ø κ′))
        transp a≈a′
          with iA′ κ′
        ...  | rel
             rewrite D-comp A κ κ′
                   | D-comp A′ κ κ′ = 𝕌-irrel rel (iA (κ ø κ′)) a≈a′
        open Π̂ (f≈f′ (κ ø κ′) (transp a≈a′))

        helper : fa ≈ fa′ ∈ El _ (ΠRT.T≈T′ (RT (κ ø κ′) (transp a≈a′))) → fa ≈ fa′ ∈ El _ (ΠRT.T≈T′ (RT′ κ′ a≈a′))
        helper fa≈fa′
          with RT (κ ø κ′) (transp a≈a′) | RT′ κ′ a≈a′
        ... | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
            | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
            rewrite ρ-comp ρ κ κ′
                  | ρ-comp ρ′ κ κ′
                  | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                  | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = 𝕌-irrel T≈T′ T≈T′₁ fa≈fa′

-- 𝕌 and El are cumulative.
mutual

  𝕌-cumu-step : ∀ i → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌 (suc i)
  𝕌-cumu-step i (ne C≈C′) = ne C≈C′
  𝕌-cumu-step i N         = N
  𝕌-cumu-step i (U′ j<i)  = U′ (m≤n⇒m≤1+n j<i)
  𝕌-cumu-step i (□ A≈B)   = □ λ κ → 𝕌-cumu-step i (A≈B κ)
  𝕌-cumu-step i (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (λ κ → 𝕌-cumu-step i (iA κ)) helper
    where helper : ∀ κ → a ≈ a′ ∈ El (suc i) (𝕌-cumu-step i (iA κ)) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 (suc i))
          helper κ a≈a′ = record
            { ⟦T⟧   = ⟦T⟧
            ; ⟦T′⟧  = ⟦T′⟧
            ; ↘⟦T⟧  = ↘⟦T⟧
            ; ↘⟦T′⟧ = ↘⟦T′⟧
            ; T≈T′  = 𝕌-cumu-step i T≈T′
            }
            where open ΠRT (RT κ (El-lower i (iA κ) a≈a′))

  -- Interestingly, in order to prove cumulativity, we must because to show levels can be lowered.
  --
  -- This is very often a blind spot for paper proof because so far we have not seen
  -- another work which has made this lowering operation explicit.
  El-lower : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El (suc i) (𝕌-cumu-step i A≈B) → a ≈ b ∈ El i A≈B
  El-lower i (ne C≈C′) (ne c≈c′)             = ne c≈c′
  El-lower i N a≈b                           = a≈b
  El-lower i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (m≤n⇒m≤1+n j<i) = a≈b
  El-lower i (□ A≈B) a≈b n κ                 = record
    { ua    = ua
    ; ub    = ub
    ; ↘ua   = ↘ua
    ; ↘ub   = ↘ub
    ; ua≈ub = El-lower i (A≈B (ins κ n)) ua≈ub
    }
    where open □̂ (a≈b n κ)
  El-lower i (Π iA RT) f≈f′ κ a≈a′
    with El-cumu-step i (iA κ) a≈a′
  ...  | a≈a′₁
       with RT κ a≈a′ | RT κ (El-lower i (iA κ) a≈a′₁) | f≈f′ κ a≈a′₁
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

  El-cumu-step : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El (suc i) (𝕌-cumu-step i A≈B)
  El-cumu-step i (ne C≈C′) (ne c≈c′)         = ne c≈c′
  El-cumu-step i N a≈b                       = a≈b
  El-cumu-step i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (m≤n⇒m≤1+n j<i) = a≈b
  El-cumu-step i (□ A≈B) a≈b n κ             = record
    { ua    = ua
    ; ub    = ub
    ; ↘ua   = ↘ua
    ; ↘ub   = ↘ub
    ; ua≈ub = El-cumu-step i (A≈B (ins κ n)) ua≈ub
    }
    where open □̂ (a≈b n κ)
  El-cumu-step i (Π iA RT) f≈f′ κ a≈a′
    with El-lower i (iA κ) a≈a′
  ...  | a≈a′₁ = record
    { fa     = fa
    ; fa′    = fa′
    ; ↘fa    = ↘fa
    ; ↘fa′   = ↘fa′
    ; fa≈fa′ = El-cumu-step i T≈T′ fa≈fa′
    }
    where open ΠRT (RT κ a≈a′₁)
          open Π̂ (f≈f′ κ a≈a′₁)

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
  ⊨-sym (κ-cong Γ≈Δ)                      = κ-cong (⊨-sym Γ≈Δ)
  ⊨-sym (∺-cong {Γ} {Δ} {T} {T′} Γ≈Δ rel) = ∺-cong (⊨-sym Γ≈Δ) helper
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
  ⟦⟧ρ-sym (κ-cong Γ≈Δ) (κ-cong Δ≈Γ) (ρ≈ρ′ , eq) = ⟦⟧ρ-sym Γ≈Δ Δ≈Γ ρ≈ρ′ , sym eq
  ⟦⟧ρ-sym {_} {_} {ρ} {ρ′} (∺-cong Γ≈Δ RT) (∺-cong Δ≈Γ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
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
⟦⟧ρ-one-sided (κ-cong Γ≈Δ) (κ-cong Γ≈Δ′) (ρ≈ρ′ , eq)            = ⟦⟧ρ-one-sided Γ≈Δ Γ≈Δ′ ρ≈ρ′ , eq
⟦⟧ρ-one-sided {_} {_} {_} {ρ} {ρ′} (∺-cong Γ≈Δ RT) (∺-cong Γ≈Δ′ RT′) (ρ≈ρ′ , ρ0≈ρ′0)
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

-- Transitivity
mutual

  ⊨-trans : ⊨ Γ ≈ Γ′ → ⊨ Γ′ ≈ Γ″ → ⊨ Γ ≈ Γ″
  ⊨-trans []-≈ []-≈                                                             = []-≈
  ⊨-trans (κ-cong Γ≈Γ′) (κ-cong Γ′≈Γ″)                                          = κ-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″)
  ⊨-trans (∺-cong {_} {_} {T} {T′} Γ≈Γ′ RT) (∺-cong {_} {_} {_} {T″} Γ′≈Γ″ RT′) = ∺-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″) helper
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
  ⟦⟧ρ-trans (κ-cong Γ≈Γ′) (κ-cong Γ′≈Γ″) (κ-cong Γ≈Γ″) (ρ≈ρ′ , eq) (ρ′≈ρ″ , eq′) = ⟦⟧ρ-trans Γ≈Γ′ Γ′≈Γ″ Γ≈Γ″ ρ≈ρ′ ρ′≈ρ″ , trans eq eq′
  ⟦⟧ρ-trans {_} {_} {_} {ρ} {ρ′} {ρ″} (∺-cong Γ≈Γ′ RT) (∺-cong Γ′≈Γ″ RT′) (∺-cong Γ≈Γ″ RT″) (ρ≈ρ′ , ρ0≈ρ′0) (ρ′≈ρ″ , ρ′0≈ρ″0)
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
  { Carrier              = Ctxs
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
  { Carrier              = Envs
  ; _≈_                  = ⟦ Γ≈Δ ⟧ρ

  ; isPartialEquivalence = ⟦⟧ρ-isPER Γ≈Δ
  }

module ⟦⟧ρR {Γ Δ} (Γ≈Δ : ⊨ Γ ≈ Δ) = PS (⟦⟧ρ-PER Γ≈Δ)


⟦⟧ρ-transport : (⊨Γ : ⊨ Γ) (⊨Δ : ⊨ Δ) → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → ⊨ Γ ≈ Δ → ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ
⟦⟧ρ-transport ⊨Γ ⊨Δ ρ≈ρ′ Γ≈Δ = ⟦⟧ρ-one-sided′ Γ≈Δ ⊨Δ (⟦⟧ρ-one-sided ⊨Γ Γ≈Δ ρ≈ρ′)


-- ⟦⟧ρ is monotonic.
⟦⟧ρ-mon : ∀ (Γ≈Δ : ⊨ Γ ≈ Δ) (κ : UMoT) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ [ κ ] ≈ ρ′ [ κ ] ∈ ⟦ Γ≈Δ ⟧ρ
⟦⟧ρ-mon []-≈ κ ρ≈ρ′ = tt
⟦⟧ρ-mon {_} {_} {ρ} {ρ′} (κ-cong Γ≈Δ) κ (ρ≈ρ′ , eq)
  rewrite ρ-∥-[] ρ κ 1
        | ρ-∥-[] ρ′ κ 1
        | eq        = ⟦⟧ρ-mon Γ≈Δ (κ ∥ O ρ′ 1) ρ≈ρ′ , refl
⟦⟧ρ-mon {_} {_} {ρ} {ρ′} (∺-cong Γ≈Δ RT) κ (ρ≈ρ′ , ρ0≈ρ′0)
  rewrite sym (drop-mon ρ κ)
        | sym (drop-mon ρ′ κ)
        with ⟦⟧ρ-mon Γ≈Δ κ ρ≈ρ′
...        | ρ≈ρ′₁  = ρ≈ρ′₁ , helper
  where helper : lookup ρ 0 [ κ ] ≈ lookup ρ′ 0 [ κ ] ∈ El _ (RelTyp.T≈T′ (RT ρ≈ρ′₁))
        helper
          with RT ρ≈ρ′ | RT ρ≈ρ′₁
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
             | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
             rewrite ⟦⟧-det ↘⟦T⟧₁ (⟦⟧-mon κ ↘⟦T⟧)
                   | ⟦⟧-det ↘⟦T′⟧₁ (⟦⟧-mon κ ↘⟦T′⟧) = El-mon T≈T′ κ T≈T′₁ ρ0≈ρ′0


⊨-resp-len : ⊨ Γ ≈ Δ → len Γ ≡ len Δ
⊨-resp-len []-≈           = refl
⊨-resp-len (κ-cong Γ≈Δ)   = cong suc (⊨-resp-len Γ≈Δ)
⊨-resp-len (∺-cong Γ≈Δ _) = ⊨-resp-len Γ≈Δ


⊨-resp-head-len : ⊨ Γ ≈ Δ → len (head Γ) ≡ len (head Δ)
⊨-resp-head-len []-≈           = refl
⊨-resp-head-len (κ-cong Γ≈Δ)   = refl
⊨-resp-head-len (∺-cong Γ≈Δ _) rewrite ⊨-resp-head-len Γ≈Δ = refl

⟦⟧ρ-resp-O : ∀ {n} (Γ≈Δ : ⊨ Γ ≈ Δ) → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → n < len Γ → O ρ n ≡ O ρ′ n
⟦⟧ρ-resp-O []-≈ ρ≈ρ′ (s≤s z≤n)                     = refl
⟦⟧ρ-resp-O (κ-cong Γ≈Δ) (ρ≈ρ′ , eq) (s≤s z≤n)      = refl
⟦⟧ρ-resp-O (κ-cong Γ≈Δ) (ρ≈ρ′ , eq) (s≤s (s≤s n<)) = cong₂ _+_ eq (⟦⟧ρ-resp-O Γ≈Δ ρ≈ρ′ (s≤s n<))
⟦⟧ρ-resp-O {_} {_} {ρ} {ρ′} {n} (∺-cong Γ≈Δ _) (ρ≈ρ′ , _) n<
  with ⟦⟧ρ-resp-O Γ≈Δ ρ≈ρ′ n<
...  | res
     rewrite O-drop n ρ
           | O-drop n ρ′                           = res


-- Truncation preserves ⊨
⊨-resp-∥ : ∀ Ψs Ψs′ → ⊨ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ → len Ψs ≡ len Ψs′ → ⊨ Γ ≈ Δ
⊨-resp-∥ [] [] Γ≈Δ eq                                      = Γ≈Δ
⊨-resp-∥ (.[] ∷ Ψs) (.[] ∷ Ψs′) (κ-cong Γ≈Δ) eq            = ⊨-resp-∥ Ψs Ψs′ Γ≈Δ (suc-injective eq)
⊨-resp-∥ ((_ ∷ Ψ) ∷ Ψs) ((_ ∷ Ψ′) ∷ Ψs′) (∺-cong Γ≈Δ _) eq = ⊨-resp-∥ (Ψ ∷ Ψs) (Ψ′ ∷ Ψs′) Γ≈Δ eq


-- Truncation preserves ⟦⟧ρ
⟦⟧ρ-resp-∥ : ∀ Ψs Ψs′ (Γ≈Δ : ⊨ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ) (eq : len Ψs ≡ len Ψs′) →
               ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → ρ ∥ (len Ψs) ≈ ρ′ ∥ (len Ψs) ∈ ⟦ ⊨-resp-∥ Ψs Ψs′ Γ≈Δ eq ⟧ρ
⟦⟧ρ-resp-∥ [] [] Γ≈Δ eq ρ≈ρ′                                            = ρ≈ρ′
⟦⟧ρ-resp-∥ (_ ∷ Ψs) (_ ∷ Ψs′) (κ-cong Γ≈Δ) eq (ρ≈ρ′ , _)                = ⟦⟧ρ-resp-∥ Ψs Ψs′ Γ≈Δ (suc-injective eq) ρ≈ρ′
⟦⟧ρ-resp-∥ ((_ ∷ Ψ) ∷ Ψs) ((_ ∷ Ψ′) ∷ Ψs′) (∺-cong Γ≈Δ _) eq (ρ≈ρ′ , _) = ⟦⟧ρ-resp-∥ (Ψ ∷ Ψs) (Ψ′ ∷ Ψs′) Γ≈Δ eq ρ≈ρ′


-- If two context stacks are related, then they can both generate initial evaluation
-- environments, and the generated environments are related.
InitEnvs-related : (Γ≈Δ : ⊨ Γ ≈ Δ) → ∃₂ λ ρ ρ′ → InitEnvs Γ ρ × InitEnvs Δ ρ′ × (ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ)
InitEnvs-related []-≈           = empty , empty , base , base , tt
InitEnvs-related (κ-cong Γ≈Δ)
  with InitEnvs-related Γ≈Δ
...  | ρ , ρ′ , ↘ρ , ↘ρ′ , ρ≈ρ′ = ext ρ 1 , ext ρ′ 1 , s-κ ↘ρ , s-κ ↘ρ′ , ρ≈ρ′ , refl
InitEnvs-related {(_ ∷ Ψ) ∷ _} {(_ ∷ Ψ′) ∷ _} (∺-cong Γ≈Δ rel)
  with InitEnvs-related Γ≈Δ
...  | ρ , ρ′ , ↘ρ , ↘ρ′ , ρ≈ρ′  = ρ ↦ l′ ⟦T⟧ (len Ψ) , ρ′ ↦ l′ ⟦T′⟧ (len Ψ′)
                                 , s-∺ ↘ρ ↘⟦T⟧ , s-∺ ↘ρ′ ↘⟦T′⟧
                                 , ρ↦⟦T⟧≈ρ′↦⟦T′⟧
  where
    open RelTyp (rel ρ≈ρ′)

    ρ↦⟦T⟧≈ρ′↦⟦T′⟧ : ρ ↦ l′ ⟦T⟧ (len Ψ) ≈ ρ′ ↦ l′ ⟦T′⟧ (len Ψ′) ∈ ⟦ ∺-cong Γ≈Δ rel ⟧ρ
    ρ↦⟦T⟧≈ρ′↦⟦T′⟧
      rewrite drop-↦ ρ (l′ ⟦T⟧ (len Ψ))
            | drop-↦ ρ′ (l′ ⟦T′⟧ (len Ψ′)) = ρ≈ρ′ , realizability-Re T≈T′ (subst (λ n → l (len Ψ) ≈ l n ∈ Bot) (⊨-resp-head-len Γ≈Δ) (Bot-l _))
