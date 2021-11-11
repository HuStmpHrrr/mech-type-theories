{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.PER (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Induction
open import Data.Nat.Properties as ℕₚ
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib

open import kMLTT.Statics.Syntax
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.PER

open import kMLTT.Semantics.Properties.Domain fext

Top-mon : ∀ (κ : UnMoT) → d ≈ d′ ∈ Top → d [ κ ] ≈ d′ [ κ ] ∈ Top
Top-mon {d} {d′} κ d≈d′ ns κ′
  with d≈d′ ns (κ ø κ′)
...  | res
     rewrite Df-comp d κ κ′
           | Df-comp d′ κ κ′ = res

Bot-mon : ∀ (κ : UnMoT) → c ≈ c′ ∈ Bot → c [ κ ] ≈ c′ [ κ ] ∈ Bot
Bot-mon {c} {c′} κ c≈c′ ns κ′
  with c≈c′ ns (κ ø κ′)
...  | res
     rewrite Dn-comp c κ κ′
           | Dn-comp c′ κ κ′ = res

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
     | w′ , ↘w′₁ , ↘w′₂
     rewrite Rf-det ↘w₂ ↘w′₁ = w′ , ↘w₁ , ↘w′₂

Bot-trans : c ≈ c′ ∈ Bot → c′ ≈ c″ ∈ Bot → c ≈ c″ ∈ Bot
Bot-trans c≈c′ c′≈c″ ns κ
  with c≈c′ ns κ | c′≈c″ ns κ
...  | u  , ↘u₁  , ↘u₂
     | u′ , ↘u′₁ , ↘u′₂
     rewrite Re-det ↘u₂ ↘u′₁ = u′ , ↘u₁ , ↘u′₂

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


-- two important helpers which essentially erase some technical details
𝕌-wellfounded-≡ : ∀ {j i i′} (j<i : j < i) (j<i′ : j < i′) → 𝕌-wellfounded i j<i ≡ 𝕌-wellfounded i′ j<i′
𝕌-wellfounded-≡ (s≤s j≤i) (s≤s j≤i′) = cong (PERDef.𝕌 _)
                                            (implicit-extensionality fext
                                              λ {j′} → fext λ j′<j → 𝕌-wellfounded-≡ (≤-trans j′<j j≤i) (≤-trans j′<j j≤i′))


𝕌-wellfounded-≡-𝕌 : ∀ i {j} (j<i : j < i) → 𝕌-wellfounded i j<i ≡ 𝕌 j
𝕌-wellfounded-≡-𝕌 (suc i) {j} (s≤s j≤i) = cong (PERDef.𝕌 _)
                                               (implicit-extensionality fext
                                                 λ {j′} → fext (λ j<j′ → 𝕌-wellfounded-≡ (≤-trans j<j′ j≤i) j<j′))


private
  module <-Measure = Measure <-wellFounded (λ x → x)

  module Sym i (rc : ∀ j → j < i → ∀ {A′ B′} → A′ ≈ B′ ∈ 𝕌 j → B′ ≈ A′ ∈ 𝕌 j) where

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

      El-sym : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
      El-sym (ne _) (ne _) (ne c≈c′)      = ne (Bot-sym c≈c′)
      El-sym N N a≈b                      = Nat-sym a≈b
      El-sym (U′ j<i) (U j<i′ eq) a≈b
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<i′ = rc _ j<i′ a≈b
      El-sym (□ A≈A′) (□ A≈A′₁) a≈b n κ   = record
        { ua    = ub
        ; ub    = ua
        ; ↘ua   = ↘ub
        ; ↘ub   = ↘ua
        ; ua≈ub = El-sym (A≈A′ κ) (A≈A′₁ κ) ua≈ub
        }
        where open □̂ (a≈b n κ)
      El-sym (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈a′
        with El-sym (iA′ κ) (iA κ) a≈a′
      ...  | a≈a′₁
           with RT κ a≈a′₁ | RT′ κ a≈a′ | f≈f′ κ a≈a′₁
      ... | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
          | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁
                | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁      = record
        { fa     = _
        ; fa′    = _
        ; ↘fa    = ↘fa′
        ; ↘fa′   = ↘fa
        ; fa≈fa′ = El-sym T≈T′₁ T≈T′ fa≈fa′
        ; nat    = nat′
        ; nat′   = nat
        }

𝕌-sym : ∀ i → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
𝕌-sym i = <-Measure.wfRec (λ i → ∀ {A B} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i) Sym.𝕌-sym i

El-sym : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
El-sym i = Sym.El-sym i (λ j _ → 𝕌-sym j)


El-one-sided : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B′ ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A≈B′
El-one-sided i (ne _) (ne _) a≈b        = a≈b
El-one-sided i N N a≈b                  = a≈b
El-one-sided i (U′ j<i) (U′ j<i′) a≈b
  rewrite ≤-irrelevant j<i j<i′         = a≈b
El-one-sided i (□ A≈B) (□ A≈B′) a≈b n κ = record
  { ua    = ua
  ; ub    = ub
  ; ↘ua   = ↘ua
  ; ↘ub   = ↘ub
  ; ua≈ub = El-one-sided i (A≈B κ) (A≈B′ κ) ua≈ub
  }
  where open □̂ (a≈b n κ)
El-one-sided i (Π iA RT) (Π iA′ RT′) f≈f′ κ a≈a′
  with El-one-sided i (iA′ κ) (iA κ) a≈a′
...  | a≈a′₁
     with RT κ a≈a′₁ | RT′ κ a≈a′ | f≈f′ κ a≈a′₁
...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; T≈T′ = T≈T′ }
        | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T≈T′ = T≈T′₁ }
        | record { fa = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
        rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁       = record
  { fa     = fa
  ; fa′    = fa′
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = El-one-sided i T≈T′ T≈T′₁ fa≈fa′
  ; nat    = nat
  ; nat′   = nat′
  }


𝕌-irrel : ∀ i (A≈B A≈B′ : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A≈B′
𝕌-irrel = El-one-sided


El-one-sided′ : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B : A′ ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A′≈B
El-one-sided′ i A≈B A′≈B a≈b = El-sym i (𝕌-sym i A′≈B) A′≈B
                                      (El-one-sided i (𝕌-sym i A≈B) (𝕌-sym i A′≈B) (El-sym i A≈B (𝕌-sym i A≈B) a≈b))

private

  module Trans i (rc : ∀ j → j < i → ∀ {A A′ A″} → A ≈ A′ ∈ 𝕌 j → A′ ≈ A″ ∈ 𝕌 j → A ≈ A″ ∈ 𝕌 j) where

    mutual

      𝕌-trans : A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 i → A ≈ A″ ∈ 𝕌 i
      𝕌-trans (ne C≈C′) (ne C′≈C″)  = ne (Bot-trans C≈C′ C′≈C″)
      𝕌-trans N N                   = N
      𝕌-trans (U′ j<i) (U j<i′ eq)  = U j<i′ eq
      𝕌-trans (□ A≈A′) (□ A′≈A″)    = □ (λ κ → 𝕌-trans (A≈A′ κ) (A′≈A″ κ))
      𝕌-trans (Π {_} {_} {T} {ρ} iA RT) (Π {_} {_} {T′} {ρ′} {T″} {ρ″} iA′ RT′) = Π (λ κ → 𝕌-trans (iA κ) (iA′ κ)) helper
        where helper : ∀ κ → a ≈ a′ ∈ El i (𝕌-trans (iA κ) (iA′ κ)) → ΠRT T (ρ [ κ ] ↦ a) T″ (ρ″ [ κ ] ↦ a′) (𝕌 i)
              helper κ a≈a′
                with 𝕌-refl (iA κ) | 𝕌-trans (iA κ) (iA′ κ)
              ...  | A≈A | A≈A″
                   with RT κ (El-one-sided i A≈A (iA κ) (El-refl A≈A″ A≈A a≈a′))
                      | RT′ κ (El-one-sided′ i A≈A″ (iA′ κ) a≈a′)
              ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                      rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
                { ⟦T⟧   = _
                ; ⟦T′⟧  = _
                ; ↘⟦T⟧  = ↘⟦T⟧
                ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                ; T≈T′  = 𝕌-trans T≈T′ T≈T′₁
                }


      El-trans : ∀ (A≈A′ : A ≈ A′ ∈ 𝕌 i) (A′≈A″ : A′ ≈ A″ ∈ 𝕌 i) (A≈A″ : A ≈ A″ ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) →
                   a ≈ a′ ∈ El i A≈A′ → a′ ≈ a″ ∈ El i A′≈A″ → a ≈ a″ ∈ El i A≈A″
      El-trans (ne C≈C′) (ne C′≈C″) (ne C≈C″) _ (ne c≈c′) (ne c′≈c″) = ne (Bot-trans c≈c′ c′≈c″)
      El-trans N N N _ a≈a′ a′≈a″                                    = Nat-trans a≈a′ a′≈a″
      El-trans (U′ j<i) (U′ j<i′) (U j<i″ eq) _ a≈a′ a′≈a″
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′
              | ≤-irrelevant j<i′ j<i″
              | 𝕌-wellfounded-≡-𝕌 _ j<i″                             = rc _ j<i″ a≈a′ a′≈a″
      El-trans (□ A≈A′) (□ A′≈A″) (□ A≈A″) (□ A≈A) a≈a′ a′≈a″ n κ    = record
        { ua    = □̂₁.ua
        ; ub    = □̂₂.ub
        ; ↘ua   = □̂₁.↘ua
        ; ↘ub   = □̂₂.↘ub
        ; ua≈ub = El-trans (A≈A′ κ) (A′≈A″ κ) (A≈A″ κ) (A≈A κ)
                           □̂₁.ua≈ub
                           (subst (_≈ _ ∈ El i (A′≈A″ κ)) (unbox-det □̂₂.↘ua □̂₁.↘ub) □̂₂.ua≈ub)
        }
        where module □̂₁ = □̂ (a≈a′ n κ)
              module □̂₂ = □̂ (a′≈a″ n κ)
      El-trans (Π iA RT) (Π iA′ RT′) (Π iA″ RT″) (Π iA‴ RT‴) f≈f′ f′≈f″ κ a≈a′
        with El-one-sided i (iA″ κ) (iA κ) a≈a′ | El-one-sided′ i (iA″ κ) (iA′ κ) a≈a′
      ...  | a≈a′₁ | a≈a′₂
           with El-refl′ (iA κ) (iA‴ κ) a≈a′₁ | El-refl (iA κ) (iA‴ κ) a≈a′₁
      ...     | a≈a | a≈a₁
              with RT κ a≈a | RT′ κ a≈a′₂ | RT″ κ a≈a′ | RT‴ κ a≈a₁ | f≈f′ κ a≈a | f′≈f″ κ a≈a′₂
      ...        | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
                 | record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
                 | record { ↘fa = ↘fa  ; ↘fa′ = ↘fa′  ; fa≈fa′ = fa≈fa′  ; nat = nat }
                 | record { ↘fa = ↘fa₁ ; ↘fa′ = ↘fa′₁ ; fa≈fa′ = fa≈fa′₁ ; nat′ = nat′₁ }
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
        ; nat    = nat
        ; nat′   = nat′₁
        }


      𝕌-refl : A ≈ B ∈ 𝕌 i → A ≈ A ∈ 𝕌 i
      𝕌-refl A≈B = 𝕌-trans A≈B (𝕌-sym i A≈B)

      El-refl : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈A
      El-refl A≈B A≈A a≈b = El-trans A≈B (𝕌-sym i A≈B) A≈A A≈A a≈b (El-sym i A≈B (𝕌-sym i A≈B) a≈b)

      El-refl′ : ∀ (A≈B : A ≈ B ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈B
      El-refl′ A≈B A≈A a≈b = El-one-sided i A≈A A≈B (El-refl A≈B A≈A a≈b)
