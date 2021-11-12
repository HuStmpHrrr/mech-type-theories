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

Nat-mon : (κ : UnMoT) → a ≈ b ∈ Nat → a [ κ ] ≈ b [ κ ] ∈ Nat
Nat-mon κ ze        = ze
Nat-mon κ (su a≈b)  = su (Nat-mon κ a≈b)
Nat-mon κ (ne c≈c′) = ne (Bot-mon κ c≈c′)

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
                ; nat   = nat′
                ; nat′  = nat
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
        ; ua≈ub = El-sym (A≈A′ (ins κ n)) (A≈A′₁ (ins κ n)) ua≈ub
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

𝕌-sym : ∀ {i} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
𝕌-sym {i = i} = <-Measure.wfRec (λ i → ∀ {A B} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i) Sym.𝕌-sym i

El-sym : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
El-sym {i = i} = Sym.El-sym i (λ j _ → 𝕌-sym {i = j})


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
...     | record { ↘⟦T⟧               = ↘⟦T⟧  ; T≈T′ = T≈T′ }
        | record { ↘⟦T⟧               = ↘⟦T⟧₁ ; T≈T′ = T≈T′₁ }
        | record { fa                 = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
        rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁     = record
  { fa     = fa
  ; fa′    = fa′
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = El-one-sided T≈T′ T≈T′₁ fa≈fa′
  ; nat    = nat
  ; nat′   = nat′
  }


𝕌-irrel : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j A≈B′
𝕌-irrel = El-one-sided


El-one-sided′ : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B : A′ ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El j A′≈B
El-one-sided′ A≈B A′≈B a≈b = El-sym (𝕌-sym A′≈B) A′≈B
                                      (El-one-sided (𝕌-sym A≈B) (𝕌-sym A′≈B) (El-sym A≈B (𝕌-sym A≈B) a≈b))

private

  module Trans i (rc : ∀ j → j < i → ∀ {A A′ A″ k} → A ≈ A′ ∈ 𝕌 j → A′ ≈ A″ ∈ 𝕌 k → A ≈ A″ ∈ 𝕌 j) where

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
              ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′  ; nat = nat }
                      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ ; nat′ = nat′ }
                      rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
                { ⟦T⟧   = _
                ; ⟦T′⟧  = _
                ; ↘⟦T⟧  = ↘⟦T⟧
                ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                ; T≈T′  = 𝕌-trans T≈T′ T≈T′₁
                ; nat   = nat
                ; nat′  = nat′
                }


      El-trans : ∀ {k} (A≈A′ : A ≈ A′ ∈ 𝕌 i) (A′≈A″ : A′ ≈ A″ ∈ 𝕌 k) (A≈A″ : A ≈ A″ ∈ 𝕌 i) (A≈A : A ≈ A ∈ 𝕌 i) →
                   a ≈ a′ ∈ El i A≈A′ → a′ ≈ a″ ∈ El k A′≈A″ → a ≈ a″ ∈ El i A≈A″
      El-trans (ne C≈C′) (ne C′≈C″) (ne C≈C″) _ (ne c≈c′) (ne c′≈c″) = ne (Bot-trans c≈c′ c′≈c″)
      El-trans N N N _ a≈a′ a′≈a″                                    = Nat-trans a≈a′ a′≈a″
      El-trans (U′ j<i) (U′ j<k) (U j<i′ eq) _ a≈a′ a′≈a″
        rewrite ≡-irrelevant eq refl
              | ≤-irrelevant j<i j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<i
              | 𝕌-wellfounded-≡-𝕌 _ j<i′
              | 𝕌-wellfounded-≡-𝕌 _ j<k                              = rc _ j<i a≈a′ a′≈a″
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
El-trans {i = i} A≈A′ A′≈A″ A≈A″ = Trans.El-trans i (λ j j<i → 𝕌-trans) A≈A′ A′≈A″ A≈A″ (𝕌-refl A≈A″)

El-refl : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈B
El-refl {i = i} A≈B = Trans.El-refl′ i (λ j j<i → 𝕌-trans) A≈B (𝕌-refl A≈B)

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

El-transport : ∀ {i j k} (A≈A : A ≈ A ∈ 𝕌 i) (B≈B : B ≈ B ∈ 𝕌 j) → a ≈ b ∈ El i A≈A → A ≈ B ∈ 𝕌 k → a ≈ b ∈ El j B≈B
El-transport A≈A B≈B a≈b A≈B = El-one-sided′ A≈B B≈B (El-one-sided A≈A A≈B a≈b)


𝕌-mon : ∀ {i} (κ : UnMoT) → A ≈ B ∈ 𝕌 i → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i
𝕌-mon κ (ne C≈C′)                            = ne (Bot-mon κ C≈C′)
𝕌-mon κ N                                    = N
𝕌-mon κ (U′ j<i)                             = U′ j<i
𝕌-mon κ (□ {A} {B} A≈B)                      = □ λ κ′ → helper κ κ′
  where helper : ∀ κ κ′ → A [ ins κ 1 ] [ κ′ ] ≈ B [ ins κ 1 ] [ κ′ ] ∈ 𝕌 _
        helper κ κ′
          with A≈B (ins κ 1 ø κ′)
        ...  | rel
             rewrite D-comp A (ins κ 1) κ′
                   | D-comp B (ins κ 1) κ′     = rel
𝕌-mon κ (Π {A} {B} {T} {ρ} {T′} {ρ′} A≈B RT) = Π (λ κ′ → helper κ κ′) helper′
  where helper : ∀ κ κ′ → A [ κ ] [ κ′ ] ≈ B [ κ ] [ κ′ ] ∈ 𝕌 _
        helper κ κ′
          rewrite D-comp A κ κ′
                | D-comp B κ κ′                = A≈B (κ ø κ′)
        helper′ : ∀ κ′ → a ≈ b ∈ El _ (helper κ κ′) → ΠRT T (ρ [ κ ] [ κ′ ] ↦ a) T′ (ρ′ [ κ ] [ κ′ ] ↦ b) (𝕌 _)
        helper′ κ′ a≈b
          rewrite D-comp A κ κ′
                | D-comp B κ κ′
                | ρ-comp ρ κ κ′
                | ρ-comp ρ′ κ κ′               = RT (κ ø κ′) a≈b


El-mon : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (κ : UnMoT) (A≈B′ : A [ κ ] ≈ B [ κ ] ∈ 𝕌 j) → a ≈ b ∈ El i A≈B → a [ κ ] ≈ b [ κ ] ∈ El j A≈B′
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
        | ins-1-ø-ins-n κ κ′ n            = record
  { ua    = ua
  ; ub    = ub
  ; ↘ua   = ↘ua
  ; ↘ub   = ↘ub
  ; ua≈ub = 𝕌-irrel (A≈B (ins (κ ø κ′) n)) rel ua≈ub
  }
  where open □̂ (a≈b n (κ ø κ′))
El-mon {Π A _ ρ} {Π A′ _ ρ′} {f} {f′} (Π iA RT) κ (Π iA′ RT′) f≈f′ {a} {a′} κ′ a≈a′
  rewrite D-comp f κ κ′
        | D-comp f′ κ κ′                  = record
  { fa     = fa
  ; fa′    = fa′
  ; ↘fa    = ↘fa
  ; ↘fa′   = ↘fa′
  ; fa≈fa′ = helper fa≈fa′
  ; nat    = nat
  ; nat′   = nat′
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


mutual

  𝕌-cumu-step : ∀ i → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌 (suc i)
  𝕌-cumu-step i (ne C≈C′) = ne C≈C′
  𝕌-cumu-step i N         = N
  𝕌-cumu-step i (U′ j<i)  = U′ (≤-step j<i)
  𝕌-cumu-step i (□ A≈B)   = □ λ κ → 𝕌-cumu-step i (A≈B κ)
  𝕌-cumu-step i (Π {_} {_} {T} {ρ} {T′} {ρ′} iA RT) = Π (λ κ → 𝕌-cumu-step i (iA κ)) helper
    where helper : ∀ κ → a ≈ a′ ∈ El (suc i) (𝕌-cumu-step i (iA κ)) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 (suc i))
          helper κ a≈a′ = record
            { ⟦T⟧   = ⟦T⟧
            ; ⟦T′⟧  = ⟦T′⟧
            ; ↘⟦T⟧  = ↘⟦T⟧
            ; ↘⟦T′⟧ = ↘⟦T′⟧
            ; T≈T′  = 𝕌-cumu-step i T≈T′
            ; nat   = nat
            ; nat′  = nat′
            }
            where open ΠRT (RT κ (El-lower i (iA κ) a≈a′))

  El-lower : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El (suc i) (𝕌-cumu-step i A≈B) → a ≈ b ∈ El i A≈B
  El-lower i (ne C≈C′) (ne c≈c′)             = ne c≈c′
  El-lower i N a≈b                           = a≈b
  El-lower i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (≤-step j<i) = a≈b
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
          | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ ; nat = nat ; nat′ = nat′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = record
    { fa     = _
    ; fa′    = _
    ; ↘fa    = ↘fa
    ; ↘fa′   = ↘fa′
    ; fa≈fa′ = 𝕌-irrel T≈T′₁ T≈T′ (El-lower i T≈T′₁ fa≈fa′)
    ; nat    = nat
    ; nat′   = nat′
    }

  El-cumu-step : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El (suc i) (𝕌-cumu-step i A≈B)
  El-cumu-step i (ne C≈C′) (ne c≈c′)         = ne c≈c′
  El-cumu-step i N a≈b                       = a≈b
  El-cumu-step i (U′ j<i) a≈b
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
          | 𝕌-wellfounded-≡-𝕌 _ (≤-step j<i) = a≈b
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
    ; nat    = nat
    ; nat′   = nat′
    }
    where open ΠRT (RT κ a≈a′₁) hiding (nat; nat′)
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

𝕌-sub-∞ : ∀ i → A ≈ B ∈ 𝕌 i → A ≈ B ∈ 𝕌∞
𝕌-sub-∞ i A≈B = i , A≈B

El-sub-∞ : ∀ i (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El∞ (𝕌-sub-∞ i A≈B)
El-sub-∞ i A≈B a≈b = a≈b

𝕌∞-irrel : (A≈B A≈B′ : A ≈ B ∈ 𝕌∞) → a ≈ b ∈ El∞ A≈B → a ≈ b ∈ El∞ A≈B′
𝕌∞-irrel (i , A≈B) (j , A≈B′) a≈b = 𝕌-irrel A≈B A≈B′ a≈b
