{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Various properties of the PER model
module NonCumulative.Semantics.Properties.PER (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties as ℕₚ
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

open import Lib

open import NonCumulative.Statics.Ascribed.Syntax
open import NonCumulative.Semantics.Domain
open import NonCumulative.Semantics.Evaluation
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Realizability fext
open import NonCumulative.Semantics.PER

open import NonCumulative.Semantics.Properties.PER.Core fext public

-- easy constructors for type formers

Π-𝕌 : ∀ {i j k} →
      (iA : A ≈ A′ ∈ 𝕌 i) →
      (∀ {a a′} →
         a ≈ a′ ∈ El i iA →
         ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 j)) →
      k ≡ max i j →
      Π i A (T ↙ j) ρ ≈ Π i A′ (T′ ↙ j) ρ′ ∈ 𝕌 k
Π-𝕌 {A} {A′} {T} {ρ} {T′} {ρ′} {i} {j} {k} iA RT refl
  with (λ iA (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El i _ iA → ΠRT _ _ _ _ (PERDef.𝕌 j _)) → PERDef.𝕌.Π {k} {𝕌-wellfounded _} {A} {A′} {T} {ρ} {T′} {ρ′} {i} {_} {j} refl iA RT refl refl)
...  | helper
     rewrite 𝕌-wf-gen i (ΠI≤′ i j refl)
     rewrite 𝕌-wf-gen j (ΠO≤′ i j refl) = helper iA RT

Π-bundle : ∀ {i j k} →
      (iA : A ≈ A′ ∈ 𝕌 i) →
      (∀ {a a′} →
         a ≈ a′ ∈ El i iA →
         Σ (ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 j)) (λ res → Π̂ f a f′ a′ (El _ (ΠRT.T≈T′ res)))) →
      k ≡ max i j →
      Σ (Π i A (T ↙ j) ρ ≈ Π i A′ (T′ ↙ j) ρ′ ∈ 𝕌 k) (λ R → f ≈ f′ ∈ El _ R)
Π-bundle {A} {A′} {T} {ρ} {T′} {ρ′} {f} {f′} {i} {j} {k} iA RT refl = helper
  where constr : (iA : A ≈ A′ ∈ PERDef.𝕌 i _) →
                 (∀ {a a′} →
                    a ≈ a′ ∈ PERDef.El i _ iA →
                    Σ (ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 j _)) (λ res → Π̂ f a f′ a′ (PERDef.El _ _ (ΠRT.T≈T′ res)))) →
                 Σ (Π i A (T ↙ j) ρ ≈ Π i A′ (T′ ↙ j) ρ′ ∈ PERDef.𝕌 k _) λ R → f ≈ f′ ∈ PERDef.El _ _ R
        constr iA comb = PERDef.𝕌.Π  {k} {𝕌-wellfounded _} refl iA (λ inp → proj₁ (comb inp)) refl refl
                       , λ inp → proj₂ (comb inp)

        helper : Σ (Π i A (T ↙ j) ρ ≈ Π i A′ (T′ ↙ j) ρ′ ∈ 𝕌 k) (λ R → f ≈ f′ ∈ El _ R)
        helper
          with constr
        ...  | constr
             rewrite 𝕌-wf-gen i (ΠI≤′ i j refl)
             rewrite 𝕌-wf-gen j (ΠO≤′ i j refl) = constr iA RT

L-𝕌 : ∀ {i j k} →
        A ≈ A′ ∈ 𝕌 k →
        i ≡ j + k →
        Li j k A ≈ Li j k A′ ∈ 𝕌 i
L-𝕌 {A} {A′} {i} {j} {k} A≈A′ refl
  with (λ A≈A′ → PERDef.𝕌.L {i} {𝕌-wellfounded _} {A} {A′} {j} {_} {k} refl A≈A′ refl refl)
...  | helper
     rewrite 𝕌-wf-gen k (Li≤′ j k refl) = helper A≈A′

L-bundle : ∀ {i j k}
           (A≈A′ : A ≈ A′ ∈ 𝕌 k) →
           a ≈ a′ ∈ Unli (El _ A≈A′) →
           i ≡ j + k →
           Σ (Li j k A ≈ Li j k A′ ∈ 𝕌 i) (λ R → a ≈ a′ ∈ El _ R)
L-bundle {A} {A′} {a} {a′} {i} {j} {k} A≈A′ a≈a′ refl = helper
  where constr : (A≈A′ : A ≈ A′ ∈ PERDef.𝕌 k _) →
                 a ≈ a′ ∈ Unli (PERDef.El _ _ A≈A′) →
                 Σ (Li j k A ≈ Li j k A′ ∈ PERDef.𝕌 i _) λ R → a ≈ a′ ∈ PERDef.El _ _ R
        constr A≈A′ a≈a′ = L {i} {𝕌-wellfounded _} refl A≈A′ refl refl , a≈a′

        helper : Σ (Li j k A ≈ Li j k A′ ∈ 𝕌 i) (λ R → a ≈ a′ ∈ El _ R)
        helper
          with constr
        ...  | constr
             rewrite 𝕌-wf-gen k (Li≤′ j k refl) = constr A≈A′ a≈a′

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
Bot⊆Top : ∀ {i} → c ≈ c′ ∈ Bot → ↓ i (↑ (ℕ.suc i) A C) (↑ i B c) ≈ ↓ i (↑ (ℕ.suc i) A′ C′) (↑ i B′ c′) ∈ Top
Bot⊆Top c≈c′ n
  with c≈c′ n
...  | u , ↘u , ↘u′ = ne u , Rne′ n ↘u , Rne′ n ↘u′

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
  module Sym where
    mutual

      𝕌-sym : ∀ i (Univ : ∀ {j} → j < i → Ty) (rc : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i) →
              A ≈ B ∈ PERDef.𝕌 i Univ → B ≈ A ∈ PERDef.𝕌 i Univ
      𝕌-sym i Univ rc (ne′ C≈C′)         = ne′ (Bot-sym C≈C′)
      𝕌-sym i Univ rc N′                 = N′
      𝕌-sym i Univ rc U′                 = U′
      𝕌-sym {Π _ _ (T ↙ _) ρ} {Π _ _ (T′ ↙ _) ρ′} i Univ rc (Π′ {j} {k} iA RT)
                                         = Π′ sym-iA helper
        where sym-iA = 𝕌-sym _ _ (λ _ _ → rc _ _) iA
              helper : a ≈ a′ ∈ PERDef.El _ _ sym-iA → ΠRT T′ (ρ′ ↦ a) T (ρ ↦ a′) (PERDef.𝕌 k _)
              helper a≈a′ = record
                { ⟦T⟧     = ⟦T′⟧
                ; ⟦T′⟧    = ⟦T⟧
                ; ↘⟦T⟧    = ↘⟦T′⟧
                ; ↘⟦T′⟧   = ↘⟦T⟧
                ; T≈T′    = 𝕌-sym _ _ (λ _ _ → rc _ _) T≈T′
                }
                where open ΠRT (RT (El-sym _ _ (λ _ _ → rc _ _) sym-iA iA a≈a′))
      𝕌-sym {Li _ _ A} {Li _ _ B} i Univ rc (L′ {j} {k} A≈B)
                                         = L′ (𝕌-sym k _ (λ _ _ → rc _ _) A≈B)

      -- Watch the type here. Due to proof relevance, we must supply two symmetric
      -- witnesses, one for the premise and the other for the conclusion. This
      -- duplication of arguments can be taken away later once we establish the
      -- irrelevance lemma. But it cannot be done at this point it cannot be done yet.
      El-sym : ∀ i (Univ : ∀ {j} → j < i → Ty) (rc : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i) →
               (A≈B : A ≈ B ∈ PERDef.𝕌 i Univ) (B≈A : B ≈ A ∈ PERDef.𝕌 i Univ) →
               a ≈ b ∈ PERDef.El i Univ A≈B → b ≈ a ∈ PERDef.El i Univ B≈A
      El-sym i Univ rc (ne′ _) (ne _ _ _) (ne′ c≈c′) = ne′ (Bot-sym c≈c′)
      El-sym i Univ rc N′ N′ a≈b                     = Nat-sym a≈b
      El-sym i Univ rc U′ (U eq _) a≈b
        rewrite ≡-irrelevant eq refl                 = rc _ _ a≈b
      El-sym i Univ rc (Π′ {j} {k} iA RT) (Π eq iA′ RT′ _ _) f≈f′ a≈a′
        rewrite ≡-irrelevant eq refl
        with El-sym _ _ (λ _ _ → rc _ _) iA′ iA a≈a′
      ...  | a≈a′₁
           with RT a≈a′₁ | RT′ a≈a′ | f≈f′ a≈a′₁
      ...     | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
              | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
              | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
              rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T′⟧₁
                    | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁             = record
        { fa     = _
        ; fa′    = _
        ; ↘fa    = ↘fa′
        ; ↘fa′   = ↘fa
        ; fa≈fa′ = El-sym _ _ (λ _ _ → rc _ _) T≈T′₁ T≈T′ fa≈fa′
        }
      El-sym {Li _ _ A} {Li _ _ B} i Univ rc (L′ {j} {k} A≈B) (L eq B≈A _ _) a≈b
        rewrite ≡-irrelevant eq refl                 = record
          { ua    = ub
          ; ub    = ua
          ; ↘ua   = ↘ub
          ; ↘ub   = ↘ua
          ; ua≈ub = El-sym _ _ (λ _ _ → rc _ _) A≈B B≈A ua≈ub
          }
        where open Unli a≈b


-- wrap up symmetry by well-founded induction
𝕌-sym : ∀ {i} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
𝕌-sym {i = i} = <-Measure.wfRec (λ i → ∀ {A B} → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i) (λ i rc → helper i rc) i
  where helper : ∀ i → (∀ j → j < i → ∀ {A B} → A ≈ B ∈ 𝕌 j → B ≈ A ∈ 𝕌 j) → A ≈ B ∈ 𝕌 i → B ≈ A ∈ 𝕌 i
        helper i
          with (λ {A} {B} → Sym.𝕌-sym {A} {B} i (𝕌-wellfounded i))
        ...  | d
             rewrite 𝕌-wf-simpl i = d

El-sym : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → b ≈ a ∈ El i B≈A
El-sym {i = i}
  with Sym.El-sym i (𝕌-wellfounded i)
...  | helper
     rewrite 𝕌-wf-simpl i = helper (λ _ _ → 𝕌-sym)

private
  El-one-sided-gen : ∀ {i} (Univ : ∀ {j} → j < i → Ty) →
                       (A≈B : A ≈ B ∈ PERDef.𝕌 i Univ) (A≈B′ : A ≈ B′ ∈ PERDef.𝕌 i Univ) → a ≈ b ∈ PERDef.El i Univ A≈B → a ≈ b ∈ PERDef.El i Univ A≈B′
  El-one-sided-gen Univ (ne′ _) (ne _ _ _) a≈b = a≈b
  El-one-sided-gen Univ N′ N′ a≈b = a≈b
  El-one-sided-gen Univ (U′ {j}) (U eq _) a≈b
    rewrite ≡-irrelevant eq refl = a≈b
  El-one-sided-gen Univ (Π′ {j} {k} iA RT) (Π eq iA′ RT′ _ _) f≈f′ a≈a′
    rewrite ≡-irrelevant eq refl
    with El-one-sided-gen _ iA′ iA a≈a′
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
    ; fa≈fa′ = El-one-sided-gen _ T≈T′ T≈T′₁ fa≈fa′
    }
  El-one-sided-gen Univ (L′ {j} {k} A≈B) (L eq A≈B′ _ _) record { ua = ua ; ub = ub ; ↘ua = ↘ua ; ↘ub = ↘ub ; ua≈ub = ua≈ub }
    rewrite ≡-irrelevant eq refl = record
      { ua    = ua
      ; ub    = ub
      ; ↘ua   = ↘ua
      ; ↘ub   = ↘ub
      ; ua≈ub = El-one-sided-gen _ A≈B A≈B′ ua≈ub
      }

  El-one-sided-gen′ : ∀ {i} (Univ : ∀ {j} → j < i → Ty) →
                       (A≈B : A ≈ B ∈ PERDef.𝕌 i Univ) (A′≈B : A′ ≈ B ∈ PERDef.𝕌 i Univ) → a ≈ b ∈ PERDef.El i Univ A≈B → a ≈ b ∈ PERDef.El i Univ A′≈B
  El-one-sided-gen′ Univ (ne′ _) (ne _ _ _) a≈b = a≈b
  El-one-sided-gen′ Univ N′ N′ a≈b = a≈b
  El-one-sided-gen′ Univ (U′ {j}) (U eq refl) a≈b
    rewrite ≡-irrelevant eq refl = a≈b
  El-one-sided-gen′ Univ (Π′ {j} {k} iA RT) (Π eq iA′ RT′ refl refl) f≈f′ a≈a′
    rewrite ≡-irrelevant eq refl
    with El-one-sided-gen′ _ iA′ iA a≈a′
  ...  | a≈a′₁
       with RT a≈a′₁ | RT′ a≈a′ | f≈f′ a≈a′₁
  ...     | record { ↘⟦T′⟧ = ↘⟦T⟧  ; T≈T′ = T≈T′ }
          | record { ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T≈T′₁ }
          | record { fa = fa ; fa′ = fa′ ; ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁     = record
    { fa     = fa
    ; fa′    = fa′
    ; ↘fa    = ↘fa
    ; ↘fa′   = ↘fa′
    ; fa≈fa′ = El-one-sided-gen′ _ T≈T′ T≈T′₁ fa≈fa′
    }
  El-one-sided-gen′ Univ (L′ {j} {k} A≈B) (L eq A′≈B refl refl) record { ua = ua ; ub = ub ; ↘ua = ↘ua ; ↘ub = ↘ub ; ua≈ub = ua≈ub }
    rewrite ≡-irrelevant eq refl = record
      { ua    = ua
      ; ub    = ub
      ; ↘ua   = ↘ua
      ; ↘ub   = ↘ub
      ; ua≈ub = El-one-sided-gen′ _ A≈B A′≈B ua≈ub
      }

-- El only focuses on one side (left) of relation of 𝕌.
El-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B′ ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A≈B′
El-one-sided {i = i} = El-one-sided-gen (𝕌-wellfounded i)


-- In other words, the witness of 𝕌 is irrelevant in El.
𝕌-irrel : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A≈B′
𝕌-irrel = El-one-sided


-- Combined with symmetry, we can see that El can also focus on the right side of 𝕌.
El-one-sided′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B : A′ ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i A′≈B
El-one-sided′ {i = i} = El-one-sided-gen′ (𝕌-wellfounded i)

-- 𝕌 and El are transitive.
private
  module Trans where
    mutual

      𝕌-refl : ∀ i (Univ : ∀ {j} → j < i → Ty)
                 (sy : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i)
                 (tr : ∀ j (j<i : j < i) → ∀ {A A′ A″} → A ≈ A′ ∈ Univ j<i → A′ ≈ A″ ∈ Univ j<i → A ≈ A″ ∈ Univ j<i) →
                  A ≈ B ∈ PERDef.𝕌 i Univ → A ≈ A ∈ PERDef.𝕌 i Univ
      𝕌-refl i Univ sy tr A≈B = 𝕌-trans i Univ sy tr A≈B (Sym.𝕌-sym _ Univ sy A≈B)

      El-refl : ∀ i (Univ : ∀ {j} → j < i → Ty)
                 (sy : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i)
                 (tr : ∀ j (j<i : j < i) → ∀ {A A′ A″} → A ≈ A′ ∈ Univ j<i → A′ ≈ A″ ∈ Univ j<i → A ≈ A″ ∈ Univ j<i) →
                 (A≈B : A ≈ B ∈ PERDef.𝕌 i Univ) (A≈A : A ≈ A ∈ PERDef.𝕌 i Univ) → a ≈ b ∈ PERDef.El i _ A≈B → a ≈ a ∈ PERDef.El i _ A≈A
      El-refl i Univ sy tr A≈B A≈A a≈b = El-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _)
                                                  A≈B (Sym.𝕌-sym _ Univ sy A≈B) A≈A A≈A
                                                  a≈b
                                                  (Sym.El-sym _ Univ sy A≈B (Sym.𝕌-sym _ Univ sy A≈B) a≈b)

      El-refl′ : ∀ i (Univ : ∀ {j} → j < i → Ty)
                   (sy : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i)
                   (tr : ∀ j (j<i : j < i) → ∀ {A A′ A″} → A ≈ A′ ∈ Univ j<i → A′ ≈ A″ ∈ Univ j<i → A ≈ A″ ∈ Univ j<i) →
                   (A≈B : A ≈ B ∈ PERDef.𝕌 i Univ) (A≈A : A ≈ A ∈ PERDef.𝕌 i Univ) → a ≈ b ∈ PERDef.El i _ A≈B → a ≈ a ∈ PERDef.El i _ A≈B
      El-refl′ i Univ sy tr A≈B A≈A a≈b = El-one-sided-gen Univ A≈A A≈B (El-refl i Univ sy tr A≈B A≈A a≈b)

      𝕌-trans : ∀ i (Univ : ∀ {j} → j < i → Ty)
                  (sy : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i)
                  (tr : ∀ j (j<i : j < i) → ∀ {A A′ A″} → A ≈ A′ ∈ Univ j<i → A′ ≈ A″ ∈ Univ j<i → A ≈ A″ ∈ Univ j<i) →
                  ∀ {A A′ A″} →
                  A ≈ A′ ∈ PERDef.𝕌 i Univ → A′ ≈ A″ ∈ PERDef.𝕌 i Univ → A ≈ A″ ∈ PERDef.𝕌 i Univ
      𝕌-trans i Univ sy tr (ne′ C≈C′) (ne C′≈C″ _ refl)  = ne′ (Bot-trans C≈C′ C′≈C″)
      𝕌-trans i Univ sy tr N′ N′                         = N′
      𝕌-trans i Univ sy tr U′ (U _ refl)                 = U′
      𝕌-trans i Univ sy tr {Π _ _ (T ↙ _) ρ} {Π _ _ (T′ ↙ _) ρ′} {Π _ _ (T″ ↙ _) ρ″} (Π′ {j} {k} iA RT) (Π eq iA′ RT′ refl refl)
        rewrite ≡-irrelevant eq refl = Π′ iA″ helper
        where iA″ = 𝕌-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) iA iA′
              helper : a ≈ a′ ∈ PERDef.El j _ iA″ → ΠRT T (ρ ↦ a) T″ (ρ″ ↦ a′) _
              helper a≈a′
                with 𝕌-refl _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) iA | 𝕌-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) iA iA′
              ...  | A≈A | A≈A″
                   with RT (El-one-sided-gen _ A≈A iA (El-refl _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) A≈A″ A≈A a≈a′))
                      | RT′ (El-one-sided-gen′ _ A≈A″ iA′ a≈a′)
              ...     | record { ↘⟦T⟧ = ↘⟦T⟧  ; ↘⟦T′⟧ = ↘⟦T′⟧  ; T≈T′ = T≈T′ }
                      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                      rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧₁ = record
                { ⟦T⟧   = _
                ; ⟦T′⟧  = _
                ; ↘⟦T⟧  = ↘⟦T⟧
                ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                ; T≈T′  = 𝕌-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) T≈T′ T≈T′₁
                }
      𝕌-trans i Univ sy tr (L′ A≈A′) (L eq A′≈A″ refl refl)
        rewrite ≡-irrelevant eq refl = L′ (𝕌-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) A≈A′ A′≈A″)

      -- Again, similar to symmetry, we have the same problem here. We must supply
      -- three premises in tranitivity and remove this duplication later.
      El-trans : ∀ i (Univ : ∀ {j} → j < i → Ty)
                   (sy : ∀ j (j<i : j < i) → ∀ {A′ B′} → A′ ≈ B′ ∈ Univ j<i → B′ ≈ A′ ∈ Univ j<i)
                   (tr : ∀ j (j<i : j < i) → ∀ {A A′ A″} → A ≈ A′ ∈ Univ j<i → A′ ≈ A″ ∈ Univ j<i → A ≈ A″ ∈ Univ j<i) →
                   ∀ {A A′ A″}
                     (A≈A′ : A ≈ A′ ∈ PERDef.𝕌 i Univ) (A′≈A″ : A′ ≈ A″ ∈ PERDef.𝕌 i Univ)
                     (A≈A″ : A ≈ A″ ∈ PERDef.𝕌 i Univ) (A≈A : A ≈ A ∈ PERDef.𝕌 i Univ) →
                      a ≈ a′ ∈ PERDef.El i _ A≈A′ → a′ ≈ a″ ∈ PERDef.El i _ A′≈A″ → a ≈ a″ ∈ PERDef.El i _ A≈A″
      El-trans i Univ sy tr (ne′ C≈C′) (ne C′≈C″ _ refl) (ne C≈C″ _ _) (ne C≈C _ _) (ne′ c≈c′) (ne c′≈c″ _ refl)
        = ne′ (Bot-trans c≈c′ c′≈c″)
      El-trans i Univ sy tr N′ N′ N′ N′ a≈a′ a′≈a″
        = Nat-trans a≈a′ a′≈a″
      El-trans i Univ sy tr U′ (U eq refl) (U eq′ _) (U _ _) a≈a′ a′≈a″
        rewrite ≡-irrelevant eq refl
              | ≡-irrelevant eq′ refl = tr _ _ a≈a′ a′≈a″
      El-trans i Univ sy tr (Π′ iA RT) (Π eq′ iA′ RT′ refl refl) (Π eq″ iA″ RT″ _ _) (Π eq‴ iA‴ RT‴ _ _) f≈f′ f′≈f″ a≈a′
        rewrite ≡-irrelevant eq′ refl
              | ≡-irrelevant eq″ refl
              | ≡-irrelevant eq‴ refl
              with El-one-sided-gen _ iA″ iA a≈a′ | El-one-sided-gen′ _ iA″ iA′ a≈a′
      ...  | a≈a′₁ | a≈a′₂
           with El-refl′ _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) iA iA‴ a≈a′₁ | El-refl _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) iA iA‴ a≈a′₁
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
        ; fa≈fa′ = El-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) T≈T′ T≈T′₁ T≈T′₂ T≈T′₃ fa≈fa′ fa≈fa′₁
        }
      El-trans i Univ sy tr (L′ {_} {_} A≈A′) (L eq A′≈A″ refl refl) (L eq′ A≈A″ _ _) (L eq″ A≈A _ _)
               record { ua = ua ; ub = ub ; ↘ua = ↘ua ; ↘ub = ↘ub ; ua≈ub = ua≈ub }
               record { ua = ua′ ; ub = ub′ ; ↘ua = ↘ua′ ; ↘ub = ↘ub′ ; ua≈ub = ua≈ub′ }
        rewrite ≡-irrelevant eq refl
              | ≡-irrelevant eq′ refl
              | ≡-irrelevant eq″ refl
              | unli-det ↘ub ↘ua′ = record
              { ua    = ua
              ; ub    = ub′
              ; ↘ua   = ↘ua
              ; ↘ub   = ↘ub′
              ; ua≈ub = El-trans _ _ (λ _ _ → sy _ _) (λ _ _ → tr _ _) A≈A′ A′≈A″ A≈A″ A≈A ua≈ub ua≈ub′
              }


𝕌-trans : ∀ {i} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 i → A ≈ A″ ∈ 𝕌 i
𝕌-trans {i = i} = <-Measure.wfRec (λ i → ∀ {A A′ A″} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 i → A ≈ A″ ∈ 𝕌 i) helper i
  where helper : ∀ i → (∀ j → j < i → ∀ {A A′ A″} → A ≈ A′ ∈ 𝕌 j → A′ ≈ A″ ∈ 𝕌 j → A ≈ A″ ∈ 𝕌 j) →
                 ∀ {A A′ A″} → A ≈ A′ ∈ 𝕌 i → A′ ≈ A″ ∈ 𝕌 i → A ≈ A″ ∈ 𝕌 i
        helper i
          with Trans.𝕌-trans i (𝕌-wellfounded i)
        ...  | d
             rewrite 𝕌-wf-simpl i = d (λ _ _ → 𝕌-sym)

𝕌-refl : ∀ {i} → A ≈ B ∈ 𝕌 i → A ≈ A ∈ 𝕌 i
𝕌-refl A≈B = 𝕌-trans A≈B (𝕌-sym A≈B)

El-trans : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) (A′≈A″ : A′ ≈ A″ ∈ 𝕌 i) (A≈A″ : A ≈ A″ ∈ 𝕌 i) →
           a ≈ a′ ∈ El i A≈A′ → a′ ≈ a″ ∈ El i A′≈A″ → a ≈ a″ ∈ El i A≈A″
El-trans {A} {A′} {A″} {a} {a′} {a″} {i} A≈A′ A′≈A″ A≈A″
  with Trans.El-trans {a} {a′} {a″} i (𝕌-wellfounded i) | 𝕌-refl A≈A″
...  | helper | A≈A
     rewrite 𝕌-wf-simpl i = helper (λ _ _ → 𝕌-sym) (λ _ _ → 𝕌-trans) A≈A′ A′≈A″ A≈A″ A≈A

El-refl : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ a ∈ El i A≈B
El-refl {i = i} A≈B a≈b = El-one-sided (𝕌-trans A≈B (𝕌-sym A≈B)) A≈B
                                       (El-trans A≈B (𝕌-sym A≈B) (𝕌-trans A≈B (𝕌-sym A≈B))
                                                 a≈b
                                                 (El-sym A≈B (𝕌-sym A≈B) a≈b))


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

El-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (B≈A : B ≈ A ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → a ≈ b ∈ El i B≈A
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
El-transport : ∀ {i} (A≈A : A ≈ A ∈ 𝕌 i) (B≈B : B ≈ B ∈ 𝕌 i) → a ≈ b ∈ El i A≈A → A ≈ B ∈ 𝕌 i → a ≈ b ∈ El i B≈B
El-transport A≈A B≈B a≈b A≈B = El-one-sided′ A≈B B≈B (El-one-sided A≈A A≈B a≈b)

El-transp : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → a ≈ b ∈ El i A≈B → A ≡ A′ → a ≈ b ∈ El i A′≈B′
El-transp A≈B A′≈B′ a≈b refl = El-one-sided A≈B A′≈B′ a≈b


-- Properties for the PER models of context stacks and evaluation environments
--
-- These properties essentially just replay the proofs above but just simpler.

-- Symmetry
mutual

  ⊨-sym : ⊨ Γ ≈ Δ → ⊨ Δ ≈ Γ
  ⊨-sym []-≈                                   = []-≈
  ⊨-sym (∷-cong {Γ} {Δ} {T} {T′} Γ≈Δ rel refl) = ∷-cong (⊨-sym Γ≈Δ) helper refl
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
  ⟦⟧ρ-sym {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT refl) (∷-cong Δ≈Γ RT′ _) (ρ≈ρ′ , ρ0≈ρ′0)
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
⟦⟧ρ-one-sided {_} {_} {_} {ρ} {ρ′} (∷-cong Γ≈Δ RT refl) (∷-cong Γ≈Δ′ RT′ refl) (ρ≈ρ′ , ρ0≈ρ′0)
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
  ⊨-trans (∷-cong {_} {_} {T} {T′} Γ≈Γ′ RT refl) (∷-cong {_} {_} {_} {T″} Γ′≈Γ″ RT′ refl) = ∷-cong (⊨-trans Γ≈Γ′ Γ′≈Γ″) helper refl
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
  ⟦⟧ρ-trans {_} {_} {_} {ρ} {ρ′} {ρ″} (∷-cong Γ≈Γ′ RT refl) (∷-cong Γ′≈Γ″ RT′ refl) (∷-cong Γ≈Γ″ RT″ _) (ρ≈ρ′ , ρ0≈ρ′0) (ρ′≈ρ″ , ρ′0≈ρ″0)
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
⊨-resp-len (∷-cong Γ≈Δ _ _) = cong ℕ.suc (⊨-resp-len Γ≈Δ)


-- If two context stacks are related, then they can both generate initial evaluation
-- environments, and the generated environments are related.
InitEnvs-related : (Γ≈Δ : ⊨ Γ ≈ Δ) → ∃₂ λ ρ ρ′ → InitEnvs Γ ρ × InitEnvs Δ ρ′ × (ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ)
InitEnvs-related []-≈           = emp , emp , base , base , tt
InitEnvs-related {_ ∷ Γ} {_ ∷ Δ} (∷-cong Γ≈Δ rel refl)
  with InitEnvs-related Γ≈Δ
...  | ρ , ρ′ , ↘ρ , ↘ρ′ , ρ≈ρ′  = ρ ↦ l′ _ ⟦T⟧ (len Γ) , ρ′ ↦ l′ _ ⟦T′⟧ (len Δ)
                                 , s-∷ ↘ρ ↘⟦T⟧ , s-∷ ↘ρ′ ↘⟦T′⟧
                                 , ρ↦⟦T⟧≈ρ′↦⟦T′⟧
  where
    open RelTyp (rel ρ≈ρ′)

    ρ↦⟦T⟧≈ρ′↦⟦T′⟧ : ρ ↦ l′ _ ⟦T⟧ (len Γ) ≈ ρ′ ↦ l′ _ ⟦T′⟧ (len Δ) ∈ ⟦ ∷-cong Γ≈Δ rel refl ⟧ρ
    ρ↦⟦T⟧≈ρ′↦⟦T′⟧ = ρ≈ρ′ , Bot⊆El T≈T′ (subst (λ n → l (len Γ) ≈ l n ∈ Bot) (⊨-resp-len Γ≈Δ) (Bot-l _))
