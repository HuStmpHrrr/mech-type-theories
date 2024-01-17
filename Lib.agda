{-# OPTIONS --without-K --safe #-}

module Lib where

open import Data.Empty public
open import Data.Unit using (⊤; tt) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤?_; _≤_; _<_) renaming (_⊔_ to max) public
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; ∃₂; _×_; _,_; -,_; proj₁; proj₂) public
open import Data.List using (List; []; _∷_; _++_; unzip) public
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (here; there; _─_) public
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_) public
open import Data.List.Membership.Propositional hiding (_─_; find) public
open import Data.List.Relation.Binary.Sublist.Propositional using ([]; _∷_; _∷ʳ_; _⊆_; ⊆-refl; ⊆-trans) public

open import Induction.WellFounded as Wf
open import Relation.Nullary using (¬_; yes; no) public
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; Reveal_·_is_; inspect; module ≡-Reasoning)
  renaming([_] to insp) public

import Data.Fin
import Relation.Binary.Reasoning.Base.Triple as Triple

module L    = Data.List
module All′ = Data.List.Relation.Unary.All
module F    = Data.Fin
open _≤_ public

pattern rhere = here refl
pattern 1+ x = there x
pattern 0d = rhere
pattern 1d = 1+ 0d
pattern 2d = 1+ 1d
pattern 3d = 1+ 2d

module _ {a} {A : Set a} where

  private
    variable
      b c     : A
      l l′ l″ : List A

  ∈-⊆ : b ∈ l → l ⊆ l′ → b ∈ l′
  ∈-⊆ b∈l (y ∷ʳ l⊆l′)        = there (∈-⊆ b∈l l⊆l′)
  ∈-⊆ (here refl) (x ∷ l⊆l′) = here x
  ∈-⊆ (there b∈l) (x ∷ l⊆l′) = there (∈-⊆ b∈l l⊆l′)

  ∈-⊆-trans : ∀ (b∈l : b ∈ l) (l⊆l′ : l ⊆ l′) (l′⊆l″ : l′ ⊆ l″) →
                ∈-⊆ (∈-⊆ b∈l l⊆l′) l′⊆l″ ≡ ∈-⊆ b∈l (⊆-trans l⊆l′ l′⊆l″)
  ∈-⊆-trans b∈l (y ∷ʳ l⊆l′) (z ∷ʳ l′⊆l″)          = cong there (∈-⊆-trans b∈l (y ∷ʳ l⊆l′) l′⊆l″)
  ∈-⊆-trans b∈l (y ∷ʳ l⊆l′) (x ∷ l′⊆l″)           = cong there (∈-⊆-trans b∈l l⊆l′ l′⊆l″)
  ∈-⊆-trans b∈l (x ∷ l⊆l′) (y ∷ʳ l′⊆l″)           = cong there (∈-⊆-trans b∈l (x ∷ l⊆l′) l′⊆l″)
  ∈-⊆-trans (here refl) (refl ∷ l⊆l′) (z ∷ l′⊆l″) = refl
  ∈-⊆-trans (there b∈l) (x ∷ l⊆l′) (z ∷ l′⊆l″)    = cong there (∈-⊆-trans b∈l l⊆l′ l′⊆l″)

  ⊆-refl-trans : ∀ (l⊆l′ : l ⊆ l′) → ⊆-trans ⊆-refl l⊆l′ ≡ l⊆l′
  ⊆-refl-trans []                  = refl
  ⊆-refl-trans {[]} (y ∷ʳ l⊆l′)    = cong (y ∷ʳ_) (⊆-refl-trans l⊆l′)
  ⊆-refl-trans {x ∷ l} (y ∷ʳ l⊆l′) = cong (y ∷ʳ_) (⊆-refl-trans l⊆l′)
  ⊆-refl-trans (x ∷ l⊆l′)          = cong (x ∷_) (⊆-refl-trans l⊆l′)

  ⊆-trans-refl : ∀ (l⊆l′ : l ⊆ l′) → ⊆-trans l⊆l′ ⊆-refl ≡ l⊆l′
  ⊆-trans-refl []            = refl
  ⊆-trans-refl (y ∷ʳ l⊆l′)   = cong (y ∷ʳ_) (⊆-trans-refl l⊆l′)
  ⊆-trans-refl (refl ∷ l⊆l′) = cong (refl ∷_) (⊆-trans-refl l⊆l′)

  ⊆-trans-∷ʳ-refl : ∀ b (l⊆l′ : l ⊆ l′) → ⊆-trans l⊆l′ (b ∷ʳ ⊆-refl) ≡ b ∷ʳ l⊆l′
  ⊆-trans-∷ʳ-refl b []            = refl
  ⊆-trans-∷ʳ-refl b (y ∷ʳ l⊆l′)   = cong (λ l → b ∷ʳ (y ∷ʳ l)) (⊆-trans-refl l⊆l′)
  ⊆-trans-∷ʳ-refl b (refl ∷ l⊆l′) = cong (λ l → b ∷ʳ (refl ∷ l)) (⊆-trans-refl l⊆l′)

  ∈-⊆-refl : ∀ (b∈l : b ∈ l) → ∈-⊆ b∈l ⊆-refl ≡ b∈l
  ∈-⊆-refl {l = x ∷ l} (here refl) = refl
  ∈-⊆-refl {l = x ∷ l} (there b∈l) = cong there (∈-⊆-refl b∈l)

  infixr 5 _++ˡ_ _++ʳ_
  infixl 5 _++ʳ′_

  _++ˡ_ : ∀ l → l′ ⊆ l″ → l ++ l′ ⊆ l ++ l″
  [] ++ˡ l′⊆l″      = l′⊆l″
  (x ∷ l) ++ˡ l′⊆l″ = refl ∷ (l ++ˡ l′⊆l″)

  _++ʳ_ : ∀ l → l′ ⊆ l″ → l′ ⊆ l ++ l″
  [] ++ʳ l′⊆l″      = l′⊆l″
  (x ∷ l) ++ʳ l′⊆l″ = x ∷ʳ (l ++ʳ l′⊆l″)

  _++ʳ′_ : l′ ⊆ l″ → ∀ l → l′ ++ l ⊆ l″ ++ l
  [] ++ʳ′ l = ⊆-refl
  (x ∷ʳ l′⊆l″) ++ʳ′ l = x ∷ʳ (l′⊆l″ ++ʳ′ l)
  (eq ∷ l′⊆l″) ++ʳ′ l = eq ∷ (l′⊆l″ ++ʳ′ l)


  ⊆ʳ : ∀ (l l′ : List A) → l′ ⊆ l ++ l′
  ⊆ʳ [] l′      = ⊆-refl
  ⊆ʳ (x ∷ l) l′ = x ∷ʳ ⊆ʳ l l′

  ⊆-++ʳ : ∀ (l⊆l′ : l ⊆ l′) (l′⊆l″ : l′ ⊆ l″) l‴ → ⊆-trans l⊆l′ (l‴ ++ʳ l′⊆l″) ≡ l‴ ++ʳ ⊆-trans l⊆l′ l′⊆l″
  ⊆-++ʳ l⊆l′ l′⊆l″ []              = refl
  ⊆-++ʳ [] l′⊆l″ (x ∷ l‴)          = cong (x ∷ʳ_) (⊆-++ʳ [] l′⊆l″ l‴)
  ⊆-++ʳ (y ∷ʳ l⊆l′) l′⊆l″ (x ∷ l‴) = cong (x ∷ʳ_) (⊆-++ʳ (y ∷ʳ l⊆l′) l′⊆l″ l‴)
  ⊆-++ʳ (y ∷ l⊆l′) l′⊆l″ (x ∷ l‴)  = cong (x ∷ʳ_) (⊆-++ʳ (y ∷ l⊆l′) l′⊆l″ l‴)

  ⊆-++ʳ′ : ∀ (l⊆l′ : l ⊆ l′) l″ → ⊆-trans l⊆l′ (l″ ++ʳ ⊆-refl) ≡ l″ ++ʳ l⊆l′
  ⊆-++ʳ′ l⊆l′ l″
    rewrite ⊆-++ʳ l⊆l′ ⊆-refl l″ = cong (l″ ++ʳ_) (⊆-trans-refl _)

  ⊆-++ʳ-++ˡ : ∀ (l⊆l′ : l ⊆ l′) (l′⊆l″ : l′ ⊆ l″) l‴ → ⊆-trans (l‴ ++ʳ l⊆l′) (l‴ ++ˡ l′⊆l″) ≡ l‴ ++ʳ ⊆-trans l⊆l′ l′⊆l″
  ⊆-++ʳ-++ˡ l⊆l′ l′⊆l″ []       = refl
  ⊆-++ʳ-++ˡ l⊆l′ l′⊆l″ (x ∷ l‴) = cong (x ∷ʳ_) (⊆-++ʳ-++ˡ l⊆l′ l′⊆l″ l‴)

  ∈-⊆-++ : ∀ l‴ (b∈l : b ∈ l) (l⊆l′ : l ⊆ l′) → ∈-⊆ (++⁺ʳ l‴ b∈l) (l‴ ++ˡ l⊆l′) ≡ ++⁺ʳ l‴ (∈-⊆ b∈l l⊆l′)
  ∈-⊆-++ [] b∈l l⊆l′       = refl
  ∈-⊆-++ (c ∷ l‴) b∈l l⊆l′ = cong there (∈-⊆-++ l‴ b∈l l⊆l′)

  ++ˡ-assoc : ∀ l₁ l₂ {l₃ l₄ : List A} (l₃⊆l₄ : l₃ ⊆ l₄) →
    subst₂ _⊆_ (++-assoc l₁ l₂ l₃) (++-assoc l₁ l₂ l₄) ((l₁ ++ l₂) ++ˡ l₃⊆l₄) ≡ l₁ ++ˡ l₂ ++ˡ l₃⊆l₄
  ++ˡ-assoc [] l₂ l₃⊆l₄               = refl
  ++ˡ-assoc (x ∷ l₁) l₂ {l₃} {l₄} l₃⊆l₄
    with (l₁ ++ l₂) ++ l₃ | (l₁ ++ l₂) ++ l₄
       | (l₁ ++ l₂) ++ˡ l₃⊆l₄
       | ++-assoc l₁ l₂ l₃ | ++-assoc l₁ l₂ l₄
       | ++ˡ-assoc l₁ l₂ l₃⊆l₄
  ... | _ | _ | _ | refl | refl | rec = cong (refl ∷_) rec

  ++⁺ʳ-assoc : ∀ l₁ l₂ (b∈l : b ∈ l) → subst (b ∈_) (++-assoc l₁ l₂ l) (++⁺ʳ (l₁ ++ l₂) b∈l) ≡ ++⁺ʳ l₁ (++⁺ʳ l₂ b∈l)
  ++⁺ʳ-assoc [] l₂ b∈l     = refl
  ++⁺ʳ-assoc {l = l} (x ∷ l₁) l₂ b∈l
    with (l₁ ++ l₂)  ++ l | ++⁺ʳ (l₁ ++ l₂) b∈l | ++-assoc l₁ l₂ l | ++⁺ʳ-assoc l₁ l₂ b∈l
  ... | _ | _ | refl | rec = cong there rec

  find : List A → ℕ → Maybe A
  find [] n            = nothing
  find (x ∷ l) zero    = just x
  find (x ∷ l) (suc n) = find l n

  infix 2 _∶_∈_
  data _∶_∈_ : ℕ → A → List A → Set a where
    here : ∀ {x} → 0 ∶ x ∈ x ∷ l
    there : ∀ {n x y l} → n ∶ x ∈ l → suc n ∶ x ∈ y ∷ l

  find⇒∈ : ∀ {n} → find l n ≡ just b → n ∶ b ∈ l
  find⇒∈ {[]} ()
  find⇒∈ {x ∷ l} {_} {zero} refl = here
  find⇒∈ {x ∷ l} {_} {suc n} eq  = there (find⇒∈ eq)

  length-∈ : ∀ {a} l → L.length l ∶ a ∈ l ++ a ∷ l′
  length-∈ []      = here
  length-∈ (x ∷ l) = there (length-∈ l)

  split-∈ : ∀ {x a} → x ∶ a ∈ l → ∃₂ λ l′ l″ → l ≡ l′ ++ a ∷ l″ × x ≡ L.length l′
  split-∈ here              = [] , _ , refl , refl
  split-∈ (there a∈l)
    with split-∈ a∈l
  ...  | l′ , l″ , eq , eql = _ ∷ l′ , l″ , cong (_ ∷_) eq , cong suc eql

  ∈-++ʳ : ∀ {x a} → x ∶ a ∈ l → x ∶ a ∈ l ++ l′
  ∈-++ʳ here        = here
  ∈-++ʳ (there a∈l) = there (∈-++ʳ a∈l)

subst₃ : ∀ {a b c ℓ} {A : Set a} {B : Set b} {C : Set c} (P : A → B → C → Set ℓ) {x y z u v w} → x ≡ u → y ≡ v → z ≡ w → P x y z → P u v w
subst₃ _ refl refl refl p = p

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

≤-diff : ∀ {m n} → m ≤ n → ℕ
≤-diff {_} {n} z≤n = n
≤-diff (s≤s m≤n)   = ≤-diff m≤n

≤-diff-+ : ∀ {m n} (m≤n : m ≤ n) → m + ≤-diff m≤n ≡ n
≤-diff-+ z≤n       = refl
≤-diff-+ (s≤s m≤n) = cong suc (≤-diff-+ m≤n)

ap : ∀ {i j} {A : Set i} {B : A → Set j} {f g : (a : A) → B a} → f ≡ g → ∀ a → f a ≡ g a
ap refl a = refl

lookup : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookup [] n             = nothing
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc n) = lookup xs n

repeat : ∀ {i} {A : Set i} → (A → A) → ℕ → A → A
repeat f zero x    = x
repeat f (suc n) x = f (repeat f n x)

module Measure {a b ℓ} {A : Set a} {B : Set b} {_≺_ : Rel A ℓ}
               (≺-wf : WellFounded _≺_)
               (m : B → A) where

  open import Level using () renaming (zero to lzero)
  open Wf.Inverse-image {_<_ = _≺_} m using (wellFounded)

  open Wf.All (wellFounded ≺-wf) lzero using (wfRec) public

module <-Measure = Measure <-wellFounded (λ x → x)
