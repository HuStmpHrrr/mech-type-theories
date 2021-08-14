{-# OPTIONS --without-K --safe #-}

module LibNonEmpty where

import Data.List.NonEmpty hiding ([_])
open import Data.Nat
open import Data.Product
open import Data.List as List hiding (length)
open import Relation.Binary.PropositionalEquality

open import Data.Nat.Properties
open import Data.Maybe.Properties

import Data.Fin as F

module List⁺ = Data.List.NonEmpty
open List⁺ hiding (module List⁺) public

record HasLength {i} (A : Set i) : Set i where
  field
    len : A → ℕ

open HasLength {{...}} public

instance
  ListLength : ∀ {i} {A : Set i} → HasLength (List A)
  ListLength = record { len = List.length }

  List⁺Length : ∀ {i} {A : Set i} → HasLength (List⁺ A)
  List⁺Length = record { len = length }

module _ {i} {A : Set i} where
  private
    L = List⁺ A

  truncate : L → ℕ → L
  truncate l 0                 = l
  truncate (x ∷ []) (suc n)    = x ∷ []
  truncate (x ∷ y ∷ l) (suc n) = truncate (y ∷ l) n

  length-++⁺ : (l : List A) (l′ : L) → len (l ++⁺ l′) ≡ len l + len l′
  length-++⁺ [] l′          = refl
  length-++⁺ (x ∷ l) l′
    rewrite length-++⁺ l l′ = refl

  length-++⁺′ : (l : List A) (l′ : L) → len (l ++⁺ l′) ≡ suc (len l + len (List⁺.tail l′))
  length-++⁺′ [] l′          = refl
  length-++⁺′ (x ∷ l) l′
    rewrite length-++⁺′ l l′ = refl

  chop : ∀ {n} → (l : L) → n < len l → ∃₂ λ l₁ l₂ → l ≡ l₁ ++⁺ l₂ × len l₁ ≡ n
  chop {0}     l n< = [] , l , refl , refl
  chop {suc n} (x ∷ y ∷ l) (s≤s n<)
    with chop {n} (y ∷ l) n<
  ...  | l₁ , l₂ , refl , refl = x ∷ l₁ , l₂ , refl , refl

  ++-++⁺ : (l : List A) → ∀ {l′ l″} → (l ++ l′) ++⁺ l″ ≡ l ++⁺ l′ ++⁺ l″
  ++-++⁺ []      = refl
  ++-++⁺ (x ∷ l) = cong (x ∷_) (cong toList (++-++⁺ l))

  ++⁺̂ˡ-cancel : ∀ l l′ {l″ l‴ : L} → l ++⁺ l″ ≡ l′ ++⁺ l‴ → len l ≡ len l′ → l″ ≡ l‴
  ++⁺̂ˡ-cancel [] [] eq eql = eq
  ++⁺̂ˡ-cancel (x ∷ l) (y ∷ l′) eq eql = ++⁺̂ˡ-cancel l l′ (just-injective (cong fromList (cong List⁺.tail eq)))
                                                         (suc-injective eql)
  ++⁺̂ˡ-cancel′ : ∀ l {l″ l‴ : L} → l ++⁺ l″ ≡ l ++⁺ l‴ → l″ ≡ l‴
  ++⁺̂ˡ-cancel′ l eq = ++⁺̂ˡ-cancel l l eq refl

  length-<-++⁺ : ∀ l {l′ : L} → len l < len (l ++⁺ l′)
  length-<-++⁺ []      = s≤s z≤n
  length-<-++⁺ (x ∷ l) = s≤s (length-<-++⁺ l)

  find-tail : ∀ (l : List A) {l′} l″ {l‴ n} → l ++⁺ l′ ≡ l″ ++⁺ l‴ → len l″ ≡ len l + n → ∃ λ l₀ → l″ ≡ l ++ l₀ × len l₀ ≡ n
  find-tail [] {_} l″ eq eql = l″ , refl , eql
  find-tail (x ∷ l) {_} (y ∷ l″) eq eql
    with cong List⁺.head eq
  ...  | refl
    with find-tail l l″ (just-injective (cong fromList (cong List⁺.tail eq))) (suc-injective eql)
  ...  | l₀ , eq′ , eql′     = l₀ , cong (x ∷_) eq′ , eql′

  trunc⁺ : (l : L) → F.Fin (len l) → L
  trunc⁺ (x ∷ l) F.zero        = x ∷ l
  trunc⁺ (x ∷ y ∷ l) (F.suc n) = trunc⁺ (y ∷ l) n

sum⁺ : List⁺ ℕ → ℕ
sum⁺ (x ∷ l) = x + sum l
