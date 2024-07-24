{-# OPTIONS --without-K --safe #-}

module LibNonEmpty where

import Data.List.NonEmpty
open import Data.List.NonEmpty.Properties
  using ( length-++⁺
        ; length-++⁺-tail
        ; ++-++⁺
        ; ++⁺-cancelˡ′
        ; ++⁺-cancelˡ
        ; drop-+-++⁺
        ; map-++⁺
        ; length-map
        )
  public
open import Data.Nat
open import Data.Product hiding (map)
open import Data.List as List hiding (map; length)
open import Relation.Binary.PropositionalEquality

open import Data.Nat.Properties
open import Data.Maybe.Properties

import Data.Fin as F

module List⁺ = Data.List.NonEmpty
open List⁺ hiding (module List⁺; [_]) public


record HasOength {i} (A : Set i) : Set i where
  field
    len : A → ℕ

open HasOength {{...}} public

instance
  ListLength : ∀ {i} {A : Set i} → HasOength (List A)
  ListLength = record { len = List.length }

  List⁺Length : ∀ {i} {A : Set i} → HasOength (List⁺ A)
  List⁺Length = record { len = length }

module _ {i} {A : Set i} where
  private
    L = List⁺ A

  chop : ∀ {n} → (l : L) → n < len l → ∃₂ λ l₁ l₂ → l ≡ l₁ ++⁺ l₂ × len l₁ ≡ n
  chop {0}     l n< = [] , l , refl , refl
  chop {suc n} (x ∷ y ∷ l) (s≤s n<)
    with chop {n} (y ∷ l) n<
  ...  | l₁ , l₂ , refl , refl = x ∷ l₁ , l₂ , refl , refl

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

  drop+-map : ∀ {j} {B : Set j} {l n l″} {f : B → A} l′ → l ≡ l′ ++⁺ l″ → len l′ ≡ n → drop+ n (map f l) ≡ map f l″
  drop+-map [] refl refl       = refl
  drop+-map (x ∷ l′) refl refl = drop+-map l′ refl refl

  drop+-++⁺ : ∀ n (xs : List A) ys → len xs ≡ n → drop+ n (xs ++⁺ ys) ≡ ys
  drop+-++⁺ zero [] ys eq          = refl
  drop+-++⁺ (suc n) (x ∷ xs) ys eq = drop+-++⁺ n xs ys (suc-injective eq)

sum⁺ : List⁺ ℕ → ℕ
sum⁺ (x ∷ l) = x + sum l
