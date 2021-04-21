{-# OPTIONS --without-K --safe #-}

module Data.List.ExtraProperties where

open import Level using (Level)

open import Data.Nat
open import Data.Product
open import Data.List
open import Data.Nat.Properties
open import Data.List.Properties public

open import Relation.Binary.PropositionalEquality

private
  variable
    a : Level
    A : Set a
    l l′ l″ l‴ : List A

++-length-inv : ∀ l l″ →
                l ++ l′ ≡ l″ ++ l‴ →
                length l″ ≤ length l →
                ∃ λ ll → l‴ ≡ ll ++ l′ × l ≡ l″ ++ ll
++-length-inv [] [] refl l″≤l      = [] , refl , refl
++-length-inv (x ∷ l) [] refl l″≤l = x ∷ l , refl , refl
++-length-inv (x ∷ l) (y ∷ l″) eq (s≤s l″≤l) with ∷-injective eq
... | refl , eq′ with ++-length-inv l l″ eq′ l″≤l
... | ll , eq″ , eq‴               = ll , eq″ , cong (x ∷_) eq‴

<-length : ∀ {n} (l : List A) →
           n < length l →
           ∃₂ λ l′ l″ → l ≡ l′ ++ l″ × n ≡ length l′ × length l ∸ n ≡ length l″ × 0 < length l″
<-length (x ∷ []) (s≤s z≤n)           = [] , x ∷ [] , refl , refl , refl , s≤s z≤n
<-length (x ∷ y ∷ l) (s≤s z≤n)        = [] , x ∷ y ∷ l , refl , refl , refl , s≤s z≤n
<-length (x ∷ y ∷ l) (s≤s (s≤s n≤l)) with <-length (y ∷ l) (s≤s n≤l)
... | l′ , l″ , eq , eq′ , eq″ , 0≤l″ = x ∷ l′ , l″ , cong (x ∷_) eq , cong suc eq′ , eq″ , 0≤l″

length-≡ : ∀ (l l″ : List A) →
           l ++ l′ ≡ l″ ++ l‴ →
           length l ≡ length l″ →
           l ≡ l″
length-≡ [] [] eq eq′ = refl
length-≡ (x ∷ l) (y ∷ l″) eq eq′ with ∷-injective eq
... | refl , eq″      = cong (x ∷_) (length-≡ l l″ eq″ (suc-injective eq′))

≤-length : ∀ {n} (l : List A) →
           n ≤ length l →
           ∃₂ λ l′ l″ → l ≡ l′ ++ l″ × n ≡ length l′ × length l ∸ n ≡ length l″
≤-length [] z≤n                = [] , [] , refl , refl , refl
≤-length (x ∷ l) z≤n           = [] , x ∷ l , refl , refl , refl
≤-length (x ∷ l) (s≤s n≤) with ≤-length l n≤
... | l′ , l″ , eq , eq′ , eq″ = x ∷ l′ , l″ , cong (x ∷_) eq , cong suc eq′ , eq″

length-∷-inv : ∀ {a} l l″ →
               l ++ l′ ≡ l″ ++ a ∷ l‴ →
               length l ≡ suc (length l″) →
               l′ ≡ l‴
length-∷-inv (x ∷ []) [] refl eq′ = refl
length-∷-inv (x ∷ l) (y ∷ l″) eq eq′ with ∷-injective eq
... | refl , eq″                  = length-∷-inv l l″ eq″ (suc-injective eq′)

∷-∷-inv : ∀ {a b} l l″ →
          l ++ l′ ≡ l″ ++ a ∷ b ∷ l‴ →
          2 + length l″ ≤ length l →
          ∃ λ ll → l‴ ≡ ll ++ l′ × l ≡ l″ ++ a ∷ b ∷ ll
∷-∷-inv (x ∷ []) [] eq (s≤s ())
∷-∷-inv (x ∷ y ∷ l) [] refl (s≤s (s≤s ≤l)) = l , refl , refl
∷-∷-inv (x ∷ l) (y ∷ l″) eq (s≤s ≤l) with ∷-injective eq
... | refl , eq′ with ∷-∷-inv l l″ eq′ ≤l
... | ll , refl , refl                     = ll , refl , refl
