{-# OPTIONS --without-K --safe #-}

module Data.Nat.ExtraProperties where

open import Data.Nat
open import Data.Nat.Properties public
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

_≤?>_ : ∀ m n → Tri (m ≤ n) (m ≡ 1 + n) (1 + n < m)
zero ≤?> n           = tri< z≤n (λ ()) (λ ())
1 ≤?> 0              = tri≈ (λ ()) refl λ { (s≤s ()) }
suc (suc m) ≤?> zero = tri> (λ ()) (λ ()) (s≤s (s≤s z≤n))
suc m ≤?> suc n with m ≤?> n
... | tri< a ¬b ¬c   = tri< (s≤s a) (λ x → ¬b (suc-injective x)) λ { (s≤s x) → ¬c x }
... | tri≈ ¬a b ¬c   = tri≈ (λ { (s≤s x) → ¬a x }) (cong suc b) λ { (s≤s x) → ¬c x }
... | tri> ¬a ¬b c   = tri> (λ { (s≤s x) → ¬a x }) (λ x → ¬b (suc-injective x)) (s≤s c)
