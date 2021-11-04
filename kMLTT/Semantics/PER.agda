{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.PER where

open import Lib
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Readback
open import Relation.Binary
  using ( Rel
        ; IsPartialEquivalence
        ; PartialSetoid
        ; Symmetric
        ; Transitive)

Ty : Set₁
Ty = Rel D _

Evs : Set₁
Evs = Rel Envs _

Bot : Dn → Dn → Set
Bot c c′ = ∀ ns (κ : UnMoT) → ∃ λ u → Re ns - c [ κ ] ↘ u × Re ns - c′ [ κ ] ↘ u

Top : Df → Df → Set
Top d d′ = ∀ ns (κ : UnMoT) → ∃ λ w → Rf ns - d [ κ ] ↘ w × Rf ns - d′ [ κ ] ↘ w

data Nat : Ty where
  ze : ze ≈ ze ∈ Nat
  su : a ≈ b ∈ Nat →
       -----------------
       su a ≈ su b ∈ Nat
  ne : c ≈ c′ ∈ Bot →
       --------------------
       ↑ N c ≈ ↑ N c′ ∈ Nat

data Neu : Ty where
  ne : c ≈ c′ ∈ Bot →
       ---------------------
       ↑ A c ≈ ↑ A′ c′ ∈ Neu
