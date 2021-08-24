{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.Soundness (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Restricted
open import Unbox.Gluing
open import Unbox.StaticProps
open import Unbox.SemanticProps fext
open import Unbox.GluingProps fext


v⇒Bot-gen : ∀ Γ″ {T} {Γ′} → Δ ∷ Δs ⊢r σ ∶ Γ ∷ Γs → Γ ≡ Γ″ ++ T ∷ Γ′ → Δ ∷ Δs ⊢ v (len Γ″) [ σ ] ≈ v (len Δ ∸ len Γ′ ∸ 1) ∶ T
v⇒Bot-gen Γ″ {T} {Γ′} (r-I σ≈I) refl       = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈I)
                                             (≈-trans ([I] (vlookup (length-∈ Γ″))) helper)
  where eq : len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1 ≡ len Γ″
        eq = begin
          len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1
            ≡⟨ cong (λ n → n ∸ len Γ′ ∸ 1) (Lₚ.length-++ Γ″) ⟩
          len Γ″ + suc (len Γ′) ∸ len Γ′ ∸ 1
            ≡⟨ cong (_∸ 1) (ℕₚ.+-∸-assoc (len Γ″) {suc (len Γ′)} (ℕₚ.≤-step ℕₚ.≤-refl)) ⟩
          len Γ″ + (suc (len Γ′) ∸ len Γ′) ∸ 1
            ≡⟨ cong (λ n → len Γ″ + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (len Γ′)) ⟩
          len Γ″ + 1 ∸ 1
            ≡⟨ ℕₚ.m+n∸n≡m (len Γ″) 1 ⟩
          len Γ″
            ∎
          where open ≡-Reasoning

        helper : (Γ″ ++ T ∷ Γ′) ∷ _ ⊢ v (len Γ″) ≈ v (len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1) ∶ T
        helper rewrite eq = v-≈ (length-∈ Γ″)
v⇒Bot-gen Γ″ (r-p {_} {_} {T} ⊢δ σ≈p) refl = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈p)
                                             (≈-trans ([p] (⊢r⇒⊢s ⊢δ) (length-∈ Γ″))
                                                      (v⇒Bot-gen (T ∷ Γ″) ⊢δ refl))
v⇒Bot-gen [] (r-； _ _ _ _) ()
v⇒Bot-gen (_ ∷ Γ″) (r-； _ _ _ _) ()
