{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module kMLTT.Semantics.Properties.Evaluation (fext : Extensionality 0ℓ 0ℓ) where

open import Data.Nat.Properties
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

open import Lib
open import kMLTT.Statics.Syntax
import kMLTT.Statics.Properties.Ops as Sₚ
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Evaluation

unbox-mon : ∀ {n} (κ : UnMoT) → unbox∙ n , a ↘ b → unbox∙ L κ n , a [ κ ∥ n ] ↘ b′ → b [ κ ] ≡ b′
unbox-mon {box a} κ (box↘ n) (box↘ .(L κ n))
  rewrite D-comp a (ins vone n) κ
        | D-comp a (ins (κ ∥ n) 1) (ins vone (L κ n))
        | ins-vone-ø n κ
        | ins-1-ø-ins-vone (κ ∥ n) (L κ n) = refl
unbox-mon κ (unbox∙ {A} n) (unbox∙ .(L κ n))
  rewrite D-comp A (ins vone n) κ
        | D-comp A (ins (κ ∥ n) 1) (ins vone (L κ n))
        | ins-vone-ø n κ
        | ins-1-ø-ins-vone (κ ∥ n) (L κ n) = refl

unbox-mon-⇒ : ∀ {n} (κ : UnMoT) → unbox∙ n , a ↘ b → unbox∙ L κ n , a [ κ ∥ n ] ↘ b [ κ ]
unbox-mon-⇒ {_} {_} {n} κ ↘b = let b′ , ↘b′ = helper κ ↘b
                               in subst (unbox∙ L κ n , _ [ κ ∥ _ ] ↘_) (sym (unbox-mon κ ↘b ↘b′)) ↘b′
  where helper : ∀ {n} (κ : UnMoT) → unbox∙ n , a ↘ b → ∃ λ b′ → unbox∙ L κ n , a [ κ ∥ n ] ↘ b′
        helper {box a} κ (box↘ n)       = a [ ins (κ ∥ n) 1 ] [ ins vone (L κ n) ]
                                        , box↘ (L κ n)
        helper {↑ (□ A) c} κ (unbox∙ n) = unbox′ (A [ ins (κ ∥ n) 1 ] [ ins vone (L κ n) ]) (L κ n) (c [ κ ∥ n ])
                                        , unbox∙ (L κ n)

unbox-mon-⇐ : ∀ {n} (κ : UnMoT) → unbox∙ L κ n , a [ κ ∥ n ] ↘ b′ → ∃ λ b → unbox∙ n , a ↘ b
unbox-mon-⇐ {box a} {_} {n} κ (box↘ .(L κ n))       = a [ ins vone n ] , box↘ n
unbox-mon-⇐ {↑ (□ A) c} {_} {n} κ (unbox∙ .(L κ n)) = unbox′ (A [ ins vone n ]) n c , unbox∙ n

L-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → L ρ (L σ n) ≡ L ρ′ n
L-⟦⟧s n ⟦I⟧
  rewrite Sₚ.L-I n          = refl
L-⟦⟧s n (⟦p⟧ {σ} {_} {ρ′} ↘ρ′)
  rewrite Sₚ.L-p n σ
        | L-drop n ρ′       = L-⟦⟧s n ↘ρ′
L-⟦⟧s n (⟦,⟧ {σ} {_} {ρ′} {t} {a} ↘ρ′ ↘a)
  rewrite Sₚ.L-, n σ t
  rewrite L-↦ n ρ′ a        = L-⟦⟧s n ↘ρ′
L-⟦⟧s zero (⟦；⟧ ↘ρ′)       = refl
L-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)
  rewrite L-ρ-+ ρ m (L σ n) = cong (L ρ m +_) (L-⟦⟧s n ↘ρ′)
L-⟦⟧s n (⟦∘⟧ {δ} {_} {_} {σ} ↘ρ′ ↘ρ″)
  rewrite Sₚ.L-∘ n σ δ
        | L-⟦⟧s (L σ n) ↘ρ′ = L-⟦⟧s n ↘ρ″

∥-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ∥ n ⟧s ρ ∥ L σ n ↘ ρ′ ∥ n
∥-⟦⟧s 0 ↘ρ′                               = ↘ρ′
∥-⟦⟧s (suc n) ⟦I⟧
  rewrite Sₚ.I-∥ n
        | Sₚ.L-I n                        = ⟦I⟧
∥-⟦⟧s (suc n) (⟦p⟧ ↘ρ′)                   = ∥-⟦⟧s (suc n) ↘ρ′
∥-⟦⟧s (suc n) (⟦,⟧ ↘ρ′ ↘a)                = ∥-⟦⟧s (suc n) ↘ρ′
∥-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′) = subst (⟦ σ ∥ n ⟧s_↘ ρ′ ∥ n) (fext λ l → cong ρ (sym (+-assoc m (L σ n) l))) (∥-⟦⟧s n ↘ρ′)
∥-⟦⟧s (suc n) (⟦∘⟧ {σ = σ} ↘ρ′ ↘ρ″)       = ⟦∘⟧ (∥-⟦⟧s (L σ (suc n)) ↘ρ′) (∥-⟦⟧s (suc n) ↘ρ″)

↦-drop : ∀ ρ → drop ρ ↦ lookup ρ 0 ≡ ρ
↦-drop ρ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                    ; (suc m) → refl }))
                  ; (suc n) → refl }
