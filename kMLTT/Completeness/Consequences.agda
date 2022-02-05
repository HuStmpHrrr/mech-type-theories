{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module kMLTT.Completeness.Consequences (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics
open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Fundamental fext

Se≈⇒eq-lvl : ∀ {i j k} →
             Γ ⊢ Se i ≈ Se j ∶ Se k →
             i ≡ j
Se≈⇒eq-lvl Se≈
  with fundamental-t≈t′ Se≈
...  | ⊨Γ , _ , rel
     with InitEnvs-related ⊨Γ
...     | _ , _ , _ , _ , ρ∈
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U k< _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Se⟧ _ ; t≈t′ = t≈t′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ k<
           with t≈t′
...           | U _ eq = eq
