{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

-- Properties of the evaluation operation
module Mint.Semantics.Properties.Evaluation (fext : Extensionality 0ℓ 0ℓ) where

open import Data.Nat.Properties
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

open import Lib hiding (lookup)
open import Mint.Statics.Syntax
import Mint.Statics.Properties.Ops as Sₚ
open import Mint.Semantics.Domain
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Evaluation
open import Mint.Semantics.Properties.NoFunExt.Evaluation public

-- monotonicity of evaluation and associated operations

unbox-mon : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → unbox∙ O κ n , a [ κ ∥ n ] ↘ b′ → b [ κ ] ≡ b′
unbox-mon {box a} κ (box↘ n) (box↘ .(O κ n))
  rewrite D-comp a (ins vone n) κ
        | D-comp a (ins (κ ∥ n) 1) (ins vone (O κ n))
        | ins-vone-ø n κ
        | ins-1-ø-ins-vone (κ ∥ n) (O κ n) = refl
unbox-mon κ (unbox∙ {A} n) (unbox∙ .(O κ n))
  rewrite D-comp A (ins vone n) κ
        | D-comp A (ins (κ ∥ n) 1) (ins vone (O κ n))
        | ins-vone-ø n κ
        | ins-1-ø-ins-vone (κ ∥ n) (O κ n) = refl

unbox-mon-⇒ : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → unbox∙ O κ n , a [ κ ∥ n ] ↘ b [ κ ]
unbox-mon-⇒ {_} {_} {n} κ ↘b = let b′ , ↘b′ = helper κ ↘b
                               in subst (unbox∙ O κ n , _ [ κ ∥ _ ] ↘_) (sym (unbox-mon κ ↘b ↘b′)) ↘b′
  where helper : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → ∃ λ b′ → unbox∙ O κ n , a [ κ ∥ n ] ↘ b′
        helper {box a} κ (box↘ n)       = a [ ins (κ ∥ n) 1 ] [ ins vone (O κ n) ]
                                        , box↘ (O κ n)
        helper {↑ (□ A) c} κ (unbox∙ n) = unbox′ (A [ ins (κ ∥ n) 1 ] [ ins vone (O κ n) ]) (O κ n) (c [ κ ∥ n ])
                                        , unbox∙ (O κ n)

unbox-mon-⇐ : ∀ {n} (κ : UMoT) → unbox∙ O κ n , a [ κ ∥ n ] ↘ b′ → ∃ λ b → unbox∙ n , a ↘ b
unbox-mon-⇐ {box a} {_} {n} κ (box↘ .(O κ n))       = a [ ins vone n ] , box↘ n
unbox-mon-⇐ {↑ (□ A) c} {_} {n} κ (unbox∙ .(O κ n)) = unbox′ (A [ ins vone n ]) n c , unbox∙ n

∥-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ∥ n ⟧s ρ ∥ O σ n ↘ ρ′ ∥ n
∥-⟦⟧s 0 ↘ρ′                               = ↘ρ′
∥-⟦⟧s (suc n) ⟦I⟧
  rewrite Sₚ.I-∥ n
        | Sₚ.O-I n                        = ⟦I⟧
∥-⟦⟧s (suc n) ⟦wk⟧                        = ⟦I⟧
∥-⟦⟧s (suc n) (⟦,⟧ ↘ρ′ ↘a)                = ∥-⟦⟧s (suc n) ↘ρ′
∥-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′) = subst (⟦ σ ∥ n ⟧s_↘ ρ′ ∥ n) (fext λ l → cong ρ (sym (+-assoc m (O σ n) l))) (∥-⟦⟧s n ↘ρ′)
∥-⟦⟧s (suc n) (⟦∘⟧ {σ = σ} ↘ρ′ ↘ρ″)       = ⟦∘⟧ (∥-⟦⟧s (O σ (suc n)) ↘ρ′) (∥-⟦⟧s (suc n) ↘ρ″)

↦-drop : ∀ ρ → drop ρ ↦ lookup ρ 0 ≡ ρ
↦-drop ρ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                    ; (suc m) → refl }))
                  ; (suc n) → refl }

-- Evaluation is monotonic.
--
-- This is a very pleasant consequence of having UMoTs. In other words, evaluting in a
-- modal transformed environment is the same as modal transforming the result of
-- evaluation in the original environment.
mutual
  ⟦⟧-mon : (κ : UMoT) → ⟦ T ⟧ ρ ↘ A → ⟦ T ⟧ ρ [ κ ] ↘ A [ κ ]
  ⟦⟧-mon κ ⟦N⟧                                                    = ⟦N⟧
  ⟦⟧-mon κ (⟦Π⟧ ↘A)                                               = ⟦Π⟧ (⟦⟧-mon κ ↘A)
  ⟦⟧-mon κ (⟦Se⟧ i)                                               = ⟦Se⟧ i
  ⟦⟧-mon {□ T} {ρ} {□ A} κ (⟦□⟧ ↘A)                               = ⟦□⟧ (subst (⟦ T ⟧_↘ A [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (⟦⟧-mon (ins κ 1) ↘A))
  ⟦⟧-mon κ (⟦v⟧ n)                                                = ⟦v⟧ n
  ⟦⟧-mon κ ⟦ze⟧                                                   = ⟦ze⟧
  ⟦⟧-mon κ (⟦su⟧ ↘A)                                              = ⟦su⟧ (⟦⟧-mon κ ↘A)
  ⟦⟧-mon κ (⟦rec⟧ ↘a ↘b rec↘)                                     = ⟦rec⟧ (⟦⟧-mon κ ↘a) (⟦⟧-mon κ ↘b) (rec-mon κ rec↘)
  ⟦⟧-mon κ (⟦Λ⟧ t)                                                = ⟦Λ⟧ t
  ⟦⟧-mon κ (⟦$⟧ ↘f ↘a ↘A)                                         = ⟦$⟧ (⟦⟧-mon κ ↘f) (⟦⟧-mon κ ↘a) (∙-mon κ ↘A)
  ⟦⟧-mon {box t} {ρ} {box A} κ (⟦box⟧ ↘A)                         = ⟦box⟧ (subst (⟦ t ⟧_↘ A [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (⟦⟧-mon (ins κ 1) ↘A))
  ⟦⟧-mon {unbox .n t} {ρ} {A} κ (⟦unbox⟧ {_} {_} {a} n ↘a unbox↘) = ⟦unbox⟧ n
                                                                            (subst (⟦ t ⟧_↘ a [ κ ∥ O ρ n ]) (sym (ρ-∥-[] ρ κ n)) (⟦⟧-mon (κ ∥ O ρ n) ↘a))
                                                                            (subst (unbox∙_, a [ κ ∥ O ρ n ] ↘ A [ κ ]) (sym (O-ρ-[] ρ κ n)) (unbox-mon-⇒ κ unbox↘))
  ⟦⟧-mon κ (⟦[]⟧ ↘ρ′ ↘A)                                          = ⟦[]⟧ (⟦⟧s-mon κ ↘ρ′) (⟦⟧-mon κ ↘A)

  ⟦⟧s-mon : (κ : UMoT) → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ [ κ ] ↘ ρ′ [ κ ]
  ⟦⟧s-mon κ ⟦I⟧                                  = ⟦I⟧
  ⟦⟧s-mon {_} {ρ} κ ⟦wk⟧                         = subst (⟦ wk ⟧s ρ [ κ ] ↘_) (sym (drop-mon ρ κ)) ⟦wk⟧
  ⟦⟧s-mon {σ , t} {ρ} κ (⟦,⟧ ↘ρ′ ↘a)             = subst (⟦ σ , t ⟧s ρ [ κ ] ↘_) (sym (↦-mon _ _ κ)) (⟦,⟧ (⟦⟧s-mon κ ↘ρ′) (⟦⟧-mon κ ↘a))
  ⟦⟧s-mon {σ ； n} {ρ} κ (⟦；⟧ {_} {_} {ρ′} ↘ρ′) = subst (⟦ σ ； n ⟧s ρ [ κ ] ↘_)
                                                          (trans (cong (ext _) (O-ρ-[] ρ κ n)) (sym (ext-mon ρ′ (O ρ n) κ)))
                                                          (⟦；⟧ (subst (⟦ σ ⟧s_↘ ρ′ [ κ ∥ O ρ n ]) (sym (ρ-∥-[] ρ κ n)) (⟦⟧s-mon (κ ∥ O ρ n) ↘ρ′)))
  ⟦⟧s-mon κ (⟦∘⟧ ↘ρ″ ↘ρ′)                        = ⟦∘⟧ (⟦⟧s-mon κ ↘ρ″) (⟦⟧s-mon κ ↘ρ′)

  ∙-mon : ∀ {fa} → (κ : UMoT) → f ∙ a ↘ fa → f [ κ ] ∙ a [ κ ] ↘ fa [ κ ]
  ∙-mon {_} {a} {fa} κ (Λ∙ {t} {ρ} ↘fa) = Λ∙ (subst (⟦ t ⟧_↘ fa [ κ ]) (↦-mon ρ a κ) (⟦⟧-mon κ ↘fa))
  ∙-mon κ ($∙ {T} {ρ} {a} {B} A c ↘B)   = $∙ (A [ κ ]) (c [ κ ]) (subst (⟦ T ⟧_↘ B [ κ ]) (↦-mon ρ a κ) (⟦⟧-mon κ ↘B))

  rec-mon : (κ : UMoT) → rec∙ T , a , r , ρ , b ↘ A → rec∙ T , a [ κ ] , r , ρ [ κ ] , b [ κ ] ↘ A [ κ ]
  rec-mon κ ze↘ = ze↘
  rec-mon {r = r} {A = A} κ (su↘ {ρ = ρ} {b} {b′} rec↘ ↘A) = su↘ (rec-mon κ rec↘) (subst (⟦ r ⟧_↘ A [ κ ]) (trans (↦-mon (ρ ↦ b) b′ κ) (cong (_↦ b′ [ κ ]) (↦-mon ρ b κ))) (⟦⟧-mon κ ↘A))
  rec-mon κ (rec∙ {T} {ρ} {c} {A} ↘A) = rec∙ (subst (⟦ T ⟧_↘ A [ κ ]) (↦-mon ρ (↑ N c) κ) (⟦⟧-mon κ ↘A))
