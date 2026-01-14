{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Unascribed.Properties.NbE.Soundness (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib hiding (lookup)
open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Ascribed.Semantics.Domain as A
open import NonCumulative.Ascribed.Semantics.Evaluation as A
open import NonCumulative.Ascribed.Semantics.Readback as A
open import NonCumulative.Ascribed.Soundness fext as ANS
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Semantics.Domain as U
open import NonCumulative.Unascribed.Semantics.Evaluation as U
open import NonCumulative.Unascribed.Semantics.Readback as U
open import NonCumulative.Unascribed.Statics.Transfer
open import NonCumulative.Unascribed.Properties.Equivalence.Soundness fext as US
open import NonCumulative.Unascribed.Properties.Equivalence.Completeness as UC
open import NonCumulative.Unascribed.Properties.NbE.Totality fext as UT


Nf⇒Exp↝⌊⌋ : ∀ w →
         A.Nf⇒Exp w ↝ U.Nf⇒Exp ⌊ w ⌋ⁿᶠ
Nf⇒Exp↝⌊⌋ w
  rewrite (⌊⌋ⁿᶠ-Nf⇒Exp-comm w)
  = ⌊⌋⇒↝

unbe-soundness : U.Γ′ ⊢ U.t′ ∶ U.T′ →
                 ∃ λ w′ → U.NbE U.Γ′ U.t′ U.T′ w′ × U.Γ′ U.⊢ U.t′ ≈ U.Nf⇒Exp w′ ∶ U.T′
unbe-soundness {Γ′} {t′} {T′} ⊢t′
  with Γ , t , i , T , Γ↝ , t↝ , T↝ , ⊢t ← U⇒A-tm ⊢t′ 
  with w , nbe , t≈w ← soundness ⊢t
  with t′≈w′ ← A⇒U-≈ t≈w Γ↝ t↝ (Nf⇒Exp↝⌊⌋ w) T↝
  with nbe′ ← NbE-⌊⌋-total nbe
  = ⌊ w ⌋ⁿᶠ , helper , t′≈w′
  
  where
    helper : U.NbE Γ′ t′ T′ ⌊ w ⌋ⁿᶠ
    helper 
      rewrite (sym (↝⇒⌊⌋ t↝))
      rewrite (sym (↝⇒⌊⌋ T↝))
      rewrite (sym (↝[]⇒[⌊⌋] Γ↝))
      = nbe′

