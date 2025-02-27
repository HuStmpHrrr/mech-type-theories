{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Unascribed.Properties.NbE.Completeness (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib hiding (lookup)
open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Ascribed.Semantics.Domain as A
open import NonCumulative.Ascribed.Semantics.Evaluation as A
open import NonCumulative.Ascribed.Semantics.Readback as A
open import NonCumulative.Ascribed.Completeness fext as ANS
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Semantics.Domain as U
open import NonCumulative.Unascribed.Semantics.Evaluation as U
open import NonCumulative.Unascribed.Semantics.Readback as U
open import NonCumulative.Unascribed.Statics.Transfer
open import NonCumulative.Unascribed.Properties.Equivalence.Soundness fext as US
open import NonCumulative.Unascribed.Properties.Equivalence.Completeness as UC
open import NonCumulative.Unascribed.Properties.NbE.Totality fext as UT

unbe-completeness : U.Γ′ ⊢ U.t′ ≈ U.s′ ∶ U.T′ →
                    ∃ λ w′ → U.NbE U.Γ′ U.t′ U.T′ w′ × U.NbE U.Γ′ U.s′ U.T′ w′
unbe-completeness {Γ′} {t′} {s′} {T′} s′≈t′
  with Γ , t , s , i , T , Γ↝ , t↝ , s↝ , T↝ , t≈s ← U⇒A-≈ s′≈t′ 
  with w , nbet , nbes ← completeness t≈s 
  with nbet′ ← NbE-⌊⌋-total nbet
     | nbes′ ← NbE-⌊⌋-total nbes
  = _ , helpert , helpers

  where
    helpert : U.NbE Γ′ t′ T′ ⌊ w ⌋ⁿᶠ
    helpert 
      rewrite (sym (↝⇒⌊⌋ t↝))
      rewrite (sym (↝⇒⌊⌋ T↝))
      rewrite (sym (↝[]⇒[⌊⌋] Γ↝))
      = nbet′

    helpers : U.NbE Γ′ s′ T′ ⌊ w ⌋ⁿᶠ
    helpers 
      rewrite (sym (↝⇒⌊⌋ s↝))
      rewrite (sym (↝⇒⌊⌋ T↝))
      rewrite (sym (↝[]⇒[⌊⌋] Γ↝))
      = nbes′