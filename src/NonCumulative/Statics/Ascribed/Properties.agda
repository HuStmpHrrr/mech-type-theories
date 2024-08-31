{-# OPTIONS --without-K --safe #-}

-- The overall properties of the Concise formulation which are used by later modules.
--
-- Many properties have been proved in the Full formulation. We can use the
-- equivalence between the Full and Concise formulation to bring existing conclusion
-- to this file so later modules can conveniently use these results.
module NonCumulative.Statics.Ascribed.Properties where

open import Lib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)
import Relation.Binary.Reasoning.PartialSetoid as PS

-- open import MLTT.Statics.Syntax public
open import NonCumulative.Statics.Ascribed.Full
import NonCumulative.Statics.Ascribed.Presup as Presup
import NonCumulative.Statics.Ascribed.Refl as Refl
import NonCumulative.Statics.Ascribed.Misc as Misc
import NonCumulative.Statics.Ascribed.PER as PER
import NonCumulative.Statics.Ascribed.CtxEquiv as CtxEquiv
import NonCumulative.Statics.Ascribed.Properties.Contexts as Ctxₚ
import NonCumulative.Statics.Ascribed.Properties.Subst as Subₚ
open Misc
  using ( _[wk]*_)
  public

⊢≈-refl : ⊢ Γ →
          --------
          ⊢ Γ ≈ Γ
⊢≈-refl ⊢Γ = (Refl.≈-Ctx-refl ⊢Γ)

⊢≈-trans : ⊢ Γ ≈ Γ′ → ⊢ Γ′ ≈ Γ″ → ⊢ Γ ≈ Γ″
⊢≈-trans ⊢Γ≈Γ′ ⊢Γ′≈Γ′′ = PER.⊢≈-trans ⊢Γ≈Γ′ ⊢Γ′≈Γ′′

-- inversions of judgments

⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ⊢≈-refl ⊢Γ
⊢I-inv (s-conv ⊢I Δ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Δ′≈Δ

[I]-inv : ∀ { i } → Γ ⊢ t [ I ] ∶[ i ] T → Γ ⊢ t ∶[ i ] T
[I]-inv (t[σ] ⊢t[I] ⊢sI) with ⊢t ← CtxEquiv.ctxeq-tm (Ctxₚ.⊢≈-sym (⊢I-inv ⊢sI)) ⊢t[I] = conv ⊢t (≈-sym ([I] (proj₂ (Presup.presup-tm ⊢t))))
[I]-inv (conv ⊢t[I] S≈T) = conv ([I]-inv ⊢t[I]) S≈T
