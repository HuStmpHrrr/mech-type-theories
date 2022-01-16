{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.Properties.NoFunExt.LogRel where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel


®Nat⇒∈Nat : Γ ⊢ t ∶N® a ∈Nat → a ∈′ Nat
®Nat⇒∈Nat ze         = ze
®Nat⇒∈Nat (su _ rel) = su (®Nat⇒∈Nat rel)
®Nat⇒∈Nat (ne c∈ _)  = ne c∈

®Nat⇒∶Nat : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ → Γ ⊢ t ∶ N
®Nat⇒∶Nat ze ⊢Γ         = ze-I ⊢Γ
®Nat⇒∶Nat (su t≈ _) ⊢Γ  = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (ne _ rel) ⊢Γ = [I]-inv (proj₁ (proj₂ (presup-≈ (rel (⊢rI ⊢Γ)))))

®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Γ ⊢ T ∶ Se i
®⇒ty (ne C≈C′) (⊢T , _)  = ⊢T
®⇒ty N T∼A          = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (U j<i eq) T∼A = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (□ A≈B) T∼A    = proj₁ (proj₂ (presup-≈ T≈))
  where open Glu□ T∼A
®⇒ty (Π iA RT) T∼A  = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T∼A
