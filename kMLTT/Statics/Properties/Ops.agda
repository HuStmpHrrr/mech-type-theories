{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Ops where

open import Data.Nat.Properties as Nₚ
open import Data.List.Properties as Lₚ

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Properties.Contexts

L-<-len : Γ ⊢s σ ∶ Δ →
        ∀ n →
        n < len Δ →
        --------------
        L σ n < len Γ
L-<-len ⊢σ zero n<l              = s≤s z≤n
L-<-len (s-I x) (suc n) n<l      = n<l
L-<-len (s-p ⊢σ) (suc n) n<l     = L-<-len ⊢σ (suc n) n<l
L-<-len (s-∘ ⊢σ ⊢δ) (suc n) n<l  = L-<-len ⊢σ _ (L-<-len ⊢δ (suc n) n<l)
L-<-len (s-, ⊢σ _ _) (suc n) n<l = L-<-len ⊢σ (suc n) n<l
L-<-len (s-； {Γ} {n = m} Ψs ⊢σ _ eq) (suc n) (s≤s n<l)
  rewrite length-++⁺′ Ψs Γ | eq
  with L-<-len ⊢σ n n<l
...  | s≤s L<l                   = s≤s (+-monoʳ-≤ m L<l)
L-<-len (s-conv ⊢σ Δ′≈Δ) (suc n) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)      = L-<-len ⊢σ (suc n) n<l

∥-⊢s : Γ ⊢s σ ∶ Δ →
       ∀ n →
       n < len Δ →
       --------------------------------------------------
       ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
          Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
          len Ψs ≡ L σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ∶ Δ′
∥-⊢s ⊢σ zero n<l                                   = [] , [] , -, -, refl , refl , refl , refl , ⊢σ
∥-⊢s {Γ} (s-I ⊢Γ) (suc n) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                          = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , s-I (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-⊢s (s-p ⊢σ) (suc n) n<l
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , (T ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (s-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) (suc n) n<l
  with ∥-⊢s ⊢δ (suc n) n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , ⊢δ∥
     with ∥-⊢s ⊢σ (L δ (suc n)) (L-<-len ⊢δ (suc n) n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , ⊢σ∥
        rewrite ++⁺ˡ-cancel Ψs Ψs‴
                            (trans (sym eq) eq‴)
                            (trans eql (sym eql‴)) = Ψs″ , Ψs′ , Δ′ , Γ′ , eq″ , eq′ , eql″ , eql′ , s-∘ ⊢σ∥ ⊢δ∥
∥-⊢s (s-, ⊢σ _ _) (suc n) n<l
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , (_ ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (s-； Ψs ⊢σ _ eq) (suc n) (s≤s n<l)
  with ∥-⊢s ⊢σ n n<l
...  | Ψs′ , Ψs″ , Γ′ , Δ′
     , refl , eq″ , eql′ , eql″ , ⊢σ∥              = Ψs ++ Ψs′ , [] ∷ Ψs″ , Γ′ , Δ′
                                                   , sym (++-++⁺ Ψs) , cong ([] ∷⁺_) eq″
                                                   , trans (length-++ Ψs) (cong₂ _+_ eq eql′) , cong suc eql″ , ⊢σ∥
∥-⊢s (s-conv ⊢σ Δ′≈Δ) (suc n) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥
     with ≈⇒∥⇒∥ Ψs′ Δ′≈Δ
...    | Ψs″ , Δ″ , eq″ , eql″ , Δ′≈Δ∥             = Ψs , Ψs″ , Γ′ , Δ″ , eq , eq″ , eql , trans (sym eql″) eql′ , s-conv ⊢σ∥ Δ′≈Δ∥
