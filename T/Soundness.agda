{-# OPTIONS --without-K --safe #-}

module T.Soundness where

open import Lib
open import T.Statics
open import T.TypedSem

import Data.Nat.Properties as ℕₚ

open Typing

Pred : Set₁
Pred = Exp → D → Set

DPred : Set₁
DPred = Env → Pred

record TopPred Δ σ t a T : Set where
  field
    nf  : Nf
    ↘nf : Rf List′.length Δ - ↓ T a ↘ nf
    ≈nf : Δ ⊢ t [ σ ] ≈ Nf⇒Exp nf ∶ T

record Top T Γ t a : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : (σ : Weaken Δ Γ) → TopPred Δ (Weaken⇒Subst σ) t a T

record BotPred Δ σ t e T : Set where
  field
    neu : Ne
    ↘ne : Re List′.length Δ - e ↘ neu
    ≈ne : Δ ⊢ t [ σ ] ≈ Ne⇒Exp neu ∶ T

record Bot T Γ t e : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : (σ : Weaken Δ Γ) → BotPred Δ (Weaken⇒Subst σ) t e T

Bot′ : Typ → DPred
Bot′ T Γ t a = ∃ λ e → a ≡ ↑ T e × Bot T Γ t e

record FunPred (B : DPred) Δ σ t f a s : Set where
  field
    fa   : D
    ↘fa  : f ∙ a ↘ fa
    $Bfa : B Δ (t [ σ ] $ s) fa

record ⟦_⊨[_]_⇒[_]_⟧ Γ S (A : DPred) T (B : DPred) t f : Set where
  field
    t∶S⟶T : Γ ⊢ t ∶ S ⟶ T
    krip  : (σ : Weaken Δ Γ) → A Δ s a → FunPred B Δ (Weaken⇒Subst σ) t f a s

[_]_⇒[_]_ : Typ → DPred → Typ → DPred → DPred
[ S ] A ⇒[ T ] B = ⟦_⊨[ S ] A ⇒[ T ] B ⟧

⟦_⟧ : Typ → DPred
⟦ N ⟧     = Top N
⟦ S ⟶ T ⟧ = [ S ] ⟦ S ⟧ ⇒[ T ] ⟦ T ⟧

⟦⟧⇒⊢ : ∀ T → ⟦ T ⟧ Γ t a → Γ ⊢ t ∶ T
⟦⟧⇒⊢ N ⟦T⟧       = t∶T
  where open Top ⟦T⟧
⟦⟧⇒⊢ (S ⟶ T) ⟦T⟧ = t∶S⟶T
  where open ⟦_⊨[_]_⇒[_]_⟧ ⟦T⟧

Bot⇒TopN : Bot N Γ t e → Top N Γ t (↑ N e)
Bot⇒TopN bot = record
  { t∶T  = t∶T
  ; krip = λ σ →
    let open BotPred (krip σ) in
    record
    { nf  = ne neu
    ; ↘nf = Rne _ ↘ne
    ; ≈nf = ≈ne
    }
  }
  where open Bot bot

v⇒Bot-helper : (σ : Weaken Δ (S ∷ Γ)) → Δ ⊢ v 0 [ Weaken⇒Subst σ ] ≈ v (List′.length Δ ∸ List′.length Γ ∸ 1) ∶ S
v⇒Bot-helper {Δ} {S} {Γ} I = ≈-trans ([I] (vlookup here))
                                     (subst (λ n → S ∷ Γ ⊢ v 0 ≈ v n ∶ S)
                                            (sym (cong (λ n → n ∸ 1) (ℕₚ.m+n∸n≡m 1 (List′.length Γ))))
                                            (≈-refl (vlookup here)))
v⇒Bot-helper (P T σ)       = ≈-trans ([∘] S-↑ (Weaken⇒Subst⇒⊢s σ) (vlookup here))
                             (≈-trans ([]-cong ↑-≈ (v⇒Bot-helper σ))
                             (≈-trans (↑-lookup {!!})
                                      {!!}))
v⇒Bot-helper (Q _ σ)       = {!!}

v⇒Bot : ∀ Γ → Bot S (S ∷ Γ) (v 0) (l (List′.length Γ))
v⇒Bot Γ = record
  { t∶T  = vlookup here
  ; krip = λ σ → record
    { neu = v _
    ; ↘ne = Rl _ _
    ; ≈ne = v⇒Bot-helper σ
    }
  }

mutual
  Bot⇒⟦⟧ : ∀ T → Bot T Γ t e → ⟦ T ⟧ Γ t (↑ T e)
  Bot⇒⟦⟧ N bot       = Bot⇒TopN bot
  Bot⇒⟦⟧ (S ⟶ T) bot = record
    { t∶S⟶T = t∶T
    ; krip  = λ σ sSa → record
      { fa   = [ T ] _ $′ ↓ S _
      ; ↘fa  = $∙ S T _ _
      ; $Bfa = Bot⇒⟦⟧ T record
        { t∶T  = Λ-E (t[σ] t∶T (Weaken⇒Subst⇒⊢s σ)) (⟦⟧⇒⊢ S sSa)
        ; krip = λ δ →
          let open BotPred (krip (σ ∘∘ δ))
              module S = Top (⟦⟧⇒Top S sSa)
              open TopPred (S.krip δ) in
          record
          { neu = neu $ nf
          ; ↘ne = R$ _ ↘ne ↘nf
          ; ≈ne = let ⊢δ = Weaken⇒Subst⇒⊢s δ
                      ⊢σ = Weaken⇒Subst⇒⊢s σ
                  in
                  ≈-trans ($-[] ⊢δ (t[σ] t∶T ⊢σ) (⟦⟧⇒⊢ S sSa))
                          ($-cong (≈-trans (≈-sym ([∘] ⊢δ ⊢σ t∶T))
                                  (≈-trans  ([]-cong (Weaken⇒Subst∘∘ σ δ) (≈-refl t∶T))
                                            ≈ne))
                                  ≈nf)
          }
        }
      }
    }
    where open Bot bot

  ⟦⟧⇒Top : ∀ T → ⟦ T ⟧ Γ t a → Top T Γ t a
  ⟦⟧⇒Top N ⟦T⟧       = ⟦T⟧
  ⟦⟧⇒Top (S ⟶ T) ⟦T⟧ = record
    { t∶T  = t∶S⟶T
    ; krip = λ σ →
      -- let bod = ⟦⟧⇒Top T {!!} in
      record
      { nf  = Λ {!!}
      ; ↘nf = RΛ _ {!krip (P S σ) (Bot⇒⟦⟧ S ?) !} {!!}
      ; ≈nf = {!krip!}
      }
    }
    where open ⟦_⊨[_]_⇒[_]_⟧ ⟦T⟧
