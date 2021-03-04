{-# OPTIONS --without-K --safe #-}

module T.Soundness where

open import Lib
open import T.Statics
open import T.TypedSem

import Data.List.Properties as Lₚ
import Data.Nat.Properties as ℕₚ

open Typing

weaken : Env → Subst
weaken []      = I
weaken (T ∷ Γ) = weaken Γ ∘ ↑

weaken⊨s : ∀ Δ → Δ ++ Γ ⊢s weaken Δ ∶ Γ
weaken⊨s []      = S-I
weaken⊨s (T ∷ Δ) = S-∘ S-↑ (weaken⊨s Δ)

weaken-∘ : ∀ Δ′ Δ → Δ′ List′.++ Δ List′.++ Γ ⊢s weaken Δ ∘ weaken Δ′ ≈ weaken (Δ′ List′.++ Δ) ∶ Γ
weaken-∘ []       Δ = ∘-I (weaken⊨s Δ)
weaken-∘ (T ∷ Δ′) Δ = S-≈-trans (S-≈-sym (∘-assoc (weaken⊨s Δ) (weaken⊨s Δ′) S-↑))
                                (∘-cong ↑-≈ (weaken-∘ Δ′ Δ))

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
    krip : ∀ Δ → TopPred (Δ ++ Γ) (weaken Δ) t a T

record BotPred Δ σ t e T : Set where
  field
    neu : Ne
    ↘ne : Re List′.length Δ - e ↘ neu
    ≈ne : Δ ⊢ t [ σ ] ≈ Ne⇒Exp neu ∶ T

record Bot T Γ t e : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : ∀ Δ → BotPred (Δ ++ Γ) (weaken Δ) t e T

record FunPred (B : DPred) Δ σ t f a s : Set where
  field
    fa   : D
    ↘fa  : f ∙ a ↘ fa
    $Bfa : B Δ (t [ σ ] $ s) fa

record ⟦_⊨[_]_⇒[_]_⟧ Γ S (A : DPred) T (B : DPred) t f : Set where
  field
    t∶S⟶T : Γ ⊢ t ∶ S ⟶ T
    krip  : ∀ Δ → A (Δ ++ Γ) s a → FunPred B (Δ ++ Γ) (weaken Δ) t f a s

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

v⇒Bot-helper : ∀ Δ → Δ ++ S ∷ Γ ⊢ v 0 [ weaken Δ ] ≈ v (List′.length (Δ ++ S ∷ Γ) ∸ List′.length Γ ∸ 1) ∶ S
v⇒Bot-helper {S} {Γ} []      = ≈-trans ([I] (vlookup here))
                                       (subst (λ n → S ∷ Γ ⊢ v 0 ≈ v n ∶ S)
                                              (sym (cong (λ n → n ∸ 1) (ℕₚ.m+n∸n≡m 1 (List′.length Γ))))
                                              (≈-refl (vlookup here)))
v⇒Bot-helper {S} {Γ} (T ∷ Δ) = ≈-trans ([∘] S-↑ (weaken⊨s Δ) (vlookup here))
                               (≈-trans ([]-cong ↑-≈ (v⇒Bot-helper Δ))
                               (≈-trans (↑-lookup (helper Δ))
                                        (subst (λ n → T ∷ Δ ++ S ∷ Γ ⊢ v n ≈ v (List′.length (T ∷ Δ ++ S ∷ Γ) ∸ List′.length Γ ∸ 1) ∶ S)
                                               (sym (eq Δ S Γ))
                                               (≈-refl (vlookup (helper (T ∷ Δ)))))))
  where eq : ∀ Δ S Γ → suc (List′.length (Δ ++ S ∷ Γ) ∸ List′.length Γ ∸ 1) ≡ suc (List′.length (Δ ++ S ∷ Γ)) ∸ List′.length Γ ∸ 1
        eq Δ S Γ = begin
          suc (List′.length (Δ ++ S ∷ Γ) ∸ List′.length Γ ∸ 1)
            ≡⟨ cong (λ n → suc (n ∸ List′.length Γ ∸ 1)) (Lₚ.length-++ Δ) ⟩
          suc (List′.length Δ + List′.length (S ∷ Γ) ∸ List′.length Γ ∸ 1)
            ≡⟨ cong (λ n → suc (n ∸ 1)) (ℕₚ.+-∸-assoc (List′.length Δ) {suc (List′.length Γ)} (ℕₚ.≤-step ℕₚ.≤-refl)) ⟩
          suc (List′.length Δ + (List′.length (S ∷ Γ) ∸ List′.length Γ) ∸ 1)
            ≡⟨ cong (λ n → suc (List′.length Δ + n ∸ 1)) (ℕₚ.m+n∸n≡m 1 (List′.length Γ)) ⟩
          suc (List′.length Δ + 1 ∸ 1)
            ≡⟨ cong suc (ℕₚ.m+n∸n≡m (List′.length Δ) 1) ⟩
          suc (List′.length Δ)
            ≡˘⟨ ℕₚ.m+n∸n≡m (suc (List′.length Δ)) 1 ⟩
          suc (List′.length Δ) + 1 ∸ 1
            ≡˘⟨ cong (λ n → suc (List′.length Δ) + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (List′.length Γ)) ⟩
          suc (List′.length Δ) + (List′.length (S ∷ Γ) ∸ List′.length Γ) ∸ 1
            ≡˘⟨ cong (λ n → n ∸ 1) (ℕₚ.+-∸-assoc (suc (List′.length Δ)) {suc (List′.length Γ)} (ℕₚ.≤-step ℕₚ.≤-refl)) ⟩
          suc (List′.length Δ) + List′.length (S ∷ Γ) ∸ List′.length Γ ∸ 1
            ≡˘⟨ cong (λ n → n ∸ List′.length Γ ∸ 1) (Lₚ.length-++ (S ∷ Δ)) ⟩
          suc (List′.length (Δ ++ S ∷ Γ)) ∸ List′.length Γ ∸ 1
            ∎
          where open ≡-Reasoning

        helper : ∀ {S Γ} Δ → List′.length (Δ ++ S ∷ Γ) ∸ List′.length Γ ∸ 1 ∶ S ∈ Δ ++ S ∷ Γ
        helper {S} {Γ} []      = subst (λ n → n ∸ 1 ∶ S ∈ S ∷ Γ) (sym (ℕₚ.m+n∸n≡m 1 (List′.length Γ))) here
        helper {S} {Γ} (T ∷ Δ) = subst (λ n → n ∶ S ∈ T ∷ Δ ++ S ∷ Γ) (eq Δ S Γ) (there (helper {S} Δ))

v⇒Bot : ∀ S Γ → Bot S (S ∷ Γ) (v 0) (l (List′.length Γ))
v⇒Bot S Γ = record
  { t∶T  = vlookup here
  ; krip = λ Δ → record
    { neu = v _
    ; ↘ne = Rl _ _
    ; ≈ne = v⇒Bot-helper Δ
    }
  }

mutual
  Bot⇒⟦⟧ : ∀ T → Bot T Γ t e → ⟦ T ⟧ Γ t (↑ T e)
  Bot⇒⟦⟧ N bot                   = Bot⇒TopN bot
  Bot⇒⟦⟧ {Γ} {t} {e} (S ⟶ T) bot = record
    { t∶S⟶T = t∶T
    ; krip  = λ Δ sSa → record
      { fa   = [ T ] _ $′ ↓ S _
      ; ↘fa  = $∙ S T _ _
      ; $Bfa = Bot⇒⟦⟧ T record
        { t∶T  = Λ-E (t[σ] t∶T (weaken⊨s Δ)) (⟦⟧⇒⊢ S sSa)
        ; krip = λ Δ′ →
          let open BotPred (krip (Δ′ ++ Δ))
              module S = Top (⟦⟧⇒Top S sSa)
              open TopPred (S.krip Δ′) in
          record
          { neu = neu $ nf
          ; ↘ne = R$ _ (subst (λ l → Re List′.length l - e ↘ neu) (Lₚ.++-assoc Δ′ Δ Γ) ↘ne)
                       ↘nf
          ; ≈ne = let wΔ′ = weaken⊨s Δ′
                      wΔ  = weaken⊨s Δ
                  in
                  ≈-trans ($-[] wΔ′ (t[σ] t∶T wΔ) (⟦⟧⇒⊢ S sSa))
                          ($-cong (≈-trans (≈-sym ([∘] wΔ′ wΔ t∶T))
                                  (≈-trans ([]-cong (weaken-∘ Δ′ Δ) (≈-refl t∶T))
                                           (subst (λ l → l ⊢ t [ weaken (Δ′ ++ Δ) ] ≈ Ne⇒Exp neu ∶ S ⟶ T) (Lₚ.++-assoc Δ′ _ _) ≈ne)))
                                  ≈nf)
          }
        }
      }
    }
    where open Bot bot

  ⟦⟧⇒Top : ∀ T → ⟦ T ⟧ Γ t a → Top T Γ t a
  ⟦⟧⇒Top N ⟦T⟧       = ⟦T⟧
  ⟦⟧⇒Top {Γ} (S ⟶ T) ⟦T⟧ = record
    { t∶T  = t∶S⟶T
    ; krip = λ Δ →
      let vSl = Bot⇒⟦⟧ S (v⇒Bot S (Δ ++ Γ))
          open FunPred (krip (S ∷ Δ) vSl)
          module T = Top (⟦⟧⇒Top T $Bfa)
          open TopPred (T.krip [])
      in
      record
      { nf  = Λ nf
      ; ↘nf = RΛ _ ↘fa ↘nf
      ; ≈nf = ≈-trans (Λ-η (t[σ] t∶S⟶T (weaken⊨s Δ)))
              (Λ-cong (≈-trans ($-cong (≈-sym ([∘] S-↑ (weaken⊨s Δ) t∶S⟶T)) (v-≈ here))
                      (≈-trans (≈-sym ([I] (Λ-E (t[σ] t∶S⟶T (S-∘ S-↑ (weaken⊨s Δ))) (vlookup here))))
                               ≈nf)))
      }
    }
    where open ⟦_⊨[_]_⇒[_]_⟧ ⟦T⟧
