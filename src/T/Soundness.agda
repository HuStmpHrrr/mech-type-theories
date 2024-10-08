{-# OPTIONS --without-K --safe #-}

module T.Soundness where

open import Lib
open import T.Statics
open import T.TypedSem
open import T.StaticProps

import Data.List.Properties as Lₚ
import Data.Nat.Properties as ℕₚ

open Typing

weaken : Ctx → Subst
weaken []      = I
weaken (T ∷ Γ) = weaken Γ ∘ ↑

weaken⊨s : ∀ Δ → Δ ++ Γ ⊢s weaken Δ ∶ Γ
weaken⊨s []      = S-I
weaken⊨s (T ∷ Δ) = S-∘ S-↑ (weaken⊨s Δ)

weaken-∘ : ∀ Δ′ Δ → Δ′ ++ Δ ++ Γ ⊢s weaken Δ ∘ weaken Δ′ ≈ weaken (Δ′ ++ Δ) ∶ Γ
weaken-∘ []       Δ = ∘-I (weaken⊨s Δ)
weaken-∘ (T ∷ Δ′) Δ = S-≈-trans (S-≈-sym (∘-assoc (weaken⊨s Δ) (weaken⊨s Δ′) S-↑))
                                (∘-cong ↑-≈ (weaken-∘ Δ′ Δ))

Pred : Set₁
Pred = Exp → D → Set

DPred : Set₁
DPred = Ctx → Pred

record TopPred Δ σ t a T : Set where
  field
    nf  : Nf
    ↘nf : Rf L.length Δ - ↓ T a ↘ nf
    ≈nf : Δ ⊢ t [ σ ] ≈ Nf⇒Exp nf ∶ T

record Top T Γ t a : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : ∀ Δ → TopPred (Δ ++ Γ) (weaken Δ) t a T

record BotPred Δ σ t e T : Set where
  field
    neu : Ne
    ↘ne : Re L.length Δ - e ↘ neu
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

v⇒Bot-helper : ∀ Δ → Δ ++ S ∷ Γ ⊢ v 0 [ weaken Δ ] ≈ v (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1) ∶ S
v⇒Bot-helper {S} {Γ} []      = ≈-trans ([I] (vlookup here))
                                       (subst (λ n → S ∷ Γ ⊢ v 0 ≈ v n ∶ S)
                                              (sym (cong (λ n → n ∸ 1) (ℕₚ.m+n∸n≡m 1 (L.length Γ))))
                                              (≈-refl (vlookup here)))
v⇒Bot-helper {S} {Γ} (T ∷ Δ) = ≈-trans ([∘] S-↑ (weaken⊨s Δ) (vlookup here))
                               (≈-trans ([]-cong ↑-≈ (v⇒Bot-helper Δ))
                               (≈-trans (↑-lookup (helper Δ))
                                        (subst (λ n → T ∷ Δ ++ S ∷ Γ ⊢ v n ≈ v (L.length (T ∷ Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1) ∶ S)
                                               (sym (eq Δ S Γ))
                                               (≈-refl (vlookup (helper (T ∷ Δ)))))))
  where eq : ∀ Δ S Γ → suc (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1) ≡ suc (L.length (Δ ++ S ∷ Γ)) ∸ L.length Γ ∸ 1
        eq Δ S Γ = begin
          suc (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1)
            ≡⟨ cong (λ n → suc (n ∸ L.length Γ ∸ 1)) (Lₚ.length-++ Δ) ⟩
          suc (L.length Δ + L.length (S ∷ Γ) ∸ L.length Γ ∸ 1)
            ≡⟨ cong (λ n → suc (n ∸ 1)) (ℕₚ.+-∸-assoc (L.length Δ) {suc (L.length Γ)} (ℕₚ.m≤n⇒m≤1+n ℕₚ.≤-refl)) ⟩
          suc (L.length Δ + (L.length (S ∷ Γ) ∸ L.length Γ) ∸ 1)
            ≡⟨ cong (λ n → suc (L.length Δ + n ∸ 1)) (ℕₚ.m+n∸n≡m 1 (L.length Γ)) ⟩
          suc (L.length Δ + 1 ∸ 1)
            ≡⟨ cong suc (ℕₚ.m+n∸n≡m (L.length Δ) 1) ⟩
          suc (L.length Δ)
            ≡˘⟨ ℕₚ.m+n∸n≡m (suc (L.length Δ)) 1 ⟩
          suc (L.length Δ) + 1 ∸ 1
            ≡˘⟨ cong (λ n → suc (L.length Δ) + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (L.length Γ)) ⟩
          suc (L.length Δ) + (L.length (S ∷ Γ) ∸ L.length Γ) ∸ 1
            ≡˘⟨ cong (λ n → n ∸ 1) (ℕₚ.+-∸-assoc (suc (L.length Δ)) {suc (L.length Γ)} (ℕₚ.m≤n⇒m≤1+n ℕₚ.≤-refl)) ⟩
          suc (L.length Δ) + L.length (S ∷ Γ) ∸ L.length Γ ∸ 1
            ≡˘⟨ cong (λ n → n ∸ L.length Γ ∸ 1) (Lₚ.length-++ (S ∷ Δ)) ⟩
          suc (L.length (Δ ++ S ∷ Γ)) ∸ L.length Γ ∸ 1
            ∎
          where open ≡-Reasoning

        helper : ∀ {S Γ} Δ → L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1 ∶ S ∈ Δ ++ S ∷ Γ
        helper {S} {Γ} []      = subst (λ n → n ∸ 1 ∶ S ∈ S ∷ Γ) (sym (ℕₚ.m+n∸n≡m 1 (L.length Γ))) here
        helper {S} {Γ} (T ∷ Δ) = subst (λ n → n ∶ S ∈ T ∷ Δ ++ S ∷ Γ) (eq Δ S Γ) (there (helper {S} Δ))

v⇒Bot : ∀ S Γ → Bot S (S ∷ Γ) (v 0) (l (L.length Γ))
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
          ; ↘ne = R$ _ (subst (λ l → Re L.length l - e ↘ neu) (Lₚ.++-assoc Δ′ Δ Γ) ↘ne)
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

⟦⟧-resp-trans : ∀ T → ⟦ T ⟧ Γ t a → Γ ⊢ t′ ≈ t ∶ T → ⟦ T ⟧ Γ t′ a
⟦⟧-resp-trans N       tTa t′≈ = record
  { t∶T  = ≈⇒⊢ t′≈
  ; krip = λ Δ →
    let open TopPred (krip Δ)
    in record
    { nf  = nf
    ; ↘nf = ↘nf
    ; ≈nf = ≈-trans ([]-cong (S-≈-refl (weaken⊨s Δ)) t′≈)
                    ≈nf
    }
  }
  where open Top tTa
⟦⟧-resp-trans (S ⟶ T) tTa t′≈ = record
  { t∶S⟶T = ≈⇒⊢ t′≈
  ; krip  = λ Δ sSa →
    let open FunPred (krip Δ sSa)
    in record
    { fa   = fa
    ; ↘fa  = ↘fa
    ; $Bfa = ⟦⟧-resp-trans T $Bfa ($-cong ([]-cong (S-≈-refl (weaken⊨s Δ)) t′≈) (≈-refl (⟦⟧⇒⊢ S sSa)))
    }
  }
  where open ⟦_⊨[_]_⇒[_]_⟧ tTa

inv-t[σ] : Γ ⊢ t [ σ ] ∶ T →
           ∃ λ Δ → Δ ⊢ t ∶ T × Γ ⊢s σ ∶ Δ
inv-t[σ] (t[σ] t σ) = -, t , σ

weaken-comp : ∀ Δ′ S Δ →
              Γ ⊢ t ∶ T →
              -------------------------------------------------------------------------------
              Δ′ ++ S ∷ Δ ++ Γ ⊢ t [ weaken Δ ∘ ↑ ] [ weaken Δ′ ] ≈ t [ weaken Δ ] [ weaken (Δ′ ++ S ∷ []) ] ∶ T
weaken-comp {Γ} Δ′ S Δ t∶T =
  let assoc-eq  = Lₚ.++-assoc Δ′ (S ∷ []) (Δ ++ Γ)
      assoc-eq′ = Lₚ.++-assoc Δ′ (S ∷ []) Δ
  in ≈-trans (≈-sym ([∘] (weaken⊨s Δ′) (weaken⊨s (S ∷ Δ)) t∶T))
     (≈-trans ([]-cong (weaken-∘ Δ′ (S ∷ Δ)) (≈-refl t∶T))
     (≈-trans ([]-cong (subst₂ (λ l₁ l′₁ → l₁ ⊢s weaken l′₁ ≈ _ ∘ _ ∶ Γ)
                               assoc-eq assoc-eq′
                               (S-≈-sym (weaken-∘ (Δ′ ++ S ∷ []) Δ))) (≈-refl t∶T))
              ([∘] (subst (λ l → l ⊢s _ ∶ _) assoc-eq (weaken⊨s (Δ′ ++ S ∷ []))) (weaken⊨s Δ) t∶T)))

⟦⟧-weaken : ∀ Δ T → ⟦ T ⟧ Γ t a → ⟦ T ⟧ (Δ ++ Γ) (t [ weaken Δ ]) a
⟦⟧-weaken [] T tTa                         = ⟦⟧-resp-trans T tTa ([I] (⟦⟧⇒⊢ T tTa))
⟦⟧-weaken {Γ} {t} {a} (S ∷ Δ) N tTa        =
  let t∶T = ⟦⟧⇒⊢ N tTa
      wkΔ = weaken⊨s Δ
  in record
  { t∶T  = t[σ] t∶T (S-∘ S-↑ wkΔ)
  ; krip = λ Δ′ →
    let open TopPred (krip (Δ′ ++ S ∷ []))
        assoc-eq  = Lₚ.++-assoc Δ′ (S ∷ []) (Δ ++ Γ)
        assoc-eq′ = Lₚ.++-assoc Δ′ (S ∷ []) Δ
    in record
      { nf  = nf
      ; ↘nf = subst (λ l → Rf L.length l - ↓ N a ↘ nf) assoc-eq ↘nf
      ; ≈nf = ≈-trans (weaken-comp Δ′ S Δ t∶T)
                      (subst (λ l → l ⊢ _ ≈ Nf⇒Exp nf ∶ N) assoc-eq ≈nf)
      }
  }
  where open Top (⟦⟧-weaken Δ N tTa)
⟦⟧-weaken {Γ} {t} {a} (S ∷ Δ) (T′ ⟶ T) tTa =
  let t∶T = ⟦⟧⇒⊢ (T′ ⟶ T) tTa
      wkΔ = weaken⊨s Δ
  in record
  { t∶S⟶T = t[σ] t∶T (S-∘ S-↑ wkΔ)
  ; krip  = λ Δ′ sT′b →
    let assoc-eq  = Lₚ.++-assoc Δ′ (S ∷ []) (Δ ++ Γ)
        assoc-eq′ = Lₚ.++-assoc Δ′ (S ∷ []) Δ
        open FunPred (krip (Δ′ ++ S ∷ []) (subst (λ l → ⟦ T′ ⟧ l _ _) (sym assoc-eq) sT′b))
    in record
      { fa   = fa
      ; ↘fa  = ↘fa
      ; $Bfa = ⟦⟧-resp-trans T
                             (subst (λ l → ⟦ T ⟧ l _ fa) assoc-eq $Bfa)
                             ($-cong (weaken-comp Δ′ S Δ t∶T) (≈-refl (⟦⟧⇒⊢ T′ sT′b)))
      }
  }
  where open ⟦_⊨[_]_⇒[_]_⟧ (⟦⟧-weaken Δ (T′ ⟶ T) tTa)

infix 4 _∼_∈⟦_⟧_ _⊨_∶_ _⊨s_∶_
record _∼_∈⟦_⟧_ σ (ρ : Env) Γ Δ : Set where
  field
    ⊢σ   : Δ ⊢s σ ∶ Γ
    lkup : ∀ {x T} → x ∶ T ∈ Γ → ⟦ T ⟧ Δ (v x [ σ ]) (ρ x)

record Intp Δ σ ρ t T : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    tT   : ⟦ T ⟧ Δ (t [ σ ]) ⟦t⟧

_⊨_∶_ : Ctx → Exp → Typ → Set
Γ ⊨ t ∶ T = ∀ {σ ρ Δ} → σ ∼ ρ ∈⟦ Γ ⟧ Δ → Intp Δ σ ρ t T

record Intps Δ′ σ′ ρ σ Δ : Set where
  field
    ⟦σ⟧  : Env
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    asso : (σ ∘ σ′) ∼ ⟦σ⟧ ∈⟦ Δ ⟧ Δ′

  open _∼_∈⟦_⟧_ asso public

_⊨s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊨s σ ∶ Δ = ∀ {σ′ ρ Δ′} → σ′ ∼ ρ ∈⟦ Γ ⟧ Δ′ → Intps Δ′ σ′ ρ σ Δ

∼-ext : ∀ Δ′ → σ ∼ ρ ∈⟦ Γ ⟧ Δ → ⟦ T ⟧ (Δ′ ++ Δ) t a → ((σ ∘ weaken Δ′) , t) ∼ ρ ↦ a ∈⟦ T ∷ Γ ⟧ Δ′ ++ Δ
∼-ext Δ′ σ∼ρ tTa = record
  { ⊢σ   = S-, (S-∘ (weaken⊨s Δ′) (_∼_∈⟦_⟧_.⊢σ σ∼ρ)) (⟦⟧⇒⊢ _ tTa)
  ; lkup = helper Δ′ σ∼ρ tTa
  }
  where helper : ∀ {x} Δ′ → σ ∼ ρ ∈⟦ Γ ⟧ Δ → ⟦ T ⟧ (Δ′ ++ Δ) t a → x ∶ S ∈ T ∷ Γ → ⟦ S ⟧ (Δ′ ++ Δ) (v x [ (σ ∘ weaken Δ′) , t ]) ((ρ ↦ a) x)
        helper {S = S} Δ′ σ∼ρ tTa here                = ⟦⟧-resp-trans S tTa ([,]-v-ze (S-∘ (weaken⊨s Δ′) ⊢σ) (⟦⟧⇒⊢ S tTa))
          where open _∼_∈⟦_⟧_ σ∼ρ
        helper {T = T} {S = S} Δ′ σ∼ρ tTa (there S∈Γ) = ⟦⟧-resp-trans S
                                                                      (⟦⟧-weaken Δ′ S (lkup S∈Γ))
                                                                      (≈-trans ([,]-v-su (S-∘ (weaken⊨s Δ′) ⊢σ) (⟦⟧⇒⊢ T tTa) S∈Γ)
                                                                               ([∘] (weaken⊨s Δ′) ⊢σ (vlookup S∈Γ)))
          where open _∼_∈⟦_⟧_ σ∼ρ

I-Init : ∀ Γ → I ∼ InitialEnv Γ ∈⟦ Γ ⟧ Γ
I-Init []      = record
  { ⊢σ   = S-I
  ; lkup = λ { () }
  }
I-Init (T ∷ Γ) = record
  { ⊢σ   = S-I
  ; lkup = helper
  }
  where open _∼_∈⟦_⟧_ (I-Init Γ)
        helper : ∀ {x} → x ∶ S ∈ T ∷ Γ → ⟦ S ⟧ (T ∷ Γ) (v x [ I ]) (InitialEnv (T ∷ Γ) x)
        helper here            = ⟦⟧-resp-trans T (Bot⇒⟦⟧ T (v⇒Bot T Γ)) ([I] (vlookup here))
        helper {S} (there S∈Γ) = ⟦⟧-resp-trans S
                                               (⟦⟧-weaken (T ∷ []) S (lkup S∈Γ))
                                               (≈-trans ([I] (vlookup (there S∈Γ)))
                                               (≈-trans (≈-sym (↑-lookup S∈Γ))
                                                        (≈-sym ([]-cong (I-∘ S-↑) ([I] (vlookup S∈Γ))))))

⊨⇒⊢ : Γ ⊨ t ∶ T →
      -------------
      Γ ⊢ t ∶ T
⊨⇒⊢ {Γ} {t} {T} t∶T = helper (⟦⟧⇒⊢ T tT)
  where open Intp (t∶T (I-Init _))
        helper : Γ ⊢ t [ I ] ∶ T → Γ ⊢ t ∶ T
        helper (t[σ] t∶T S-I) = t∶T

⊨s⇒⊢s : Γ ⊨s σ ∶ Δ →
        -------------
        Γ ⊢s σ ∶ Δ
⊨s⇒⊢s {Γ} {σ} {Δ} ⊨σ = helper ⊢σ
  where open Intps (⊨σ (I-Init _))
        helper : Γ ⊢s σ ∘ I ∶ Δ → Γ ⊢s σ ∶ Δ
        helper (S-∘ S-I ⊢σ) = ⊢σ

vlookup′ : ∀ {x} →
           x ∶ T ∈ Γ →
           -----------------
           Γ ⊨ v x ∶ T
vlookup′ T∈Γ σ∼ρ = record
  { ⟦t⟧  = _
  ; ↘⟦t⟧ = ⟦v⟧ _
  ; tT   = lkup T∈Γ
  }
  where open _∼_∈⟦_⟧_ σ∼ρ

ze-I′ : Γ ⊨ ze ∶ N
ze-I′ σ∼ρ = record
  { ⟦t⟧  = ze
  ; ↘⟦t⟧ = ⟦ze⟧
  ; tT   = record
    { t∶T = t[σ] ze-I ⊢σ
    ; krip = λ Δ → record
      { nf  = ze
      ; ↘nf = Rze (L.length (Δ ++ _))
      ; ≈nf = ≈-trans ([]-cong (S-≈-refl (weaken⊨s Δ)) (ze-[] ⊢σ))
                      (ze-[] (weaken⊨s Δ))
      }
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ

su-I′ : Γ ⊨ t ∶ N →
        ---------------
        Γ ⊨ su t ∶ N
su-I′ t σ∼ρ = record
  { ⟦t⟧  = su ⟦t⟧
  ; ↘⟦t⟧ = ⟦su⟧ ↘⟦t⟧
  ; tT   =
    let _ , t , σ = inv-t[σ] t∶T
    in record
    { t∶T  = t[σ] (su-I t) σ
    ; krip = λ Δ →
      let open TopPred (krip Δ)
          wΔ = weaken⊨s Δ
      in record
      { nf  = su nf
      ; ↘nf = Rsu _ ↘nf
      ; ≈nf = ≈-trans (≈-sym ([∘] wΔ σ (su-I t)))
              (≈-trans (su-[] (S-∘ wΔ σ) t)
                       (su-cong (≈-trans ([∘] wΔ σ t)
                                         ≈nf)))
      }
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        open Intp (t σ∼ρ)
        open Top tT

Λ-I′ : S ∷ Γ ⊨ t ∶ T →
       ------------------
       Γ ⊨ Λ t ∶ S ⟶ T
Λ-I′ {T = T} t σ∼ρ =
  let t∶T = ⊨⇒⊢ t
  in record
  { ⟦t⟧  = Λ _ _
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; tT   = record
    { t∶S⟶T = t[σ] (Λ-I t∶T) ⊢σ
    ; krip  = λ Δ sSa →
      let open Intp (t (∼-ext _ σ∼ρ sSa))
          wΔ  = weaken⊨s Δ
          s∶S = ⟦⟧⇒⊢ _ sSa
          s≈s = ≈-refl s∶S
          σΔ  = S-∘ wΔ ⊢σ
          qσΔ = q⇒⊢s _ σΔ
      in record
      { fa   = ⟦t⟧
      ; ↘fa  = Λ∙ ↘⟦t⟧
      ; $Bfa = ⟦⟧-resp-trans T tT
                             (≈-trans ($-cong (≈-sym ([∘] wΔ ⊢σ (Λ-I t∶T))) s≈s)
                             (≈-trans ($-cong (Λ-[] σΔ t∶T) s≈s)
                             (≈-trans (Λ-β (t[σ] t∶T qσΔ) s∶S)
                             (≈-trans (≈-sym ([∘] (S-, S-I s∶S) qσΔ t∶T))
                                      ([]-cong (S-≈-trans (,-∘ (S-, S-I s∶S) (S-∘ S-↑ σΔ) (vlookup here))
                                                          (,-cong (S-≈-trans (∘-assoc σΔ S-↑ (S-, S-I s∶S))
                                                                  (S-≈-trans (∘-cong (↑-∘-, S-I s∶S) (S-≈-refl σΔ))
                                                                             (∘-I σΔ)))
                                                                  ([,]-v-ze S-I s∶S)))
                                               (≈-refl t∶T))))))
      }
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ

TopPred-su : Γ ⊢ t ∶ N →
             TopPred (Δ ++ Γ) (weaken Δ) (su t) (su a) N →
             TopPred (Δ ++ Γ) (weaken Δ) t a N
TopPred-su {_} {t} {Δ} ⊢t record { nf = su a ; ↘nf = (Rsu ._ ↘nf) ; ≈nf = ≈nf } = record
  { nf  = a
  ; ↘nf = ↘nf
  ; ≈nf = inv-su-≈ (begin
    su (t [ weaken Δ ]) ≈˘⟨ su-[] (weaken⊨s Δ) ⊢t ⟩
    su t [ weaken Δ ]   ≈⟨ ≈nf ⟩
    su (Nf⇒Exp a)       ∎)
  }
  where open TR

N-E-helper : ∀ T →
             σ ∼ ρ ∈⟦ Γ ⟧ Δ →
             (s′ : Intp Δ σ ρ s T) →
             Γ ⊢ s ∶ T →
             (r′ : Intp Δ σ ρ r (N ⟶ T ⟶ T)) →
             Γ ⊢ r ∶ N ⟶ T ⟶ T →
             Δ ⊢ Nf⇒Exp w ∶ N →
             (∀ Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Nf⇒Exp w) b N) →
             Rf L.length Δ - ↓ N b ↘ w →
             ∃ λ a → rec T , Intp.⟦t⟧ s′ , Intp.⟦t⟧ r′ , b ↘ a × ⟦ T ⟧ Δ (rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp w)) a
N-E-helper {σ} {_} {_} {_} {s} {r} T σ∼ρ s′ ⊢s r′ ⊢r ⊢w k (Rze _)           =
  let sσ = t[σ] ⊢s ⊢σ in
  s.⟦t⟧ , rze , ⟦⟧-resp-trans T s.tT (rec-β-ze sσ (t[σ] ⊢r ⊢σ))
  where module s = Intp s′
        open _∼_∈⟦_⟧_ σ∼ρ
N-E-helper {σ} {_} {_} {Δ} {s} {r} {su w} T σ∼ρ s′ ⊢s r′ ⊢r (su-I ⊢w) k (Rsu {n} _ ↘w)
  with N-E-helper T σ∼ρ s′ ⊢s r′ ⊢r ⊢w (λ Δ′ → TopPred-su ⊢w (k Δ′)) ↘w
...  | a , ↘a , Ta                                                          =
  let sσ   = t[σ] ⊢s ⊢σ
      rσ   = t[σ] ⊢r ⊢σ
      ⊢rn  = ⟦⟧⇒⊢ (T ⟶ T) rn.$Bfa
      ⊢rec = ⟦⟧⇒⊢ T Ta in
  rna.fa , rsu ↘a rn.↘fa rna.↘fa , ⟦⟧-resp-trans T rna.$Bfa (begin
    rec T (s [ σ ]) (r [ σ ]) (su (Nf⇒Exp w))
      ≈⟨ rec-β-su sσ rσ ⊢w ⟩
    r [ σ ] $ Nf⇒Exp w $ rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp w)
      ≈⟨ $-cong ($-cong (≈-sym ([I] rσ)) (≈-refl ⊢w)) (≈-refl ⊢rec) ⟩
    r [ σ ] [ I ] $ Nf⇒Exp w $ rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp w)
      ≈⟨ $-cong (≈-sym ([I] ⊢rn)) (≈-refl ⊢rec) ⟩
    (r [ σ ] [ I ] $ Nf⇒Exp w) [ I ] $ rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp w)
      ∎)
  where module s = Intp s′
        module r = Intp r′
        open _∼_∈⟦_⟧_ σ∼ρ
        module rn where
          open ⟦_⊨[_]_⇒[_]_⟧ r.tT public
          wTop : Top N Δ (Nf⇒Exp w) n
          wTop = record
            { t∶T  = ⊢w
            ; krip = λ Δ′ → TopPred-su ⊢w (k Δ′)
            }

          open FunPred (krip [] wTop) public
        module rna where
          open ⟦_⊨[_]_⇒[_]_⟧ rn.$Bfa public
          open FunPred (krip [] Ta) public
        open TR
N-E-helper {σ} {_} {_} {Δ} {s} {r} T σ∼ρ s′ ⊢s r′ ⊢r ⊢w k (Rne {e} {u} _ ↘e) = rec′ T T (↓ T s.⟦t⟧) (↓ (N ⟶ T ⟶ T) r.⟦t⟧) _
                                                                             , rec
                                                                             , Bot⇒⟦⟧ T record
  { t∶T  = N-E (t[σ] ⊢s ⊢σ) (t[σ] ⊢r ⊢σ) ⊢w
  ; krip = λ Δ′ →
    let wΔ′ = weaken⊨s Δ′
        sσ = t[σ] ⊢s ⊢σ
        rσ = t[σ] ⊢r ⊢σ
        neu , ↘ne , ≈ne = helper Δ′ (k Δ′)
    in record
    { neu = rec T (TopPred.nf (s.krip Δ′)) (TopPred.nf (r.krip Δ′)) neu
    ; ↘ne = Rr _ (s.k.↘nf Δ′) (r.k.↘nf Δ′) ↘ne
    ; ≈ne = begin
      rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp (ne u)) [ weaken Δ′ ]
        ≈⟨ rec-[] wΔ′ sσ rσ ⊢w ⟩
      rec T (s [ σ ] [ weaken Δ′ ]) (r [ σ ] [ weaken Δ′ ]) (Nf⇒Exp (ne u) [ weaken Δ′ ])
        ≈⟨ rec-cong (s.k.≈nf Δ′) (r.k.≈nf Δ′) ≈ne ⟩
      Ne⇒Exp (rec T (s.k.nf Δ′) (r.k.nf Δ′) neu)
        ∎
    }
  }
  where module s where
          open Intp s′ public
          open Top (⟦⟧⇒Top T tT) public
          module k Δ = TopPred (krip Δ)

        module r where
          open Intp r′ public
          open Top (⟦⟧⇒Top (N ⟶ T ⟶ T) tT) public
          module k Δ = TopPred (krip Δ)

        helper : ∀ {T} Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Ne⇒Exp u) (↑ T e) N →
                 ∃ λ neu → Re L.length (Δ′ ++ Δ) - e ↘ neu × Δ′ ++ Δ ⊢ Ne⇒Exp u [ weaken Δ′ ] ≈ Ne⇒Exp neu ∶ N
        helper Δ′ record { nf = .(ne _) ; ↘nf = (Rne ._ ↘ne) ; ≈nf = ≈nf } = _ , ↘ne , ≈nf

        open _∼_∈⟦_⟧_ σ∼ρ
        open TR

N-E′ : Γ ⊨ s ∶ T →
       Γ ⊨ r ∶ N ⟶ T ⟶ T →
       Γ ⊨ t ∶ N →
       ----------------------
       Γ ⊨ rec T s r t ∶ T
N-E′ {_} {s} {T} {r} {t} ⊨s ⊨r ⊨t {σ} {_} {Δ} σ∼ρ =
  let a , ↘a , nfTa = N-E-helper T σ∼ρ (⊨s σ∼ρ) (⊨⇒⊢ ⊨s) (⊨r σ∼ρ) (⊨⇒⊢ ⊨r) (≈⇒⊢′ ≈nf) helper ↘nf
  in record
  { ⟦t⟧  = a
  ; ↘⟦t⟧ = ⟦rec⟧ s.↘⟦t⟧ r.↘⟦t⟧ t.↘⟦t⟧ ↘a
  ; tT   = ⟦⟧-resp-trans T nfTa (begin
    rec T s r t [ σ ]                     ≈⟨ rec-[] ⊢σ ⊢s ⊢r ⊢t ⟩
    rec T (s [ σ ]) (r [ σ ]) (t [ σ ])   ≈⟨ rec-cong (≈-refl (t[σ] ⊢s ⊢σ))
                                                       (≈-refl (t[σ] ⊢r ⊢σ))
                                                       (≈-trans (≈-sym ([I] (t[σ] ⊢t ⊢σ))) ≈nf) ⟩
    rec T (s [ σ ]) (r [ σ ]) (Nf⇒Exp nf) ∎)
  }
  where module s = Intp (⊨s σ∼ρ)
        module r = Intp (⊨r σ∼ρ)
        module t = Intp (⊨t σ∼ρ)
        open Top t.tT
        open _∼_∈⟦_⟧_ σ∼ρ
        open TR

        ⊢s = ⊨⇒⊢ ⊨s
        ⊢r = ⊨⇒⊢ ⊨r
        ⊢t = ⊨⇒⊢ ⊨t

        helper : ∀ Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Nf⇒Exp (TopPred.nf (krip []))) t.⟦t⟧ N
        helper Δ′ = record
          { nf  = nf
          ; ↘nf = ↘nf
          ; ≈nf = begin
            Nf⇒Exp k.nf [ weaken Δ′ ]   ≈˘⟨ []-cong (S-≈-refl (weaken⊨s Δ′)) k.≈nf ⟩
            t [ σ ] [ I ] [ weaken Δ′ ] ≈⟨ []-cong (S-≈-refl (weaken⊨s Δ′)) ([I] (t[σ] ⊢t ⊢σ)) ⟩
            t [ σ ] [ weaken Δ′ ]       ≈⟨ ≈nf ⟩
            Nf⇒Exp nf                   ∎
          }
          where module k = TopPred (krip [])
                open TopPred (krip Δ′)

        open TopPred (krip [])

Λ-E′ : Γ ⊨ r ∶ S ⟶ T →
       Γ ⊨ s ∶ S →
       -----------------
       Γ ⊨ r $ s ∶ T
Λ-E′ {_} {r} {_} {T} {s} ⊨r ⊨s {σ} σ∼ρ = record
  { ⟦t⟧  = fa
  ; ↘⟦t⟧ = ⟦$⟧ r.↘⟦t⟧ s.↘⟦t⟧ ↘fa
  ; tT   = ⟦⟧-resp-trans T $Bfa (begin
    (r $ s) [ σ ]           ≈⟨ $-[] ⊢σ ⊢r ⊢s ⟩
    r [ σ ] $ s [ σ ]       ≈⟨ $-cong (≈-sym ([I] (t[σ] ⊢r ⊢σ))) (≈-refl (t[σ] ⊢s ⊢σ)) ⟩
    r [ σ ] [ I ] $ s [ σ ] ∎)
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        module r = Intp (⊨r σ∼ρ)
        module s = Intp (⊨s σ∼ρ)
        open ⟦_⊨[_]_⇒[_]_⟧ r.tT
        open FunPred (krip [] s.tT)
        open TR
        ⊢s = ⊨⇒⊢ ⊨s
        ⊢r = ⊨⇒⊢ ⊨r

t[σ]′ : Δ ⊨ t ∶ T →
        Γ ⊨s σ ∶ Δ →
        -----------------
        Γ ⊨ t [ σ ] ∶ T
t[σ]′ {T = T} ⊨t ⊨σ σ∼ρ = record
  { ⟦t⟧  = ⟦t⟧
  ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦t⟧
  ; tT   = ⟦⟧-resp-trans T tT (≈-sym ([∘] ⊢σ (⊨s⇒⊢s ⊨σ) (⊨⇒⊢ ⊨t)))
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        module σ = Intps (⊨σ σ∼ρ)
        open σ hiding (⊢σ)
        open Intp (⊨t asso)

S-I′ : Γ ⊨s I ∶ Γ
S-I′ σ∼ρ = record
  { ⟦σ⟧ = _
  ; ↘⟦σ⟧ = ⟦I⟧
  ; asso = record
    { ⊢σ   = S-∘ ⊢σ S-I
    ; lkup = λ {_} {T} T∈Γ → ⟦⟧-resp-trans T (lkup T∈Γ) ([]-cong (I-∘ ⊢σ) (v-≈ T∈Γ))
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ

S-↑′ : S ∷ Γ ⊨s ↑ ∶ Γ
S-↑′ {σ′ = σ} σ∼ρ = record
  { ⟦σ⟧  = _
  ; ↘⟦σ⟧ = ⟦↑⟧
  ; asso = record
    { ⊢σ   = S-∘ ⊢σ S-↑
    ; lkup = λ {x} {T} T∈Γ → ⟦⟧-resp-trans T (lkup (there T∈Γ)) (begin
      v x [ ↑ ∘ σ ]   ≈⟨ [∘] ⊢σ S-↑ (vlookup T∈Γ) ⟩
      v x [ ↑ ] [ σ ] ≈⟨ []-cong (S-≈-refl ⊢σ) (↑-lookup T∈Γ) ⟩
      v (suc x) [ σ ] ∎)
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        open TR

S-∘′ : Γ ⊨s τ ∶ Γ′ →
       Γ′ ⊨s σ ∶ Γ″ →
       ----------------
       Γ ⊨s σ ∘ τ ∶ Γ″
S-∘′ {_} {τ} {_} {σ} ⊨τ ⊨σ {σ′} σ∼ρ = record
  { ⟦σ⟧  = σ.⟦σ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧
  ; asso = record
    { ⊢σ   = S-∘ ⊢σ′ (S-∘ ⊢τ ⊢σ)
    ; lkup = λ {x} {T} T∈Γ″ →
      ⟦⟧-resp-trans T (σ.lkup T∈Γ″) ([]-cong (∘-assoc ⊢σ ⊢τ ⊢σ′) (v-≈ T∈Γ″))
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ renaming (⊢σ to ⊢σ′)
        open TRS
        module τ = Intps (⊨τ σ∼ρ)
        module σ = Intps (⊨σ τ.asso)
        ⊢τ  = ⊨s⇒⊢s ⊨τ
        ⊢σ = ⊨s⇒⊢s ⊨σ

S-,′ : Γ ⊨s σ ∶ Δ →
       Γ ⊨ s ∶ S →
         -------------------
      Γ ⊨s σ , s ∶ S ∷ Δ
S-,′ {_} {σ} {Δ} {s} {S} ⊨σ ⊨s {σ′} {_} {Δ′} σ∼ρ = record
  { ⟦σ⟧  = σ.⟦σ⟧ ↦ s.⟦t⟧
  ; ↘⟦σ⟧ = ⟦,⟧ σ.↘⟦σ⟧ s.↘⟦t⟧
  ; asso = record
    { ⊢σ   = S-∘ ⊢σ′ (S-, ⊢σ ⊢s)
    ; lkup = helper
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ renaming (⊢σ to ⊢σ′)
        open TR
        module σ = Intps (⊨σ σ∼ρ)
        module s = Intp (⊨s σ∼ρ)
        ⊢σ = ⊨s⇒⊢s ⊨σ
        ⊢s = ⊨⇒⊢ ⊨s
        helper : ∀ {x} → x ∶ T ∈ S ∷ Δ → ⟦ T ⟧ Δ′ (v x [ (σ , s) ∘ σ′ ]) ((σ.⟦σ⟧ ↦ s.⟦t⟧) x)
        helper here                    = ⟦⟧-resp-trans S s.tT (begin
          v 0 [ (σ , s) ∘ σ′ ] ≈⟨ [∘] ⊢σ′ (S-, ⊢σ ⊢s) (vlookup here) ⟩
          v 0 [ σ , s ] [ σ′ ] ≈⟨ []-cong (S-≈-refl ⊢σ′) ([,]-v-ze ⊢σ ⊢s) ⟩
          s [ σ′ ]             ∎)
        helper {T} {suc x} (there T∈Δ) = ⟦⟧-resp-trans T (σ.lkup T∈Δ) (begin
          v (suc x) [ (σ , s) ∘ σ′ ] ≈⟨ [∘] ⊢σ′ (S-, ⊢σ ⊢s) (vlookup (there T∈Δ)) ⟩
          v (suc x) [ σ , s ] [ σ′ ] ≈⟨ []-cong (S-≈-refl ⊢σ′) ([,]-v-su ⊢σ ⊢s T∈Δ) ⟩
          v x [ σ ] [ σ′ ]           ≈⟨ ≈-sym ([∘] ⊢σ′ ⊢σ (vlookup T∈Δ)) ⟩
          v x [ σ ∘ σ′ ]             ∎)

mutual
  fundamental : Γ ⊢ t ∶ T → Γ ⊨ t ∶ T
  fundamental (vlookup T∈Γ) = vlookup′ T∈Γ
  fundamental ze-I          = ze-I′
  fundamental (su-I t)      = su-I′ (fundamental t)
  fundamental (N-E s r t)   = N-E′ (fundamental s) (fundamental r) (fundamental t)
  fundamental (Λ-I t)       = Λ-I′ (fundamental t)
  fundamental (Λ-E r s)     = Λ-E′ (fundamental r) (fundamental s)
  fundamental (t[σ] t σ)    = t[σ]′ (fundamental t) (fundamentals σ)

  fundamentals : Γ ⊢s σ ∶ Δ → Γ ⊨s σ ∶ Δ
  fundamentals S-↑       = S-↑′
  fundamentals S-I       = S-I′
  fundamentals (S-∘ τ σ) = S-∘′ (fundamentals τ) (fundamentals σ)
  fundamentals (S-, σ t) = S-,′ (fundamentals σ) (fundamental t)

record Soundness Γ ρ t T : Set where
  field
    nf  : Nf
    nbe : Nbe (L.length Γ) ρ t T nf
    ≈nf : Γ ⊢ t ≈ Nf⇒Exp nf ∶ T

soundness : Γ ⊢ t ∶ T → Soundness Γ (InitialEnv Γ) t T
soundness {Γ} {t} {T} ⊢t = record
  { nf  = nf
  ; nbe = record
    { ⟦t⟧  = ⟦t⟧
    ; ↘⟦t⟧ = ↘⟦t⟧
    ; ↓⟦t⟧ = ↘nf
    }
  ; ≈nf = begin
    t             ≈˘⟨ [I] ⊢t ⟩
    t [ I ]       ≈˘⟨ [I] (t[σ] ⊢t S-I) ⟩
    t [ I ] [ I ] ≈⟨ ≈nf ⟩
    Nf⇒Exp nf     ∎
  }
  where open Intp (fundamental ⊢t (I-Init Γ))
        open Top (⟦⟧⇒Top T tT)
        open TopPred (krip [])
        open TR

nbe-comp : Γ ⊢ t ∶ T → ∃ λ w → Nbe (L.length Γ) (InitialEnv Γ) t T w
nbe-comp t = nf , nbe
  where open Soundness (soundness t)
