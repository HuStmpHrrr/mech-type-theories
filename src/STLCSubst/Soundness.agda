{-# OPTIONS --without-K --safe #-}

module STLCSubst.Soundness where

open import Lib
open import STLCSubst.Statics
open import STLCSubst.Statics.Properties
open import STLCSubst.Semantics.Definitions

import Data.List.Properties as Lₚ
import Data.Nat.Properties as ℕₚ


weaken : Ctx → Wk
weaken Γ = repeat ⇑ (L.length Γ)

weaken⊢wk : ∀ Δ → Δ ++ Γ ⊢w weaken Δ ∶ Γ
weaken⊢wk []      = ⊢w-id
weaken⊢wk (T ∷ Δ) = ⊢wk-∙ ⊢⇑ (weaken⊢wk Δ)

weaken-∙ : ∀ Δ′ Δ → weaken Δ ∙ weaken Δ′ ≗ weaken (Δ′ ++ Δ)
weaken-∙ [] Δ         = ≗.refl
weaken-∙ (T ∷ Δ′) Δ x = cong suc (weaken-∙ Δ′ Δ x)

Pred : Set₁
Pred = Exp → D → Set

DPred : Set₁
DPred = Ctx → Pred

record TopPred Δ (ϕ : Wk) t a T : Set where
  field
    nf  : Nf
    ↘nf : Rf L.length Δ - ↓ T a ↘ nf
    ≈nf : Δ ⊢ t [ ϕ ] ≈ Nf⇒Exp nf ∶ T

record Top T Γ t a : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : ∀ Δ → TopPred (Δ ++ Γ) (weaken Δ) t a T

record BotPred Δ (ϕ : Wk) t e T : Set where
  field
    neu : Ne
    ↘ne : Re L.length Δ - e ↘ neu
    ≈ne : Δ ⊢ t [ ϕ ] ≈ Ne⇒Exp neu ∶ T

record Bot T Γ t e : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : ∀ Δ → BotPred (Δ ++ Γ) (weaken Δ) t e T

record FunPred (B : DPred) Δ (ϕ : Wk) t f a s : Set where
  field
    fa   : D
    ↘fa  : f ∙ a ↘ fa
    $Bfa : B Δ ((t [ ϕ ]) $ s) fa

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

weaken-0-length : ∀ Δ → weaken Δ 0 ≡ L.length Δ
weaken-0-length [] = refl
weaken-0-length (T ∷ Δ) = cong suc (weaken-0-length Δ)

v⇒Bot-helper′ : ∀ Δ (S : Typ) (Γ : Ctx) → v 0 [ weaken Δ ] ≡ v (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1)
v⇒Bot-helper′ Δ S Γ = begin
  v 0 [ weaken Δ ]
    ≡⟨ cong v (weaken-0-length Δ) ⟩
  v (L.length Δ)
    ≡˘⟨ cong v (ℕₚ.m+n∸n≡m (L.length Δ) 1) ⟩
  v ((L.length Δ) + 1 ∸ 1)
    ≡˘⟨ cong (λ n → v ((L.length Δ) + n ∸ 1)) (ℕₚ.m+n∸n≡m 1 (L.length Γ)) ⟩
  v ((L.length Δ) + (L.length (S ∷ Γ) ∸ L.length Γ) ∸ 1)
    ≡˘⟨ cong (λ n → v (n ∸ 1)) (ℕₚ.+-∸-assoc (L.length Δ) {suc (L.length Γ)} (ℕₚ.m≤n⇒m≤1+n ℕₚ.≤-refl)) ⟩
  v ((L.length Δ + L.length (S ∷ Γ)) ∸ L.length Γ ∸ 1)
    ≡˘⟨ cong (λ n → v (n ∸ L.length Γ ∸ 1)) (Lₚ.length-++ Δ) ⟩
  v (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1) ∎
  where open ≡-Reasoning

v⇒Bot-helper : ∀ Δ → Δ ++ S ∷ Γ ⊢ v 0 [ weaken Δ ] ≈ v (L.length (Δ ++ S ∷ Γ) ∸ L.length Γ ∸ 1) ∶ S
v⇒Bot-helper {S} {Γ} Δ
  rewrite sym (v⇒Bot-helper′ Δ S Γ) = ≈-refl (⊢conv-subst (weaken⊢wk Δ) here)

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
        { t∶T  = Λ-E (⊢wk-app t∶T (weaken⊢wk Δ)) (⟦⟧⇒⊢ S sSa)
        ; krip = λ Δ′ →
          let open BotPred (krip (Δ′ ++ Δ))
              module S = Top (⟦⟧⇒Top S sSa)
              open TopPred (S.krip Δ′) in
          record
          { neu = neu $ nf
          ; ↘ne = R$ _ (subst (λ l → Re L.length l - e ↘ neu) (Lₚ.++-assoc Δ′ Δ Γ) ↘ne)
                       ↘nf
          ; ≈ne = $-cong (subst₂ (_⊢_≈ _ ∶ _)
                                 (Lₚ.++-assoc Δ′ Δ Γ)
                                 (trans (wk-transp t (≗.sym (weaken-∙ Δ′ Δ)))
                                        (sym (wk-app-comb t (weaken Δ) (weaken Δ′))))
                                 ≈ne)
                         ≈nf
          }
        }
      }
    }
    where open Bot bot

  ⟦⟧⇒Top : ∀ T → ⟦ T ⟧ Γ t a → Top T Γ t a
  ⟦⟧⇒Top N ⟦T⟧               = ⟦T⟧
  ⟦⟧⇒Top {Γ} {t} (S ⟶ T) ⟦T⟧ = record
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
      ; ≈nf = ≈-trans (Λ-η (⊢wk-app t∶S⟶T (weaken⊢wk Δ)))
                      (Λ-cong (subst (λ x → _ ⊢ x $ v 0 ≈ Nf⇒Exp nf ∶ T)
                              (trans (wk-app-id (t [ weaken (S ∷ Δ) ]))
                              (trans (wk-transp t (≗.sym (weaken-∙ (S ∷ []) Δ)))
                                     (sym (wk-app-comb t (weaken Δ) (weaken (S ∷ []))))))
                              ≈nf))
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
    ; ≈nf = ≈-trans (≈-resp-wk t′≈ (weaken⊢wk Δ))
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
    ; $Bfa = ⟦⟧-resp-trans T $Bfa ($-cong (≈-resp-wk t′≈ (weaken⊢wk Δ)) (≈-refl (⟦⟧⇒⊢ S sSa)))
    }
  }
  where open ⟦_⊨[_]_⇒[_]_⟧ tTa


⟦⟧-weaken : ∀ Δ T → ⟦ T ⟧ Γ t a → ⟦ T ⟧ (Δ ++ Γ) (t [ weaken Δ ]) a
⟦⟧-weaken {Γ} {t} [] T tTa
  rewrite wk-app-id t                      = tTa
⟦⟧-weaken {Γ} {t} {a} (S ∷ Δ) N tTa        =
  let t∶T = ⟦⟧⇒⊢ N tTa
  in record
  { t∶T  = ⊢wk-app t∶T (weaken⊢wk (S L.∷ Δ))
  ; krip = λ Δ′ →
    let open TopPred (krip (Δ′ ++ S ∷ []))
        assoc-eq  = Lₚ.++-assoc Δ′ (S ∷ []) (Δ ++ Γ)
        assoc-eq′ = Lₚ.++-assoc Δ′ (S ∷ []) Δ
    in record
      { nf  = nf
      ; ↘nf = subst (λ l → Rf L.length l - ↓ N a ↘ nf) assoc-eq ↘nf
      ; ≈nf = subst₂ (_⊢_≈ Nf⇒Exp nf ∶ N)
                     assoc-eq
                     (trans (wk-app-comb t (weaken Δ) (weaken (Δ′ ++ S ∷ [])))
                     (trans (wk-transp t (weaken-∙ (Δ′ ++ S ∷ []) Δ))
                     (trans (cong (λ Γ → t [ weaken Γ ]) assoc-eq′)
                     (trans (sym (wk-transp t (weaken-∙ Δ′ (S ∷ Δ))))
                            (sym (wk-app-comb t (weaken (S ∷ Δ)) (weaken Δ′)))))))
                     ≈nf
      }
  }
  where open Top (⟦⟧-weaken Δ N tTa)
⟦⟧-weaken {Γ} {t} {a} (S ∷ Δ) (T′ ⟶ T) tTa =
  let t∶T = ⟦⟧⇒⊢ (T′ ⟶ T) tTa
  in record
  { t∶S⟶T = ⊢wk-app t∶T (weaken⊢wk (S ∷ Δ))
  ; krip  = λ Δ′ sT′b →
    let assoc-eq  = Lₚ.++-assoc Δ′ (S ∷ []) (Δ ++ Γ)
        assoc-eq′ = Lₚ.++-assoc Δ′ (S ∷ []) Δ
        open FunPred (krip (Δ′ ++ S ∷ []) (subst (λ l → ⟦ T′ ⟧ l _ _) (sym assoc-eq) sT′b))
    in record
      { fa   = fa
      ; ↘fa  = ↘fa
      ; $Bfa = subst₂ (λ a b → ⟦ T ⟧ a b fa)
                      assoc-eq
                      (cong (_$ _)
                            (trans (wk-app-comb t (weaken Δ) (weaken (Δ′ ++ S ∷ [])))
                            (trans (wk-transp t (weaken-∙ (Δ′ ++ S ∷ []) Δ))
                            (trans (cong (λ Γ → t [ weaken Γ ]) assoc-eq′)
                            (trans (sym (wk-transp t (weaken-∙ Δ′ (S ∷ Δ))))
                                   (sym (wk-app-comb t (weaken (S ∷ Δ)) (weaken Δ′))))))))
                      $Bfa
      }
  }
  where open ⟦_⊨[_]_⇒[_]_⟧ (⟦⟧-weaken Δ (T′ ⟶ T) tTa)

infix 4 _∼_∈⟦_⟧_ _⊨_∶_ _⊨s_∶_
record _∼_∈⟦_⟧_ σ (ρ : Env) Γ Δ : Set where
  field
    ⊢σ   : Δ ⊢s σ ∶ Γ
    lkup : ∀ {x T} → x ∶ T ∈ Γ → ⟦ T ⟧ Δ (v x [ σ ]) (ρ x)

record Intp Δ (σ : Subst) ρ t T : Set where
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
    asso : (σ ∙ σ′) ∼ ⟦σ⟧ ∈⟦ Δ ⟧ Δ′

  open _∼_∈⟦_⟧_ asso public

_⊨s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊨s σ ∶ Δ = ∀ {σ′ ρ Δ′} → σ′ ∼ ρ ∈⟦ Γ ⟧ Δ′ → Intps Δ′ σ′ ρ σ Δ

∼-ext : ∀ Δ′ → σ ∼ ρ ∈⟦ Γ ⟧ Δ → ⟦ T ⟧ (Δ′ ++ Δ) t a → ((σ [ weaken Δ′ ]) ↦ t) ∼ ρ ↦ a ∈⟦ T ∷ Γ ⟧ Δ′ ++ Δ
∼-ext Δ′ σ∼ρ tTa = record
  { ⊢σ   = ⊢ext (⊢wk-subst (_∼_∈⟦_⟧_.⊢σ σ∼ρ) (weaken⊢wk Δ′)) (⟦⟧⇒⊢ _ tTa)
  ; lkup = helper Δ′ σ∼ρ tTa
  }
  where helper : ∀ {x} Δ′ → σ ∼ ρ ∈⟦ Γ ⟧ Δ → ⟦ T ⟧ (Δ′ ++ Δ) t a → x ∶ S ∈ T ∷ Γ → ⟦ S ⟧ (Δ′ ++ Δ) (v x [ (σ [ weaken Δ′ ]) ↦ t ]) ((ρ ↦ a) x)
        helper {S = S} Δ′ σ∼ρ tTa here                = tTa
        helper {T = T} {S = S} Δ′ σ∼ρ tTa (there S∈Γ) = ⟦⟧-weaken Δ′ S (lkup S∈Γ)
          where open _∼_∈⟦_⟧_ σ∼ρ

id-Init : ∀ Γ → id ∼ InitialEnv Γ ∈⟦ Γ ⟧ Γ
id-Init []      = record
  { ⊢σ   = ⊢id
  ; lkup = λ { () }
  }
id-Init (T ∷ Γ) = record
  { ⊢σ   = ⊢id
  ; lkup = helper
  }
  where open _∼_∈⟦_⟧_ (id-Init Γ)
        helper : ∀ {x} → x ∶ S ∈ T ∷ Γ → ⟦ S ⟧ (T ∷ Γ) (v x [ v ]) (InitialEnv (T ∷ Γ) x)
        helper here            = Bot⇒⟦⟧ T (v⇒Bot T Γ)
        helper {S} (there S∈Γ) = ⟦⟧-weaken (T ∷ []) S (lkup S∈Γ)

⊨⇒⊢ : Γ ⊨ t ∶ T →
      -------------
      Γ ⊢ t ∶ T
⊨⇒⊢ {Γ} {t} {T} t∶T = helper (⟦⟧⇒⊢ T tT)
  where open Intp (t∶T (id-Init _))
        helper : Γ ⊢ t [ v ] ∶ T → Γ ⊢ t ∶ T
        helper ⊢t
          rewrite subst-app-id t = ⊢t

-- ⊨s⇒⊢s : Γ ⊨s σ ∶ Δ →
--         -------------
--         Γ ⊢s σ ∶ Δ
-- ⊨s⇒⊢s {Γ} {σ} {Δ} ⊨σ = helper ⊢σ
--   where open Intps (⊨σ (id-Init _))
--         helper : Γ ⊢s σ ∘ I ∶ Δ → Γ ⊢s σ ∶ Δ
--         helper (S-∘ S-I ⊢σ) = ⊢σ

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
    { t∶T = ze-I
    ; krip = λ Δ → record
      { nf  = ze
      ; ↘nf = Rze (L.length (Δ ++ _))
      ; ≈nf = ze-≈
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
    record
    { t∶T  = su-I t∶T
    ; krip = λ Δ →
      let open TopPred (krip Δ)
      in record
      { nf  = su nf
      ; ↘nf = Rsu _ ↘nf
      ; ≈nf = su-cong ≈nf
      }
    }
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        open Intp (t σ∼ρ)
        open Top tT

Λ-I′ : S ∷ Γ ⊨ t ∶ T →
       ------------------
       Γ ⊨ Λ t ∶ S ⟶ T
Λ-I′ {S} {_} {t} {T} ⊨t {σ} {_} {Δ′} σ∼ρ =
  let t∶T = ⊨⇒⊢ ⊨t
  in record
  { ⟦t⟧  = Λ _ _
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; tT   = record
    { t∶S⟶T = ⊢subst-app (Λ-I t∶T) ⊢σ
    ; krip  = λ {s} Δ sSa →
      let open Intp (⊨t (∼-ext _ σ∼ρ sSa))
          s∶S = ⟦⟧⇒⊢ S sSa
          s≈s = ≈-refl s∶S
      in record
      { fa   = ⟦t⟧
      ; ↘fa  = Λ∙ ↘⟦t⟧
      ; $Bfa = ⟦⟧-resp-trans T tT
                             (subst₂ (λ x y → Δ ++ Δ′ ⊢ x $ s ≈ y ∶ T)
                                    (sym (wk-app-subst (Λ t) σ (weaken Δ)))
                                    (subst-q-ext₁ t s (σ [ weaken Δ ]))
                                    (Λ-β (⊢subst-app t∶T (⊢subst-q S (⊢wk-subst ⊢σ (weaken⊢wk Δ)))) s∶S))
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
  ; ≈nf = inv-su-≈ ≈nf
  }

N-E-helper : ∀ T →
             σ ∼ ρ ∈⟦ Γ ⟧ Δ →
             (s′ : Intp Δ σ ρ s T) →
             Γ ⊢ s ∶ T →
             T ∷ N ∷ Γ ⊨ r ∶ T →
             Δ ⊢ Nf⇒Exp w ∶ N →
             (∀ Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Nf⇒Exp w) b N) →
             Rf L.length Δ - ↓ N b ↘ w →
             ∃ λ a → rec T , Intp.⟦t⟧ s′ , r , ρ , b ↘ a × ⟦ T ⟧ Δ (rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w)) a
N-E-helper {σ} {_} {_} {_} {s} {r} T σ∼ρ s′ ⊢s r′ ⊢w k (Rze _)
  = s.⟦t⟧
  , rze
  , ⟦⟧-resp-trans T
                  s.tT
                  (rec-β-ze (⊢subst-app ⊢s ⊢σ) (⊢subst-app ⊢r (⊢subst-q T (⊢subst-q N ⊢σ))))
  where module s = Intp s′
        open _∼_∈⟦_⟧_ σ∼ρ
        ⊢r = ⊨⇒⊢ r′
N-E-helper {σ} {_} {_} {Δ} {s} {r} {su w} T σ∼ρ s′ ⊢s r′ (su-I ⊢w) k (Rsu {n} _ ↘w)
  with N-E-helper T σ∼ρ s′ ⊢s r′ ⊢w (λ Δ′ → TopPred-su ⊢w (k Δ′)) ↘w
...  | a , ↘a , Ta
  = r′.⟦t⟧
  , rsu ↘a r′.↘⟦t⟧
  , ⟦⟧-resp-trans T
                  r′.tT
                  (subst (Δ ⊢ rec T _ _ _ ≈_∶ T)
                         (begin
                           r [ q (q σ) ] [ id ↦ Nf⇒Exp w ↦ rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w) ]
                             ≡⟨ subst-q-ext₂ r (Nf⇒Exp w) (rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w)) σ ⟩
                           r [ σ ↦ Nf⇒Exp w ↦ rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w) ]
                             ≡˘⟨ subst-transp r (subst-ext-cong (subst-ext-cong (subst-wk-id σ) refl) refl) ⟩
                           r [ σ [ id ] ↦ Nf⇒Exp w ↦ rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w) ]
                             ≡˘⟨ subst-transp r (subst-ext-cong (subst-wk-id (σ [ id ] ↦ Nf⇒Exp w)) refl) ⟩
                           r [ (σ [ id ] ↦ Nf⇒Exp w) [ id ] ↦ rec T (s [ σ ]) (r [ q (q σ) ]) (Nf⇒Exp w) ]
                             ∎)
                         (rec-β-su (⊢subst-app ⊢s ⊢σ) (⊢subst-app ⊢r (⊢subst-q T (⊢subst-q N ⊢σ))) ⊢w))
  where module s = Intp s′
        σw∼ρb   = ∼-ext {T = N} [] σ∼ρ record { t∶T = ⊢w ; krip = λ Δ′ → TopPred-su ⊢w (k Δ′) }
        σwr∼ρba = ∼-ext {T = T} [] σw∼ρb Ta
        module r′ = Intp (r′ σwr∼ρba)
        ⊢r = ⊨⇒⊢ r′
        open _∼_∈⟦_⟧_ σ∼ρ
        open ≡-Reasoning
N-E-helper {σ} {_} {_} {Δ} {s} {r} T σ∼ρ s′ ⊢s r′ ⊢w k (Rne {e} {u} _ ↘e)
  = rec′ T T (↓ T s.⟦t⟧) r _ e
  , rec
  , Bot⇒⟦⟧ T record
  { t∶T  = N-E (⊢subst-app ⊢s ⊢σ) (⊢subst-app ⊢r (⊢subst-q T (⊢subst-q N ⊢σ))) ⊢w
  ; krip = λ Δ′ →
    let σ∼ρN  = ∼-ext {T = N} (N ∷ Δ′) σ∼ρ (Bot⇒⟦⟧ N (v⇒Bot N (Δ′ ++ Δ)))
        σ∼ρNT = ∼-ext {T = T} (T ∷ []) σ∼ρN (Bot⇒⟦⟧ T (v⇒Bot T (N ∷ Δ′ ++ Δ))) -- (Bot⇒⟦⟧ T {!(v⇒Bot T (N ∷ Δ′ ++ Δ))!})
        module r′ = Intp (r′ σ∼ρNT)
        module r′Top = Top (⟦⟧⇒Top T r′.tT)
        neu , ↘ne , ≈ne = helper Δ′ (k Δ′)
        open ≡-Reasoning
    in record
    { neu = rec T (TopPred.nf (s.krip Δ′)) (TopPred.nf (r′Top.krip L.[])) neu
    ; ↘ne = Rr _ (s.k.↘nf Δ′) r′.↘⟦t⟧ (TopPred.↘nf (r′Top.krip [])) ↘ne
    ; ≈ne = rec-cong (s.k.≈nf Δ′)
                     (subst (_ ⊢_≈ Nf⇒Exp (TopPred.nf (r′Top.krip [])) ∶ T)
                            (begin
                              r [ (σ [ weaken (N ∷ Δ′) ] ↦ v 0) [ ⇑ ] ↦ v 0 ] [ weaken [] ]
                                ≡⟨ wk-app-id (r [ (σ [ weaken (N ∷ Δ′) ] ↦ v 0) [ ⇑ ] ↦ v 0 ]) ⟩
                              r [ (σ [ weaken (N ∷ Δ′) ] ↦ v 0) [ ⇑ ] ↦ v 0 ]
                                ≡˘⟨ subst-transp r (subst-q-equiv (σ [ weaken (N ∷ Δ′) ] ↦ v 0)) ⟩
                              r [ q (σ [ weaken (N ∷ Δ′) ] ↦ v 0) ]
                                ≡˘⟨ subst-transp r (subst-q-cong (subst-ext-cong (λ x → wk-transp (σ x) (weaken-∙ (N ∷ []) Δ′)) refl)) ⟩
                              r [ q (σ [ weaken Δ′ ∙ ⇑ ] ↦ v 0) ]
                                ≡˘⟨ subst-transp r (subst-q-cong (subst-ext-cong (λ x → wk-app-comb (σ x) (weaken Δ′) ⇑) refl)) ⟩
                              r [ q (σ [ weaken Δ′ ] [ ⇑ ] ↦ v 0) ]
                                ≡˘⟨ subst-transp r (subst-q-cong (subst-q-equiv (σ [ weaken Δ′ ]))) ⟩
                              r [ q (q (σ [ weaken Δ′ ])) ]
                                ≡˘⟨ subst-transp r (wk-subst-q₂ σ (weaken Δ′)) ⟩
                              r [ q (q σ) [ q (q (weaken Δ′)) ] ]
                                ≡˘⟨ wk-app-subst r (q (q σ)) (q (q (weaken Δ′))) ⟩
                              r [ q (q σ) ] [ q (q (weaken Δ′)) ]
                                ∎)
                            (TopPred.≈nf (r′Top.krip [])))
                     ≈ne
    }
  }
  where module s where
          open Intp s′ public
          open Top (⟦⟧⇒Top T tT) public
          module k Δ = TopPred (krip Δ)
        ⊢r = ⊨⇒⊢ r′
        helper : ∀ {T} Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Ne⇒Exp u) (↑ T e) N →
                 ∃ λ neu → Re L.length (Δ′ ++ Δ) - e ↘ neu × Δ′ ++ Δ ⊢ Ne⇒Exp u [ weaken Δ′ ] ≈ Ne⇒Exp neu ∶ N
        helper Δ′ record { nf = .(ne _) ; ↘nf = (Rne ._ ↘ne) ; ≈nf = ≈nf } = _ , ↘ne , ≈nf
        open _∼_∈⟦_⟧_ σ∼ρ

N-E′ : Γ ⊨ s ∶ T →
       T ∷ N ∷ Γ ⊨ r ∶ T →
       Γ ⊨ t ∶ N →
       ----------------------
       Γ ⊨ rec T s r t ∶ T
N-E′ {_} {s} {T} {r} {t} ⊨s ⊨r ⊨t {σ} {_} {Δ} σ∼ρ =
  let a , ↘a , nfTa = N-E-helper T σ∼ρ (⊨s σ∼ρ) (⊨⇒⊢ ⊨s) ⊨r (≈⇒⊢′ ≈nf) helper ↘nf
  in record
  { ⟦t⟧  = a
  ; ↘⟦t⟧ = ⟦rec⟧ s.↘⟦t⟧ t.↘⟦t⟧ ↘a
  ; tT   = ⟦⟧-resp-trans T
                         nfTa
                         (rec-cong (≈-refl ((⊢subst-app ⊢s ⊢σ)))
                                   (≈-refl ((⊢subst-app ⊢r (⊢subst-q T (⊢subst-q N ⊢σ)))))
                                   (subst (_ ⊢_≈ _ ∶ _) (wk-app-id (t [ σ ])) ≈nf))
  }
  where module s = Intp (⊨s σ∼ρ)
        module t = Intp (⊨t σ∼ρ)
        open Top t.tT
        open _∼_∈⟦_⟧_ σ∼ρ
        ⊢s = ⊨⇒⊢ ⊨s
        ⊢r = ⊨⇒⊢ ⊨r
        ⊢t = ⊨⇒⊢ ⊨t

        helper : ∀ Δ′ → TopPred (Δ′ ++ Δ) (weaken Δ′) (Nf⇒Exp (TopPred.nf (krip []))) t.⟦t⟧ N
        helper Δ′ = record
          { nf = nf
          ; ↘nf = ↘nf
          ; ≈nf = begin
            Nf⇒Exp k.nf [ weaken Δ′ ]   ≈˘⟨ ≈-resp-wk (subst (_ ⊢_≈ _ ∶ _) (wk-app-id (t [ σ ])) k.≈nf) (weaken⊢wk Δ′) ⟩
            t [ σ ] [ weaken Δ′ ]       ≈⟨ ≈nf ⟩
            Nf⇒Exp nf                   ∎
          }
          where module k = TopPred (krip [])
                open TopPred (krip Δ′)
                open TR

        open TopPred (krip [])

Λ-E′ : Γ ⊨ r ∶ S ⟶ T →
       Γ ⊨ s ∶ S →
       -----------------
       Γ ⊨ r $ s ∶ T
Λ-E′ {_} {r} {_} {T} {s} ⊨r ⊨s {σ} σ∼ρ = record
  { ⟦t⟧  = fa
  ; ↘⟦t⟧ = ⟦$⟧ r.↘⟦t⟧ s.↘⟦t⟧ ↘fa
  ; tT   = subst (λ x → ⟦ T ⟧ _ (x $ _) _) (wk-app-id (r [ σ ])) $Bfa
  }
  where open _∼_∈⟦_⟧_ σ∼ρ
        module r = Intp (⊨r σ∼ρ)
        module s = Intp (⊨s σ∼ρ)
        open ⟦_⊨[_]_⇒[_]_⟧ r.tT
        open FunPred (krip [] s.tT)



fundamental : Γ ⊢ t ∶ T → Γ ⊨ t ∶ T
fundamental (vlookup T∈Γ) = vlookup′ T∈Γ
fundamental ze-I          = ze-I′
fundamental (su-I t)      = su-I′ (fundamental t)
fundamental (N-E s r t)   = N-E′ (fundamental s) (fundamental r) (fundamental t)
fundamental (Λ-I t)       = Λ-I′ (fundamental t)
fundamental (Λ-E r s)     = Λ-E′ (fundamental r) (fundamental s)

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
  ; ≈nf = subst (_ ⊢_≈ Nf⇒Exp nf ∶ _) (trans (wk-app-id (t [ v ])) (subst-app-id t)) ≈nf
  }
  where open Intp (fundamental ⊢t (id-Init Γ))
        open Top (⟦⟧⇒Top T tT)
        open TopPred (krip [])

nbe-comp : Γ ⊢ t ∶ T → ∃ λ w → Nbe (L.length Γ) (InitialEnv Γ) t T w
nbe-comp t = nf , nbe
  where open Soundness (soundness t)
