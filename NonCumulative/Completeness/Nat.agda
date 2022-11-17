{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Nat
module NonCumulative.Completeness.Nat (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import NonCumulative.Completeness.LogRel

open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Realizability fext


N-≈′ : ⊨ Γ →
       ----------------
       Γ ⊨ N ≈ N ∶[ 1 ] Se 0
N-≈′ ⊨Γ = ⊨Γ , λ ρ≈ρ′ → record
                        { ↘⟦T⟧  = ⟦Se⟧ _
                        ; ↘⟦T′⟧ = ⟦Se⟧ _
                        ; T≈T′  = U′
                        }
                        , record
                        { ↘⟦t⟧  = ⟦N⟧
                        ; ↘⟦t′⟧ = ⟦N⟧
                        ; t≈t′  = N′
                        }

ze-≈′ : ⊨ Γ →
        ----------------
        Γ ⊨ ze ≈ ze ∶[ 0 ] N
ze-≈′ ⊨Γ = ⊨Γ , λ ρ≈ρ′ → record
                         { ↘⟦T⟧  = ⟦N⟧
                         ; ↘⟦T′⟧ = ⟦N⟧
                         ; T≈T′  = N′
                         }
                         , record
                         { ↘⟦t⟧  = ⟦ze⟧
                         ; ↘⟦t′⟧ = ⟦ze⟧
                         ; t≈t′  = ze
                         }

su-cong′ : Γ ⊨ t ≈ t′ ∶[ 0 ] N →
           ----------------
           Γ ⊨ su t ≈ su t′ ∶[ 0 ] N
su-cong′ {_} {t} {t′} (⊨Γ , t≈t′) = ⊨Γ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ------------------------------------------------------------
             Σ (RelTyp 0 N ρ N ρ′)
             λ rel → RelExp (su t) ρ (su t′) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N′ }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                        { ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N′
                        }
                        , record
                        { ↘⟦t⟧  = ⟦su⟧ ↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦su⟧ ↘⟦t′⟧
                        ; t≈t′  = su t≈t′
                        }


-- A lemma to handle asymmetry appears in several Nat judgements.
-- This follows the trick of []-cong′ in NonCumulative.Completeness.Terms.
--
-- An example of asymmetry is in the return type of rec-cong′:
--
--   Γ ⊨ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
--
-- Here, the RHS says that rec T′ s′ r′ t′ is of T [| t ], and thus
-- has different terms (t′ and t) unlike the LHS.
RelExp-refl : ∀ {n} (⊨Γ : ⊨ Γ) →
              ({ρ ρ′ : Env} → (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp n T ρ T′ ρ′) (λ rel → RelExp t ρ t′ ρ′ (El _ (RelTyp.T≈T′ rel)))) →
              ({ρ ρ′ : Env} → (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp n T ρ T ρ′) (λ rel → RelExp t ρ t ρ′ (El _ (RelTyp.T≈T′ rel))))
RelExp-refl ⊨Γ TT′ ρ≈ρ′
  with TT′ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′)
     | TT′ ρ≈ρ′
     | TT′ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
     , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
     | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ }
     , record { ↘⟦t⟧ = ↘⟦t⟧₁ ; ↘⟦t′⟧ = ↘⟦t′⟧₁ }
     | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
     , record { ↘⟦t⟧ = ↘⟦t⟧₂ ; ↘⟦t′⟧ = ↘⟦t′⟧₂ ; t≈t′ = t≈t′₂ }
    rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
          | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₂
          | ⟦⟧-det ↘⟦t⟧ ↘⟦t⟧₁
          | ⟦⟧-det ↘⟦t′⟧ ↘⟦t′⟧₂ = record
                                { ↘⟦T⟧ = ↘⟦T⟧₁
                                ; ↘⟦T′⟧ = ↘⟦T⟧₂
                                ; T≈T′ = 𝕌-trans T≈T′ (𝕌-sym T≈T′₂)
                                }
                              , record
                                { ↘⟦t⟧ = ↘⟦t⟧₁
                                ; ↘⟦t′⟧ = ↘⟦t⟧₂
                                ; t≈t′ = El-trans T≈T′ (𝕌-sym T≈T′₂) (𝕌-trans T≈T′ (𝕌-sym T≈T′₂)) t≈t′ (El-sym T≈T′₂ (𝕌-sym T≈T′₂) t≈t′₂)
                                }

rec-helper : ∀ {i}
             (⊨Γ : ⊨ Γ)
             (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) →
             (TT′ : (N₀ ∷ Γ) ⊨ T ≈ T′ ∶[ 1 + i ] Se i) →
             (ss′ : Γ ⊨ s ≈ s′ ∶[ i ] T [| ze ∶ N₀ ]) →
             (rr′ : (T ↙ i) ∷ N₀ ∷ Γ ⊨ r ≈ r′ ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ]) →
             a ≈ b ∈ Nat →
             -----------------------------------------------------
             let (_   , _   ) = TT′
                 (⊨Γ₂ , s≈s′) = ss′
                 (_   , _   ) = rr′
                 re = proj₂ (s≈s′ (⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′))
             in Σ (RelTyp i T (ρ ↦ a) T (ρ′ ↦ b))
                  λ rel → ∃₂ λ a′ b′ → rec∙ T ↙ i , (RelExp.⟦t⟧ re) , r , ρ , a ↘ a′
                                     × rec∙ T′ ↙ i , (RelExp.⟦t′⟧ re) , r′ , ρ′ , b ↘ b′
                                     × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
rec-helper {_} {ρ} {ρ′} {T} {T′} {s} {s′} {r} {r′} {i = i} ⊨Γ ρ≈ρ′ (∷-cong ⊨Γ₁ Nrel₁ eq , Trel₁) (⊨Γ₂ , s≈s′) (∷-cong (∷-cong ⊨Γ₃ Nrel₃ _) Trel₃ _ , r≈r′) a≈b
  with ρ≈ρ′₂ ← ⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′ = helper a≈b
  where helper : a ≈ b ∈ Nat →
                 let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                 in Σ (RelTyp i T (ρ ↦ a) T (ρ′ ↦ b))
                      λ rel → ∃₂ λ a′ b′ → rec∙ T ↙ i , re.⟦t⟧ , r , ρ , a ↘ a′
                                         × rec∙ T′ ↙ i , re.⟦t′⟧ , r′ , ρ′ , b ↘ b′
                                         × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper {.ze} {.ze} ze
          with s≈s′ ρ≈ρ′₂
        ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             = record
             { ⟦T⟧   = ⟦T⟧
             ; ⟦T′⟧  = ⟦T′⟧
             ; ↘⟦T⟧  = ↘⟦T⟧
             ; ↘⟦T′⟧ = ↘⟦T′⟧
             ; T≈T′  = T≈T′
             }
             , _ , _
             , ze↘
             , ze↘
             , t≈t′

        helper {su a} {su b} (su a≈b)
          with s≈s′ ρ≈ρ′₂ | helper a≈b
        ...  | _ , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , a′ , b′ , ↘a′ , ↘b′ , a′≈b′ = helper-su
          where ρ≈ρ′₃ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₃ ⟧ρ
                ρ≈ρ′₃ = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

                a≈b₃ : a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
                a≈b₃
                  with record { T≈T′ = N′ } ← Nrel₃ ρ≈ρ′₃ = a≈b

                a′≈b′₃ : (R : RelTyp _ T (ρ ↦ a) T (ρ′ ↦ b)) → a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ R)
                a′≈b′₃ R
                  with record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ } ← R
                  rewrite ⟦⟧-det ↘⟦T⟧₃ ↘⟦T⟧
                        | ⟦⟧-det ↘⟦T′⟧₃ ↘⟦T′⟧ = 𝕌-irrel T≈T′ T≈T′₃ a′≈b′

                helper-su : Σ (RelTyp i T (ρ ↦ su a) T (ρ′ ↦ su b))
                                λ rel → ∃₂ λ a′ b′ → rec∙ T ↙ i , ⟦t⟧ , r , ρ , su a ↘ a′ × rec∙ T′ ↙ i , ⟦t′⟧ , r′ , ρ′ , su b ↘ b′ × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
                helper-su
                  with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                     , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                     = record
                     { ↘⟦T⟧ = ↘⟦T⟧
                     ; ↘⟦T′⟧ = ↘⟦T′⟧
                     ; T≈T′ = T≈T′
                     }
                     , _ , _
                     , su↘ ↘a′ ↘⟦r⟧
                     , su↘ ↘b′ ↘⟦r′⟧
                     , r≈r′

        helper {↑ 0 N c} {↑ 0 N c′} (ne c≈c′)
          with s≈s′ ρ≈ρ′₂
        ...  | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ze ; T≈T′ = T≈T′ze }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = s≈s′ } = helper-ne
          where ρ≈ρ′₁ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₁ ⟧ρ
                ρ≈ρ′₁ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′

                a≈b₁ : {a b : D} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₁ ρ≈ρ′₁))
                a≈b₁ a≈b
                  with record { T≈T′ = N′ } ← Nrel₁ ρ≈ρ′₁ = a≈b

                a≈b₁′ : ↑ 0 N c ≈ ↑ 0 N c′ ∈ El _ (RelTyp.T≈T′ (Nrel₁ ρ≈ρ′₁))
                a≈b₁′
                  with record { T≈T′ = N′ } ← Nrel₁ ρ≈ρ′₁ = ne c≈c′

                helper-ne : Σ (RelTyp i T (ρ ↦ ↑ 0 N c) T (ρ′ ↦ ↑ 0 N c′))
                                λ rel → ∃₂ λ a′ b′ → rec∙ T ↙ i , ⟦t⟧ , r , ρ , ↑ 0 N c ↘ a′
                                                   × rec∙ T′ ↙ i , ⟦t′⟧ , r′ , ρ′ , ↑ 0 N c′ ↘ b′
                                                   × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
                helper-ne
                  with RelExp-refl (∷-cong ⊨Γ₁ Nrel₁ eq) Trel₁ {ρ ↦ ↑ 0 N c} {ρ′ ↦ ↑ 0 N c′} (ρ≈ρ′₁ , a≈b₁′)
                     | Trel₁ {ρ ↦ ↑ 0 N c} {ρ′ ↦ ↑ 0 N c′} (ρ≈ρ′₁ , a≈b₁′)
                ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₁ _ }
                     , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₂ _ }
                     , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
                     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₁))
                     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₂))
                     with refl ← ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                                                   { ⟦T⟧   = _
                                                   ; ⟦T′⟧  = _
                                                   ; ↘⟦T⟧  = ↘⟦T⟧
                                                   ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                   ; T≈T′  = T≈T′
                                                   }
                                                   , _ , _
                                                   , rec∙ ↘⟦T⟧₁
                                                   , rec∙ ↘⟦T′⟧₁
                                                   , El-one-sided T≈T′₁ T≈T′ (Bot⊆El T≈T′₁ bot-helper)
                  where bot-helper : rec (T ↙ i) ⟦t⟧ r ρ c ≈ rec (T′ ↙ i) ⟦t′⟧ r′ ρ′ c′ ∈ Bot
                        bot-helper n
                          with c≈c′ n
                             | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ (ne (Bot-l n))))
                             | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ ze))
                        ...  | cc , c↘ , c′↘
                             | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₃ _ }
                             , record { ⟦t⟧ = ⟦T⟧n ; ⟦t′⟧ = ⟦T′⟧n ; ↘⟦t⟧ = ↘⟦T⟧n ; ↘⟦t′⟧ = ↘⟦T′⟧n ; t≈t′ = T≈T′ns }
                             | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₄ _ }
                             , record { ⟦t⟧ = ⟦T⟧ze₁ ; ⟦t′⟧ = ⟦T′⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; ↘⟦t′⟧ = ↘⟦T′⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                             rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₃))
                             rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₄)) = bot-helper′
                          where ρ≈ρ′₃ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₃ ⟧ρ
                                ρ≈ρ′₃ = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

                                a≈b₃ : l′ 0 N n ∈′ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
                                a≈b₃
                                  with record { T≈T′ = N′ } ← Nrel₃ ρ≈ρ′₃ = ne (Bot-l n)

                                a′≈b′₃ : (R : RelTyp i T (ρ ↦ l′ 0 N n) T (ρ′ ↦ l′ 0 N n)) →
                                         l′ i ⟦T⟧n (1 + n) ≈ l′ i ⟦T′⟧n (1 + n) ∈ El _ (RelTyp.T≈T′ R)
                                a′≈b′₃ R
                                  with record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ } ← R
                                  rewrite ⟦⟧-det ↘⟦T⟧₃ ↘⟦T⟧n = El-one-sided T≈T′ns T≈T′₃ (Bot⊆El T≈T′ns (Bot-l (1 + n)))

                                bot-helper′ : ∃ λ u → Re n - rec (T ↙ i) ⟦t⟧ r ρ c ↘ u
                                                    × Re n - rec (T′ ↙ i) ⟦t′⟧ r′ ρ′ c′ ↘ u
                                bot-helper′
                                  with r≈r′ {_ ↦ _} {_ ↦ _} ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃ (Trel₃ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₃ , a≈b₃)))
                                     | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ (su (ne (Bot-l n)))))
                                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧su ; T≈T′ = T≈T′su }
                                     , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₆ _ }
                                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ⟦t′⟧ = ⟦T′⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; ↘⟦t′⟧ = ↘⟦T′⟧su₁ ; t≈t′ = T≈T′su₁ }
                                     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₆))
                                     rewrite ⟦⟧-det ↘⟦T⟧ze₁ ↘⟦T⟧ze
                                           | ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                                        with 𝕌⊆TopT T≈T′ns (1 + n)
                                           | El⊆Top T≈T′ze₁ (El-one-sided T≈T′ze T≈T′ze₁ s≈s′) n
                                           | El⊆Top T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (2 + n)
                                ...        | _ , Tns↘ , T′ns↘
                                           | _ , Tze↘ , T′ze↘
                                           | _ , Tsu↘ , T′su↘
                                          rewrite ⟦⟧-det ↘⟦T⟧ze ↘⟦T⟧ze₁ = rec _ _ _ cc
                                                                        , Rr n ↘⟦T⟧n Tns↘ ↘⟦T⟧ze₁ Tze↘ ↘⟦r⟧ ↘⟦T⟧su₁ Tsu↘ c↘
                                                                        , Rr n ↘⟦T′⟧n T′ns↘ ↘⟦T′⟧ze₁ T′ze↘ ↘⟦r′⟧ ↘⟦T′⟧su₁ T′su↘ c′↘

rec-cong′ : ∀ {i} →
            N₀ ∷ Γ ⊨ T ≈ T′ ∶[ 1 + i ] Se i →
            Γ ⊨ s ≈ s′ ∶[ i ] T [| ze ∶ N₀ ] →
            (T ↙ i) ∷ N₀ ∷ Γ ⊨ r ≈ r′ ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
            Γ ⊨ t ≈ t′ ∶[ 0 ] N →
            ---------------------------------------------------
            Γ ⊨ rec (T ↙ i) s r t ≈ rec (T′ ↙ i) s′ r′ t′ ∶[ i ] T [| t ∶ N₀ ]
rec-cong′ {_} {T} {T′} {s} {s′} {r} {r′} {t} {t′} {i = i} TT′@(_ , _) ss′@(⊨Γ₂ , s≈s′) rr′@(_ , _) tt′@(⊨Γ₄ , t≈t′) = ⊨Γ₄ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ →
             -----------------------------------------------------------------------------
             Σ (RelTyp _ (T [| t ∶ N₀ ]) ρ (T [| t ∶ N₀ ]) ρ′)
             λ rel → RelExp (rec (T ↙ i) s r t) ρ (rec (T′ ↙ i) s′ r′ t′) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with RelExp-refl ⊨Γ₄ t≈t′ ρ≈ρ′
         | t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N refl }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         | record { T≈T′ = N refl }
         , record { ↘⟦t⟧ = ↘⟦t⟧₁ ; ↘⟦t′⟧ = ↘⟦t′⟧₁ ; t≈t′ = t≈t′₁ }
       with rec-helper ⊨Γ₄ ρ≈ρ′ TT′ ss′ rr′ t≈t′
          | rec-helper ⊨Γ₄ ρ≈ρ′ TT′ ss′ rr′ t≈t′₁
    ...   | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
          , res , res′ , ↘res , ↘res′ , res≈res′
          | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          , res₁ , res′₁ , ↘res₁ , ↘res′₁ , res≈res′₁
        rewrite ⟦⟧-det ↘⟦t⟧₁ ↘⟦t⟧
              | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                                  { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧) ↘⟦T⟧
                                  ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t′⟧) ↘⟦T′⟧
                                  ; T≈T′ = T≈T′
                                  }
                                , record
                                  { ↘⟦t⟧ = ⟦rec⟧ s≈s′.↘⟦t⟧ ↘⟦t⟧ ↘res₁
                                  ; ↘⟦t′⟧ = ⟦rec⟧ s≈s′.↘⟦t′⟧ ↘⟦t′⟧₁ ↘res′₁
                                  ; t≈t′ = El-one-sided T≈T′₁ T≈T′ res≈res′₁
                                  }
      where
        module s≈s′ = RelExp (proj₂ (s≈s′ (⟦⟧ρ-one-sided ⊨Γ₄ ⊨Γ₂ ρ≈ρ′)))

rec-β-ze′   : ∀ {i} →
              N₀ ∷ Γ ⊨ T ∶[ 1 + i ] Se i →
              Γ ⊨ s ∶[ i ] T [| ze ∶ N₀ ] →
              (T ↙ i) ∷ N₀ ∷ Γ ⊨ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
              ---------------------------------------------
              Γ ⊨ rec (T ↙ i) s r ze ≈ s ∶[ i ] T [| ze ∶ N₀ ]
rec-β-ze′ {_} {T} {s} {r} {i = i} ⊨T ⊨s@(⊨Γ , s≈s′) ⊨r = ⊨Γ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             -------------------------------------------------------------
             Σ (RelTyp _ (T [| ze ∶ N₀ ]) ρ (T [| ze ∶ N₀ ]) ρ′)
             λ rel → RelExp (rec (T ↙ i) s r ze) ρ s ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with Trel , srel ← s≈s′ ρ≈ρ′ = Trel
                                   , record
                                     { RelExp srel
                                     ; ↘⟦t⟧ = ⟦rec⟧ (RelExp.↘⟦t⟧ srel) ⟦ze⟧ ze↘
                                     }

rec-β-su′ : ∀ {i} →
            N₀ ∷ Γ ⊨ T ∶[ 1 + i ] Se i →
            Γ ⊨ s ∶[ i ] T [| ze ∶ N₀ ] →
            (T ↙ i) ∷ N₀ ∷ Γ ⊨ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
            Γ ⊨ t ∶[ 0 ] N →
            -----------------------------------------------------------------
            Γ ⊨ rec (T ↙ i) s r (su t) ≈ r [ (I , t ∶ N₀) , rec (T ↙ i) s r t ∶ T ↙ i ] ∶[ i ] T [| su t ∶ N₀ ]
rec-β-su′ {_} {T} {s} {r} {t} {i = i} ⊨T@(_ , _) ⊨s@(⊨Γ₂ , s≈s′) ⊨r@(_ , _) (⊨Γ₄ , t≈t′) = ⊨Γ₄ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ →
             -----------------------------------------------------------------------------------------------
             Σ (RelTyp _ (T [| su t ∶ N₀ ]) ρ (T [| su t ∶ N₀ ]) ρ′)
             λ rel → RelExp (rec (T ↙ i) s r (su t)) ρ (r [ (I , t ∶ N₀) , rec (T ↙ i) s r t ∶ T ↙ i ]) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N refl }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
        with rec-helper ⊨Γ₄ ρ≈ρ′ ⊨T ⊨s ⊨r (su t≈t′)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
           , res , res′ , ↘res , su↘ ↘res′ ↘r , res≈res′ = record
                                              { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ (⟦su⟧ ↘⟦t⟧)) ↘⟦T⟧
                                              ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ (⟦su⟧ ↘⟦t′⟧)) ↘⟦T′⟧
                                              ; T≈T′ = T≈T′
                                              }
                                            , record
                                              { ↘⟦t⟧ = ⟦rec⟧ s≈s′.↘⟦t⟧ (⟦su⟧ ↘⟦t⟧) ↘res
                                              ; ↘⟦t′⟧ = ⟦[]⟧ (⟦,⟧ (⟦,⟧ ⟦I⟧ ↘⟦t′⟧) (⟦rec⟧ s≈s′.↘⟦t′⟧ ↘⟦t′⟧ ↘res′)) ↘r
                                              ; t≈t′ = res≈res′
                                              }
      where
        module s≈s′ = RelExp (proj₂ (s≈s′ (⟦⟧ρ-one-sided ⊨Γ₄ ⊨Γ₂ ρ≈ρ′)))


N-[]′ : Γ ⊨s σ ∶ Δ →
        -----------------------
        Γ ⊨ N [ σ ] ≈ N ∶[ 1 ] Se 0
N-[]′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 --------------------------------------------------
                 Σ (RelTyp _ (Se 0) ρ (Se 0) ρ′)
                 λ rel → RelExp (N [ σ ]) ρ N ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
                        { ↘⟦T⟧  = ⟦Se⟧ _
                        ; ↘⟦T′⟧ = ⟦Se⟧ _
                        ; T≈T′  = U′
                        }
                    , record
                        { ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦N⟧
                        ; ↘⟦t′⟧ = ⟦N⟧
                        ; t≈t′  = N refl
                        }
          where module σ = RelSubst (⊨σ ρ≈ρ′)


ze-[]′ : Γ ⊨s σ ∶ Δ →
         ----------------------
         Γ ⊨ ze [ σ ] ≈ ze ∶[ 0 ] N
ze-[]′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------------------------
                 Σ (RelTyp 0 N ρ N ρ′)
                 λ rel → RelExp (ze [ σ ]) ρ ze ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
                        { ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N refl
                        }
                    , record
                        { ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦ze⟧
                        ; ↘⟦t′⟧ = ⟦ze⟧
                        ; t≈t′  = ze
                        }
          where module σ = RelSubst (⊨σ ρ≈ρ′)


su-[]′ : Γ ⊨s σ ∶ Δ →
         Δ ⊨ t ∶[ 0 ] N →
         ----------------------------------
         Γ ⊨ su t [ σ ] ≈ su (t [ σ ]) ∶[ 0 ] N
su-[]′ {_} {σ} {_} {t} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------------------------------------
                 Σ (RelTyp 0 N ρ N ρ′)
                 λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ N ρ N ρ′)
                       λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with ⊨t (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ⟦N⟧ ; T≈T′ = N refl }
                     , re = record
                              { ↘⟦T⟧  = ⟦N⟧
                              ; ↘⟦T′⟧ = ⟦N⟧
                              ; T≈T′  = N refl
                              }
                          , record
                              { ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦su⟧ re.↘⟦t⟧)
                              ; ↘⟦t′⟧ = ⟦su⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                              ; t≈t′  = su re.t≈t′
                              }
                  where module re = RelExp re

-- We need one more separate helper for rec-[]′ other than rec-helper,
-- because rec-helper does not allow us to use two inequivalent environments:
-- ρ and (σ≈σ′ ρ≈ρ).⟦σ⟧
rec-[]′-helper : ∀ {res i} →
                 (⊨Γ : ⊨ Γ) →
                 (⊨σ : Γ ⊨s σ ∶ Δ) →
                 (ρ≈ρ : ρ ∈′ ⟦ ⊨Γ ⟧ρ) →
                 (⊨T : (N₀ ∷ Δ) ⊨ T ∶[ 1 + i ] Se i) →
                 (⊨s : Δ ⊨ s ∶[ i ] T [| ze ∶ N₀ ]) →
                 (⊨r : (T ↙ i) ∷ N₀ ∷ Δ ⊨ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ]) →
                 a ∈′ Nat →
                 let (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) = ⊨σ
                     rs = σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
                     (_   , _)    = ⊨T
                     (⊨Δ₃ , s≈s′) = ⊨s
                     (_   , _)    = ⊨r
                     re = proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ (RelSubst.σ≈δ rs))) in
                 rec∙ T ↙ i , (RelExp.⟦t⟧ re) , r , (RelSubst.⟦σ⟧ rs) , a ↘ res →
                 -----------------------------------------------------------------------------------------
                 ∃ λ res′ → rec∙ (T [ q N₀ σ ] ↙ i) , RelExp.⟦t⟧ re , (r [ q (T ↙ i) (q N₀ σ) ]) , ρ , a ↘ res′
                          × Σ (RelTyp i T (RelSubst.⟦σ⟧ rs ↦ a) T (RelSubst.⟦σ⟧ rs ↦ a))
                            λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel)
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {ze} {i = i} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∷-cong ⊨Δ₂ Nrel₂ _ , _) (⊨Δ₃ , s≈s′) ⊨r@(_ , _) ze ze↘
  with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧
      with s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)
...      | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { t≈t′ = t≈t′ } = _ , ze↘
                                  , record
                                   { ↘⟦T⟧ = ↘⟦T⟧
                                   ; ↘⟦T′⟧ = ↘⟦T′⟧
                                   ; T≈T′ = T≈T′
                                   }
                                 , El-refl T≈T′ t≈t′
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {su a} {res} {i} ⊨Γ ⊨σ@(⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ ⊨T@(_ , _) ⊨s@(⊨Δ₃ , s≈s′) ⊨r@(∷-cong (∷-cong ⊨Δ₄ Nrel₄ _) Trel₄ _ , r≈r′) (su a≈a) (su↘ {b′ = b} ↘res ↘r)
  with rec-[]′-helper ⊨Γ ⊨σ ρ≈ρ ⊨T ⊨s ⊨r a≈a ↘res
...  | b′ , ↘b′ , record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } , b≈b′
    with record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
      rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ⟦σ⟧≈⟦σ⟧ : ⟦σ⟧ ≈ ⟦σ⟧ ∈ ⟦ ⊨Δ₄ ⟧ρ
    ⟦σ⟧≈⟦σ⟧ = ⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ

    a≈a₄ : a ∈′ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧))
    a≈a₄
      with record { T≈T′ = N refl } ← Nrel₄ ⟦σ⟧≈⟦σ⟧ = a≈a

    b≈b′₄ : (R : RelTyp _ T (⟦σ⟧ ↦ a) T (⟦σ⟧ ↦ a)) →  b ≈ b′ ∈ El _ (RelTyp.T≈T′ R)
    b≈b′₄ record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
      rewrite ⟦⟧-det ↘⟦T⟧₄ ↘⟦T⟧
            | ⟦⟧-det ↘⟦T′⟧₄ ↘⟦T′⟧ = 𝕌-irrel T≈T′ T≈T′₄ b≈b′

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q N₀ σ ] ↙ i) , re.⟦t⟧ , (r [ q (T ↙ i) (q N₀ σ) ]) , ρ , su a ↘ res′
                      × Σ (RelTyp i T (⟦σ⟧ ↦ su a) T (⟦σ⟧ ↦ su a))
                        λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel)
    helper
      with r≈r′ {_ ↦ _} {_ ↦ _} ((⟦σ⟧≈⟦σ⟧ , a≈a₄) , b≈b′₄ (Trel₄ (⟦σ⟧≈⟦σ⟧ , a≈a₄)))
    ... | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧₄ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
        , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
        rewrite ⟦⟧-det ↘r ↘⟦r⟧ = _ , su↘ ↘b′ (⟦[]⟧ (⟦q⟧ (⟦q⟧ ↘⟦σ⟧)) ↘⟦r′⟧)
                               , record
                                 { ↘⟦T⟧ = ↘⟦T⟧₄
                                 ; ↘⟦T′⟧ = ↘⟦T′⟧₄
                                 ; T≈T′ = T≈T′₄
                                 }
                               , r≈r′
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {↑ 0 N c} {↑ _ T′ (rec _ _ _ _ _)} {i} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∷-cong ⊨Δ₂ Nrel₂ _ , Trel₂) (⊨Δ₃ , s≈s′) (∷-cong (∷-cong ⊨Δ₄ Nrel₄ _) Trel₄ _ , r≈r′) (ne c≈c) (rec∙ T↘)
  with record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ⟦σ⟧≈⟦σ⟧₂ : drop (⟦σ⟧ ↦ ↑ 0 N c) ∈′ ⟦ ⊨Δ₂ ⟧ρ
    ⟦σ⟧≈⟦σ⟧₂ = ⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ

    ↑Nc≈↑Nc : ↑ 0 N c ∈′ El _ (RelTyp.T≈T′ (Nrel₂ ⟦σ⟧≈⟦σ⟧₂))
    ↑Nc≈↑Nc
      with record { T≈T′ = N refl } ← Nrel₂ ⟦σ⟧≈⟦σ⟧₂ = ne c≈c

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q N₀ σ ] ↙ i) , re.⟦t⟧ , (r [ q (T ↙ i) (q N₀ σ) ]) , ρ , ↑ 0 N c ↘ res′
                      × Σ (RelTyp i T (⟦σ⟧ ↦ ↑ 0 N c) T (⟦σ⟧ ↦ ↑ 0 N c))
                          (λ rel → ↑ _ T′ (rec (T ↙ i) re.⟦t⟧ r ⟦σ⟧ c) ≈ res′ ∈ El _ (RelTyp.T≈T′ rel))
    helper
      with Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , ↑Nc≈↑Nc)
    ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₁ _ }
         , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₁))
          with refl ← ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧
             | refl ← ⟦⟧-det ↘⟦T⟧ T↘                = _ , rec∙ (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧) T↘)
                                                    , record
                                                      { ↘⟦T⟧ = ↘⟦T⟧
                                                      ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                      ; T≈T′ = T≈T′
                                                      }
                                                    , Bot⊆El T≈T′ bot-helper
      where
        bot-helper : rec (T ↙ i) re.⟦t⟧ r ⟦σ⟧ c ≈ rec (T [ q N₀ σ ] ↙ i) re.⟦t⟧ (r [ q (T ↙ i) (q N₀ σ) ]) ρ c ∈ Bot
        bot-helper n
          with c≈c n
        ...  | _ , ↘c , _ = bot-helper′
          where
            ⟦σ⟧≈⟦σ⟧₂′ : ⟦σ⟧ ≈ ⟦σ⟧ ∈ ⟦ ⊨Δ₂ ⟧ρ
            ⟦σ⟧≈⟦σ⟧₂′ = ⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ

            a≈b₂ : ∀ {a b} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₂ ⟦σ⟧≈⟦σ⟧₂′))
            a≈b₂ {a} {b} a≈b
              with record { T≈T′ = N refl } ← Nrel₂ ⟦σ⟧≈⟦σ⟧₂′ = a≈b

            bot-helper′ : ∃ λ u → Re n - rec (T ↙ i) re.⟦t⟧ r ⟦σ⟧ c ↘ u
                                × Re n - rec (T [ q N₀ σ ] ↙ i) re.⟦t⟧ (r [ q (T ↙ i) (q N₀ σ) ]) ρ c ↘ u
            bot-helper′
              with Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ (ne (Bot-l n))))
                 | s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)
                 | Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ ze))
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₂ _ }
                 , record { ⟦t⟧ = ⟦T⟧n ; ↘⟦t⟧ = ↘⟦T⟧n ; t≈t′ = T≈T′ns }
                 | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; t≈t′ = s≈s′ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₃ _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                 rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₂))
                       | 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₃))
                       | ⟦⟧-det ↘⟦T⟧ze₁ ↘⟦T⟧ze
                       with 𝕌⊆TopT T≈T′ns (1 + n)
                          | El⊆Top T≈T′ze₁ (El-one-sided T≈T′ze T≈T′ze₁ s≈s′) n
            ...           | _ , Tns↘ , T′ns↘
                          | _ , Tze↘ , T′ze↘
                         rewrite ⟦⟧-det ↘⟦T⟧ze ↘⟦T⟧ze₁ = bot-helper″
              where
                ⟦σ⟧≈⟦σ⟧₄ : ⟦σ⟧ ∈′ ⟦ ⊨Δ₄ ⟧ρ
                ⟦σ⟧≈⟦σ⟧₄ = ⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ

                a≈b₄ : l′ 0 N n ∈′ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧₄))
                a≈b₄
                  with record { T≈T′ = N refl } ← Nrel₄ ⟦σ⟧≈⟦σ⟧₄ = ne (Bot-l n)

                a′≈b′₄ : (R : RelTyp i T (⟦σ⟧ ↦ l′ 0 N n) T (⟦σ⟧ ↦ l′ 0 N n)) → l′ i ⟦T⟧n (1 + n) ∈′ El _ (RelTyp.T≈T′ R)
                a′≈b′₄ R
                  with record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ } ← R
                    rewrite ⟦⟧-det ↘⟦T′⟧₄ ↘⟦T⟧₄
                          | ⟦⟧-det ↘⟦T⟧₄ ↘⟦T⟧n = Bot⊆El T≈T′₄ (Bot-l (1 + n))

                bot-helper″ : ∃ λ u → Re n - rec (T ↙ i) ⟦s⟧ r ⟦σ⟧ c ↘ u
                                × Re n - rec (T [ q N₀ σ ] ↙ i) ⟦s⟧ (r [ q (T ↙ i) (q N₀ σ) ]) ρ c ↘ u
                bot-helper″
                  with r≈r′ {_ ↦ _} {_ ↦ _} ((⟦σ⟧≈⟦σ⟧₄ , a≈b₄) , a′≈b′₄ (Trel₄ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₄ , a≈b₄)))
                     | Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ (su (ne (Bot-l n)))))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; t≈t′ = r≈r′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq₄ _ }
                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; t≈t′ = T≈T′su₁ }
                    rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq₄))
                          | ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                          with El⊆Top T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (2 + n)
                ...          | _ , Tsu↘ , T′su↘ = _
                                                , Rr n ↘⟦T⟧n Tns↘ ↘⟦T⟧ze₁ Tze↘ ↘⟦r⟧ ↘⟦T⟧su₁ Tsu↘ ↘c
                                                , Rr n
                                                     (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧) ↘⟦T⟧n)
                                                     Tns↘
                                                     (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧) ↘⟦T⟧ze₁)
                                                     Tze↘
                                                     (⟦[]⟧ (⟦q⟧ (⟦q⟧ ↘⟦σ⟧)) ↘⟦r⟧) (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧) ↘⟦T⟧su₁)
                                                     Tsu↘
                                                     ↘c

rec-[]′ : ∀ {i} →
          Γ ⊨s σ ∶ Δ →
          N₀ ∷ Δ ⊨ T ∶[ 1 + i ] Se i →
          Δ ⊨ s ∶[ i ] T [| ze ∶ N₀ ] →
          (T ↙ i) ∷ N₀ ∷ Δ ⊨ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
          Δ ⊨ t ∶[ 0 ] N →
          -------------------------------------------------------------------------------------------------
          Γ ⊨ rec (T ↙ i) s r t [ σ ] ≈ rec (T [ q N₀ σ ] ↙ i) (s [ σ ]) (r [ q (T ↙ i) (q N₀ σ) ]) (t [ σ ]) ∶[ i ] T [ σ , t [ σ ] ∶ N₀ ]
rec-[]′ {_} {σ} {_} {T} {s} {r} {t} {i = i} ⊨σ@(⊨Γ , ⊨Δ , σ≈σ′) ⊨T@(_ , _) ⊨s@(⊨Δ₂ , s≈s′) ⊨r@(∷-cong (∷-cong ⊨Δ₃ Nrel₃ _) Trel₃ _ , r≈r′) (⊨Δ₄ , t≈t′) = ⊨Γ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             -----------------------------------------------------------------------------------------------------------------------
             Σ (RelTyp i (T [ σ , t [ σ ] ∶ N₀ ]) ρ (T [ σ , t [ σ ] ∶ N₀ ]) ρ′)
             λ rel → RelExp (rec (T ↙ i) s r t [ σ ]) ρ (rec (T [ q N₀ σ ] ↙ i) (s [ σ ]) (r [ q (T ↙ i) (q N₀ σ) ]) (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ ρ≈ρ′
        with t≈t′ (⊨-irrel ⊨Δ ⊨Δ₄ σ≈δ)
    ...    | record { T≈T′ = N refl }
           , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
          with rec-helper ⊨Δ σ≈δ ⊨T ⊨s ⊨r t≈t′
             | ⟦⟧ρ-refl ⊨Γ ⊨Γ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
    ...      | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , res , res′ , ↘res , ↘res′ , res≈res′
             | ρ′≈ρ′
            with record { ↘⟦σ⟧ = ↘⟦δ⟧₁ ; σ≈δ = δ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ ρ′≈ρ′)
               | rec-[]′-helper′ ← rec-[]′-helper {res = res′} ⊨Γ ⊨σ ρ′≈ρ′ ⊨T ⊨s ⊨r (El-refl (N refl) (El-sym′ (N refl) t≈t′))
              with s≈s′ (⟦⟧ρ-one-sided ⊨Δ ⊨Δ₂ σ≈δ)
                 | s≈s′ (⟦⟧ρ-one-sided ⊨Δ ⊨Δ₂ δ≈δ)
    ...          | _ , record { ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ }
                 | _ , record { ↘⟦t⟧ = ↘⟦s′⟧₁ ; ↘⟦t′⟧ = ↘⟦s⟧₁ ; t≈t′ = s≈s }
                rewrite ⟦⟧s-det ↘⟦δ⟧₁ ↘⟦δ⟧
                      | ⟦⟧-det ↘⟦s′⟧₁ ↘⟦s′⟧
                  with rec-[]′-helper′ ↘res′
    ...              | _
                     , ↘res′₁
                     , record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ } , res′≈res′₁
                    rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T′⟧
                          | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧ = record
                                                 { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ (⟦[]⟧ ↘⟦σ⟧ ↘⟦t⟧)) ↘⟦T⟧
                                                 ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦δ⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)) ↘⟦T′⟧
                                                 ; T≈T′ = T≈T′
                                                 }
                                               , record
                                                 { ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦rec⟧ ↘⟦s⟧ ↘⟦t⟧ ↘res)
                                                 ; ↘⟦t′⟧ = ⟦rec⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦s′⟧) (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧) ↘res′₁
                                                 ; t≈t′ = El-trans′ T≈T′ res≈res′ (El-one-sided′ T≈T′₁ T≈T′ res′≈res′₁)
                                                 }
