{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Nat
module MLTT.Completeness.Nat (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import MLTT.Completeness.LogRel

open import MLTT.Semantics.Properties.PER fext
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Realizability fext


N-≈′ : ∀ {i} →
       ⊨ Γ →
       ----------------
       Γ ⊨ N ≈ N ∶ Se i
N-≈′ {_} {i} ⊨Γ = ⊨Γ , 1 + i , λ ρ≈ρ′ → record
                             { ↘⟦T⟧  = ⟦Se⟧ _
                             ; ↘⟦T′⟧ = ⟦Se⟧ _
                             ; T≈T′  = U′ ≤-refl
                             }
                           , record
                             { ↘⟦t⟧  = ⟦N⟧
                             ; ↘⟦t′⟧ = ⟦N⟧
                             ; t≈t′  = PERDef.N
                             }

ze-≈′ : ⊨ Γ →
        ----------------
        Γ ⊨ ze ≈ ze ∶ N
ze-≈′ ⊨Γ = ⊨Γ , 0 , λ ρ≈ρ′ → record
                             { ↘⟦T⟧  = ⟦N⟧
                             ; ↘⟦T′⟧ = ⟦N⟧
                             ; T≈T′  = N
                             }
                           , record
                             { ↘⟦t⟧  = ⟦ze⟧
                             ; ↘⟦t′⟧ = ⟦ze⟧
                             ; t≈t′  = ze
                             }

su-cong′ : Γ ⊨ t ≈ t′ ∶ N →
           ----------------
           Γ ⊨ su t ≈ su t′ ∶ N
su-cong′ {_} {t} {t′} (⊨Γ , n , t≈t′) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ------------------------------------------------------------
             Σ (RelTyp n N ρ N ρ′)
             λ rel → RelExp (su t) ρ (su t′) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                        { ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N
                        }
                      , record
                        { ↘⟦t⟧  = ⟦su⟧ ↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦su⟧ ↘⟦t′⟧
                        ; t≈t′  = su t≈t′
                        }


-- A lemma to handle asymmetry appears in several Nat judgements.
-- This follows the trick of []-cong′ in MLTT.Completeness.Terms.
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
             (TT′ : (N ∷ Γ) ⊨ T ≈ T′ ∶ Se i) →
             (ss′ : Γ ⊨ s ≈ s′ ∶ (T [| ze ])) →
             (rr′ : (T ∷ N ∷ Γ) ⊨ r ≈ r′ ∶ (T [ (wk ∘ wk) , su (v 1) ])) →
             a ≈ b ∈ Nat →
             -----------------------------------------------------
             let (_   , n₁ , _   ) = TT′
                 (⊨Γ₂ , n₂ , s≈s′) = ss′
                 (_   , n₃ , _   ) = rr′
                 re = proj₂ (s≈s′ (⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′))
             in Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) T (ρ ↦ a) T (ρ′ ↦ b))
                λ rel → ∃₂ λ a′ b′ → rec∙ T , (RelExp.⟦t⟧ re) , r , ρ , a ↘ a′
                                   × rec∙ T′ , (RelExp.⟦t′⟧ re) , r′ , ρ′ , b ↘ b′
                                   × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
rec-helper {_} {ρ} {ρ′} {T} {T′} {s} {s′} {r} {r′} {i = i} ⊨Γ ρ≈ρ′ (∷-cong ⊨Γ₁ Nrel₁ , n₁ , Trel₁) (⊨Γ₂ , n₂ , s≈s′) (∷-cong (∷-cong ⊨Γ₃ Nrel₃) Trel₃ , n₃ , r≈r′) a≈b
  with ρ≈ρ′₂ ← ⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′ = helper a≈b
  where
    helper : a ≈ b ∈ Nat →
             ----------------------------------------------------------------
             let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
             in Σ (RelTyp _ T (ρ ↦ a) T (ρ′ ↦ b))
                λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , a ↘ a′
                                     × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , b ↘ b′
                                     × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
    helper ze
      with s≈s′ ρ≈ρ′₂
    ...  | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧₁ ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
         , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; t≈t′ = s≈s′ } = record
                 { ↘⟦T⟧  = ↘⟦T⟧₁
                 ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                 ; T≈T′ = 𝕌-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₃)) T≈T′₁
                 }
               , ⟦s⟧ , ⟦s′⟧ , ze↘ , ze↘ , El-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₃)) T≈T′₁ s≈s′
    helper {su a} {su b} (su a≈b)
      with helper a≈b
    ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , a′ , b′ , ↘a′ , ↘b′ , a′≈b′ = helper-su
      where
        ρ≈ρ′₃ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₃ ⟧ρ
        ρ≈ρ′₃ = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

        a≈b₃ : a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
        a≈b₃
          with record { T≈T′ = N } ← Nrel₃ ρ≈ρ′₃ = a≈b

        a′≈b′₃ : (R : RelTyp _ T (ρ ↦ a) T (ρ′ ↦ b)) → a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ R)
        a′≈b′₃ R
          with record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ } ← R
            rewrite ⟦⟧-det ↘⟦T⟧₃ ↘⟦T⟧
                  | ⟦⟧-det ↘⟦T′⟧₃ ↘⟦T′⟧ = 𝕌-irrel T≈T′ T≈T′₃ a′≈b′

        module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))

        helper-su : Σ (RelTyp _ T (ρ ↦ su a) T (ρ′ ↦ su b))
                    λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , su a ↘ a′
                                         × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , su b ↘ b′
                                         × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-su
          with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
        ... | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ } = record
                            { ↘⟦T⟧ = ↘⟦T⟧
                            ; ↘⟦T′⟧ = ↘⟦T′⟧
                            ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′
                            }
                          , _ , _ , su↘ ↘a′ ↘⟦r⟧ , su↘ ↘b′ ↘⟦r′⟧ , El-cumu (m≤n⊔m _ _) T≈T′ r≈r′
    helper (ne {c} {c′} c≈c′) = helper-ne
      where
        ρ≈ρ′₁ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₁ ⟧ρ
        ρ≈ρ′₁ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′

        a≈b₁ : {a b : D} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₁ ρ≈ρ′₁))
        a≈b₁ a≈b
          with record { T≈T′ = N } ← Nrel₁ ρ≈ρ′₁ = a≈b

        a≈b₁′ : ↑ N c ≈ ↑ N c′ ∈ El _ (RelTyp.T≈T′ (Nrel₁ ρ≈ρ′₁))
        a≈b₁′
          with record { T≈T′ = N } ← Nrel₁ ρ≈ρ′₁ = ne c≈c′

        helper-ne : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp _ T (ρ ↦ ↑ N c) T (ρ′ ↦ ↑ N c′))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , ↑ N c ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , ↑ N c′ ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-ne
          with RelExp-refl (∷-cong ⊨Γ₁ Nrel₁) Trel₁ {ρ ↦ ↑ N c} {ρ′ ↦ ↑ N c′} (ρ≈ρ′₁ , a≈b₁′)
             | Trel₁ {ρ ↦ ↑ N c} {ρ′ ↦ ↑ N c′} (ρ≈ρ′₁ , a≈b₁′)
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
             , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
             | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁₁ _ }
             , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
            with T≈T′ ← 𝕌-cumu (<⇒≤ i<n₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁) T≈T′)
               | T≈T′₁ ← 𝕌-cumu (<⇒≤ i<n₁₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁₁) T≈T′₁)
               with refl ← ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                          { ↘⟦T⟧ = ↘⟦T⟧
                          ; ↘⟦T′⟧ = ↘⟦T′⟧
                          ; T≈T′ = 𝕌-cumu (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₃)) T≈T′
                          }
                        , _ , _ , rec∙ ↘⟦T⟧₁ , rec∙ ↘⟦T′⟧₁ , El-cumu (≤-trans (m≤m⊔n n₁ n₂) (m≤m⊔n _ n₃)) T≈T′ (El-one-sided T≈T′₁ T≈T′ (Bot⊆El T≈T′₁ bot-helper))
          where
            bot-helper : rec T (RelExp.⟦t⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r ρ c ≈ rec T′ (RelExp.⟦t′⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r′ ρ′ c′ ∈ Bot
            bot-helper n
              with c≈c′ n
                 | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ (ne (Bot-l n))))
                 | s≈s′ ρ≈ρ′₂
                 | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ ze))
            ...  | cc , c↘ , c′↘
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ns _ }
                 , record { ⟦t⟧ = ⟦T⟧n ; ⟦t′⟧ = ⟦T′⟧n ; ↘⟦t⟧ = ↘⟦T⟧n ; ↘⟦t′⟧ = ↘⟦T′⟧n ; t≈t′ = T≈T′ns }
                 | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; t≈t′ = s≈s′ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ze _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ⟦t′⟧ = ⟦T′⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; ↘⟦t′⟧ = ↘⟦T′⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                with T≈T′ns ← 𝕌-cumu (<⇒≤ i<n₁ns) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ns) T≈T′ns)
                   | T≈T′ze₁ ← 𝕌-cumu (<⇒≤ i<n₁ze) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ze) T≈T′ze₁) = bot-helper′
              where
                ρ≈ρ′₃ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₃ ⟧ρ
                ρ≈ρ′₃ = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

                a≈b₃ : l′ N n ∈′ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
                a≈b₃
                  with record { T≈T′ = N } ← Nrel₃ ρ≈ρ′₃ = ne (Bot-l n)

                a′≈b′₃ : (R : RelTyp _ T (ρ ↦ l′ N n) T (ρ′ ↦ l′ N n)) → l′ ⟦T⟧n (1 + n) ≈ l′ ⟦T′⟧n (1 + n) ∈ El _ (RelTyp.T≈T′ R)
                a′≈b′₃ R
                  with record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ } ← R
                  rewrite ⟦⟧-det ↘⟦T⟧₃ ↘⟦T⟧n = El-one-sided T≈T′ns T≈T′₃ (Bot⊆El T≈T′ns (Bot-l (1 + n)))

                bot-helper′ : ∃ λ u → Re n - rec T ⟦s⟧ r ρ c ↘ u
                                    × Re n - rec T′ ⟦s′⟧ r′ ρ′ c′ ↘ u
                bot-helper′
                  with r≈r′ {_ ↦ _} {_ ↦ _} ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃ (Trel₃ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₃ , a≈b₃)))
                     | Trel₁ {_ ↦ _} {_ ↦ _} (ρ≈ρ′₁ , (a≈b₁ (su (ne (Bot-l n)))))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁su _ }
                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ⟦t′⟧ = ⟦T′⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; ↘⟦t′⟧ = ↘⟦T′⟧su₁ ; t≈t′ = T≈T′su₁ }
                    with T≈T′su₁ ← 𝕌-cumu (<⇒≤ i<n₁su) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁su) T≈T′su₁)
                      rewrite ⟦⟧-det ↘⟦T⟧ze₁ ↘⟦T⟧ze
                            | ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                        with 𝕌⊆TopT T≈T′ns (1 + n)
                           | El⊆Top T≈T′ze₁ (El-one-sided T≈T′ze T≈T′ze₁ s≈s′) n
                           | El⊆Top T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (2 + n)
                ...        | _ , Tns↘ , T′ns↘
                           | _ , Tze↘ , T′ze↘
                           | _ , Tsu↘ , T′su↘
                          rewrite ⟦⟧-det ↘⟦T⟧ze ↘⟦T⟧ze₁ = rec _ _ _ cc , Rr n ↘⟦T⟧n Tns↘ ↘⟦T⟧ze₁ Tze↘ ↘⟦r⟧ ↘⟦T⟧su₁ Tsu↘ c↘ , Rr n ↘⟦T′⟧n T′ns↘ ↘⟦T′⟧ze₁ T′ze↘ ↘⟦r′⟧ ↘⟦T′⟧su₁ T′su↘ c′↘

rec-cong′ : ∀ {i} →
            N ∷ Γ ⊨ T ≈ T′ ∶ Se i →
            Γ ⊨ s ≈ s′ ∶ T [| ze ] →
            T ∷ N ∷ Γ ⊨ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
            Γ ⊨ t ≈ t′ ∶ N →
            ---------------------------------------------------
            Γ ⊨ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
rec-cong′ {_} {T} {T′} {s} {s′} {r} {r′} {t} {t′} TT′@(_ , _ , _) ss′@(⊨Γ₂ , _ , s≈s′) rr′@(_ , _ , _) tt′@(⊨Γ₄ , _ , t≈t′) = ⊨Γ₄ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ →
             -----------------------------------------------------------------------------
             Σ (RelTyp _ (T [| t ]) ρ (T [| t ]) ρ′)
             λ rel → RelExp (rec T s r t) ρ (rec T′ s′ r′ t′) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with RelExp-refl ⊨Γ₄ t≈t′ ρ≈ρ′
         | t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         | record { T≈T′ = N }
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
              N ∷ Γ ⊨ T ∶ Se i →
              Γ ⊨ s ∶ T [| ze ] →
              T ∷ N ∷ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              ---------------------------------------------
              Γ ⊨ rec T s r ze ≈ s ∶ T [| ze ]
rec-β-ze′ {_} {T} {s} {r} ⊨T ⊨s@(⊨Γ , _ , s≈s′) ⊨r = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             -------------------------------------------------------------
             Σ (RelTyp _ (T [| ze ]) ρ (T [| ze ]) ρ′)
             λ rel → RelExp (rec T s r ze) ρ s ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with Trel , srel ← s≈s′ ρ≈ρ′ = Trel
                                   , record
                                     { RelExp srel
                                     ; ↘⟦t⟧ = ⟦rec⟧ (RelExp.↘⟦t⟧ srel) ⟦ze⟧ ze↘
                                     }

rec-β-su′ : ∀ {i} →
            N ∷ Γ ⊨ T ∶ Se i →
            Γ ⊨ s ∶ T [| ze ] →
            T ∷ N ∷ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
            Γ ⊨ t ∶ N →
            -----------------------------------------------------------------
            Γ ⊨ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
rec-β-su′ {_} {T} {s} {r} {t} ⊨T@(_ , _ , _) ⊨s@(⊨Γ₂ , _ , s≈s′) ⊨r@(_ , _ , _) (⊨Γ₄ , _ , t≈t′) = ⊨Γ₄ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ →
             -----------------------------------------------------------------------------------------------
             Σ (RelTyp _ (T [| su t ]) ρ (T [| su t ]) ρ′)
             λ rel → RelExp (rec T s r (su t)) ρ (r [ (I , t) , rec T s r t ]) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper ρ≈ρ′
      with t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N }
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


N-[]′ : ∀ i →
        Γ ⊨s σ ∶ Δ →
        -----------------------
        Γ ⊨ N [ σ ] ≈ N ∶ Se i
N-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 --------------------------------------------------
                 Σ (RelTyp _ (Se i) ρ (Se i) ρ′)
                 λ rel → RelExp (N [ σ ]) ρ N ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
                        { ↘⟦T⟧  = ⟦Se⟧ _
                        ; ↘⟦T′⟧ = ⟦Se⟧ _
                        ; T≈T′  = U′ ≤-refl
                        }
                    , record
                        { ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦N⟧
                        ; ↘⟦t′⟧ = ⟦N⟧
                        ; t≈t′  = PERDef.N
                        }
          where module σ = RelSubst (⊨σ ρ≈ρ′)


ze-[]′ : Γ ⊨s σ ∶ Δ →
         ----------------------
         Γ ⊨ ze [ σ ] ≈ ze ∶ N
ze-[]′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------------------------
                 Σ (RelTyp 0 N ρ N ρ′)
                 λ rel → RelExp (ze [ σ ]) ρ ze ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
                        { ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N
                        }
                    , record
                        { ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦ze⟧
                        ; ↘⟦t′⟧ = ⟦ze⟧
                        ; t≈t′  = ze
                        }
          where module σ = RelSubst (⊨σ ρ≈ρ′)


su-[]′ : Γ ⊨s σ ∶ Δ →
         Δ ⊨ t ∶ N →
         ----------------------------------
         Γ ⊨ su t [ σ ] ≈ su (t [ σ ]) ∶ N
su-[]′ {_} {σ} {_} {t} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨t) = ⊨Γ , _ , helper
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
                ...  | record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ⟦N⟧ ; T≈T′ = N }
                     , re = record
                              { ↘⟦T⟧  = ⟦N⟧
                              ; ↘⟦T′⟧ = ⟦N⟧
                              ; T≈T′  = N
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
                 (⊨T : (N ∷ Δ) ⊨ T ∶ Se i) →
                 (⊨s : Δ ⊨ s ∶ T [| ze ]) →
                 (⊨r : T ∷ N ∷ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ]) →
                 a ∈′ Nat →
                 let (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) = ⊨σ
                     rs = σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
                     (_   , n₂  , _)    = ⊨T
                     (⊨Δ₃ , n₃  , s≈s′) = ⊨s
                     (_   , n₄  , _)    = ⊨r
                     re = proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ (RelSubst.σ≈δ rs))) in
                 rec∙ T , (RelExp.⟦t⟧ re) , r , (RelSubst.⟦σ⟧ rs) , a ↘ res →
                 -----------------------------------------------------------------------------------------
                 ∃ λ res′ → rec∙ (T [ q σ ]) , RelExp.⟦t⟧ re , (r [ q (q σ) ]) , ρ , a ↘ res′
                          × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (RelSubst.⟦σ⟧ rs ↦ a) T (RelSubst.⟦σ⟧ rs ↦ a))
                            λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel)
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {ze} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∷-cong ⊨Δ₂ Nrel₂ , _ , _) (⊨Δ₃ , _ , s≈s′) ⊨r@(_ , n₄ , _) ze ze↘
  with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧
      with s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)
...      | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { t≈t′ = t≈t′ } = _ , ze↘
                                  , record
                                   { ↘⟦T⟧ = ↘⟦T⟧
                                   ; ↘⟦T′⟧ = ↘⟦T′⟧
                                   ; T≈T′ = 𝕌-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₄)) T≈T′
                                   }
                                 , El-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₄)) T≈T′ (El-refl T≈T′ t≈t′)
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {su a} {res} ⊨Γ ⊨σ@(⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ ⊨T@(_ , n₂ , _) ⊨s@(⊨Δ₃ , n₃ , s≈s′) ⊨r@(∷-cong (∷-cong ⊨Δ₄ Nrel₄) Trel₄ , n₄ , r≈r′) (su a≈a) (su↘ {b′ = b} ↘res ↘r)
  with rec-[]′-helper ⊨Γ ⊨σ ρ≈ρ ⊨T ⊨s ⊨r a≈a ↘res
...  | b′ , ↘b′ , record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } , b≈b′
    with record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
      rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ⟦σ⟧≈⟦σ⟧ : ⟦σ⟧ ≈ ⟦σ⟧ ∈ ⟦ ⊨Δ₄ ⟧ρ
    ⟦σ⟧≈⟦σ⟧ = ⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ

    a≈a₄ : a ∈′ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧))
    a≈a₄
      with record { T≈T′ = N } ← Nrel₄ ⟦σ⟧≈⟦σ⟧ = a≈a

    b≈b′₄ : (R : RelTyp _ T (⟦σ⟧ ↦ a) T (⟦σ⟧ ↦ a)) →  b ≈ b′ ∈ El _ (RelTyp.T≈T′ R)
    b≈b′₄ record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
      rewrite ⟦⟧-det ↘⟦T⟧₄ ↘⟦T⟧
            | ⟦⟧-det ↘⟦T′⟧₄ ↘⟦T′⟧ = 𝕌-irrel T≈T′ T≈T′₄ b≈b′

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q σ ]) , re.⟦t⟧ , (r [ q (q σ) ]) , ρ , su a ↘ res′
                      × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (⟦σ⟧ ↦ su a) T (⟦σ⟧ ↦ su a))
                        λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel)
    helper
      with r≈r′ {_ ↦ _} {_ ↦ _} ((⟦σ⟧≈⟦σ⟧ , a≈a₄) , b≈b′₄ (Trel₄ (⟦σ⟧≈⟦σ⟧ , a≈a₄)))
    ... | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧₄ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
        , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
        rewrite ⟦⟧-det ↘r ↘⟦r⟧ = _ , su↘ ↘b′ (⟦[]⟧ (⟦q⟧ (⟦q⟧ ↘⟦σ⟧)) ↘⟦r′⟧)
                               , record
                                 { ↘⟦T⟧ = ↘⟦T⟧₄
                                 ; ↘⟦T′⟧ = ↘⟦T′⟧₄
                                 ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′₄
                                 }
                               , El-cumu (m≤n⊔m _ _) T≈T′₄ r≈r′
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {↑ N c} {↑ T′ (rec _ _ _ _ _)} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∷-cong ⊨Δ₂ Nrel₂ , n₂ , Trel₂) (⊨Δ₃ , n₃ , s≈s′) (∷-cong (∷-cong ⊨Δ₄ Nrel₄) Trel₄ , n₄ , r≈r′) (ne c≈c) (rec∙ T↘)
  with record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ⟦σ⟧≈⟦σ⟧₂ : drop (⟦σ⟧ ↦ ↑ N c) ∈′ ⟦ ⊨Δ₂ ⟧ρ
    ⟦σ⟧≈⟦σ⟧₂ = ⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ

    ↑Nc≈↑Nc : ↑ N c ∈′ El _ (RelTyp.T≈T′ (Nrel₂ ⟦σ⟧≈⟦σ⟧₂))
    ↑Nc≈↑Nc
      with record { T≈T′ = N } ← Nrel₂ ⟦σ⟧≈⟦σ⟧₂ = ne c≈c

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q σ ]) , re.⟦t⟧ , (r [ q (q σ) ]) , ρ , ↑ N c ↘ res′
                      × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (⟦σ⟧ ↦ ↑ N c) T (⟦σ⟧ ↦ ↑ N c))
                          (λ rel → ↑ T′ (rec T re.⟦t⟧ r ⟦σ⟧ c) ≈ res′ ∈ El _ (RelTyp.T≈T′ rel))
    helper
      with Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , ↑Nc≈↑Nc)
    ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ _ }
         , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₂
          with refl ← ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧
             | refl ← ⟦⟧-det ↘⟦T⟧ T↘                = _ , rec∙ (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧) T↘)
                                                    , record
                                                      { ↘⟦T⟧ = ↘⟦T⟧
                                                      ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                      ; T≈T′ = 𝕌-cumu (≤-trans (<⇒≤ i<n₂) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₄))) T≈T′
                                                      }
                                                    , El-cumu (≤-trans (<⇒≤ i<n₂) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₄))) T≈T′ (Bot⊆El T≈T′ bot-helper)
      where
        bot-helper : rec T re.⟦t⟧ r ⟦σ⟧ c ≈ rec (T [ q σ ]) re.⟦t⟧ (r [ q (q σ) ]) ρ c ∈ Bot
        bot-helper n
          with c≈c n
        ...  | _ , ↘c , _ = bot-helper′
          where
            ⟦σ⟧≈⟦σ⟧₂′ : ⟦σ⟧ ≈ ⟦σ⟧ ∈ ⟦ ⊨Δ₂ ⟧ρ
            ⟦σ⟧≈⟦σ⟧₂′ = ⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ

            a≈b₂ : ∀ {a b} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₂ ⟦σ⟧≈⟦σ⟧₂′))
            a≈b₂ {a} {b} a≈b
              with record { T≈T′ = N } ← Nrel₂ ⟦σ⟧≈⟦σ⟧₂′ = a≈b

            bot-helper′ : ∃ λ u → Re n - rec T re.⟦t⟧ r ⟦σ⟧ c ↘ u
                                × Re n - rec (T [ q σ ]) re.⟦t⟧ (r [ q (q σ) ]) ρ c ↘ u
            bot-helper′
              with Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ (ne (Bot-l n))))
                 | s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)
                 | Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ ze))
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ns _ }
                 , record { ⟦t⟧ = ⟦T⟧n ; ↘⟦t⟧ = ↘⟦T⟧n ; t≈t′ = T≈T′ns }
                 | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; t≈t′ = s≈s′ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ze _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                with T≈T′ns ← 𝕌-cumu (<⇒≤ i<n₂ns) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂ns) T≈T′ns)
                   | T≈T′ze₁ ← 𝕌-cumu (<⇒≤ i<n₂ze) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂ze) T≈T′ze₁)
                  rewrite ⟦⟧-det ↘⟦T⟧ze₁ ↘⟦T⟧ze
                    with 𝕌⊆TopT T≈T′ns (1 + n)
                       | El⊆Top T≈T′ze₁ (El-one-sided T≈T′ze T≈T′ze₁ s≈s′) n
            ...        | _ , Tns↘ , T′ns↘
                       | _ , Tze↘ , T′ze↘
                      rewrite ⟦⟧-det ↘⟦T⟧ze ↘⟦T⟧ze₁ = bot-helper″
              where
                ⟦σ⟧≈⟦σ⟧₄ : ⟦σ⟧ ∈′ ⟦ ⊨Δ₄ ⟧ρ
                ⟦σ⟧≈⟦σ⟧₄ = ⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ

                a≈b₄ : l′ N n ∈′ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧₄))
                a≈b₄
                  with record { T≈T′ = N } ← Nrel₄ ⟦σ⟧≈⟦σ⟧₄ = ne (Bot-l n)

                a′≈b′₄ : (R : RelTyp _ T (⟦σ⟧ ↦ l′ N n) T (⟦σ⟧ ↦ l′ N n)) → l′ ⟦T⟧n (1 + n) ∈′ El _ (RelTyp.T≈T′ R)
                a′≈b′₄ R
                  with record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ } ← R
                    rewrite ⟦⟧-det ↘⟦T′⟧₄ ↘⟦T⟧₄
                          | ⟦⟧-det ↘⟦T⟧₄ ↘⟦T⟧n = Bot⊆El T≈T′₄ (Bot-l (1 + n))

                bot-helper″ : ∃ λ u → Re n - rec T ⟦s⟧ r ⟦σ⟧ c ↘ u
                                    × Re n - rec (T [ q σ ]) ⟦s⟧ (r [ q (q σ) ]) ρ c ↘ u
                bot-helper″
                  with r≈r′ {_ ↦ _} {_ ↦ _} ((⟦σ⟧≈⟦σ⟧₄ , a≈b₄) , a′≈b′₄ (Trel₄ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₄ , a≈b₄)))
                     | Trel₂ {_ ↦ _} {_ ↦ _} (⟦σ⟧≈⟦σ⟧₂ , (a≈b₂ (su (ne (Bot-l n)))))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; t≈t′ = r≈r′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂su _ }
                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; t≈t′ = T≈T′su₁ }
                    with T≈T′su₁ ← 𝕌-cumu (<⇒≤ i<n₂su) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂su) T≈T′su₁)
                      rewrite ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                         with El⊆Top T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (2 + n)
                ...         | _ , Tsu↘ , T′su↘ = _
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
          N ∷ Δ ⊨ T ∶ Se i →
          Δ ⊨ s ∶ T [| ze ] →
          T ∷ N ∷ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
          Δ ⊨ t ∶ N →
          -------------------------------------------------------------------------------------------------
          Γ ⊨ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]
rec-[]′ {_} {σ} {_} {T} {s} {r} {t} ⊨σ@(⊨Γ , ⊨Δ , σ≈σ′) ⊨T@(_ , n₁ , _) ⊨s@(⊨Δ₂ , n₂ , s≈s′) ⊨r@(∷-cong (∷-cong ⊨Δ₃ Nrel₃) Trel₃ , n₃ , r≈r′) (⊨Δ₄ , _ , t≈t′) = ⊨Γ , n₁ ⊔ n₂ ⊔ n₃ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             -----------------------------------------------------------------------------------------------------------------------
             Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) (T [ σ , t [ σ ] ]) ρ (T [ σ , t [ σ ] ]) ρ′)
             λ rel → RelExp (rec T s r t [ σ ]) ρ (rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← σ≈σ′ ρ≈ρ′
        with t≈t′ (⊨-irrel ⊨Δ ⊨Δ₄ σ≈δ)
    ...    | record { T≈T′ = N }
           , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
          with rec-helper ⊨Δ σ≈δ ⊨T ⊨s ⊨r t≈t′
             | ⟦⟧ρ-refl ⊨Γ ⊨Γ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
    ...      | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , res , res′ , ↘res , ↘res′ , res≈res′
             | ρ′≈ρ′
            with record { ↘⟦σ⟧ = ↘⟦δ⟧₁ ; σ≈δ = δ≈δ } ← σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ ρ′≈ρ′)
               | rec-[]′-helper′ ← rec-[]′-helper {res = res′} ⊨Γ ⊨σ ρ′≈ρ′ ⊨T ⊨s ⊨r (El-refl {i = 0} N (El-sym′ {i = 0} N t≈t′))
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
