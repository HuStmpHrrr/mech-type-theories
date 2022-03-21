{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext


N-≈′ : ∀ {i} →
       ⊨ Γ →
       ----------------
       Γ ⊨ N ≈ N ∶ Se i
N-≈′ {_} {i} ⊨Γ = ⊨Γ , suc i , λ ρ≈ρ′ → record
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
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp n N ρ N ρ′) (λ rel → RelExp (su t) ρ (su t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
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


RelExp-refl : ∀ {n} (⊨Γ : ⊨ Γ) →
              ({ρ ρ′ : Envs} → (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp n T ρ T′ ρ′) (λ rel → RelExp t ρ t′ ρ′ (El _ (RelTyp.T≈T′ rel)))) →
              ({ρ ρ′ : Envs} → (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp n T ρ T ρ′) (λ rel → RelExp t ρ t ρ′ (El _ (RelTyp.T≈T′ rel))))
RelExp-refl ⊨Γ TT′ ρ≈ρ′
  with TT′ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′) | TT′ ρ≈ρ′ | TT′ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
... | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
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
             (TT′ : (N ∺ Γ) ⊨ T ≈ T′ ∶ Se i) →
             (ss′ : Γ ⊨ s ≈ s′ ∶ (T [| ze ])) →
             (rr′ : (T ∺ N ∺ Γ) ⊨ r ≈ r′ ∶ (T [ (wk ∘ wk) , su (v 1) ])) →
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
rec-helper {_} {ρ} {ρ′} {T} {T′} {s} {s′} {r} {r′} {i = i} ⊨Γ ρ≈ρ′ (∺-cong ⊨Γ₁ Nrel₁ , n₁ , Trel₁) (⊨Γ₂ , n₂ , s≈s′) (∺-cong (∺-cong ⊨Γ₃ Nrel₃) Trel₃ , n₃ , r≈r′) a≈b
  with ⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′
...  | ρ≈ρ′₂ = helper a≈b
  where
    helper : a ≈ b ∈ Nat →
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
        ρ≈ρ′₃ : drop (drop (ρ ↦ a ↦ a′)) ≈ drop (drop (ρ′ ↦ b ↦ b′)) ∈ ⟦ ⊨Γ₃ ⟧ρ
        ρ≈ρ′₃
          rewrite drop-↦ (ρ ↦ a) a′
                | drop-↦ (ρ′ ↦ b) b′
                | drop-↦ ρ a
                | drop-↦ ρ′ b = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

        a≈b₃ : a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
        a≈b₃
          with Nrel₃ ρ≈ρ′₃
        ...  | record { T≈T′ = N } = a≈b

        a′≈b′₃ : a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
        a′≈b′₃
          with Trel₃ (ρ≈ρ′₃ , a≈b₃)
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
            rewrite drop-↦ (ρ ↦ a) a′
                  | drop-↦ (ρ′ ↦ b) b′
                  | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₃
                  | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₃ = 𝕌-irrel T≈T′ T≈T′₃ a′≈b′

        helper-su : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp _ T (ρ ↦ su a) T (ρ′ ↦ su b))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , su a ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , su b ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-su
          with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃)
        ... | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                rewrite drop-↦ (ρ ↦ a) a′
                      | drop-↦ (ρ′ ↦ b) b′
                      | drop-↦ ρ a
                      | drop-↦ ρ′ b = record
                            { ↘⟦T⟧ = ↘⟦T⟧
                            ; ↘⟦T′⟧ = ↘⟦T′⟧
                            ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′
                            }
                          , _ , _ , su↘ ↘a′ ↘⟦r⟧ , su↘ ↘b′ ↘⟦r′⟧ , El-cumu (m≤n⊔m _ _) T≈T′ r≈r′
    helper (ne {c} {c′} c≈c′) = helper-ne
      where
        ρ≈ρ′₁ : {a b : D} (κ : UMoT) → drop (ρ [ κ ] ↦ a) ≈ drop (ρ′ [ κ ] ↦ b) ∈ ⟦ ⊨Γ₁ ⟧ρ
        ρ≈ρ′₁ {a} {b} κ
          rewrite drop-↦ (ρ [ κ ]) a
                | drop-↦ (ρ′ [ κ ]) b = ⟦⟧ρ-mon ⊨Γ₁ κ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)

        ρ≈ρ′₁′ : {a b : D} → drop (ρ ↦ a) ≈ drop (ρ′ ↦ b) ∈ ⟦ ⊨Γ₁ ⟧ρ
        ρ≈ρ′₁′ {a} {b}
          rewrite sym (ρ-ap-vone ρ)
                | sym (ρ-ap-vone ρ′) = ρ≈ρ′₁ vone

        a≈b₁ : {a b : D} (κ : UMoT) → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₁ (ρ≈ρ′₁ {a} {b} κ)))
        a≈b₁ {a} {b} κ a≈b
          with Nrel₁ (ρ≈ρ′₁ {a} {b} κ)
        ... | record { T≈T′ = N } = a≈b

        a≈b₁′ : {a b : D} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₁ (ρ≈ρ′₁′ {a} {b})))
        a≈b₁′ {a} {b} a≈b
          with Nrel₁ (ρ≈ρ′₁′ {a} {b})
        ... | record { T≈T′ = N } = a≈b

        helper-ne : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp _ T (ρ ↦ ↑ N c) T (ρ′ ↦ ↑ N c′))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , ↑ N c ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , ↑ N c′ ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-ne
          with RelExp-refl (∺-cong ⊨Γ₁ Nrel₁) Trel₁ (ρ≈ρ′₁′ , a≈b₁′ (ne c≈c′)) | Trel₁ (ρ≈ρ′₁′ , a≈b₁′ (ne c≈c′))
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
             , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
             | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁₁ _ }
             , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
            with 𝕌-cumu (<⇒≤ i<n₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁) T≈T′) | 𝕌-cumu (<⇒≤ i<n₁₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁₁) T≈T′₁)
        ...    | T≈T′ | T≈T′₁
               with ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
        ...       | refl = record
                          { ↘⟦T⟧ = ↘⟦T⟧
                          ; ↘⟦T′⟧ = ↘⟦T′⟧
                          ; T≈T′ = 𝕌-cumu (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₃)) T≈T′
                          }
                        , _ , _ , rec∙ ↘⟦T⟧₁ , rec∙ ↘⟦T′⟧₁ , El-cumu (≤-trans (m≤m⊔n n₁ n₂) (m≤m⊔n _ n₃)) T≈T′ (El-one-sided T≈T′₁ T≈T′ (realizability-Re T≈T′₁ bot-helper))
          where
            bot-helper : rec T (RelExp.⟦t⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r ρ c ≈ rec T′ (RelExp.⟦t′⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r′ ρ′ c′ ∈ Bot
            bot-helper ns κ
              with c≈c′ ns κ | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ (ne (Bot-l (head ns))))) | s≈s′ ρ≈ρ′₂ | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ ze))
            ...  | cc , c↘ , c′↘
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ns _ }
                 , record { ⟦t⟧ = ⟦T⟧ns ; ⟦t′⟧ = ⟦T′⟧ns ; ↘⟦t⟧ = ↘⟦T⟧ns ; ↘⟦t′⟧ = ↘⟦T′⟧ns ; t≈t′ = T≈T′ns }
                 | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; t≈t′ = s≈s′ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ze _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ⟦t′⟧ = ⟦T′⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; ↘⟦t′⟧ = ↘⟦T′⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                with 𝕌-cumu (<⇒≤ i<n₁ns) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ns) T≈T′ns)
                   | 𝕌-cumu (<⇒≤ i<n₁ze) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ze) T≈T′ze₁)
            ...    | T≈T′ns
                   | T≈T′ze₁ = bot-helper′
              where
                ρ≈ρ′₃ : drop (drop (ρ [ κ ] ↦ l′ N (head ns) ↦ l′ ⟦T⟧ns (suc (head ns)))) ≈ drop (drop (ρ′ [ κ ] ↦ l′ N (head ns) ↦ l′ ⟦T′⟧ns (suc (head ns)))) ∈ ⟦ ⊨Γ₃ ⟧ρ
                ρ≈ρ′₃
                  rewrite drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                        | drop-↦ (ρ′ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T′⟧ns (suc (head ns)))
                        | drop-↦ (ρ [ κ ]) (l′ N (head ns))
                        | drop-↦ (ρ′ [ κ ]) (l′ N (head ns)) = ⟦⟧ρ-mon ⊨Γ₃ κ (⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′)

                a≈b₃ : l′ N (head ns) ≈ l′ N (head ns) ∈ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
                a≈b₃
                  with Nrel₃ ρ≈ρ′₃
                ...  | record { T≈T′ = N } = ne (Bot-l (head ns))

                a′≈b′₃ : l′ ⟦T⟧ns (suc (head ns)) ≈ l′ ⟦T′⟧ns (suc (head ns)) ∈ El _ (RelTyp.T≈T′ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
                a′≈b′₃
                  with Trel₃ (ρ≈ρ′₃ , a≈b₃)
                ...  | record { ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
                    rewrite drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                          | drop-↦ (ρ′ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T′⟧ns (suc (head ns)))
                          | ⟦⟧-det ↘⟦T⟧ns ↘⟦T⟧₃ = El-one-sided T≈T′ns T≈T′₃ (realizability-Re T≈T′ns (Bot-l (suc (head ns))))

                bot-helper′ : ∃ λ u → Re ns - rec T ⟦s⟧ r ρ c [ κ ] ↘ u × Re ns - rec T′ ⟦s′⟧ r′ ρ′ c′ [ κ ] ↘ u
                bot-helper′
                  with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃) | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ (su (ne (Bot-l (head ns))))))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁su _ }
                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ⟦t′⟧ = ⟦T′⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; ↘⟦t′⟧ = ↘⟦T′⟧su₁ ; t≈t′ = T≈T′su₁ }
                    with 𝕌-cumu (<⇒≤ i<n₁su) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁su) T≈T′su₁)
                ...    | T≈T′su₁
                      rewrite drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                            | drop-↦ (ρ′ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T′⟧ns (suc (head ns)))
                            | drop-↦ (ρ [ κ ]) (l′ N (head ns))
                            | drop-↦ (ρ′ [ κ ]) (l′ N (head ns))
                            | sym (↦-mon ρ ze κ)
                            | ⟦⟧-det ↘⟦T⟧ze₁ (⟦⟧-mon κ ↘⟦T⟧ze)
                            | ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                        with realizability-Rty T≈T′ns (inc ns) vone
                           | realizability-Rf T≈T′ze₁ (El-one-sided (𝕌-mon κ T≈T′ze) T≈T′ze₁ (El-mon T≈T′ze κ (𝕌-mon κ T≈T′ze) s≈s′)) ns vone
                           | realizability-Rf T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (inc (inc ns)) vone
                ...        | _ , Tns↘ , T′ns↘
                           | _ , Tze↘ , T′ze↘
                           | _ , Tsu↘ , T′su↘
                          rewrite D-ap-vone ⟦T⟧ns
                                | D-ap-vone ⟦T′⟧ns
                                | ⟦⟧-det (⟦⟧-mon κ ↘⟦T⟧ze) ↘⟦T⟧ze₁
                                | ↦-mon ρ ze κ
                                | D-ap-vone ⟦T⟧ze₁
                                | D-ap-vone ⟦T′⟧ze₁
                                | D-ap-vone (⟦s⟧ [ κ ])
                                | D-ap-vone (⟦s′⟧ [ κ ])
                                | D-ap-vone ⟦T⟧su₁
                                | D-ap-vone ⟦T′⟧su₁
                                | D-ap-vone ⟦r⟧
                                | D-ap-vone ⟦r′⟧ = rec _ _ _ cc , Rr ns ↘⟦T⟧ns Tns↘ ↘⟦T⟧ze₁ Tze↘ ↘⟦r⟧ ↘⟦T⟧su₁ Tsu↘ c↘ , Rr ns ↘⟦T′⟧ns T′ns↘ ↘⟦T′⟧ze₁ T′ze↘ ↘⟦r′⟧ ↘⟦T′⟧su₁ T′su↘ c′↘

rec-cong′ : ∀ {i} →
            N ∺ Γ ⊨ T ≈ T′ ∶ Se i →
            Γ ⊨ s ≈ s′ ∶ T [| ze ] →
            T ∺ N ∺ Γ ⊨ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
            Γ ⊨ t ≈ t′ ∶ N →
            --------------------------------------------
            Γ ⊨ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
rec-cong′ {_} {T} {T′} {s} {s′} {r} {r′} {t} {t′} TT′@(_ , _ , _) ss′@(⊨Γ₂ , _ , s≈s′) rr′@(_ , _ , _) tt′@(⊨Γ₄ , _ , t≈t′) = ⊨Γ₄ , _ , helper
  where
    helper : {ρ ρ′ : Envs} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ → Σ (RelTyp _ (T [| t ]) ρ (T [| t ]) ρ′) (λ rel → RelExp (rec T s r t) ρ (rec T′ s′ r′ t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
    helper ρ≈ρ′
      with RelExp-refl ⊨Γ₄ t≈t′ ρ≈ρ′ | t≈t′ ρ≈ρ′
    ...  | record { T≈T′ = N }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
         | record { T≈T′ = N }
         , record { ↘⟦t⟧ = ↘⟦t⟧₁ ; ↘⟦t′⟧ = ↘⟦t′⟧₁ ; t≈t′ = t≈t′₁ }
       with rec-helper ⊨Γ₄ ρ≈ρ′ TT′ ss′ rr′ t≈t′ | rec-helper ⊨Γ₄ ρ≈ρ′ TT′ ss′ rr′ t≈t′₁
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
              N ∺ Γ ⊨ T ∶ Se i →
              Γ ⊨ s ∶ T [| ze ] →
              T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              ---------------------------------------------
              Γ ⊨ rec T s r ze ≈ s ∶ T [| ze ]
rec-β-ze′ {_} {T} {s} {r} ⊨T ⊨s@(⊨Γ , _ , s≈s′) ⊨r = ⊨Γ , _ , helper
  where
    helper : {ρ ρ′ : Envs} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (T [| ze ]) ρ (T [| ze ]) ρ′) (λ rel → RelExp (rec T s r ze) ρ s ρ′ (El _ (RelTyp.T≈T′ rel)))
    helper ρ≈ρ′
      with s≈s′ ρ≈ρ′
    ... | Trel , srel = Trel
                      , record
                        { RelExp srel
                        ; ↘⟦t⟧ = ⟦rec⟧ (RelExp.↘⟦t⟧ srel) ⟦ze⟧ ze↘
                        }

rec-β-su′ : ∀ {i} →
            N ∺ Γ ⊨ T ∶ Se i →
            Γ ⊨ s ∶ T [| ze ] →
            T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
            Γ ⊨ t ∶ N →
            -----------------------------------------------------------------
            Γ ⊨ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
rec-β-su′ {_} {T} {s} {r} {t} ⊨T@(_ , _ , _) ⊨s@(⊨Γ₂ , _ , s≈s′) ⊨r@(_ , _ , _) (⊨Γ₄ , _ , t≈t′) = ⊨Γ₄ , _ , helper
  where
    helper : {ρ ρ′ : Envs} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ₄ ⟧ρ → Σ (RelTyp _ (T [| su t ]) ρ (T [| su t ]) ρ′) (λ rel → RelExp (rec T s r (su t)) ρ (r [ (I , t) , rec T s r t ]) ρ′ (El _ (RelTyp.T≈T′ rel)))
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
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (N [ σ ]) ρ N ρ′ (El _ (RelTyp.T≈T′ rel)))
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
          where module σ = RelSubsts (⊨σ ρ≈ρ′)


ze-[]′ : Γ ⊨s σ ∶ Δ →
         ----------------------
         Γ ⊨ ze [ σ ] ≈ ze ∶ N
ze-[]′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp 0 N ρ N ρ′) (λ rel → RelExp (ze [ σ ]) ρ ze ρ′ (El _ (RelTyp.T≈T′ rel)))
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
          where module σ = RelSubsts (⊨σ ρ≈ρ′)


su-[]′ : Γ ⊨s σ ∶ Δ →
         Δ ⊨ t ∶ N →
         ----------------------------------
         Γ ⊨ su t [ σ ] ≈ su (t [ σ ]) ∶ N
su-[]′ {_} {σ} {_} {t} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨t) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp 0 N ρ N ρ′) (λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ N ρ N ρ′) (λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
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

rec-[]′-helper : ∀ {res i} →
                (⊨Γ : ⊨ Γ) →
                (⊨σ : Γ ⊨s σ ∶ Δ) →
                (ρ≈ρ : ρ ≈ ρ ∈ ⟦ ⊨Γ ⟧ρ) →
                (⊨T : (N ∺ Δ) ⊨ T ∶ Se i) →
                (⊨s : Δ ⊨ s ∶ (T [| ze ])) →
                (⊨r : (T ∺ N ∺ Δ) ⊨ r ∶ (T [ (wk ∘ wk) , su (v 1) ])) →
                a ≈ a ∈ Nat →
                let (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) = ⊨σ
                    rs = σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
                    (_   , n₂  , _)    = ⊨T
                    (⊨Δ₃ , n₃  , s≈s′) = ⊨s
                    (_   , n₄  , _)    = ⊨r
                    re = proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ (RelSubsts.σ≈δ rs))) in
                rec∙ T , (RelExp.⟦t⟧ re) , r , (RelSubsts.⟦σ⟧ rs) , a ↘ res →
                -----------------------------------------------------
                ∃ λ res′ → rec∙ (T [ q σ ]) , RelExp.⟦t⟧ re , (r [ q (q σ) ]) , ρ , a ↘ res′ × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (RelSubsts.⟦σ⟧ rs ↦ a) T (RelSubsts.⟦σ⟧ rs ↦ a)) (λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel))
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {ze} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∺-cong ⊨Δ₂ Nrel₂ , _ , _) (⊨Δ₃ , _ , s≈s′) ⊨r@(_ , n₄ , _) ze ze↘
  with σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
...  | record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧
      with s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)
...      | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[|ze]⟧ ↘⟦T′⟧ ; T≈T′ = T≈T′ }
         , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = _ , ze↘
                                               , record
                                                { ↘⟦T⟧ = ↘⟦T⟧
                                                ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                ; T≈T′ = 𝕌-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₄)) T≈T′
                                                }
                                              , El-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₄)) T≈T′ (El-refl T≈T′ t≈t′)
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {su a} {res} ⊨Γ ⊨σ@(⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ ⊨T@(_ , n₂ , _) ⊨s@(⊨Δ₃ , n₃ , s≈s′) ⊨r@(∺-cong (∺-cong ⊨Δ₄ Nrel₄) Trel₄ , n₄ , r≈r′) (su a≈a) (su↘ {b′ = b} ↘res ↘r)
  with rec-[]′-helper ⊨Γ ⊨σ ρ≈ρ ⊨T ⊨s ⊨r a≈a ↘res
...  | b′ , ↘b′ , record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } , b≈b′
    with σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
...    | record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
      rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ↘⟦σ⟧₁ : ⟦ σ ⟧s drop (drop (ρ ↦ a ↦ b′)) ↘ ⟦σ⟧
    ↘⟦σ⟧₁
      rewrite drop-↦ (ρ ↦ a) b′
            | drop-↦ ρ a = ↘⟦σ⟧

    ⟦σ⟧≈⟦σ⟧ : drop (drop (⟦σ⟧ ↦ a ↦ b)) ≈ drop (drop (⟦σ⟧ ↦ a ↦ b′)) ∈ ⟦ ⊨Δ₄ ⟧ρ
    ⟦σ⟧≈⟦σ⟧
      rewrite drop-↦ (⟦σ⟧ ↦ a) b
            | drop-↦ (⟦σ⟧ ↦ a) b′
            | drop-↦ ⟦σ⟧ a = ⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ

    a≈a₄ : a ≈ a ∈ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧))
    a≈a₄
      with Nrel₄ ⟦σ⟧≈⟦σ⟧
    ...  | record { T≈T′ = N } = a≈a

    b≈b′₄ : b ≈ b′ ∈ El _ (RelTyp.T≈T′ (Trel₄ (⟦σ⟧≈⟦σ⟧ , a≈a₄)))
    b≈b′₄
      with Trel₄ (⟦σ⟧≈⟦σ⟧ , a≈a₄)
    ...  | record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
        rewrite drop-↦ (⟦σ⟧ ↦ a) b
              | drop-↦ (⟦σ⟧ ↦ a) b′
              | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₄
              | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₄ = 𝕌-irrel T≈T′ T≈T′₄ b≈b′

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q σ ]) , re.⟦t⟧ , (r [ q (q σ) ]) , ρ , su a ↘ res′ × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (⟦σ⟧ ↦ su a) T (⟦σ⟧ ↦ su a)) (λ rel → res ≈ res′ ∈ El _ (RelTyp.T≈T′ rel))
    helper
      with r≈r′ ((⟦σ⟧≈⟦σ⟧ , a≈a₄) , b≈b′₄)
    ... | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧₄ ; ↘⟦T′⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
        , record { ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
        rewrite ⟦⟧-det ↘r ↘⟦r⟧
              | drop-↦ (⟦σ⟧ ↦ a) b
              | drop-↦ (⟦σ⟧ ↦ a) b′
              | drop-↦ ⟦σ⟧ a         = _ , su↘ ↘b′ (⟦[]⟧ (⟦q⟧ (⟦q⟧ ↘⟦σ⟧₁)) ↘⟦r′⟧)
                                     , record
                                       { ↘⟦T⟧ = ↘⟦T⟧₄
                                       ; ↘⟦T′⟧ = ↘⟦T′⟧₄
                                       ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′₄
                                       }
                                     , El-cumu (m≤n⊔m _ _) T≈T′₄ r≈r′
rec-[]′-helper {_} {σ} {_} {ρ} {T} {s} {r} {↑ N c} {↑ T′ (rec _ _ _ _ _)} ⊨Γ (⊨Γ₁ , ⊨Δ₁ , σ≈σ′) ρ≈ρ (∺-cong ⊨Δ₂ Nrel₂ , n₂ , Trel₂) (⊨Δ₃ , n₃ , s≈s′) (∺-cong (∺-cong ⊨Δ₄ Nrel₄) Trel₄ , n₄ , r≈r′) (ne c≈c) (rec∙ T↘)
  with σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ)
...  | record { ⟦σ⟧ = ⟦σ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
    rewrite ⟦⟧s-det ↘⟦δ⟧ ↘⟦σ⟧ = helper
  where
    ⟦σ⟧≈⟦σ⟧₂ : drop (⟦σ⟧ ↦ ↑ N c) ≈ drop (⟦σ⟧ ↦ ↑ N c) ∈ ⟦ ⊨Δ₂ ⟧ρ
    ⟦σ⟧≈⟦σ⟧₂ rewrite drop-↦ ⟦σ⟧ (↑ N c) = ⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ

    ↑Nc≈↑Nc : ↑ N c ≈ ↑ N c ∈ El _ (RelTyp.T≈T′ (Nrel₂ ⟦σ⟧≈⟦σ⟧₂))
    ↑Nc≈↑Nc
      with Nrel₂ ⟦σ⟧≈⟦σ⟧₂
    ... | record { T≈T′ = N } = ne c≈c

    module re = RelExp (proj₂ (s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ)))

    helper : ∃ λ res′ → rec∙ (T [ q σ ]) , re.⟦t⟧ , (r [ q (q σ) ]) , ρ , ↑ N c ↘ res′ × Σ (RelTyp (n₂ ⊔ n₃ ⊔ n₄) T (⟦σ⟧ ↦ ↑ N c) T (⟦σ⟧ ↦ ↑ N c)) (λ rel → ↑ T′ (rec T re.⟦t⟧ r ⟦σ⟧ c) ≈ res′ ∈ El _ (RelTyp.T≈T′ rel))
    helper
      with Trel₂ (⟦σ⟧≈⟦σ⟧₂ , ↑Nc≈↑Nc)
    ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ _ }
         , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₂
          with ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧ | ⟦⟧-det ↘⟦T⟧ T↘
    ...      | refl | refl                         = _ , rec∙ (⟦[]⟧ (⟦q⟧ (subst (⟦ σ ⟧s_↘ ⟦σ⟧) (sym (drop-↦ _ _)) ↘⟦σ⟧)) T↘)
                                                   , record
                                                     { ↘⟦T⟧ = ↘⟦T⟧
                                                     ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                     ; T≈T′ = 𝕌-cumu (≤-trans (<⇒≤ i<n₂) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₄))) T≈T′
                                                     }
                                                   , El-cumu (≤-trans (<⇒≤ i<n₂) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₄))) T≈T′ (realizability-Re T≈T′ bot-helper)
      where
        bot-helper : rec T re.⟦t⟧ r ⟦σ⟧ c ≈ rec (T [ q σ ]) re.⟦t⟧ (r [ q (q σ) ]) ρ c ∈ Bot
        bot-helper ns κ
          with c≈c ns κ
        ...  | _ , ↘c , _ = bot-helper′
          where
            ↘⟦σ⟧drop : ∀ {a} → ⟦ σ ⟧s drop (ρ [ κ ] ↦ a) ↘ ⟦σ⟧ [ κ ]
            ↘⟦σ⟧drop {a} rewrite drop-↦ (ρ [ κ ]) a = ⟦⟧s-mon κ ↘⟦σ⟧

            ↘⟦σ⟧dropdrop : ∀ {a b} → ⟦ σ ⟧s drop (drop (ρ [ κ ] ↦ a ↦ b)) ↘ ⟦σ⟧ [ κ ]
            ↘⟦σ⟧dropdrop {a} {b}
              rewrite drop-↦ (ρ [ κ ] ↦ a) b
                    | drop-↦ (ρ [ κ ]) a = ⟦⟧s-mon κ ↘⟦σ⟧

            ⟦σ⟧[κ]≈⟦σ⟧[κ]₂ : ∀ {a b} → drop (⟦σ⟧ [ κ ] ↦ a) ≈ drop (⟦σ⟧ [ κ ] ↦ b) ∈ ⟦ ⊨Δ₂ ⟧ρ
            ⟦σ⟧[κ]≈⟦σ⟧[κ]₂ {a} {b}
              rewrite drop-↦ (⟦σ⟧ [ κ ]) a
                    | drop-↦ (⟦σ⟧ [ κ ]) b = ⟦⟧ρ-mon ⊨Δ₂ κ (⊨-irrel ⊨Δ₁ ⊨Δ₂ σ≈δ)

            a≈b₂ : ∀ {a b} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₂ (⟦σ⟧[κ]≈⟦σ⟧[κ]₂ {a} {b})))
            a≈b₂ {a} {b} a≈b
              with Nrel₂ (⟦σ⟧[κ]≈⟦σ⟧[κ]₂ {a} {b})
            ...  | record { T≈T′ = N } = a≈b

            bot-helper′ : ∃ λ u → Re ns - rec T re.⟦t⟧ r ⟦σ⟧ c [ κ ] ↘ u × Re ns - rec (T [ q σ ]) re.⟦t⟧ (r [ q (q σ) ]) ρ c [ κ ] ↘ u
            bot-helper′
              with Trel₂ (⟦σ⟧[κ]≈⟦σ⟧[κ]₂ , (a≈b₂ (ne (Bot-l (head ns))))) | s≈s′ (⊨-irrel ⊨Δ₁ ⊨Δ₃ σ≈δ) | Trel₂ (⟦σ⟧[κ]≈⟦σ⟧[κ]₂ , (a≈b₂ ze))
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ns _ }
                 , record { ⟦t⟧ = ⟦T⟧ns ; ↘⟦t⟧ = ↘⟦T⟧ns ; t≈t′ = T≈T′ns }
                 | record { ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; t≈t′ = s≈s′ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂ze _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                with 𝕌-cumu (<⇒≤ i<n₂ns) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂ns) T≈T′ns)
                   | 𝕌-cumu (<⇒≤ i<n₂ze) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂ze) T≈T′ze₁)
            ...    | T≈T′ns | T≈T′ze₁
                  rewrite sym (↦-mon ⟦σ⟧ ze κ)
                        | ⟦⟧-det ↘⟦T⟧ze₁ (⟦⟧-mon κ ↘⟦T⟧ze)
                    with realizability-Rty T≈T′ns (inc ns) vone
                       | realizability-Rf T≈T′ze₁ (El-one-sided (𝕌-mon κ T≈T′ze) T≈T′ze₁ (El-mon T≈T′ze κ (𝕌-mon κ T≈T′ze) s≈s′)) ns vone
            ...        | _ , Tns↘ , T′ns↘
                       | _ , Tze↘ , T′ze↘
                      rewrite D-ap-vone ⟦T⟧ns
                            | ⟦⟧-det (⟦⟧-mon κ ↘⟦T⟧ze) ↘⟦T⟧ze₁
                            | ↦-mon ⟦σ⟧ ze κ
                            | D-ap-vone ⟦T⟧ze₁
                            | D-ap-vone (⟦s⟧ [ κ ])
                     = bot-helper″
              where
                ⟦σ⟧≈⟦σ⟧₄ : drop (drop (⟦σ⟧ [ κ ] ↦ l′ N (head ns) ↦ l′ ⟦T⟧ns (suc (head ns)))) ≈ drop (drop (⟦σ⟧ [ κ ] ↦ l′ N (head ns) ↦ l′ ⟦T⟧ns (suc (head ns)))) ∈ ⟦ ⊨Δ₄ ⟧ρ
                ⟦σ⟧≈⟦σ⟧₄
                  rewrite drop-↦ (⟦σ⟧ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                        | drop-↦ (⟦σ⟧ [ κ ]) (l′ N (head ns)) = ⟦⟧ρ-mon ⊨Δ₄ κ (⊨-irrel ⊨Δ₁ ⊨Δ₄ σ≈δ)

                a≈b₄ : l′ N (head ns) ≈ l′ N (head ns) ∈ El _ (RelTyp.T≈T′ (Nrel₄ ⟦σ⟧≈⟦σ⟧₄))
                a≈b₄
                  with Nrel₄ ⟦σ⟧≈⟦σ⟧₄
                ...  | record { T≈T′ = N } = ne (Bot-l (head ns))

                a′≈b′₄ : l′ ⟦T⟧ns (suc (head ns)) ≈ l′ ⟦T⟧ns (suc (head ns)) ∈ El _ (RelTyp.T≈T′ (Trel₄ (⟦σ⟧≈⟦σ⟧₄ , a≈b₄)))
                a′≈b′₄
                  with Trel₄ (⟦σ⟧≈⟦σ⟧₄ , a≈b₄)
                ...  | record { ↘⟦T⟧ = ↘⟦T⟧₄ ; ↘⟦T′⟧ = ↘⟦T′⟧₄ ; T≈T′ = T≈T′₄ }
                    rewrite drop-↦ (⟦σ⟧ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                          | drop-↦ (⟦σ⟧ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                          | ⟦⟧-det ↘⟦T⟧ns ↘⟦T⟧₄
                          | ⟦⟧-det ↘⟦T⟧₄ ↘⟦T′⟧₄ = realizability-Re T≈T′₄ (Bot-l (suc (head ns)))

                bot-helper″ : ∃ λ u → Re ns - rec T ⟦s⟧ r ⟦σ⟧ c [ κ ] ↘ u × Re ns - rec (T [ q σ ]) ⟦s⟧ (r [ q (q σ) ]) ρ c [ κ ] ↘ u
                bot-helper″
                  with r≈r′ ((⟦σ⟧≈⟦σ⟧₄ , a≈b₄) , a′≈b′₄) | Trel₂ (⟦σ⟧[κ]≈⟦σ⟧[κ]₂ , (a≈b₂ (su (ne (Bot-l (head ns))))))
                ...  | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; t≈t′ = r≈r′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₂su _ }
                     , record { ⟦t⟧ = ⟦T⟧su₁ ; ↘⟦t⟧ = ↘⟦T⟧su₁ ; t≈t′ = T≈T′su₁ }
                    with 𝕌-cumu (<⇒≤ i<n₂su) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₂su) T≈T′su₁)
                ...    | T≈T′su₁
                      rewrite drop-↦ (⟦σ⟧ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                            | drop-↦ (⟦σ⟧ [ κ ]) (l′ N (head ns))
                            | ⟦⟧-det ↘⟦T⟧su ↘⟦T⟧su₁
                         with realizability-Rf T≈T′su₁ (El-one-sided T≈T′su T≈T′su₁ r≈r′) (inc (inc ns)) vone
                ...         | _ , Tsu↘ , T′su↘
                           rewrite D-ap-vone ⟦T⟧su₁
                                 | D-ap-vone ⟦r⟧ = _
                                                 , Rr ns ↘⟦T⟧ns Tns↘ ↘⟦T⟧ze₁ Tze↘ ↘⟦r⟧ ↘⟦T⟧su₁ Tsu↘ ↘c
                                                 , Rr ns
                                                      (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧drop) ↘⟦T⟧ns)
                                                      Tns↘
                                                      (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧drop) ↘⟦T⟧ze₁)
                                                      Tze↘
                                                      (⟦[]⟧ (⟦q⟧ (⟦q⟧ ↘⟦σ⟧dropdrop)) ↘⟦r⟧) (⟦[]⟧ (⟦q⟧ ↘⟦σ⟧drop) ↘⟦T⟧su₁)
                                                      Tsu↘
                                                      ↘c

rec-[]′     : ∀ {i} →
              Γ ⊨s σ ∶ Δ →
              N ∺ Δ ⊨ T ∶ Se i →
              Δ ⊨ s ∶ T [| ze ] →
              T ∺ N ∺ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              Δ ⊨ t ∶ N →
              -----------------------------------------------------------------------------------------------
              Γ ⊨ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]
rec-[]′ {_} {σ} {_} {T} {s} {r} {t} ⊨σ@(⊨Γ , ⊨Δ , σ≈σ′) ⊨T@(_ , n₁ , _) ⊨s@(⊨Δ₂ , n₂ , s≈s′) ⊨r@(∺-cong (∺-cong ⊨Δ₃ Nrel₃) Trel₃ , n₃ , r≈r′) (⊨Δ₄ , _ , t≈t′) = ⊨Γ , n₁ ⊔ n₂ ⊔ n₃ , helper
  where
    helper : {ρ ρ′ : Envs} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
      Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) (T [ σ , t [ σ ] ]) ρ (T [ σ , t [ σ ] ]) ρ′)
      (λ rel → RelExp (rec T s r t [ σ ]) ρ (rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
    helper {ρ} {ρ′} ρ≈ρ′
      with σ≈σ′ ρ≈ρ′
    ...  | record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
        with t≈t′ (⊨-irrel ⊨Δ ⊨Δ₄ σ≈δ)
    ...    | record { T≈T′ = N }
           , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
          with rec-helper ⊨Δ σ≈δ ⊨T ⊨s ⊨r t≈t′ | ⟦⟧ρ-refl ⊨Γ ⊨Γ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
    ...      | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , res , res′ , ↘res , ↘res′ , res≈res′
             | ρ′≈ρ′
            with σ≈σ′ (⊨-irrel ⊨Γ ⊨Γ ρ′≈ρ′) | rec-[]′-helper {res = res′} ⊨Γ ⊨σ ρ′≈ρ′ ⊨T ⊨s ⊨r (El-refl {i = 0} N (El-sym′ {i = 0} N t≈t′))
    ...        | record { ↘⟦σ⟧ = ↘⟦δ⟧₁ ; σ≈δ = δ≈δ } | rec-[]′-helper′
              with s≈s′ (⟦⟧ρ-one-sided ⊨Δ ⊨Δ₂ σ≈δ) | s≈s′ (⟦⟧ρ-one-sided ⊨Δ ⊨Δ₂ δ≈δ)
    ...          | _ , record { ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ }
                 | _ , record { ↘⟦t⟧ = ↘⟦s′⟧₁ ; ↘⟦t′⟧ = ↘⟦s⟧₁ ; t≈t′ = s≈s }
                rewrite ⟦⟧s-det ↘⟦δ⟧₁ ↘⟦δ⟧
                      | ⟦⟧-det ↘⟦s′⟧₁ ↘⟦s′⟧
                  with rec-[]′-helper′ ↘res′
    ...              | _ , ↘res′₁
                     , record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ } , res′≈res′₁
                    rewrite  ⟦⟧-det ↘⟦T⟧₁ ↘⟦T′⟧
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
