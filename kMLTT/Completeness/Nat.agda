{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Terms fext

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext


N-[]′ : ∀ i →
        Γ ⊨s σ ∶ Δ →
        -----------------------
        Γ ⊨ N [ σ ] ≈ N ∶ Se i
N-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (N [ σ ]) ρ N ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′ = record
                        { ⟦T⟧   = U i
                        ; ⟦T′⟧  = U i
                        ; ↘⟦T⟧  = ⟦Se⟧ _
                        ; ↘⟦T′⟧ = ⟦Se⟧ _
                        ; T≈T′  = U′ ≤-refl
                        }
                    , record
                        { ⟦t⟧   = N
                        ; ⟦t′⟧  = N
                        ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦N⟧
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
                        { ⟦T⟧   = N
                        ; ⟦T′⟧  = N
                        ; ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N
                        }
                    , record
                        { ⟦t⟧   = ze
                        ; ⟦t′⟧  = ze
                        ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦ze⟧
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
                              { ⟦T⟧   = N
                              ; ⟦T′⟧  = N
                              ; ↘⟦T⟧  = ⟦N⟧
                              ; ↘⟦T′⟧ = ⟦N⟧
                              ; T≈T′  = N
                              }
                          , record
                              { ⟦t⟧   = su re.⟦t⟧
                              ; ⟦t′⟧  = su re.⟦t′⟧
                              ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦su⟧ re.↘⟦t⟧)
                              ; ↘⟦t′⟧ = ⟦su⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                              ; t≈t′  = su re.t≈t′
                              }
                  where module re = RelExp re


rec-helper : ∀ {i}
             (⊨Γ : ⊨ Γ)
             (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) →
             (TT′ : (N ∺ Γ) ⊨ T ≈ T′ ∶ Se i) →
             (ss′ : Γ ⊨ s ≈ s′ ∶ (T [ I , ze ])) →
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
rec-helper {_} {ρ} {ρ′} {T} {T′} {s} {s′} {r} {r′} {i = i} ⊨Γ ρ≈ρ′ (∷-cong ⊨Γ₁ Nrel₁ , n₁ , Trel₁) (⊨Γ₂ , n₂ , s≈s′) (∷-cong (∷-cong ⊨Γ₃ Nrel₃) Trel₃ , n₃ , r≈r′) a≈b
  with ⊨-irrel ⊨Γ ⊨Γ₂ ρ≈ρ′
...  | ρ≈ρ′₂ = helper a≈b
  where
    helper : a ≈ b ∈ Nat →
             let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
             in Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) T (ρ ↦ a) T (ρ′ ↦ b))
                λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , a ↘ a′
                                     × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , b ↘ b′
                                     × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
    helper ze
      with s≈s′ ρ≈ρ′₂
    ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ⟦ze⟧) ↘⟦T⟧₁ ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ⟦ze⟧) ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
          , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = _ ; ↘⟦t′⟧ = _ ; t≈t′ = s≈s′ } = record
                 { ⟦T⟧  = _
                 ; ⟦T′⟧  = _
                 ; ↘⟦T⟧  = ↘⟦T⟧₁
                 ; ↘⟦T′⟧ = ↘⟦T′⟧₁
                 ; T≈T′ = 𝕌-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₃)) T≈T′₁
                 }
               , ⟦s⟧ , ⟦s′⟧ , ze↘ , ze↘ , El-cumu (≤-trans (m≤n⊔m _ _) (m≤m⊔n _ n₃)) T≈T′₁ s≈s′
    helper {su a} {su b} (su a≈b)
      with helper a≈b
    ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
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
        ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N } = a≈b

        a′≈b′₃ : a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
        a′≈b′₃
          with Trel₃ (ρ≈ρ′₃ , a≈b₃)
        ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
            rewrite drop-↦ (ρ ↦ a) a′
                  | drop-↦ (ρ′ ↦ b) b′
                  | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₃
                  | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₃ = 𝕌-irrel T≈T′ T≈T′₃ a′≈b′

        helper-su : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) T (ρ ↦ su a) T (ρ′ ↦ su b))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , su a ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , su b ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-su
          with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃)
        ... | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ ⟦wk⟧) (⟦su⟧ (⟦v⟧ 1))) ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ ⟦wk⟧) (⟦su⟧ (⟦v⟧ 1))) ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            , record { ⟦t⟧ = _ ; ⟦t′⟧ = _ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                rewrite drop-↦ (ρ ↦ a) a′
                      | drop-↦ (ρ′ ↦ b) b′
                      | drop-↦ ρ a
                      | drop-↦ ρ′ b = record
                            { ⟦T⟧ = _
                            ; ⟦T′⟧ = _
                            ; ↘⟦T⟧ = ↘⟦T⟧
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
        ... | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N } = a≈b

        a≈b₁′ : {a b : D} → a ≈ b ∈ Nat → a ≈ b ∈ El _ (RelTyp.T≈T′ (Nrel₁ (ρ≈ρ′₁′ {a} {b})))
        a≈b₁′ {a} {b} a≈b
          with Nrel₁ (ρ≈ρ′₁′ {a} {b})
        ... | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N } = a≈b

        helper-ne : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) T (ρ ↦ ↑ N c) T (ρ′ ↦ ↑ N c′))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , ↑ N c ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , ↑ N c′ ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-ne
          with RelExp-refl (∷-cong ⊨Γ₁ Nrel₁) Trel₁ (ρ≈ρ′₁′ , a≈b₁′ (ne c≈c′)) | Trel₁ (ρ≈ρ′₁′ , a≈b₁′ (ne c≈c′))
        ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
             , record { ⟦t⟧ = _ ; ⟦t′⟧ = _ ; ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
             | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁₁ _ }
             , record { ⟦t⟧ = _ ; ⟦t′⟧ = _ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′₁ }
            with 𝕌-cumu (<⇒≤ i<n₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁) T≈T′) | 𝕌-cumu (<⇒≤ i<n₁₁) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁₁) T≈T′₁)
        ...    | T≈T′ | T≈T′₁
               with ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
        ...       | refl = record
                          { ⟦T⟧ = _
                          ; ⟦T′⟧ = _
                          ; ↘⟦T⟧ = ↘⟦T⟧
                          ; ↘⟦T′⟧ = ↘⟦T′⟧
                          ; T≈T′ = 𝕌-cumu (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ n₃)) T≈T′
                          }
                        , _ , _ , rec∙ ↘⟦T⟧₁ , rec∙ ↘⟦T′⟧₁ , El-cumu (≤-trans (m≤m⊔n n₁ n₂) (m≤m⊔n _ n₃)) T≈T′ (El-one-sided T≈T′₁ T≈T′ (realizability-Re T≈T′₁ bot-helper))
          where
            bot-helper : rec T (RelExp.⟦t⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r ρ c ≈ rec T′ (RelExp.⟦t′⟧ (proj₂ (s≈s′ ρ≈ρ′₂))) r′ ρ′ c′ ∈ Bot
            bot-helper ns κ
              with c≈c′ ns κ | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ (ne (Bot-l (head ns))))) | s≈s′ ρ≈ρ′₂ | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ ze))
            ...  | cc , c↘ , c′↘
                 | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ns _ }
                 , record { ⟦t⟧ = ⟦T⟧ns ; ⟦t′⟧ = ⟦T′⟧ns ; ↘⟦t⟧ = ↘⟦T⟧ns ; ↘⟦t′⟧ = ↘⟦T′⟧ns ; t≈t′ = T≈T′ns }
                 | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ⟦ze⟧) ↘⟦T⟧ze ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ⟦ze⟧) ↘⟦T′⟧ze ; T≈T′ = T≈T′ze }
                 , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = _ ; ↘⟦t′⟧ = _ ; t≈t′ = s≈s′ }
                 | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ze _ }
                 , record { ⟦t⟧ = ⟦T⟧ze₁ ; ⟦t′⟧ = ⟦T′⟧ze₁ ; ↘⟦t⟧ = ↘⟦T⟧ze₁ ; ↘⟦t′⟧ = ↘⟦T′⟧ze₁ ; t≈t′ = T≈T′ze₁ }
                with 𝕌-cumu (<⇒≤ i<n₁ns) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ns) T≈T′ns)
                   | 𝕌-cumu (<⇒≤ i<n₁ze) (subst (_ ≈ _ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<n₁ze) T≈T′ze₁)
            ...    | T≈T′ns
                   | T≈T′ze₁
                  with realizability-Re T≈T′ns (Bot-l (head ns))
            ...      | a′≈b′ = bot-helper′
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
                ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N } = ne (Bot-l (head ns))

                a′≈b′₃ : l′ ⟦T⟧ns (suc (head ns)) ≈ l′ ⟦T′⟧ns (suc (head ns)) ∈ El _ (RelTyp.T≈T′ (Trel₃ (ρ≈ρ′₃ , a≈b₃)))
                a′≈b′₃
                  with Trel₃ (ρ≈ρ′₃ , a≈b₃)
                ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ↘⟦T⟧₃ ; ↘⟦T′⟧ = ↘⟦T′⟧₃ ; T≈T′ = T≈T′₃ }
                    rewrite drop-↦ (ρ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T⟧ns (suc (head ns)))
                          | drop-↦ (ρ′ [ κ ] ↦ l′ N (head ns)) (l′ ⟦T′⟧ns (suc (head ns)))
                          | ⟦⟧-det ↘⟦T⟧ns ↘⟦T⟧₃ = El-one-sided T≈T′ns T≈T′₃ (realizability-Re T≈T′ns (Bot-l (suc (head ns))))

                bot-helper′ : ∃ λ u → Re ns - rec T ⟦s⟧ r ρ c [ κ ] ↘ u × Re ns - rec T′ ⟦s′⟧ r′ ρ′ c′ [ κ ] ↘ u
                bot-helper′
                  with r≈r′ ((ρ≈ρ′₃ , a≈b₃) , a′≈b′₃) | Trel₁ (ρ≈ρ′₁ κ , (a≈b₁ κ (su (ne (Bot-l (head ns))))))
                ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ ⟦wk⟧) (⟦su⟧ (⟦v⟧ 1))) ↘⟦T⟧su ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ ⟦wk⟧) (⟦su⟧ (⟦v⟧ 1))) ↘⟦T′⟧su ; T≈T′ = T≈T′su }
                     , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
                     | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁su _ }
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
                ...        | _ , RU _ Tns↘ , RU _ T′ns↘
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


-- -- -- rec-[]     : ∀ {i} →
-- -- --              Γ ⊨s σ ∶ Δ →
-- -- --              N ∺ Δ ⊨ T ∶ Se i →
-- -- --              Δ ⊨ s ∶ T [| ze ] →
-- -- --              T ∺ N ∺ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- -- --              Δ ⊨ t ∶ N →
-- -- --              -----------------------------------------------------------------------------------------------
-- -- --              Γ ⊨ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]

N-≈′ : ∀ {i} →
       ⊨ Γ →
       ----------------
       Γ ⊨ N ≈ N ∶ Se i
N-≈′ {_} {i} ⊨Γ = ⊨Γ , suc i , λ ρ≈ρ′ → record
                             { ⟦T⟧   = U _
                             ; ⟦T′⟧  = U _
                             ; ↘⟦T⟧  = ⟦Se⟧ _
                             ; ↘⟦T′⟧ = ⟦Se⟧ _
                             ; T≈T′  = U (n<1+n _) refl
                             }
                           , record
                             { ⟦t⟧   = N
                             ; ⟦t′⟧  = N
                             ; ↘⟦t⟧  = ⟦N⟧
                             ; ↘⟦t′⟧ = ⟦N⟧
                             ; t≈t′  = subst (_ ≈ _ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ (n<1+n _))) N
                             }

ze-≈′ : ⊨ Γ →
        ----------------
        Γ ⊨ ze ≈ ze ∶ N
ze-≈′ ⊨Γ = ⊨Γ , 0 , λ ρ≈ρ′ → record
                             { ⟦T⟧   = N
                             ; ⟦T′⟧  = N
                             ; ↘⟦T⟧  = ⟦N⟧
                             ; ↘⟦T′⟧ = ⟦N⟧
                             ; T≈T′  = N
                             }
                           , record
                             { ⟦t⟧   = ze
                             ; ⟦t′⟧  = ze
                             ; ↘⟦t⟧  = ⟦ze⟧
                             ; ↘⟦t′⟧ = ⟦ze⟧
                             ; t≈t′  = ze
                             }

su-≈′ : ⊨ Γ →
        Γ ⊨ t ≈ t′ ∶ N →
        ----------------
        Γ ⊨ su t ≈ su t′ ∶ N
su-≈′ {_} {t} {t′} ⊨Γ (⊨Γ₁ , n , t≈t′) = ⊨Γ , _ , helper
  where
    helper : {ρ ρ′ : Envs} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp n N ρ N ρ′) (λ rel → RelExp (su t) ρ (su t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
    helper ρ≈ρ′
      with t≈t′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
    ...  | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N }
         , record { ⟦t⟧ = _ ; ⟦t′⟧ = _ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                        { ⟦T⟧   = N
                        ; ⟦T′⟧  = N
                        ; ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = N
                        }
                      , record
                        { ⟦t⟧   = _
                        ; ⟦t′⟧  = _
                        ; ↘⟦t⟧  = ⟦su⟧ ↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦su⟧ ↘⟦t′⟧
                        ; t≈t′  = su t≈t′
                        }
  

-- -- su-cong′ : Γ ⊨ t ≈ t′ ∶ N →
-- --            ---------------------
-- --            Γ ⊨ su t ≈ su t′ ∶ N
-- -- su-cong′ {_} {t} {t′} (⊨Γ , t≈t′) = ⊨Γ , helper
-- --   where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp N ρ N ρ′) (λ rel → RelExp (su t) ρ (su t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
-- --         helper ρ≈ρ′
-- --           with t≈t′ ρ≈ρ′
-- --         ...  | record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ⟦N⟧ ; T≈T′ = _ , N }
-- --              , re = record
-- --                       { ⟦T⟧   = N
-- --                       ; ⟦T′⟧  = N
-- --                       ; ↘⟦T⟧  = ⟦N⟧
-- --                       ; ↘⟦T′⟧ = ⟦N⟧
-- --                       ; T≈T′  = 0 , N
-- --                       }
-- --                   , record
-- --                       { ⟦t⟧   = su re.⟦t⟧
-- --                       ; ⟦t′⟧  = su re.⟦t′⟧
-- --                       ; ↘⟦t⟧  = ⟦su⟧ re.↘⟦t⟧
-- --                       ; ↘⟦t′⟧ = ⟦su⟧ re.↘⟦t′⟧
-- --                       ; t≈t′  = su re.t≈t′
-- --                       }
-- --           where module re = RelExp re


-- -- -- rec-cong   : ∀ {i} →
-- -- --              N ∺ Γ ⊨ T ≈ T′ ∶ Se i →
-- -- --              Γ ⊨ s ≈ s′ ∶ T [ I , ze ] →
-- -- --              T ∺ N ∺ Γ ⊨ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- -- --              Γ ⊨ t ≈ t′ ∶ N →
-- -- --              --------------------------------------------
-- -- --              Γ ⊨ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
-- -- -- rec-β-ze   : ∀ {i} →
-- -- --              N ∺ Γ ⊨ T ∶ Se i →
-- -- --              Γ ⊨ s ∶ T [| ze ] →
-- -- --              T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- -- --              ---------------------------------------------
-- -- --              Γ ⊨ rec T s r ze ≈ s ∶ T [| ze ]
-- -- -- rec-β-su   : ∀ {i} →
-- -- --              N ∺ Γ ⊨ T ∶ Se i →
-- -- --              Γ ⊨ s ∶ T [| ze ] →
-- -- --              T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- -- --              Γ ⊨ t ∶ N →
-- -- --              -----------------------------------------------------------------
-- -- --              Γ ⊨ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
