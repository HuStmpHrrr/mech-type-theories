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
    helper (ne {c} {c′} c≈c′) = {!!} -- helper-ne
      where
        ρ≈ρ′₃ : drop (ρ ↦ ↑ N c) ≈ drop (ρ′ ↦ ↑ N c′) ∈ ⟦ ⊨Γ₃ ⟧ρ
        ρ≈ρ′₃
          rewrite drop-↦ ρ (↑ N c)
                | drop-↦ ρ′ (↑ N c′) = ⊨-irrel ⊨Γ ⊨Γ₃ ρ≈ρ′

        ↑c≈↑c′₃ : ↑ N c ≈ ↑ N c′ ∈ El _ (RelTyp.T≈T′ (Nrel₃ ρ≈ρ′₃))
        ↑c≈↑c′₃
          with Nrel₃ ρ≈ρ′₃
        ... | record { ⟦T⟧ = _ ; ⟦T′⟧ = _ ; ↘⟦T⟧ = _ ; ↘⟦T′⟧ = _ ; T≈T′ = N } = ne c≈c′

        helper-ne : let module re = RelExp (proj₂ (s≈s′ ρ≈ρ′₂))
                    in Σ (RelTyp (n₁ ⊔ n₂ ⊔ n₃) T (ρ ↦ ↑ N c) T (ρ′ ↦ ↑ N c′))
                       λ rel → ∃₂ λ a′ b′ → rec∙ T , re.⟦t⟧ , r , ρ , ↑ N c ↘ a′
                                            × rec∙ T′ , re.⟦t′⟧ , r′ , ρ′ , ↑ N c′ ↘ b′
                                            × (a′ ≈ b′ ∈ El _ (RelTyp.T≈T′ rel))
        helper-ne = {!!}
        --   with Trel₃ (ρ≈ρ′₃ , ↑c≈↑c′₃)
        -- ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } = record
        --                   { ⟦T⟧ = _
        --                   ; ⟦T′⟧ = {!!}
        --                   ; ↘⟦T⟧ = ↘⟦T⟧
        --                   ; ↘⟦T′⟧ = ↘⟦T′⟧
        --                   ; T≈T′ = 𝕌-cumu {!!} T≈T′
        --                   }
        --                 , _ , _ , rec∙ ↘⟦T⟧ , rec∙ {!!} , realizability-Re (𝕌-cumu {!!} T≈T′) c≈c′ -- El-cumu (≤-trans {!m≤m⊔n _ _!} {!m≤m⊔n _ n₃!}) {!!} {!!}

-- -- -- rec-[]     : ∀ {i} →
-- -- --              Γ ⊨s σ ∶ Δ →
-- -- --              N ∺ Δ ⊨ T ∶ Se i →
-- -- --              Δ ⊨ s ∶ T [| ze ] →
-- -- --              T ∺ N ∺ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
-- -- --              Δ ⊨ t ∶ N →
-- -- --              -----------------------------------------------------------------------------------------------
-- -- --              Γ ⊨ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]

-- -- ze-≈′ : ⊨ Γ →
-- --         ----------------
-- --         Γ ⊨ ze ≈ ze ∶ N
-- -- ze-≈′ ⊨Γ = ⊨Γ , λ ρ≈ρ′ → record
-- --                            { ⟦T⟧   = N
-- --                            ; ⟦T′⟧  = N
-- --                            ; ↘⟦T⟧  = ⟦N⟧
-- --                            ; ↘⟦T′⟧ = ⟦N⟧
-- --                            ; T≈T′  = 0 , N
-- --                            }
-- --                        , record
-- --                            { ⟦t⟧   = ze
-- --                            ; ⟦t′⟧  = ze
-- --                            ; ↘⟦t⟧  = ⟦ze⟧
-- --                            ; ↘⟦t′⟧ = ⟦ze⟧
-- --                            ; t≈t′  = ze
-- --                            }


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
