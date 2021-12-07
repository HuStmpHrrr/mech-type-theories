{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Terms (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext


⊨-lookup-gen : ∀ {x}
               (Γ≈Δ : ⊨ Γ ≈ Δ) →
               x ∶ T ∈! Γ →
               x ∶ T′ ∈! Δ →
               ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ →
               --------------------------------------------------------
               Σ (RelTyp T ρ T′ ρ′) λ rel → RelExp (v x) ρ (v x) ρ′ (El∞ (RelTyp.T≈T′ rel))
⊨-lookup-gen {T = sub T _} {sub T′ _} {ρ} {ρ′} (∷-cong Γ≈Δ rel) here here (ρ≈ρ′ , ρ0≈ρ′0)
  = record
      { ⟦T⟧   = ⟦T⟧
      ; ⟦T′⟧  = ⟦T′⟧
      ; ↘⟦T⟧  = ⟦[]⟧ {!⟦wk⟧!} ↘⟦T⟧
      ; ↘⟦T′⟧ = ⟦[]⟧ {!!} ↘⟦T′⟧
      ; T≈T′  = T≈T′
      }
  , record
      { ⟦t⟧   = _
      ; ⟦t′⟧  = _
      ; ↘⟦t⟧  = ⟦v⟧ 0
      ; ↘⟦t′⟧ = ⟦v⟧ 0
      ; t≈t′  = ρ0≈ρ′0
      }
  where open RelTyp (rel ρ≈ρ′)
⊨-lookup-gen {T = sub T _} {sub T′ _} {ρ} {ρ′} (∷-cong Γ≈Δ rel) (there T∈Γ) (there T′∈Δ) (ρ≈ρ′ , _)
  with ⊨-lookup-gen Γ≈Δ T∈Γ T′∈Δ ρ≈ρ′
...  | rt , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
  = record
                   { ⟦T⟧   = ⟦T⟧
                   ; ⟦T′⟧  = ⟦T′⟧
                   ; ↘⟦T⟧  = ⟦[]⟧ {!!} ↘⟦T⟧
                   ; ↘⟦T′⟧ = ⟦[]⟧ {!!} ↘⟦T′⟧
                   ; T≈T′  = T≈T′
                   }
               , record
                   { ⟦t⟧   = _
                   ; ⟦t′⟧  = _
                   ; ↘⟦t⟧  = ⟦v⟧ _
                   ; ↘⟦t′⟧ = ⟦v⟧ _
                   ; t≈t′  = t≈t′
                   }
  where module rt = RelTyp rt
        open rt


⊨-lookup : ∀ {x}
           (⊨Γ : ⊨ Γ) →
           x ∶ T ∈! Γ →
           ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
           --------------------------------------------------------
           Σ (RelTyp T ρ T ρ′) λ rel → RelExp (v x) ρ (v x) ρ′ (El∞ (RelTyp.T≈T′ rel))
⊨-lookup ⊨Γ T∈Γ = ⊨-lookup-gen ⊨Γ T∈Γ T∈Γ


v-≈′ : ∀ {x} →
       ⊨ Γ →
       x ∶ T ∈! Γ →
       -----------------
       Γ ⊨ v x ≈ v x ∶ T
v-≈′ ⊨Γ T∈Γ = ⊨Γ , ⊨-lookup ⊨Γ T∈Γ


[]-cong′ : Δ ⊨ t ≈ t′ ∶ T →
           Γ ⊨s σ ≈ σ′ ∶ Δ →
           ---------------------------------
           Γ ⊨ (t [ σ ]) ≈ (t′ [ σ′ ]) ∶ (T [ σ ])
[]-cong′ {_} {t} {t′} {T} {_} {σ} {σ′} (⊨Δ , t≈t′) (⊨Γ , ⊨Δ₁ , σ≈σ′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (T [ σ ]) ρ (T [ σ ]) ρ′) (λ rel → RelExp (t [ σ ]) ρ (t′ [ σ′ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′ | ⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′
        ...  | ρ≈ρ | ρ′≈ρ
             with σ≈σ′ ρ≈ρ | σ≈σ′ ρ′≈ρ | σ≈σ′ ρ≈ρ′
        ...     | record { ⟦σ⟧ = ⟦σ⟧  ; ↘⟦σ⟧ = ↘⟦σ⟧  ; ↘⟦δ⟧ = ↘⟦σ′⟧  ; σ≈δ = ⟦σ≈σ′⟧ }
                | record { ⟦σ⟧ = ⟦σ⟧′ ; ↘⟦σ⟧ = ↘⟦σ⟧′ ; ↘⟦δ⟧ = ↘⟦σ′⟧′ ; σ≈δ = ⟦σ≈σ′⟧₁ }
                | record { ⟦σ⟧ = ⟦σ⟧″ ; ↘⟦σ⟧ = ↘⟦σ⟧″ ; ↘⟦δ⟧ = ↘⟦σ′⟧″ ; σ≈δ = ⟦σ≈σ′⟧₂ }
                rewrite ⟦⟧s-det ↘⟦σ′⟧ ↘⟦σ′⟧′
                      | ⟦⟧s-det ↘⟦σ⟧″ ↘⟦σ⟧
                with ⟦⟧ρ-trans′ ⊨Δ₁ ⟦σ≈σ′⟧ (⟦⟧ρ-sym′ ⊨Δ₁ ⟦σ≈σ′⟧₁)
        ...        | σ≈σ = help
          where help : Σ (RelTyp (T [ σ ]) ρ (T [ σ ]) ρ′) (λ rel → RelExp (t [ σ ]) ρ (t′ [ σ′ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ σ≈σ) | t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ ⟦σ≈σ′⟧₂)
                ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = _ , T≈T′ } , _
                    | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = _ , T≈T′₁ } , re
                    rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                      { ⟦T⟧   = ⟦T⟧
                      ; ⟦T′⟧  = ⟦T′⟧
                      ; ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧
                      ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T′⟧
                      ; T≈T′  = _ , T≈T′
                      }
                  , record
                      { ⟦t⟧   = ⟦t⟧
                      ; ⟦t′⟧  = ⟦t′⟧
                      ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦t⟧
                      ; ↘⟦t′⟧ = ⟦[]⟧ ↘⟦σ′⟧″ ↘⟦t′⟧
                      ; t≈t′  = El-one-sided T≈T′₁ T≈T′ re.t≈t′
                      }
                  where module re = RelExp re
                        open re


[I]′ : Γ ⊨ t ∶ T →
       --------------------
       Γ ⊨ (t [ I ]) ≈ t ∶ T
[I]′ {_} {t} {T} (⊨Γ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp T ρ T ρ′) (λ rel → RelExp (t [ I ]) ρ t ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨t ρ≈ρ′
        ...  | rt , re = rt
                       , record
                           { ⟦t⟧   = ⟦t⟧
                           ; ⟦t′⟧  = ⟦t′⟧
                           ; ↘⟦t⟧  = ⟦[]⟧ ⟦I⟧ ↘⟦t⟧
                           ; ↘⟦t′⟧ = ↘⟦t′⟧
                           ; t≈t′  = t≈t′
                           }
          where open RelExp re


-- [p]        : ∀ {x} →
--              Δ ⊨s σ ∶ S ∺ Γ →
--              x ∶ T ∈! Γ →
--              ---------------------------------------------
--              Δ ⊨ v x [ p σ ] ≈ v (suc x) [ σ ] ∶ T [ p σ ]


[∘]′ : Γ ⊨s τ ∶ Γ′ →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ″ ⊨ t ∶ T →
       ---------------------------------------------
       Γ ⊨ (t [ σ ∘ τ ]) ≈ (t [ σ ] [ τ ]) ∶ (T [ σ ∘ τ ])
[∘]′ {_} {τ} {_} {σ} {_} {t} {T} (⊨Γ , ⊨Γ′ , ⊨τ) (⊨Γ′₁ , ⊨Γ″ , ⊨σ) (⊨Γ″₁ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (T [ σ ∘ τ ]) ρ (T [ σ ∘ τ ]) ρ′) (λ rel → RelExp (t [ σ ∘ τ ]) ρ (t [ σ ] [ τ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′ = record
                        { ⟦T⟧   = rt.⟦T⟧
                        ; ⟦T′⟧  = rt.⟦T′⟧
                        ; ↘⟦T⟧  = ⟦[]⟧ (⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧) rt.↘⟦T⟧
                        ; ↘⟦T′⟧ = ⟦[]⟧ (⟦∘⟧ τ.↘⟦δ⟧ σ.↘⟦δ⟧) rt.↘⟦T′⟧
                        ; T≈T′  = rt.T≈T′
                        }
                    , record
                        { ⟦t⟧   = re.⟦t⟧
                        ; ⟦t′⟧  = re.⟦t′⟧
                        ; ↘⟦t⟧  = ⟦[]⟧ (⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧) re.↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦[]⟧ τ.↘⟦δ⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                        ; t≈t′  = re.t≈t′
                        }
          where module τ = RelSubsts (⊨τ ρ≈ρ′)
                module σ = RelSubsts (⊨σ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))
                ⊨tρ = ⊨t (⊨-irrel ⊨Γ″ ⊨Γ″₁ σ.σ≈δ)
                rt = proj₁ ⊨tρ
                re = proj₂ ⊨tρ
                module rt = RelTyp rt
                module re = RelExp re


[,]-v-ze′ : ∀ {i} →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ S ∶ Se i →
            Γ ⊨ s ∶ (S [ σ ]) →
            --------------------------------
            Γ ⊨ (v 0 [ σ , s ]) ≈ s ∶ (S [ σ ])
[,]-v-ze′ {_} {σ} {_} {S} {s} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (⊨Γ₁ , ⊨s) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (S [ σ ]) ρ (S [ σ ]) ρ′) (λ rel → RelExp (v 0 [ σ , s ]) ρ s ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp (S [ σ ]) ρ (S [ σ ]) ρ′) (λ rel → RelExp (v 0 [ σ , s ]) ρ s ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ) | ⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
                ...  | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = _ , U i<j _ }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧′ ; T≈T′ = T≈T′ }
                     , re
                     rewrite 𝕌-wellfounded-≡-𝕌 _ i<j
                           | ⟦⟧s-det ↘⟦σ⟧ σ.↘⟦σ⟧
                           | ⟦⟧s-det ↘⟦σ⟧′ σ.↘⟦δ⟧
                           | ⟦⟧-det ↘⟦t⟧ ↘⟦T⟧
                           | ⟦⟧-det ↘⟦t′⟧ ↘⟦T⟧′ = record
                                                    { ⟦T⟧   = ⟦T⟧
                                                    ; ⟦T′⟧  = ⟦T′⟧
                                                    ; ↘⟦T⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ↘⟦T⟧
                                                    ; ↘⟦T′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ ↘⟦T⟧′
                                                    ; T≈T′  = T≈T′
                                                    }
                                                , record
                                                    { ⟦t⟧   = re.⟦t⟧
                                                    ; ⟦t′⟧  = re.⟦t′⟧
                                                    ; ↘⟦t⟧  = ⟦[]⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) (⟦v⟧ 0)
                                                    ; ↘⟦t′⟧ = re.↘⟦t′⟧
                                                    ; t≈t′  = re.t≈t′
                                                    }
                  where module re = RelExp re


[,]-v-su′ : ∀ {i x} →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ S ∶ Se i →
            Γ ⊨ s ∶ (S [ σ ]) →
            x ∶ T ∈! Δ →
            ---------------------------------------------
            Γ ⊨ (v (suc x) [ σ , s ]) ≈ (v x [ σ ]) ∶ (T [ σ ])
[,]-v-su′ {_} {σ} {_} {S} {s} {T} {_} {x} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (⊨Γ₁ , ⊨s) T∈Δ = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (T [ σ ]) ρ (T [ σ ]) ρ′) (λ rel → RelExp (v (suc x) [ σ , s ]) ρ (v x [ σ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                module re = RelExp (proj₂ (⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)))
                help : Σ (RelTyp (T [ σ ]) ρ (T [ σ ]) ρ′) (λ rel → RelExp (v (suc x) [ σ , s ]) ρ (v x [ σ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with ⊨-lookup ⊨Δ T∈Δ σ.σ≈δ
                ... | rt′ , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
                    = record
                        { ⟦T⟧   = rt′.⟦T⟧
                        ; ⟦T′⟧  = rt′.⟦T′⟧
                        ; ↘⟦T⟧  = ⟦[]⟧ σ.↘⟦σ⟧ rt′.↘⟦T⟧
                        ; ↘⟦T′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ rt′.↘⟦T′⟧
                        ; T≈T′  = rt′.T≈T′
                        }
                    , record
                        { ⟦t⟧   = lookup σ.⟦σ⟧ x
                        ; ⟦t′⟧  = lookup σ.⟦δ⟧ x
                        ; ↘⟦t⟧  = ⟦[]⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) (⟦v⟧ _)
                        ; ↘⟦t′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ (⟦v⟧ _)
                        ; t≈t′  = t≈t′
                        }
                    where module rt′ = RelTyp rt′


≈-conv′ : ∀ {i} →
          Γ ⊨ s ≈ t ∶ S →
          Γ ⊨ S ≈ T ∶ Se i →
          --------------------
          Γ ⊨ s ≈ t ∶ T
≈-conv′ {_} {s} {t} {S} {T} (⊨Γ , s≈t) (⊨Γ₁ , S≈T) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp T ρ T ρ′) (λ rel → RelExp s ρ t ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with S≈T (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′) | S≈T (⟦⟧ρ-refl ⊨Γ ⊨Γ₁ ρ≈ρ′) | s≈t ρ≈ρ′
        ... | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = _ , U i<j _ }
            , record { ⟦t′⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦S⟧ ; ↘⟦t′⟧ = ↘⟦T⟧ ; t≈t′ = ⟦S≈T⟧ }
            | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = _ , U i<j′ _ }
            , record { ⟦t′⟧ = ⟦T⟧′ ; ↘⟦t⟧ = ↘⟦S⟧′ ; ↘⟦t′⟧ = ↘⟦T⟧′ ; t≈t′ = ⟦S≈T⟧′ }
            | record { ↘⟦T⟧ = ↘⟦S⟧″ ; ↘⟦T′⟧ = ↘⟦T⟧″ ; T≈T′ = _ , T≈T′ }
            , re
            rewrite 𝕌-wellfounded-≡-𝕌 _ i<j
                  | 𝕌-wellfounded-≡-𝕌 _ i<j′
                  | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                  | ⟦⟧-det ↘⟦S⟧″ ↘⟦S⟧ = record
                                          { ⟦T⟧   = ⟦T⟧′
                                          ; ⟦T′⟧  = ⟦T⟧
                                          ; ↘⟦T⟧  = ↘⟦T⟧′
                                          ; ↘⟦T′⟧ = ↘⟦T⟧
                                          ; T≈T′  = _ , 𝕌-trans (𝕌-sym ⟦S≈T⟧′) ⟦S≈T⟧
                                          }
                                      , record
                                          { ⟦t⟧   = ⟦t⟧
                                          ; ⟦t′⟧  = ⟦t′⟧
                                          ; ↘⟦t⟧  = ↘⟦t⟧
                                          ; ↘⟦t′⟧ = ↘⟦t′⟧
                                          ; t≈t′  = El-one-sided′ ⟦S≈T⟧ (𝕌-trans (𝕌-sym ⟦S≈T⟧′) ⟦S≈T⟧) (El-one-sided T≈T′ ⟦S≈T⟧ t≈t′)
                                          }
          where open RelExp re


≈-sym′ : Γ ⊨ t ≈ t′ ∶ T →
         ----------------
         Γ ⊨ t′ ≈ t ∶ T
≈-sym′ {_} {t} {t′} {T} (⊨Γ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp T ρ T ρ′) (λ rel → RelExp t′ ρ t ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with t≈t′ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
        ...  | rt , re = record
                           { ⟦T⟧   = ⟦T′⟧
                           ; ⟦T′⟧  = ⟦T⟧
                           ; ↘⟦T⟧  = ↘⟦T′⟧
                           ; ↘⟦T′⟧ = ↘⟦T⟧
                           ; T≈T′  = _ , 𝕌-sym (proj₂ T≈T′)
                           }
                       , record
                           { ⟦t⟧   = ⟦t′⟧
                           ; ⟦t′⟧  = ⟦t⟧
                           ; ↘⟦t⟧  = ↘⟦t′⟧
                           ; ↘⟦t′⟧ = ↘⟦t⟧
                           ; t≈t′  = El-sym (proj₂ T≈T′) (𝕌-sym (proj₂ T≈T′)) re.t≈t′
                           }
          where module rt = RelTyp rt
                module re = RelExp re
                open rt
                open re


≈-trans′ : Γ ⊨ t ≈ t′ ∶ T →
           Γ ⊨ t′ ≈ t″ ∶ T →
           ------ ------------
           Γ ⊨ t ≈ t″ ∶ T
≈-trans′ {_} {t} {t′} {T} {t″} (⊨Γ , t≈t′) (⊨Γ₁ , t′≈t″) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp T ρ T ρ′) (λ rel → RelExp t ρ t″ ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with t≈t′ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′) | t′≈t″ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ... | record { ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = _ , T≈T′ }
            , record { ⟦t⟧ = ⟦t⟧   ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
            | rt@record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = _ , T≈T′₁ }
            , record { ⟦t′⟧ = ⟦t″⟧ ; ↘⟦t⟧ = ↘⟦t′⟧₁ ; ↘⟦t′⟧ = ↘⟦t″⟧ ; t≈t′ = t′≈t″ }
            rewrite ⟦⟧-det ↘⟦t′⟧₁ ↘⟦t′⟧
                  | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′ = rt
                                      , record
                                          { ⟦t⟧   = ⟦t⟧
                                          ; ⟦t′⟧  = ⟦t″⟧
                                          ; ↘⟦t⟧  = ↘⟦t⟧
                                          ; ↘⟦t′⟧ = ↘⟦t″⟧
                                          ; t≈t′  = El-trans′ T≈T′₁ (El-one-sided T≈T′ T≈T′₁ t≈t′) t′≈t″
                                          }
