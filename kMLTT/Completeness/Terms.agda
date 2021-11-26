{-# OPTIONS --without-K --safe #-}

open import Level using ()
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
      ; nat   = λ κ → ⟦[]⟧ {!!} (subst (⟦ T ⟧_↘ ⟦T⟧ [ κ ]) (drop-mon ρ κ) (nat κ))
      ; nat′  = λ κ → ⟦[]⟧ {!!} (subst (⟦ T′ ⟧_↘ ⟦T′⟧ [ κ ]) (drop-mon ρ′ κ) (nat′ κ))
      }
  , record
      { ⟦t⟧   = _
      ; ⟦t′⟧  = _
      ; ↘⟦t⟧  = ⟦v⟧ 0
      ; ↘⟦t′⟧ = ⟦v⟧ 0
      ; t≈t′  = ρ0≈ρ′0
      ; nat   = λ κ → ⟦v⟧ 0
      ; nat′  = λ κ → ⟦v⟧ 0
      }
  where open RelTyp (rel ρ≈ρ′)
⊨-lookup-gen {T = sub T _} {sub T′ _} {ρ} {ρ′} (∷-cong Γ≈Δ rel) (there T∈Γ) (there T′∈Δ) (ρ≈ρ′ , _)
  with ⊨-lookup-gen Γ≈Δ T∈Γ T′∈Δ ρ≈ρ′
...  | rt , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
  = record
                   { ⟦T⟧   = ⟦T⟧
                   ; ⟦T′⟧  = ⟦T′⟧
                   ; ↘⟦T⟧  = ⟦[]⟧ {!!} ↘⟦T⟧
                   ; ↘⟦T′⟧ = ⟦[]⟧ {!!} ↘⟦T′⟧
                   ; T≈T′  = T≈T′
                   ; nat   = λ κ → ⟦[]⟧ {!!} (subst (⟦ T ⟧_↘ ⟦T⟧ [ κ ]) (drop-mon ρ κ) (rt.nat κ))
                   ; nat′  = λ κ → ⟦[]⟧ {!!} (subst (⟦ T′ ⟧_↘ ⟦T′⟧ [ κ ]) (drop-mon ρ′ κ) (rt.nat′ κ))
                   }
               , record
                   { ⟦t⟧   = _
                   ; ⟦t′⟧  = _
                   ; ↘⟦t⟧  = ⟦v⟧ _
                   ; ↘⟦t′⟧ = ⟦v⟧ _
                   ; t≈t′  = t≈t′
                   ; nat   = λ κ → ⟦v⟧ _
                   ; nat′  = λ κ → ⟦v⟧ _
                   }
  where module rt = RelTyp rt
        open rt hiding (nat; nat′)


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
        ...     | record { ⟦σ⟧ = ⟦σ⟧  ; ↘⟦σ⟧ = ↘⟦σ⟧  ; ↘⟦δ⟧ = ↘⟦σ′⟧  ; σ≈δ = ⟦σ≈σ′⟧  ; nat = nat₁ }
                | record { ⟦σ⟧ = ⟦σ⟧′ ; ↘⟦σ⟧ = ↘⟦σ⟧′ ; ↘⟦δ⟧ = ↘⟦σ′⟧′ ; σ≈δ = ⟦σ≈σ′⟧₁ ; nat = nat₂ }
                | record { ⟦σ⟧ = ⟦σ⟧″ ; ↘⟦σ⟧ = ↘⟦σ⟧″ ; ↘⟦δ⟧ = ↘⟦σ′⟧″ ; σ≈δ = ⟦σ≈σ′⟧₂ ; nat′ = nat′₃ }
                rewrite ⟦⟧s-det ↘⟦σ′⟧ ↘⟦σ′⟧′
                      | ⟦⟧s-det ↘⟦σ⟧″ ↘⟦σ⟧
                with ⟦⟧ρ-trans′ ⊨Δ₁ ⟦σ≈σ′⟧ (⟦⟧ρ-sym′ ⊨Δ₁ ⟦σ≈σ′⟧₁)
        ...        | σ≈σ = help
          where help : Σ (RelTyp (T [ σ ]) ρ (T [ σ ]) ρ′) (λ rel → RelExp (t [ σ ]) ρ (t′ [ σ′ ]) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ σ≈σ) | t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ ⟦σ≈σ′⟧₂)
                ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = _ , T≈T′ ; nat = nat₄ ; nat′ = nat′₄ } , _
                    | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = _ , T≈T′₁ } , re
                    rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                      { ⟦T⟧   = ⟦T⟧
                      ; ⟦T′⟧  = ⟦T′⟧
                      ; ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧
                      ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T′⟧
                      ; T≈T′  = _ , T≈T′
                      ; nat   = λ κ → ⟦[]⟧ (nat₁ κ) (nat₄ κ)
                      ; nat′  = λ κ → ⟦[]⟧ (nat₂ κ) (nat′₄ κ)
                      }
                  , record
                      { ⟦t⟧   = ⟦t⟧
                      ; ⟦t′⟧  = ⟦t′⟧
                      ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦t⟧
                      ; ↘⟦t′⟧ = ⟦[]⟧ ↘⟦σ′⟧″ ↘⟦t′⟧
                      ; t≈t′  = El-one-sided T≈T′₁ T≈T′ re.t≈t′
                      ; nat   = λ κ → ⟦[]⟧ (nat₁ κ) (re.nat κ)
                      ; nat′  = λ κ → ⟦[]⟧ (nat′₃ κ) (re.nat′ κ)
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
                           ; nat   = λ κ → ⟦[]⟧ ⟦I⟧ (nat κ)
                           ; nat′  = nat′
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
                        ; nat   = λ κ → ⟦[]⟧ (⟦∘⟧ (τ.nat κ) (σ.nat κ)) (rt.nat κ)
                        ; nat′  = λ κ → ⟦[]⟧ (⟦∘⟧ (τ.nat′ κ) (σ.nat′ κ)) (rt.nat′ κ)
                        }
                    , record
                        { ⟦t⟧   = re.⟦t⟧
                        ; ⟦t′⟧  = re.⟦t′⟧
                        ; ↘⟦t⟧  = ⟦[]⟧ (⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧) re.↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦[]⟧ τ.↘⟦δ⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                        ; t≈t′  = re.t≈t′
                        ; nat   = λ κ → ⟦[]⟧ (⟦∘⟧ (τ.nat κ) (σ.nat κ)) (re.nat κ)
                        ; nat′  = λ κ → ⟦[]⟧ (τ.nat′ κ) (⟦[]⟧ (σ.nat′ κ) (re.nat′ κ))
                        }
          where module τ = RelSubsts (⊨τ ρ≈ρ′)
                module σ = RelSubsts (⊨σ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))
                ⊨tρ = ⊨t (⊨-irrel ⊨Γ″ ⊨Γ″₁ σ.σ≈δ)
                rt = proj₁ ⊨tρ
                re = proj₂ ⊨tρ
                module rt = RelTyp rt
                module re = RelExp re


-- [,]-v-ze   : ∀ {i} →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ S ∶ Se i →
--              Γ ⊨ s ∶ S [ σ ] →
--              --------------------------------
--              Γ ⊨ v 0 [ σ , s ] ≈ s ∶ S [ σ ]
-- [,]-v-su   : ∀ {i x} →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ S ∶ Se i →
--              Γ ⊨ s ∶ S [ σ ] →
--              x ∶ T ∈! Δ →
--              ---------------------------------------------
--              Γ ⊨ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]
-- ≈-conv     : ∀ {i} →
--              Γ ⊨ s ≈ t ∶ S →
--              Γ ⊨ S ≈ T ∶ Se i →
--              --------------------
--              Γ ⊨ s ≈ t ∶ T
-- ≈-sym      : Γ ⊨ t ≈ t′ ∶ T →
--              ----------------
--              Γ ⊨ t′ ≈ t ∶ T
-- ≈-trans    : Γ ⊨ t ≈ t′ ∶ T →
--              Γ ⊨ t′ ≈ t″ ∶ T →
--              ------ ------------
--              Γ ⊨ t ≈ t″ ∶ T
