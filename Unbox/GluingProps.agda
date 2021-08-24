{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.GluingProps (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Restricted
open import Unbox.Gluing
open import Unbox.StaticProps
open import Unbox.SemanticProps fext

-- basic properties of conversion from substitutions to untyped modal transformations

L-resp-mt : ∀ σ n → L σ n ≡ L (mt σ) n
L-resp-mt I n
  rewrite L-I n            = sym (L-vone n)
L-resp-mt (σ ∘ δ) n
  rewrite L-∘ n σ δ
        | L-ø (mt σ) (mt δ) n
        | L-resp-mt σ n    = L-resp-mt δ (L (mt σ) n)
L-resp-mt σ zero           = refl
L-resp-mt (p σ) (suc n)    = L-resp-mt σ (suc n)
L-resp-mt (σ , _) (suc n)  = L-resp-mt σ (suc n)
L-resp-mt (σ ； m) (suc n) = cong (m +_) (L-resp-mt σ n)

Tr-mt : ∀ σ n → mt (Tr σ n) ≡ Tr (mt σ) n
Tr-mt I n
  rewrite Tr-I n               = sym (Tr-vone n)
Tr-mt (σ ∘ δ) n
  rewrite Tr-∘ n σ δ
        | Tr-ø (mt σ) (mt δ) n
        | Tr-mt σ n
        | L-resp-mt σ n
        | Tr-mt δ (L (mt σ) n) = refl
Tr-mt σ zero                   = refl
Tr-mt (p σ) (suc n)            = Tr-mt σ (suc n)
Tr-mt (σ , _) (suc n)          = Tr-mt σ (suc n)
Tr-mt (σ ； m) (suc n)         = Tr-mt σ n

mt-resp-≈ : Ψ ⊢s σ ≈ δ ∶ Ψ′ → mt σ ≡ mt δ
mt-resp-≈ I-≈                               = refl
mt-resp-≈ (p-cong σ≈δ)                      = mt-resp-≈ σ≈δ
mt-resp-≈ (,-cong σ≈δ _)                    = mt-resp-≈ σ≈δ
mt-resp-≈ (；-cong Γs σ≈δ refl)             = cong (λ κ → ins κ (len Γs)) (mt-resp-≈ σ≈δ)
mt-resp-≈ (∘-cong σ≈δ σ′≈δ′)
  rewrite mt-resp-≈ σ≈δ
        | mt-resp-≈ σ′≈δ′                   = refl
mt-resp-≈ (∘-I _)                           = ø-vone _
mt-resp-≈ (I-∘ _)                           = vone-ø _
mt-resp-≈ {_} {σ ∘ σ′ ∘ σ″} (∘-assoc _ _ _) = ø-assoc (mt σ) (mt σ′) (mt σ″)
mt-resp-≈ (,-∘ _ _ _)                       = refl
mt-resp-≈ (p-∘ _ _)                         = refl
mt-resp-≈ {_} {σ ； _ ∘ δ} (；-∘ Γs _ _ refl)
  rewrite L-resp-mt δ (len Γs)
        | Tr-mt δ (len Γs)                  = ins-ø (len Γs) (mt σ) (mt δ)
mt-resp-≈ (p-, _ _)                         = refl
mt-resp-≈ (,-ext _)                         = refl
mt-resp-≈ {_} {σ} (；-ext _)
  rewrite L-resp-mt σ 1
        | +-identityʳ (mt σ 0)
        | Tr-mt σ 1                         = fext λ { zero    → refl
                                         ; (suc n) → refl }
mt-resp-≈ (s-≈-sym σ≈δ)                     = sym (mt-resp-≈ σ≈δ)
mt-resp-≈ (s-≈-trans σ≈σ′ σ′≈δ)             = trans (mt-resp-≈ σ≈σ′) (mt-resp-≈ σ′≈δ)

-- realizability of the gluing model

v∈Bot-gen : ∀ Γ″ {T} {Γ′} → Δ ∷ Δs ⊢r σ ∶ Γ ∷ Γs → Γ ≡ Γ″ ++ T ∷ Γ′ → Δ ∷ Δs ⊢ v (len Γ″) [ σ ] ≈ v (len Δ ∸ len Γ′ ∸ 1) ∶ T
v∈Bot-gen Γ″ {T} {Γ′} (r-I σ≈I) refl       = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈I)
                                             (≈-trans ([I] (vlookup (length-∈ Γ″))) helper)
  where eq : len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1 ≡ len Γ″
        eq = begin
          len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1
            ≡⟨ cong (λ n → n ∸ len Γ′ ∸ 1) (Lₚ.length-++ Γ″) ⟩
          len Γ″ + suc (len Γ′) ∸ len Γ′ ∸ 1
            ≡⟨ cong (_∸ 1) (ℕₚ.+-∸-assoc (len Γ″) {suc (len Γ′)} (ℕₚ.≤-step ℕₚ.≤-refl)) ⟩
          len Γ″ + (suc (len Γ′) ∸ len Γ′) ∸ 1
            ≡⟨ cong (λ n → len Γ″ + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (len Γ′)) ⟩
          len Γ″ + 1 ∸ 1
            ≡⟨ ℕₚ.m+n∸n≡m (len Γ″) 1 ⟩
          len Γ″
            ∎
          where open ≡-Reasoning

        helper : (Γ″ ++ T ∷ Γ′) ∷ _ ⊢ v (len Γ″) ≈ v (len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1) ∶ T
        helper rewrite eq = v-≈ (length-∈ Γ″)
v∈Bot-gen Γ″ (r-p {_} {_} {T} ⊢δ σ≈p) refl = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈p)
                                             (≈-trans ([p] (⊢r⇒⊢s ⊢δ) (length-∈ Γ″))
                                                      (v∈Bot-gen (T ∷ Γ″) ⊢δ refl))
v∈Bot-gen [] (r-； _ _ _ _) ()
v∈Bot-gen (_ ∷ _) (r-； _ _ _ _) ()

v∈Bot : ∀ T → v 0 ∼ l (len Γ) ∈ Bot T ((T ∷ Γ) ∷ Γs)
v∈Bot {Γ = Γ} T = record
  { t∶T  = vlookup here
  ; krip = λ {Ψ′} ⊢σ → record
    { neu = v (len (head Ψ′) ∸ len Γ ∸ 1)
    ; ↘ne = Rl (map len Ψ′) (len Γ)
    ; ≈ne = v∈Bot-gen [] ⊢σ refl
    }
  }

mutual
  Bot⊆《》 : ∀ T Ψ → t ∼ c ∈ Bot T Ψ → t ∼ ↑ T c ∈ 《 T 》T Ψ
  Bot⊆《》 B Ψ t∼c = bne t∼c
  Bot⊆《》 (S ⟶ T) Ψ t∼c = record
    { t∶⟶  = t∶T
    ; krip = λ {Ψ′} {σ} {s} {a} ⊢σ s∼a → record
      { fa   = [ T ] _ [ mt σ ] $′ ↓ S a
      ; ↘fa  = $∙ S T (_ [ mt σ ]) a
      ; rel  = Bot⊆《》 T Ψ′ record
        { t∶T  = ⟶-E (t[σ] t∶T (⊢r⇒⊢s ⊢σ)) (glu⇒⊢ _ s∼a)
        ; krip = λ {Ψ″} {δ} ⊢δ →
          let module krip  = BotPred (krip (⊢r-comp ⊢σ ⊢δ))
              module s∼a   = Top (《》⊆Top _ _ s∼a)
              module krip′ = TopPred (s∼a.krip ⊢δ)
          in record
          { neu = krip.neu $ krip′.nf
          ; ↘ne = R$ (map len Ψ″)
                     (subst (Re _ -_↘ krip.neu) (sym (Dn-comp _ (mt σ) (mt δ))) krip.↘ne)
                     krip′.↘nf
          ; ≈ne = ≈-trans ($-[] (⊢r⇒⊢s ⊢δ) (t[σ] t∶T (⊢r⇒⊢s ⊢σ)) (glu⇒⊢ _ s∼a))
                          ($-cong (≈-trans (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) t∶T)) krip.≈ne)
                                  krip′.≈nf)
          }
        }
      ; minv = λ κ → $∙ S T (_ [ mt σ ] [ κ ]) (a [ κ ])
      }
    }
    where open Bot t∼c
  Bot⊆《》 (□ T) Ψ t∼c = record
    { t∶□  = t∶T
    ; krip = λ {Ψ′} {σ} Γs ⊢σ → record
      { ua  = unbox′ T (len Γs) (mtran-c _ (mt σ))
      ; ↘ua = unbox∙ (len Γs)
      ; rel = Bot⊆《》 T (Γs ++⁺ Ψ′) record
        { t∶T  = □-E Γs (t[σ] t∶T (⊢r⇒⊢s ⊢σ)) refl
        ; krip = λ {Ψ″} {δ} ⊢δ →
          let Φ₁ , Φ₂ , eq , eql , Trδ = ⊢r-Tr′ Γs ⊢δ
              module krip = BotPred (krip (⊢r-comp ⊢σ Trδ))
          in record
          { neu = unbox (L (mt δ) (len Γs)) krip.neu
          ; ↘ne = Ru (map len Ψ″)
                     (L (mt δ) (len Γs))
                     (subst₂ (Re_-_↘ krip.neu)
                             (trans (sym (truncate-map Φ₁ eq eql)) (cong (truncate _) (L-resp-mt δ (len Γs))))
                             (trans (cong (λ κ → _ [ mt σ ø κ ]) (Tr-mt δ (len Γs))) (sym (Dn-comp _ (mt σ) (Tr (mt δ) (len Γs)))))
                             krip.↘ne)
          ; ≈ne = subst (λ n → Ψ″ ⊢ unbox (len Γs) (_ [ σ ]) [ δ ] ≈ unbox n (Ne⇒Exp krip.neu) ∶ T)
                    (L-resp-mt δ (len Γs))
                    (≈-trans (unbox-[] Γs (⊢r⇒⊢s ⊢δ) (t[σ] t∶T (⊢r⇒⊢s ⊢σ)) refl)
                    (subst (_⊢ _ ≈ unbox (L δ (len Γs)) (Ne⇒Exp krip.neu) ∶ T) (sym eq)
                             (unbox-cong Φ₁ (≈-trans (≈-sym ([∘] (⊢r⇒⊢s Trδ) (⊢r⇒⊢s ⊢σ) t∶T))
                                                     krip.≈ne)
                                         eql)))
          }
        }
      }
    }
    where open Bot t∼c

  《》⊆Top : ∀ T Ψ → t ∼ a ∈ 《 T 》T Ψ → t ∼ a ∈ Top T Ψ
  《》⊆Top B Ψ (bne t∼c) = record
    { t∶T  = t∶T
    ; krip = λ ⊢σ →
      let open BotPred (krip ⊢σ)
      in record
      { nf  = ne neu
      ; ↘nf = Rne _ ↘ne
      ; ≈nf = ≈ne
      }
    }
    where open Bot t∼c
  《》⊆Top (S ⟶ T) Ψ t∼a = record
    { t∶T  = t∶⟶
    ; krip = λ {Ψ′} {σ} ⊢σ →
      let open ap-rel (krip (⊢r-comp ⊢σ (r-p (r-I I-≈) (p-cong I-≈))) (Bot⊆《》 S ((S ∷ head Ψ′) ∷ tail Ψ′) (v∈Bot S)))
          module top = Top (《》⊆Top T _ rel)
          open TopPred (top.krip (r-I I-≈))
      in record
      { nf  = Λ nf
      ; ↘nf = RΛ _
                 (subst (λ κ → _ [ κ ] ∙ _ ↘ fa) (ø-vone _) ↘fa)
                 (subst (λ a → Rf _ - ↓ T a ↘ nf) (ap-vone fa) ↘nf)
      ; ≈nf = ≈-trans (⟶-η (t[σ] t∶⟶ (⊢r⇒⊢s ⊢σ)))
              (Λ-cong (≈-trans ($-cong (≈-sym ([∘] (S-p S-I) (⊢r⇒⊢s ⊢σ) t∶⟶)) (v-≈ here))
                      (≈-trans (≈-sym ([I] (⟶-E (t[σ] t∶⟶ (S-∘ (S-p S-I) (⊢r⇒⊢s ⊢σ))) (vlookup here))))
                               ≈nf)))
      }
    }
    where open Fun t∼a
  《》⊆Top (□ T) Ψ t∼a   = record
    { t∶T  = t∶□
    ; krip = λ {Ψ′} {σ} ⊢σ →
      let open unbox-rel (krip ([] ∷ []) ⊢σ)
          module top = Top (《》⊆Top T _ rel)
          open TopPred (top.krip (r-I I-≈))
      in record
      { nf  = box nf
      ; ↘nf = R□ _ ↘ua (subst (λ a → Rf _ - ↓ T a ↘ nf) (ap-vone ua) ↘nf)
      ; ≈nf = ≈-trans (□-η (t[σ] t∶□ (⊢r⇒⊢s ⊢σ)))
              (box-cong (≈-trans (≈-sym ([I] (□-E ([] ∷ []) (t[σ] t∶□ (⊢r⇒⊢s ⊢σ)) refl))) ≈nf))
      }
    }
    where open ■ t∼a
