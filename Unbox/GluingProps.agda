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
open import Unbox.StaticProps as Sₚ
open import Unbox.SemanticProps fext as Sem

-- basic properties of conversion from substitutions to untyped modal transformations

O-resp-mt : ∀ σ n → O σ n ≡ O (mt σ) n
O-resp-mt I n
  rewrite O-I n            = sym (O-vone n)
O-resp-mt (σ ∘ δ) n
  rewrite O-∘ n σ δ
        | O-ø (mt σ) (mt δ) n
        | O-resp-mt σ n    = O-resp-mt δ (O (mt σ) n)
O-resp-mt σ zero           = refl
O-resp-mt p (suc n)
  rewrite O-vone n         = refl
O-resp-mt (σ , _) (suc n)  = O-resp-mt σ (suc n)
O-resp-mt (σ ； m) (suc n) = cong (m +_) (O-resp-mt σ n)

Tr-mt : ∀ σ n → mt (Tr σ n) ≡ Tr (mt σ) n
Tr-mt I n
  rewrite Tr-I n               = sym (Tr-vone n)
Tr-mt (σ ∘ δ) n
  rewrite Tr-∘ n σ δ
        | Tr-ø (mt σ) (mt δ) n
        | Tr-mt σ n
        | O-resp-mt σ n
        | Tr-mt δ (O (mt σ) n) = refl
Tr-mt σ zero                   = refl
Tr-mt p (suc n)                = refl
Tr-mt (σ , _) (suc n)          = Tr-mt σ (suc n)
Tr-mt (σ ； m) (suc n)         = Tr-mt σ n

-- this lemma is not needed. however, this lemma shows nicely the syntax for substitutions is defined.
mt-resp-≈ : Ψ ⊢s σ ≈ δ ∶ Ψ′ → mt σ ≡ mt δ
mt-resp-≈ I-≈                               = refl
mt-resp-≈ p-≈                               = refl
mt-resp-≈ (,-cong σ≈δ _)                    = mt-resp-≈ σ≈δ
mt-resp-≈ (；-cong Γs σ≈δ refl)             = cong (λ κ → ins κ (len Γs)) (mt-resp-≈ σ≈δ)
mt-resp-≈ (∘-cong σ≈δ σ′≈δ′)
  rewrite mt-resp-≈ σ≈δ
        | mt-resp-≈ σ′≈δ′                   = refl
mt-resp-≈ (∘-I _)                           = ø-vone _
mt-resp-≈ (I-∘ _)                           = vone-ø _
mt-resp-≈ {_} {σ ∘ σ′ ∘ σ″} (∘-assoc _ _ _) = ø-assoc (mt σ) (mt σ′) (mt σ″)
mt-resp-≈ (,-∘ _ _ _)                       = refl
mt-resp-≈ {_} {σ ； _ ∘ δ} (；-∘ Γs _ _ refl)
  rewrite O-resp-mt δ (len Γs)
        | Tr-mt δ (len Γs)                  = ins-ø (len Γs) (mt σ) (mt δ)
mt-resp-≈ (p-, _ _)                         = vone-ø _
mt-resp-≈ (,-ext _)                         = sym (vone-ø _)
mt-resp-≈ {_} {σ} (；-ext _)
  rewrite O-resp-mt σ 1
        | +-identityʳ (mt σ 0)
        | Tr-mt σ 1                         = fext λ { zero    → refl
                                         ; (suc n) → refl }
mt-resp-≈ (s-≈-sym σ≈δ)                     = sym (mt-resp-≈ σ≈δ)
mt-resp-≈ (s-≈-trans σ≈σ′ σ′≈δ)             = trans (mt-resp-≈ σ≈σ′) (mt-resp-≈ σ′≈δ)

-- realizability of the gluing model
var-arith : ∀ Γ″ (T : Typ) Γ′ → len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1 ≡ len Γ″
var-arith Γ″ T Γ′ = begin
  len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1
    ≡⟨ cong (λ n → n ∸ len Γ′ ∸ 1) (Lₚ.length-++ Γ″) ⟩
  len Γ″ + suc (len Γ′) ∸ len Γ′ ∸ 1
    ≡⟨ cong (_∸ 1) (ℕₚ.+-∸-assoc (len Γ″) {suc (len Γ′)} (ℕₚ.m≤n⇒m≤1+n ℕₚ.≤-refl)) ⟩
  len Γ″ + (suc (len Γ′) ∸ len Γ′) ∸ 1
    ≡⟨ cong (λ n → len Γ″ + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (len Γ′)) ⟩
  len Γ″ + 1 ∸ 1
    ≡⟨ ℕₚ.m+n∸n≡m (len Γ″) 1 ⟩
  len Γ″
    ∎
  where open ≡-Reasoning

var-arith′ : ∀ Γ″ (T : Typ) Γ′ → len (Γ″ ++ T ∷ Γ′) ∸ len Γ″ ∸ 1 ≡ len Γ′
var-arith′ Γ″ T Γ′ = begin
  len (Γ″ ++ T ∷ Γ′) ∸ len Γ″ ∸ 1
    ≡⟨ cong (λ n → n ∸ len Γ″ ∸ 1) (Lₚ.length-++ Γ″) ⟩
  len Γ″ + suc (len Γ′) ∸ len Γ″ ∸ 1
    ≡⟨ cong (_∸ 1) (m+n∸m≡n (len Γ″) (suc (len Γ′))) ⟩
  len Γ′
    ∎
  where open ≡-Reasoning

v∈Bot-gen : ∀ Γ″ {T} {Γ′} → Δ ∷ Δs ⊢r σ ∶ Γ ∷ Γs → Γ ≡ Γ″ ++ T ∷ Γ′ → Δ ∷ Δs ⊢ v (len Γ″) [ σ ] ≈ v (len Δ ∸ len Γ′ ∸ 1) ∶ T
v∈Bot-gen Γ″ {T} {Γ′} (r-I σ≈I) refl       = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈I)
                                             (≈-trans ([I] (vlookup (length-∈ Γ″))) helper)
  where helper : (Γ″ ++ T ∷ Γ′) ∷ _ ⊢ v (len Γ″) ≈ v (len (Γ″ ++ T ∷ Γ′) ∸ len Γ′ ∸ 1) ∶ T
        helper
          rewrite var-arith Γ″ T Γ′ = v-≈ (length-∈ Γ″)
v∈Bot-gen Γ″ (r-p {_} {_} {T} ⊢δ σ≈p) refl = ≈-trans ([]-cong (v-≈ (length-∈ Γ″)) σ≈p)
                                             (≈-trans ([∘] (⊢r⇒⊢s ⊢δ) S-p (vlookup (length-∈ Γ″)))
                                             (≈-trans ([]-cong ([p] (length-∈ Γ″)) (s≈-refl (⊢r⇒⊢s ⊢δ)))
                                                      (v∈Bot-gen (T ∷ Γ″) ⊢δ refl)))
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
          { neu = unbox (O (mt δ) (len Γs)) krip.neu
          ; ↘ne = Ru (map len Ψ″)
                     (O (mt δ) (len Γs))
                     (subst₂ (Re_-_↘ krip.neu)
                             (trans (sym (drop+-map Φ₁ eq eql)) (cong (Tr _) (O-resp-mt δ (len Γs))))
                             (trans (cong (λ κ → _ [ mt σ ø κ ]) (Tr-mt δ (len Γs))) (sym (Dn-comp _ (mt σ) (Tr (mt δ) (len Γs)))))
                             krip.↘ne)
          ; ≈ne = subst (λ n → Ψ″ ⊢ unbox (len Γs) (_ [ σ ]) [ δ ] ≈ unbox n (Ne⇒Exp krip.neu) ∶ T)
                    (O-resp-mt δ (len Γs))
                    (≈-trans (unbox-[] Γs (⊢r⇒⊢s ⊢δ) (t[σ] t∶T (⊢r⇒⊢s ⊢σ)) refl)
                    (subst (_⊢ _ ≈ unbox (O δ (len Γs)) (Ne⇒Exp krip.neu) ∶ T) (sym eq)
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
      let open ap-rel (krip (⊢r-comp ⊢σ (r-p (r-I I-≈) (s-≈-sym (∘-I S-p)))) (Bot⊆《》 S ((S ∷ head Ψ′) ∷ tail Ψ′) (v∈Bot S)))
          module top = Top (《》⊆Top T _ rel)
          open TopPred (top.krip (r-I I-≈))
      in record
      { nf  = Λ nf
      ; ↘nf = RΛ _
                 (subst (λ κ → _ [ κ ] ∙ _ ↘ fa) (ø-vone _) ↘fa)
                 (subst (λ a → Rf _ - ↓ T a ↘ nf) (ap-vone fa) ↘nf)
      ; ≈nf = ≈-trans (⟶-η (t[σ] t∶⟶ (⊢r⇒⊢s ⊢σ)))
              (Λ-cong (≈-trans ($-cong (≈-sym ([∘] S-p (⊢r⇒⊢s ⊢σ) t∶⟶)) (v-≈ here))
                      (≈-trans (≈-sym ([I] (⟶-E (t[σ] t∶⟶ (S-∘ S-p (⊢r⇒⊢s ⊢σ))) (vlookup here))))
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

-- properties of the gluing model

《》-resp-≈ : ∀ T → t ∼ a ∈ 《 T 》T Ψ → Ψ ⊢ t′ ≈ t ∶ T → t′ ∼ a ∈ 《 T 》T Ψ
《》-resp-≈ B (bne t∼c) t′≈t = bne record
  { t∶T  = proj₁ (presup t′≈t)
  ; krip = λ ⊢σ →
    let open BotPred (krip ⊢σ)
    in record
    { neu = neu
    ; ↘ne = ↘ne
    ; ≈ne = ≈-trans ([]-cong t′≈t (s≈-refl (⊢r⇒⊢s ⊢σ))) ≈ne
    }
  }
  where open Bot t∼c
《》-resp-≈ (S ⟶ T) t∼a t′≈t = record
  { t∶⟶  = proj₁ (presup t′≈t)
  ; krip = λ ⊢σ s∼a →
    let open ap-rel (krip ⊢σ s∼a)
    in record
    { fa   = fa
    ; ↘fa  = ↘fa
    ; rel  = 《》-resp-≈ T rel ($-cong ([]-cong t′≈t (s≈-refl (⊢r⇒⊢s ⊢σ))) (≈-refl (glu⇒⊢ S s∼a)))
    }
  }
  where open Fun t∼a
《》-resp-≈ (□ T) t∼a t′≈t   = record
  { t∶□  = proj₁ (presup t′≈t)
  ; krip = λ Γs ⊢σ →
    let open unbox-rel (krip Γs ⊢σ)
    in record
    { ua  = ua
    ; ↘ua = ↘ua
    ; rel = 《》-resp-≈ T rel (unbox-cong Γs ([]-cong t′≈t (s≈-refl (⊢r⇒⊢s ⊢σ))) refl)
    }
  }
  where open ■ t∼a

《》-mon : ∀ T → Ψ ⊢r σ ∶ Ψ′ → t ∼ a ∈ 《 T 》T Ψ′ → t [ σ ] ∼ a [ mt σ ] ∈ 《 T 》T Ψ
《》-mon {_} {σ} B ⊢σ (bne t∼c) = bne record
  { t∶T  = t[σ] t∶T (⊢r⇒⊢s ⊢σ)
  ; krip = λ {_} {δ} ⊢δ →
    let open BotPred (krip (⊢r-comp ⊢σ ⊢δ))
    in record
    { neu = neu
    ; ↘ne = subst (Re _ -_↘ neu) (sym (Dn-comp _ (mt σ) (mt δ))) ↘ne
    ; ≈ne = ≈-trans (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) t∶T)) ≈ne
    }
  }
  where open Bot t∼c
《》-mon {_} {σ} (S ⟶ T) ⊢σ t∼f = record
  { t∶⟶  = t[σ] t∶⟶ (⊢r⇒⊢s ⊢σ)
  ; krip = λ {_} {δ} ⊢δ s∼a →
    let open ap-rel (krip (⊢r-comp ⊢σ ⊢δ) s∼a)
    in record
    { fa   = fa
    ; ↘fa  = subst (_∙ _ ↘ fa) (sym (D-comp _ (mt σ) (mt δ))) ↘fa
    ; rel  = 《》-resp-≈ T rel ($-cong (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) t∶⟶)) (≈-refl (glu⇒⊢ _ s∼a)))
    }
  }
  where open Fun t∼f
《》-mon {_} {σ} (□ T) ⊢σ t∼a   = record
  { t∶□  = t[σ] t∶□ (⊢r⇒⊢s ⊢σ)
  ; krip = λ {_} {δ} Γs ⊢δ →
    let open unbox-rel (krip Γs (⊢r-comp ⊢σ ⊢δ))
    in record
    { ua  = ua
    ; ↘ua = subst (unbox∙ _ ,_↘ ua) (sym (D-comp _ (mt σ) (mt δ))) ↘ua
    ; rel = 《》-resp-≈ T rel (unbox-cong Γs (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) (⊢r⇒⊢s ⊢σ) t∶□)) refl)
    }
  }
  where open ■ t∼a

O-《》 : ∀ n Γs → σ ∼ ρ ∈ 《 Γs 》Γs Ψ → n < len Γs → O σ n ≡ O ρ n
O-《》 zero Γs σ∼ρ n<                         = refl
O-《》 {σ} (suc n) (Γ ∷ Γ′ ∷ Γs) σ∼ρ (s≤s n<) = trans (Sₚ.O-+ σ 1 n)
                                                     (cong₂ _+_ Leq (O-《》 n (Γ′ ∷ Γs) rel n<))
  where open Cons σ∼ρ

Tr-《》 : ∀ Γs → σ ∼ ρ ∈ 《 Γs ++⁺ Ψ 》Ψ Ψ′ → ∃₂ λ Φ₁ Φ₂ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ O σ (len Γs) × (Tr σ (len Γs) ∼ Tr ρ (len Γs) ∈ 《 Ψ 》Ψ Φ₂)
Tr-《》 [] σ∼ρ           = [] , _ , refl , refl , σ∼ρ
Tr-《》 {σ} (Γ ∷ Γs) σ∼ρ = let Φ₁ , Φ₂ , eq , eql , rel′ = Tr-《》 Γs rel
                          in hds ++ Φ₁ , Φ₂
                           , trans Ψ≡ (trans (cong (hds ++⁺_) eq) (sym (++-++⁺ hds)))
                           , trans (length-++ hds) (trans (cong₂ _+_ (trans len≡ (sym Leq)) eql) (sym (Sₚ.O-+ σ 1 (len Γs))))
                           , subst (_∼ _ ∈ 《 _ 》Ψ Φ₂) (sym (Sₚ.Tr-+ σ 1 (len Γs))) rel′
  where open Cons σ∼ρ

《》-resp-≈s : ∀ Γs → σ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ′ → Ψ′ ⊢s σ′ ≈ σ ∶ Γ ∷ Γs → σ′ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ′
《》-resp-≈s [] σ∼ρ σ′≈σ                    = record
  { σ-wf  = proj₁ (presup-s σ′≈σ)
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (vlkup T∈Γ) ([]-cong (v-≈ T∈Γ) σ′≈σ)
  }
  where open Single σ∼ρ
《》-resp-≈s {_} {_} {Γ} (Γ′ ∷ Γs) σ∼ρ σ′≈σ =
  let Φ₁ , Φ₂ , eq , eql , Trσ′≈ = Tr-resp-≈′ (Γ ∷ []) σ′≈σ
  in record
  { σ-wf  = proj₁ (presup-s σ′≈σ)
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (vlkup T∈Γ) ([]-cong (v-≈ T∈Γ) σ′≈σ)
  ; Leq   = trans (O-resp-≈ 1 σ′≈σ) Leq
  ; hds   = hds
  ; Ψ|ρ0  = Ψ|ρ0
  ; Ψ≡    = Ψ≡
  ; len≡  = len≡
  ; rel   = 《》-resp-≈s Γs rel
                       (subst (_⊢s _ ≈ _ ∶ _)
                              (++⁺-cancelˡ′ Φ₁ hds
                                           (trans (sym eq) Ψ≡)
                                           (trans eql
                                           (trans (O-resp-≈ 1 σ′≈σ)
                                           (trans Leq
                                                  (sym len≡) ))))
                              Trσ′≈)
  }
  where open Cons σ∼ρ

《》Ψ-mon : ∀ Γs → Ψ″ ⊢r δ ∶ Ψ′ →  σ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ′ → σ ∘ δ ∼ ρ [ mt δ ] ∈ 《 Γ ∷ Γs 》Ψ Ψ″
《》Ψ-mon {_} {δ} {_} {σ} [] ⊢δ σ∼ρ           = record
  { σ-wf  = S-∘ (⊢r⇒⊢s ⊢δ) σ-wf
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (《》-mon _ ⊢δ (vlkup T∈Γ)) ([∘] (⊢r⇒⊢s ⊢δ) σ-wf (vlookup T∈Γ))
  }
  where open Single σ∼ρ
《》Ψ-mon {_} {δ} {_} {σ} {ρ} (Γ′ ∷ Γs) ⊢δ σ∼ρ =
  let Φ₁ , Φ₂ , eq , eql , Trδ = ⊢r-Tr′ hds (subst (_ ⊢r _ ∶_) Ψ≡ ⊢δ)
  in record
  { σ-wf  = S-∘ (⊢r⇒⊢s ⊢δ) σ-wf
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (《》-mon _ ⊢δ (vlkup T∈Γ)) ([∘] (⊢r⇒⊢s ⊢δ) σ-wf (vlookup T∈Γ))
  ; Leq   = trans (O-resp-mt δ (O σ 1)) (cong (O (mt δ)) Leq)
  ; hds   = Φ₁
  ; Ψ|ρ0  = Φ₂
  ; Ψ≡    = eq
  ; len≡  = trans eql (trans (O-resp-mt δ (len hds)) (cong (O (mt δ)) len≡))
  ; rel   = subst₂ (λ n ρ′ → Tr σ 1 ∘ Tr δ n ∼ ρ′ ∈ 《 Γ′ ∷ Γs 》Γs Φ₂)
                   (trans len≡ (sym Leq))
                   (sym (trans (Tr-ρ-[] ρ (mt δ) 1)
                               (cong (Tr ρ 1 [_])
                                     (trans (cong (Tr (mt δ)) (trans (+-identityʳ _) (sym len≡)))
                                            (sym (Tr-mt δ (len hds)))))))
                   (《》Ψ-mon Γs Trδ rel)
  }
  where open Cons σ∼ρ

rel-↦ : ∀ ρ → σ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ′ → s ∼ a ∈ 《 T 》T Ψ′ → σ , s ∼ ρ ↦ a ∈ 《 (T ∷ Γ) ∷ Γs 》Ψ Ψ′
rel-↦ {_} {_} {[]} ρ σ∼ρ s∼a      = record
  { σ-wf  = S-, (glu⇒⊢s σ∼ρ) (glu⇒⊢ _ s∼a)
  ; vlkup = λ { here        → 《》-resp-≈ _ s∼a (v-ze (glu⇒⊢s σ∼ρ) (glu⇒⊢ _ s∼a))
              ; (there T∈Γ) → 《》-resp-≈ _ (vlkup T∈Γ) (v-su (glu⇒⊢s σ∼ρ) (glu⇒⊢ _ s∼a) T∈Γ) }
  }
  where open Single σ∼ρ
rel-↦ {_} {_} {Γ′ ∷ Γs} ρ σ∼ρ s∼a =
  let ⊢σ = glu⇒⊢s σ∼ρ
  in record
  { σ-wf  = S-, ⊢σ (glu⇒⊢ _ s∼a)
  ; vlkup = λ { here        → 《》-resp-≈ _ s∼a (v-ze ⊢σ (glu⇒⊢ _ s∼a))
              ; (there T∈Γ) → 《》-resp-≈ _ (vlkup T∈Γ) (v-su ⊢σ (glu⇒⊢ _ s∼a) T∈Γ) }
  ; Leq   = Leq
  ; hds   = hds
  ; Ψ|ρ0  = Ψ|ρ0
  ; Ψ≡    = Ψ≡
  ; len≡  = len≡
  ; rel   = rel
  }
  where open Cons σ∼ρ

rel-ext : ∀ Δs ρ → σ ∼ ρ ∈ 《 Ψ 》Ψ Ψ′ → σ ； len Δs ∼ ext ρ (len Δs) ∈ 《 [] ∷⁺ Ψ 》Ψ (Δs ++⁺ Ψ′)
rel-ext Δs ρ σ∼ρ = record
  { σ-wf  = S-； Δs ⊢σ refl
  ; vlkup = λ ()
  ; Leq   = +-identityʳ _
  ; hds   = Δs
  ; Ψ|ρ0  = _
  ; Ψ≡    = refl
  ; len≡  = refl
  ; rel   = σ∼ρ
  }
  where ⊢σ = glu⇒⊢s σ∼ρ
