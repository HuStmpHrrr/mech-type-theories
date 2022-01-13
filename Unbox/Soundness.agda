{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.Soundness (fext : Extensionality 0ℓ 0ℓ) where

open import Lib

open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Restricted
open import Unbox.Gluing
open import Unbox.StaticProps
open import Unbox.SemanticProps fext
open import Unbox.GluingProps fext

lookup-Init : ∀ {x} → x ∶ T ∈ Γ → InitialEnv Γ x ≡ l′ T (len Γ ∸ x ∸ 1)
lookup-Init here        = refl
lookup-Init (there T∈Γ) = lookup-Init T∈Γ

private
  I∼Inits-helper : ∀ {x} → x ∶ T ∈ Γ → v x [ I ] ∼ InitialEnv Γ x ∈ 《 T 》T (Γ ∷ Γs)
  I∼Inits-helper {T} {Γ} {Γs} T∈Γ
    with split-∈ T∈Γ
  ...  | Γ′ , Γ″ , refl , refl
       rewrite lookup-Init T∈Γ = Bot⊆《》 _ (Γ ∷ Γs) record
       { t∶T  = t[σ] (vlookup (length-∈ Γ′)) S-I
       ; krip = λ {Ψ′} {σ} ⊢σ → record
         { neu = v _
         ; ↘ne = Rl _ _
         ; ≈ne = subst (λ n → _ ⊢ v (len Γ′) [ I ] [ σ ] ≈ v (len (head Ψ′) ∸ n ∸ 1) ∶ T)
                       (sym (var-arith′ Γ′ T Γ″))
                       (≈-trans (≈-sym ([∘] (⊢r⇒⊢s ⊢σ) S-I (vlookup (length-∈ Γ′)))) (v∈Bot-gen _ (⊢r-comp (r-I I-≈) ⊢σ) refl))
         }
       }

I∼Inits-gen : ∀ Γ Γs → I ∼ InitialEnvs (Γ ∷ Γs) ∈ 《 Γ ∷ Γs 》Ψ (Γ ∷ Γs)
I∼Inits-gen Γ [] = record
  { σ-wf  = S-I
  ; vlkup = I∼Inits-helper
  }
I∼Inits-gen Γ (Γ′ ∷ Γs) = record
  { σ-wf  = S-I
  ; vlkup = I∼Inits-helper
  ; Leq   = refl
  ; hds   = Γ ∷ []
  ; Ψ|ρ0  = Γ′ ∷ Γs
  ; Ψ≡    = refl
  ; len≡  = refl
  ; rel   = I∼Inits-gen Γ′ Γs
  }

I∼Inits : ∀ Ψ → I ∼ InitialEnvs (toList Ψ) ∈ 《 Ψ 》Ψ Ψ
I∼Inits Ψ = I∼Inits-gen _ _

⊩⇒⊢ : Ψ ⊩ t ∶ T → Ψ ⊢ t ∶ T
⊩⇒⊢ ⊩t = helper (glu⇒⊢ _ tσ∼)
       where open Intp (⊩t  _ _ (I∼Inits _))
             helper : Ψ ⊢ t [ I ] ∶ T → Ψ ⊢ t ∶ T
             helper (t[σ] t∶T S-I) = t∶T

⊩s⇒⊢s : Ψ ⊩s σ ∶ Ψ′ → Ψ ⊢s σ ∶ Ψ′
⊩s⇒⊢s ⊩σ = helper (glu⇒⊢s comp)
  where open Intps (⊩σ _ _ (I∼Inits _))
        helper : Ψ ⊢s σ ∘ I ∶ Ψ′ → Ψ ⊢s σ ∶ Ψ′
        helper (S-∘ S-I ⊢σ) = ⊢σ

vlookup′ : ∀ {x} →
           x ∶ T ∈ Γ →
           ----------------
           Γ ∷ Γs ⊩ v x ∶ T
vlookup′ T∈Γ σ ρ σ∼ρ = record
  { ⟦t⟧  = lookup ρ _
  ; ↘⟦t⟧ = ⟦v⟧ _
  ; tσ∼  = glu⇒vlookup σ∼ρ T∈Γ
  }


⟶-I′ : (S ∷ Γ) ∷ Γs ⊩ t ∶ T →
       ----------------------
       Γ ∷ Γs ⊩ Λ t ∶ S ⟶ T
⟶-I′ {t = t} ⊩t σ ρ σ∼ρ =
  let ⊢σ = glu⇒⊢s σ∼ρ
      ⊢t = ⊩⇒⊢ ⊩t
  in record
  { ⟦t⟧  = Λ _ ρ
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; tσ∼  = record
    { t∶⟶  = t[σ] (⟶-I ⊢t) ⊢σ
    ; krip = λ ⊢δ s∼a →
      let ⊢s = glu⇒⊢ _ s∼a
          open Intp (⊩t _ _ (rel-↦ _ (《》Ψ-mon _ ⊢δ σ∼ρ) s∼a))
      in record
      { fa   = ⟦t⟧
      ; ↘fa  = Λ∙ ↘⟦t⟧
      ; rel  = 《》-resp-≈ _ tσ∼
                         (≈-trans ($-cong (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) ⊢σ (⟶-I ⊢t))) (≈-refl ⊢s))
                         (≈-trans ($-cong (Λ-[] (S-∘ (⊢r⇒⊢s ⊢δ) ⊢σ) ⊢t) (≈-refl ⊢s))
                         (≈-trans (⟶-β (t[σ] ⊢t (⊢q (S-∘ (⊢r⇒⊢s ⊢δ) ⊢σ) _)) ⊢s)
                         (≈-trans (≈-sym ([∘] (S-, S-I ⊢s) (⊢q (S-∘ (⊢r⇒⊢s ⊢δ) ⊢σ) _) ⊢t))
                                  ([]-cong (≈-refl ⊢t) (⊢q∘I, (S-∘ (⊢r⇒⊢s ⊢δ) ⊢σ) ⊢s))))))
      }
    }
  }

⟶-E′ : Ψ ⊩ t ∶ S ⟶ T →
       Ψ ⊩ s ∶ S →
       -------------
       Ψ ⊩ t $ s ∶ T
⟶-E′ ⊩t ⊩s σ ρ σ∼ρ =
  let ⊢σ = glu⇒⊢s σ∼ρ
      ⊢t = ⊩⇒⊢ ⊩t
      ⊢s = ⊩⇒⊢ ⊩s
  in record
          { ⟦t⟧  = fa
          ; ↘⟦t⟧ = ⟦$⟧ t.↘⟦t⟧ s.↘⟦t⟧ (subst (_∙ _ ↘ fa) (ap-vone _) ↘fa)
          ; tσ∼  = 《》-resp-≈ _ rel
                             (≈-trans ($-[] ⊢σ ⊢t ⊢s)
                                      ($-cong (≈-sym ([I] (t[σ] ⊢t ⊢σ))) (≈-refl (t[σ] ⊢s ⊢σ))))
          }
  where module t = Intp (⊩t σ ρ σ∼ρ)
        module s = Intp (⊩s σ ρ σ∼ρ)
        open Fun t.tσ∼
        open ap-rel (krip (r-I I-≈) s.tσ∼)

□-I′ : [] ∷⁺ Ψ ⊩ t ∶ T →
       -----------------
       Ψ ⊩ box t ∶ □ T
□-I′ {_} {t} ⊩t σ ρ σ∼ρ =
  let ⊢σ = glu⇒⊢s σ∼ρ
      ⊢t = ⊩⇒⊢ ⊩t
  in record
  { ⟦t⟧  = box ⟦t⟧
  ; ↘⟦t⟧ = ⟦box⟧ ↘⟦t⟧
  ; tσ∼  = record
    { t∶□  = t[σ] (□-I ⊢t) ⊢σ
    ; krip = λ {_ } {δ} Γs ⊢δ → record
      { ua  = ⟦t⟧ [ ins (mt δ) 1 ] [ ins vone (len Γs) ]
      ; ↘ua = box↘ (len Γs)
      ; rel = let σ∘δ   = S-∘ (⊢r⇒⊢s ⊢δ) ⊢σ
                  σδ；  = S-； ([] ∷ []) σ∘δ refl
                  I；Γs = S-； Γs S-I refl
                  δ；Γs = S-； Γs (⊢r⇒⊢s ⊢δ) refl
              in 《》-resp-≈ _
                           (subst (_ ∼_∈ 《 _ 》T _)
                                  (sym (trans (D-comp _ (ins (mt δ) 1) (ins vone (len Γs)))
                                              (cong (⟦t⟧ [_]) (ins-1-ø-ins-vone (mt δ) (len Γs)))))
                                  (《》-mon _ (r-； Γs ⊢δ (s≈-refl δ；Γs) refl) tσ∼))
                           (≈-trans (unbox-cong Γs
                                                (≈-trans (≈-sym ([∘] (⊢r⇒⊢s ⊢δ) ⊢σ (□-I ⊢t)))
                                                         (box-[] σ∘δ ⊢t))
                                                refl)
                           (≈-trans (□-β Γs (t[σ] ⊢t σδ；) refl)
                           (≈-trans (≈-sym ([∘] I；Γs σδ； ⊢t))
                           (≈-trans ([]-cong (≈-refl ⊢t) (；-∘ ([] ∷ []) σ∘δ I；Γs refl))
                           (≈-trans ([]-cong (≈-refl ⊢t) (；-cong Γs (∘-I σ∘δ) (sym (+-identityʳ _))))
                           (≈-trans (≈-sym ([]-cong (≈-refl ⊢t) (；-∘ ([] ∷ []) ⊢σ δ；Γs refl)))
                                    ([∘] δ；Γs (S-； ([] ∷ []) ⊢σ refl) ⊢t)))))))
      }
    }
  }
  where open Intp (⊩t _ _ (rel-ext ([] ∷ []) ρ σ∼ρ))

□-E′ : ∀ {n} Γs →
       Ψ ⊩ t ∶ □ T →
       len Γs ≡ n →
       -------------------------
       Γs ++⁺ Ψ ⊩ unbox n t ∶ T
□-E′ {_} {t} {_} {n} Γs ⊩t refl σ ρ σ∼ρ
  with Tr-《》 Γs σ∼ρ
...  | Φ₁ , Φ₂ , refl , eql , Trσ∼ =
  let ⊢σ   = glu⇒⊢s σ∼ρ
      ⊢t   = ⊩⇒⊢ ⊩t
      ↘ua′ = subst₂ (unbox∙_,_↘ ua)
                    (trans eql (O-《》 (len Γs) _ σ∼ρ (length-<-++⁺ Γs)))
                    (ap-vone _)
                    ↘ua
  in record
  { ⟦t⟧  = ua
  ; ↘⟦t⟧ = ⟦unbox⟧ n ↘⟦t⟧ ↘ua′
  ; tσ∼  = 《》-resp-≈ _ rel
                     (≈-trans (unbox-[] Γs ⊢σ ⊢t refl)
                     (subst (λ n → Φ₁ ++⁺ _ ⊢ unbox n _ ≈ unbox _ _ ∶ _) eql
                            (unbox-cong Φ₁ (≈-sym ([I] t∶□)) refl)))
  }
  where open Intp (⊩t _ _ Trσ∼)
        open ■ tσ∼
        open unbox-rel (krip Φ₁ (r-I I-≈))

t[σ]′ : Ψ ⊩ t ∶ T →
        Ψ′ ⊩s σ ∶ Ψ →
        ----------------
        Ψ′ ⊩ t [ σ ] ∶ T
t[σ]′ ⊩t ⊩σ δ ρ δ∼ρ =
  let ⊢δ = glu⇒⊢s δ∼ρ
      ⊢t = ⊩⇒⊢ ⊩t
      ⊢σ = ⊩s⇒⊢s ⊩σ
  in record
  { ⟦t⟧  = t.⟦t⟧
  ; ↘⟦t⟧ = ⟦[]⟧ σ.↘⟦σ⟧ t.↘⟦t⟧
  ; tσ∼  = 《》-resp-≈ _ t.tσ∼ (≈-sym ([∘] ⊢δ ⊢σ ⊢t))
  }
  where module σ = Intps (⊩σ δ ρ δ∼ρ)
        module t = Intp (⊩t (_ ∘ δ) σ.⟦σ⟧ σ.comp)

S-I′ : Ψ ⊩s I ∶ Ψ
S-I′ δ ρ δ∼ρ = record
  { ⟦σ⟧  = ρ
  ; ↘⟦σ⟧ = ⟦I⟧
  ; comp = 《》-resp-≈s _ δ∼ρ (I-∘ (glu⇒⊢s δ∼ρ))
  }

drop-rel : ∀ Γs → σ ∼ ρ ∈ 《 (T ∷ Γ) ∷ Γs 》Ψ Ψ → p ∘ σ ∼ drop ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ
drop-rel [] σ∼ρ        = record
  { σ-wf  = S-∘ σ-wf S-p
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (vlkup (there T∈Γ)) (≈-trans ([∘] σ-wf S-p (vlookup T∈Γ)) ([]-cong ([p] T∈Γ) (s≈-refl σ-wf)))
  }
  where open Single σ∼ρ
drop-rel (Γ′ ∷ Γs) σ∼ρ = record
  { σ-wf  = S-∘ σ-wf S-p
  ; vlkup = λ T∈Γ → 《》-resp-≈ _ (vlkup (there T∈Γ)) (≈-trans ([∘] σ-wf S-p (vlookup T∈Γ)) ([]-cong ([p] T∈Γ) (s≈-refl σ-wf)))
  ; Leq   = Leq
  ; hds   = hds
  ; Ψ|ρ0  = Ψ|ρ0
  ; Ψ≡    = Ψ≡
  ; len≡  = len≡
  ; rel   = 《》-resp-≈s _ rel (I-∘ (glu⇒⊢s rel))
  }
  where open Cons σ∼ρ

S-p′ : (T ∷ Γ) ∷ Γs ⊩s p ∶ Γ ∷ Γs
S-p′ {_} {σ} δ ρ δ∼ρ =
  record
  { ⟦σ⟧  = drop ρ
  ; ↘⟦σ⟧ = ⟦p⟧
  ; comp = drop-rel _ δ∼ρ
  }

S-,′ : Ψ ⊩s σ ∶ Γ ∷ Γs →
       Ψ ⊩ t ∶ T →
       --------------------------
       Ψ ⊩s σ , t ∶ (T ∷ Γ) ∷ Γs
S-,′ {_} {σ} {_} {_} {t} ⊩σ ⊩t δ ρ δ∼ρ =
  let ⊢δ = glu⇒⊢s δ∼ρ
      ⊢t = ⊩⇒⊢ ⊩t
      ⊢σ = ⊩s⇒⊢s ⊩σ
  in record
  { ⟦σ⟧  = σ.⟦σ⟧ ↦ t.⟦t⟧
  ; ↘⟦σ⟧ = ⟦,⟧ σ.↘⟦σ⟧ t.↘⟦t⟧
  ; comp = 《》-resp-≈s _ (rel-↦ _ σ.comp t.tσ∼) (,-∘ ⊢σ ⊢t ⊢δ)
  }
  where module σ = Intps (⊩σ δ ρ δ∼ρ)
        module t = Intp (⊩t δ ρ δ∼ρ)

S-；′ : ∀ {n} Γs →
        Ψ ⊩s σ ∶ Ψ′ →
        len Γs ≡ n →
        -------------------------------
        Γs ++⁺ Ψ ⊩s σ ； n ∶ [] ∷⁺ Ψ′
S-；′ {_} {σ} {Ψ′} {n} Γs ⊩σ refl δ ρ δ∼ρ
  with Tr-《》 Γs δ∼ρ
...  | Φ₁ , Φ₂ , refl , eql , Trσ∼ =
  let ⊢δ   = glu⇒⊢s δ∼ρ
      ⊢σ   = ⊩s⇒⊢s ⊩σ
      eql′ = trans eql (O-《》 n _ δ∼ρ (length-<-++⁺ Γs))
  in record
  { ⟦σ⟧  = ext ⟦σ⟧ (O ρ n)
  ; ↘⟦σ⟧ = ⟦；⟧ ↘⟦σ⟧
  ; comp = 《》-resp-≈s (toList Ψ′)
                      (subst (λ m → (σ ∘ Tr δ n) ； len Φ₁ ∼ ext ⟦σ⟧ m ∈ 《 [] ∷⁺ Ψ′ 》Ψ (Φ₁ ++⁺ _)) eql′ (rel-ext Φ₁ _ comp))
                      (subst (λ m → _ ⊢s _ ≈ _ ； m ∶ _) (sym eql) (；-∘ Γs ⊢σ ⊢δ refl))
  }
  where open Intps (⊩σ _ _ Trσ∼)

S-∘′ : Ψ ⊩s σ′ ∶ Ψ′ →
       Ψ′ ⊩s σ ∶ Ψ″ →
       -----------------
       Ψ ⊩s σ ∘ σ′ ∶ Ψ″
S-∘′ ⊩σ′ ⊩σ δ ρ δ∼ρ =
  let ⊢δ  = glu⇒⊢s δ∼ρ
      ⊢σ  = ⊩s⇒⊢s ⊩σ
      ⊢σ′ = ⊩s⇒⊢s ⊩σ′
  in record
  { ⟦σ⟧  = σ.⟦σ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧
  ; comp = 《》-resp-≈s _ σ.comp (∘-assoc ⊢δ ⊢σ′ ⊢σ)
  }
  where module σ′ = Intps (⊩σ′ δ ρ δ∼ρ)
        module σ  = Intps (⊩σ _ _ σ′.comp)

-- fundamental theorem
mutual
  fund-⊢ : Ψ ⊢ t ∶ T → Ψ ⊩ t ∶ T
  fund-⊢ (vlookup T∈Γ)   = vlookup′ T∈Γ
  fund-⊢ (⟶-I t∶T)       = ⟶-I′ (fund-⊢ t∶T)
  fund-⊢ (⟶-E t∶F s∶S)   = ⟶-E′ (fund-⊢ t∶F) (fund-⊢ s∶S)
  fund-⊢ (□-I t∶T)       = □-I′ (fund-⊢ t∶T)
  fund-⊢ (□-E Γs t∶T eq) = □-E′ Γs (fund-⊢ t∶T) eq
  fund-⊢ (t[σ] t∶T σ∶Ψ′) = t[σ]′ (fund-⊢ t∶T) (fund-⊢s σ∶Ψ′)

  fund-⊢s : Ψ ⊢s σ ∶ Ψ′ → Ψ ⊩s σ ∶ Ψ′
  fund-⊢s S-I               = S-I′
  fund-⊢s S-p               = S-p′
  fund-⊢s (S-, σ∶Ψ′ t∶T)    = S-,′ (fund-⊢s σ∶Ψ′) (fund-⊢ t∶T)
  fund-⊢s (S-； Γs σ∶Ψ′ eq) = S-；′ Γs (fund-⊢s σ∶Ψ′) eq
  fund-⊢s (S-∘ σ∶Ψ′ σ′∶Ψ″)  = S-∘′ (fund-⊢s σ∶Ψ′) (fund-⊢s σ′∶Ψ″)


record Soundness Ψ ρ t T : Set where
  field
    nf  : Nf
    nbe : Nbe (map len Ψ) ρ t T nf
    ≈nf : Ψ ⊢ t ≈ Nf⇒Exp nf ∶ T

soundness : Ψ ⊢ t ∶ T → Soundness Ψ (InitialEnvs (toList Ψ)) t T
soundness t∶T = record
  { nf  = nf
  ; nbe = record
    { ⟦t⟧ = ⟦t⟧
    ; ↘⟦t⟧ = ↘⟦t⟧
    ; ↓⟦t⟧ = subst (λ a → Rf _ - ↓ _ a ↘ nf) (ap-vone _) ↘nf
    }
  ; ≈nf = ≈-trans (≈-sym ([I] t∶T)) ≈nf
  }
  where open Intp (fund-⊢ t∶T _ _ (I∼Inits _))
        open Top (《》⊆Top _  _ (《》-resp-≈ _ tσ∼ (≈-sym ([I] t∶T)))) using (krip)
        open TopPred (krip (r-I I-≈))

nbe-comp : Ψ ⊢ t ∶ T → ∃ λ w → Nbe (map len Ψ) (InitialEnvs (toList Ψ)) t T w
nbe-comp t∶T = nf , nbe
  where open Soundness (soundness t∶T)
