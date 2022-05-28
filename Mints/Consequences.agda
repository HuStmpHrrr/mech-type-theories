{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Some consequences of fundamental theorems of completeness and soundness
module Mints.Consequences (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import Mints.Statics.Properties
open import Mints.Semantics.PER
open import Mints.Semantics.Readback
open import Mints.Semantics.Properties.Domain fext
open import Mints.Semantics.Properties.PER fext
open import Mints.Semantics.Properties.Evaluation fext
open import Mints.Completeness fext
open import Mints.Completeness.LogRel
open import Mints.Completeness.Fundamental fext
open import Mints.Completeness.Consequences fext
open import Mints.Soundness fext
open import Mints.Soundness.LogRel
open import Mints.Soundness.Properties.LogRel fext
open import Mints.Soundness.Properties.Substitutions fext
open import Mints.Soundness.Cumulativity fext
open import Mints.Soundness.Realizability fext
open import Mints.Soundness.Fundamental fext


-- Equivalence of □ types is injective.
□-≈-inj : ∀ {i} →
          Γ ⊢ □ S ≈ □ T ∶ Se i →
          [] ∷⁺ Γ ⊢ S ≈ T ∶ Se i
□-≈-inj {_} {S} {T} {i} □≈
  with ⊢Γ , ⊢□S , ⊢□T , _ ← presup-≈ □≈
     with ⊢[]Γ ← ⊢κ ⊢Γ
        | ⊢S ← □-inv ⊢□S
        | ⊢T ← □-inv ⊢□T
        with ⊨Γ , _ , rel ← fundamental-t≈t′ □≈
           | record { ⊩Γ = ⊩[]Γ₁ ; krip = Skrip } ← fundamental-⊢t⇒⊩t ⊢S
           | record { ⊩Γ = ⊩[]Γ  ; krip = Tkrip } ← fundamental-⊢t⇒⊩t ⊢T
           with ρ , _ , ρinit , ρinit′ , ρ∈ ← InitEnvs-related ⊨Γ
              rewrite InitEnvs-det ρinit′ ρinit
              with rel ρ∈
                 | Skrip (InitEnvs⇒s®I ⊩[]Γ₁ (s-κ ρinit))
                 | Tkrip (InitEnvs⇒s®I ⊩[]Γ (s-κ ρinit))
...              | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U i< _ }
                 , record { ⟦t⟧ = □ ⟦S⟧ ; ⟦t′⟧ = □ ⟦T⟧ ; ↘⟦t⟧ = ⟦□⟧ ↘⟦S⟧ ; ↘⟦t′⟧ = ⟦□⟧ ↘⟦T⟧ ; t≈t′ = □S≈T }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧′ ; T∈𝕌 = U i<′ _ ; t∼⟦t⟧ = S∼⟦S⟧ }
                 | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U i<″ _ ; t∼⟦t⟧ = T∼⟦T⟧ }
                 rewrite 𝕌-wellfounded-≡-𝕌 _ i<
                       | Glu-wellfounded-≡ i<′
                       | Glu-wellfounded-≡ i<″
                       | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                       | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                 with □ S≈T ← □S≈T
                    | record { A∈𝕌 = S∈𝕌 ; rel = Srel } ← S∼⟦S⟧
                    | record { A∈𝕌 = T∈𝕌 ; rel = Trel } ← T∼⟦T⟧
                    with S≈T ← S≈T vone
                       rewrite D-ap-vone ⟦S⟧
                             | D-ap-vone ⟦T⟧ = ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T∈𝕌 (®-transport S∈𝕌 T∈𝕌 S≈T Srel) Trel))))


-- Equivalence of Π types is injective.
Π-≈-inj : ∀ {i} →
          Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se i →
          Γ ⊢ S ≈ S′ ∶ Se i × S ∺ Γ ⊢ T ≈ T′ ∶ Se i
Π-≈-inj {Γ} {S} {T} {S′} {T′} {i} Π≈
  with ⊢Γ , ⊢ΠST , ⊢ΠS′T′ , _ ← presup-≈ Π≈
    with ⊢S  , ⊢T  ← Π-inv ⊢ΠST
       | ⊢S′ , ⊢T′ ← Π-inv ⊢ΠS′T′
      with ⊨Γ , _ , rel ← fundamental-t≈t′ Π≈
         | ⊨SΓ₁@(∺-cong ⊨Γ₁ Srel₁) , _ , rel₁ ← fundamental-⊢t ⊢T
         | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t ⊢S
         | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t ⊢S′
        with ρ′ , _ , ρ′init , ρ′init₁ , ρ′∈ ← InitEnvs-related ⊨SΓ₁
          rewrite InitEnvs-det ρ′init₁ ρ′init
            with s-∺ {ρ = ρ} {A = A} ρinit S↘ ← ρ′init
               | ρ∈ , s∈ ← ρ′∈
            with rel (⊨-irrel ⊨Γ₁ ⊨Γ ρ∈)
               | Skrip (InitEnvs⇒s®I ⊩Γ ρinit)
               | S′krip (InitEnvs⇒s®I ⊩Γ₁ ρinit)
...            | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U i< _ }
               , record { ⟦t⟧ = Π ⟦S⟧ _ _ ; ⟦t′⟧ = Π ⟦S′⟧ _ _ ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦S′⟧ ; t≈t′ = ΠST≈ΠS′T′ }
               | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧′ ; T∈𝕌 = U i<′ _ ; t∼⟦t⟧ = S∼⟦S⟧ }
               | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S′⟧′ ; T∈𝕌 = U i<′₁ _ ; t∼⟦t⟧ = S′∼⟦S′⟧ }
              rewrite 𝕌-wellfounded-≡-𝕌 _ i<
                    | Glu-wellfounded-≡ i<′
                    | Glu-wellfounded-≡ i<′₁
                    | drop-↦ ρ (l′ A (len (head Γ)))
                    | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                    | ⟦⟧-det ↘⟦S′⟧′ ↘⟦S′⟧
                with Π S≈S′ Trel ← ΠST≈ΠS′T′
                   | record { A∈𝕌 = S∈𝕌 ; rel = Srel } ← S∼⟦S⟧
                   | record { A∈𝕌 = S′∈𝕌 ; rel = S′rel } ← S′∼⟦S′⟧
                  with S≈S′ ← S≈S′ vone
                     | Trel ← (λ {a} {a′} → Trel {a} {a′} vone)
                    rewrite D-ap-vone ⟦S⟧
                          | D-ap-vone ⟦S′⟧
                          | ρ-ap-vone ρ
                      with S≈S′′ ← ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ S′∈𝕌 (®-transport S∈𝕌 S′∈𝕌 S≈S′ Srel) S′rel)))) = S≈S′′ , T≈T′-helper
  where
    s∈₁ : l′ A (len (head Γ)) ∈′ El _ S≈S′
    s∈₁
      with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← Srel₁ ρ∈
        rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧ = El-one-sided S≈S′₁ S≈S′ s∈

    T≈T′-helper : S ∺ Γ ⊢ T ≈ T′ ∶ Se i
    T≈T′-helper
      with record { ⊩Γ = ⊩SΓ ; krip = Tkrip } ← fundamental-⊢t⇒⊩t ⊢T
         | record { ⊩Γ = ⊩SΓ₁ ; krip = T′krip } ← fundamental-⊢t⇒⊩t (ctxeq-tm (∺-cong (⊢≈-refl ⊢Γ) (≈-sym S≈S′′)) ⊢T′)
        with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← Trel s∈₁
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U i<′ _ ; t∼⟦t⟧ = T∼⟦T⟧ } ← Tkrip (InitEnvs⇒s®I ⊩SΓ ρ′init)
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T′⟧′ ; T∈𝕌 = U i<′₁ _ ; t∼⟦t⟧ = T′∼⟦T′⟧ } ← T′krip (InitEnvs⇒s®I ⊩SΓ₁ ρ′init)
          rewrite Glu-wellfounded-≡ i<′
                | Glu-wellfounded-≡ i<′₁
                | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                | ⟦⟧-det ↘⟦T′⟧′ ↘⟦T′⟧
            with record { A∈𝕌 = T∈𝕌 ; rel = Trel } ← T∼⟦T⟧
               | record { A∈𝕌 = T′∈𝕌 ; rel = T′rel } ← T′∼⟦T′⟧ = ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T′∈𝕌 (®-transport T∈𝕌 T′∈𝕌 T≈T′ Trel) T′rel))))


-- If two types are equivalent and well-formed in another level, then they are
-- equivalent in that level.
adjust-Se-lvl : ∀ {i j} →
                Γ ⊢ T ≈ T′ ∶ Se i →
                Γ ⊢ T ∶ Se j →
                Γ ⊢ T′ ∶ Se j →
                Γ ⊢ T ≈ T′ ∶ Se j
adjust-Se-lvl T≈T′ ⊢T ⊢T′
  with completeness T≈T′ | soundness ⊢T | soundness ⊢T′
...  | _
     , record { init = init₁ ; nbe = record { ⟦T⟧ = .(U _) ; ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU ._ ↘w } }
     , record { init = init₂ ; nbe = record { ⟦T⟧ = .(U _) ; ↘⟦t⟧ = ↘⟦T′⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU ._ ↘w′ } }
     | _ , record { init = init₃ ; nbe = record { ⟦T⟧ = .(U _) ; ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU ._ ↘w₁ } } , T≈w
     | _ , record { init = init ; nbe = record { ⟦T⟧ = .(U _) ; ↘⟦t⟧ = ↘⟦T′⟧₁ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↓⟦t⟧ = RU ._ ↘w′₁ } } , T′≈w
     rewrite InitEnvs-det init₁ init
           | InitEnvs-det init₂ init
           | InitEnvs-det init₃ init
           | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
           | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧
           | Rty-det ↘w₁ ↘w
           | Rty-det ↘w′₁ ↘w′ = ≈-trans T≈w (≈-sym T′≈w)


-----------------------
-- canonical form of N

data IsND : D → Set where
  ze : IsND ze
  su : IsND a → IsND (su a)


data IsN : Nf → Set where
  ze : IsN ze
  su : IsN w → IsN (su w)


closed-®Nat : [] ∷ [] ⊢ t ∶N® a ∈Nat →
              IsND a
closed-®Nat (ze _)      = ze
closed-®Nat (su _ t∼a)  = su (closed-®Nat t∼a)
closed-®Nat (ne c∈ rel)
  with ≈u ← rel (⊢rI ⊢[])
    with _ , _ , ⊢u , _ ← presup-≈ ≈u = ⊥-elim (no-closed-Ne ⊢u)


closed-NbE-N : [] ∷ [] ⊢ t ∶ N →
               NbE ([] ∷ []) t N w →
               IsN w
closed-NbE-N ⊢t record { envs = envs ; nbe = record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } }
  with record { ⊩Γ = ⊩[] ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧′ ; T∈𝕌 = N ; t∼⟦t⟧ = t∼⟦t⟧ , _ } ← krip {ρ = envs} (s-I ⊢[])
      rewrite ⟦⟧-det ↘⟦t⟧′ ↘⟦t⟧ = helper (closed-®Nat t∼⟦t⟧) ↓⟦t⟧
  where helper : IsND a → Rf 0 ∷ [] - ↓ N a ↘ w → IsN w
        helper ze     (Rze .(0 ∷ []))    = ze
        helper (su a) (Rsu .(0 ∷ []) ↘w) = su (helper a ↘w)


canonicity-N : [] ∷ [] ⊢ t ∶ N →
               ∃ λ w → [] ∷ [] ⊢ t ≈ Nf⇒Exp w ∶ N × IsN w
canonicity-N ⊢t
  with w , nbe , ≈w ← soundness ⊢t = w , ≈w , closed-NbE-N ⊢t nbe
