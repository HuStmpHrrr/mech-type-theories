{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Consequences (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.PER
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Completeness fext
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Completeness.Consequences fext
open import kMLTT.Soundness fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Fundamental fext


□-≈-inj : ∀ {i} →
          Γ ⊢ □ S ≈ □ T ∶ Se i →
          [] ∷⁺ Γ ⊢ S ≈ T ∶ Se i
□-≈-inj {_} {S} {T} {i} □≈
  with presup-≈ □≈
...  | ⊢Γ , ⊢□S , ⊢□T , _
     with ⊢κ ⊢Γ | □-inv ⊢□S | □-inv ⊢□T
...     | ⊢[]Γ | ⊢S | ⊢T
        with fundamental-t≈t′ □≈
           | fundamental-⊢t⇒⊩t ⊢S
           | fundamental-⊢t⇒⊩t ⊢T
...        | ⊨Γ , _ , rel
           | record { ⊩Γ = ⊩[]Γ₁ ; krip = Skrip }
           | record { ⊩Γ = ⊩[]Γ  ; krip = Tkrip }
           with InitEnvs-related ⊨Γ
...           | ρ , _ , ρinit , ρinit′ , ρ∈
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
                 with □S≈T | S∼⟦S⟧ | T∼⟦T⟧
...                 | □ S≈T
                    | record { A∈𝕌 = S∈𝕌 ; rel = Srel }
                    | record { A∈𝕌 = T∈𝕌 ; rel = Trel }
                    with S≈T vone
...                    | S≈T
                       rewrite D-ap-vone ⟦S⟧
                             | D-ap-vone ⟦T⟧ = ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T∈𝕌 (®-transport S∈𝕌 T∈𝕌 S≈T Srel) Trel))))


Π-≈-inj : ∀ {i} →
          Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se i →
          Γ ⊢ S ≈ S′ ∶ Se i × S ∺ Γ ⊢ T ≈ T′ ∶ Se i
Π-≈-inj {_} {S} {T} {S′} {T′} {i} Π≈
  with presup-≈ Π≈
...  | ⊢Γ , ⊢ΠST , ⊢ΠS′T′ , _
    with Π-inv ⊢ΠST | Π-inv ⊢ΠS′T′
...    | ⊢S , ⊢T | ⊢S′ , ⊢T′
      with fundamental-t≈t′ Π≈
         | fundamental-⊢t⇒⊩t ⊢S
         | fundamental-⊢t⇒⊩t ⊢S′
...      | ⊨Γ , _ , rel
         | record { ⊩Γ = ⊩Γ ; krip = Skrip }
         | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip }
        with InitEnvs-related ⊨Γ
...        | ρ , _ , ρinit , ρinit₁ , ρ∈
          rewrite InitEnvs-det ρinit₁ ρinit
            with rel ρ∈
               | Skrip (InitEnvs⇒s®I ⊩Γ ρinit)
               | S′krip (InitEnvs⇒s®I ⊩Γ₁ ρinit)
...            | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U i< _ }
               , record { ⟦t⟧ = Π ⟦S⟧ _ _ ; ⟦t′⟧ = Π ⟦S′⟧ _ _ ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦S′⟧ ; t≈t′ = ΠST≈ΠS′T′ }
               | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧′ ; T∈𝕌 = U i<′ _ ; t∼⟦t⟧ = S∼⟦S⟧ }
               | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S′⟧′ ; T∈𝕌 = U i<′₁ _ ; t∼⟦t⟧ = S′∼⟦S′⟧ }
              rewrite 𝕌-wellfounded-≡-𝕌 _ i<
                    | Glu-wellfounded-≡ i<′
                    | Glu-wellfounded-≡ i<′₁
                    | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                    | ⟦⟧-det ↘⟦S′⟧′ ↘⟦S′⟧
                with ΠST≈ΠS′T′ | S∼⟦S⟧ | S′∼⟦S′⟧
...                | Π S≈S′ T≈T′
                   | record { A∈𝕌 = S∈𝕌 ; rel = Srel }
                   | record { A∈𝕌 = S′∈𝕌 ; rel = S′rel }
                  with S≈S′ vone
...                  | S≈S′
                    rewrite D-ap-vone ⟦S⟧
                          | D-ap-vone ⟦S′⟧
                      with ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ S′∈𝕌 (®-transport S∈𝕌 S′∈𝕌 S≈S′ Srel) S′rel))))
...                      | S≈S′ = S≈S′ , T≈T′-helper S≈S′
  where
    T≈T′-helper : Γ ⊢ S ≈ S′ ∶ Se i → S ∺ Γ ⊢ T ≈ T′ ∶ Se i
    T≈T′-helper
      with fundamental-⊢t ⊢T
         | fundamental-⊢t⇒⊩t ⊢T
         | fundamental-⊢t⇒⊩t (ctxeq-tm (∺-cong (⊢≈-refl ⊢Γ) (≈-sym S≈S′)) ⊢T′)
    ...  | ⊨SΓ@(∺-cong _ _) , _ , rel′
         | record { ⊩Γ = ⊩SΓ ; krip = Tkrip }
         | record { ⊩Γ = ⊩SΓ₁ ; krip = T′krip }
        with InitEnvs-related ⊨SΓ
    ...    | ρ′ , _ , ρ′init , ρ′init₁ , ρ′∈
          rewrite InitEnvs-det ρ′init₁ ρ′init = {!!}
--             with rel′ ρ′∈
--                | Tkrip (InitEnvs⇒s®I ⊩SΓ ρ′init)
--                | T′krip (InitEnvs⇒s®I ⊩SΓ₁ ρ′init)
--     ...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U i<₁ _ }
--                , record { ⟦t⟧ = ⟦T⟧ ; ⟦t′⟧ = ⟦T′⟧ ; ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
--                | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U i<″ _ ; t∼⟦t⟧ = T∼⟦T⟧ }
--                | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T′⟧′ ; T∈𝕌 = U i<″₁ _ ; t∼⟦t⟧ = T′∼⟦T′⟧ }
--               rewrite 𝕌-wellfounded-≡-𝕌 _ i<₁
--                     | Glu-wellfounded-≡ i<″
--                     | Glu-wellfounded-≡ i<″₁
--                     | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
--                     | ⟦⟧-det ↘⟦T′⟧′ ↘⟦T′⟧
--                 with T∼⟦T⟧ | T′∼⟦T′⟧
--     ...            | record { A∈𝕌 = T∈𝕌 ; rel = Trel }
--                    | record { A∈𝕌 = T′∈𝕌 ; rel = T′rel } = ?


adjust-Se-lvl : ∀ {i j} →
                Γ ⊢ T ≈ T′ ∶ Se i →
                Γ ⊢ T ∶ Se j →
                Γ ⊢ T′ ∶ Se j →
                Γ ⊢ T ≈ T′ ∶ Se j
adjust-Se-lvl T≈T′ ⊢T ⊢T′
  with completeness T≈T′ | soundness ⊢T | soundness ⊢T′
...  | w
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
