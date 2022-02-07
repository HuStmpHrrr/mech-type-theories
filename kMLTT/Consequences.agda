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
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Completeness.Consequences fext
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
