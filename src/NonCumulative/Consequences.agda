{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Some consequences of fundamental theorems of completeness and soundness
module NonCumulative.Consequences (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Semantics.PER
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Semantics.Realizability fext
open import NonCumulative.Completeness fext
open import NonCumulative.Completeness.LogRel
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Completeness.Consequences fext
open import NonCumulative.Soundness fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Substitutions fext
open import NonCumulative.Soundness.Realizability fext
open import NonCumulative.Soundness.Fundamental fext

-- Equivalence of Π types is injective.
Π-≈-inj : ∀ {i j j′ k k′} →
          Γ ⊢ Π (S ↙ j) (T ↙ k) ≈ Π (S′ ↙ j′) (T′ ↙ k′) ∶[ 1 + i ] Se i →
          j ≡ j′ × k ≡ k′ × i ≡ max j k × Γ ⊢ S ≈ S′ ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + k ] Se k
Π-≈-inj {Γ} {S} {T} {S′} {T′} {i} {j} {j′} {k} {k′} Π≈
  with ⊢Γ , ⊢ΠST , ⊢ΠS′T′ , _ ← presup-≈ Π≈
  with i≡maxjk , ⊢S , ⊢T ← Π-inv ⊢ΠST
     | i≡maxj′k′ , ⊢S′ , ⊢T′ ← Π-inv ⊢ΠS′T′
  with ⊨Γ , rel ← fundamental-t≈t′ Π≈
     | ⊨SΓ₁@(∷-cong ⊨Γ₁ Srel₁ _) , rel₁ ← fundamental-⊢t ⊢T
     | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t′ ⊢S
     | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t′ ⊢S′
  with ρ′ , _ , ρ′init , ρ′init₁ , ρ′∈ ← InitEnvs-related ⊨SΓ₁
  rewrite InitEnvs-det ρ′init₁ ρ′init
  with s-∷ {ρ = ρ} {A = A} ρinit S↘ ← ρ′init
     | ρ∈ , s∈ ← ρ′∈
  with rel (⊨-irrel ⊨Γ₁ ⊨Γ ρ∈)
     | Skrip (InitEnvs⇒s®I ⊩Γ ρinit)
     | S′krip (InitEnvs⇒s®I ⊩Γ₁ ρinit)
...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U 1+i≡1+i _ }
     , record { ⟦t⟧ = Π _ ⟦S⟧ _ _ ; ⟦t′⟧ = Π _ ⟦S′⟧ _ _ ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦S′⟧ ; t≈t′ = ΠST≈ΠS′T′ }
     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧′ ; T∈𝕌 = U 1+j≡1+j _ ; t∼⟦t⟧ = S∼⟦S⟧ }
     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S′⟧′ ; T∈𝕌 = U 1+j′≡1+j′ _ ; t∼⟦t⟧ = S′∼⟦S′⟧ }
     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+i≡1+i))
           | Glu-wellfounded-≡ (≤-reflexive (sym 1+j≡1+j))
           | Glu-wellfounded-≡ (≤-reflexive (sym 1+j′≡1+j′))
           | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
           | ⟦⟧-det ↘⟦S′⟧′ ↘⟦S′⟧
           with Π refl S≈S′ Trel refl refl ← ΠST≈ΠS′T′
           rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
                 | 𝕌-wf-gen k (ΠO≤′ j k refl)
                 with record { A∈𝕌 = S∈𝕌 ; rel = Srel } ← S∼⟦S⟧
                    | record { A∈𝕌 = S′∈𝕌 ; rel = S′rel } ← S′∼⟦S′⟧
                    with S≈S′′ ← ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ S′∈𝕌 (®-transport S∈𝕌 S′∈𝕌 S≈S′ Srel) S′rel)))) = refl , (refl , (refl , (S≈S′′ , T≈T′-helper)))
    where
      s∈₁ : l′ j A (len Γ) ∈′ El _ S≈S′
      s∈₁
        with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← Srel₁ ρ∈
           rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧ = El-one-sided S≈S′₁ S≈S′ s∈

      T≈T′-helper : (S ↙ j) ∷ Γ ⊢ T ≈ T′ ∶[ 1 + k ] Se k
      T≈T′-helper
        with record { ⊩Γ = ⊩SΓ ; krip = Tkrip } ← fundamental-⊢t⇒⊩t′ ⊢T
           | record { ⊩Γ = ⊩SΓ₁ ; krip = T′krip } ← fundamental-⊢t⇒⊩t′ (ctxeq-tm (∷-cong″ (≈-sym S≈S′′)) ⊢T′)
           with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← Trel s∈₁
              | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U 1+k≡1+k _ ; t∼⟦t⟧ = T∼⟦T⟧ } ← Tkrip (InitEnvs⇒s®I ⊩SΓ ρ′init)
              | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T′⟧′ ; T∈𝕌 = U 1+k≡′1+k _ ; t∼⟦t⟧ = T′∼⟦T′⟧ } ← T′krip (InitEnvs⇒s®I ⊩SΓ₁ ρ′init)
              rewrite Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡1+k))
                    | Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡′1+k))
                    | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                    | ⟦⟧-det ↘⟦T′⟧′ ↘⟦T′⟧
                    with record { A∈𝕌 = T∈𝕌 ; rel = Trel } ← T∼⟦T⟧
                       | record { A∈𝕌 = T′∈𝕌 ; rel = T′rel } ← T′∼⟦T′⟧ = ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T′∈𝕌 (®-transport T∈𝕌 T′∈𝕌 T≈T′ Trel) T′rel))))

Liftt-≈-inj : ∀ {i j j′ k k′} →
          Γ ⊢ Liftt j (T ↙ k) ≈ Liftt j′ (T′ ↙ k′) ∶[ 1 + i ] Se i →
          j ≡ j′ × k ≡ k′ × i ≡ j + k × Γ ⊢ T ≈ T′ ∶[ 1 + k ] Se k
Liftt-≈-inj {Γ} {T} {T′} {i} {j} {j′} {k} {k′} Liftt≈
  with ⊢Γ , ⊢LifttT , ⊢LifttT′ , _ ← presup-≈ Liftt≈
  with i≡j+k , ⊢T ← Liftt-inv ⊢LifttT
  with i≡j′+k′ , ⊢T′ ← Liftt-inv ⊢LifttT′
  with ⊨Γ , rel ← fundamental-t≈t′ Liftt≈
     | ⊨Γ₁ , rel₁ ← fundamental-⊢t ⊢T
     | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t′ ⊢T
     | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t′ ⊢T′
  with  ρ , _ , ρinit , ρinit₁ , ρ∈ ← InitEnvs-related ⊨Γ₁
  rewrite InitEnvs-det ρinit₁ ρinit
  with rel (⊨-irrel ⊨Γ₁ ⊨Γ ρ∈)
     | Skrip (InitEnvs⇒s®I ⊩Γ ρinit)
     | S′krip (InitEnvs⇒s®I ⊩Γ₁ ρinit)
...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U _) ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = _ ; T≈T′ = U 1+i≡1+i _ }
     , record { ⟦t⟧ = Li _ _ ⟦T⟧ ; ⟦t′⟧ = Li _ _ ⟦T′⟧ ; ↘⟦t⟧ = ⟦Liftt⟧ ↘⟦T⟧ ; ↘⟦t′⟧ = ⟦Liftt⟧ ↘⟦T′⟧ ; t≈t′ = LifttT≈LifttT′ }
     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U 1+j≡1+j _ ; t∼⟦t⟧ = T∼⟦T⟧ }
     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T′⟧′ ; T∈𝕌 = U 1+j′≡1+j′ _ ; t∼⟦t⟧ = T′∼⟦T′⟧ }
     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+i≡1+i))
           | Glu-wellfounded-≡ (≤-reflexive (sym 1+j≡1+j))
           | Glu-wellfounded-≡ (≤-reflexive (sym 1+j′≡1+j′))
           | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
           | ⟦⟧-det ↘⟦T′⟧′ ↘⟦T′⟧
           with L refl T≈T′ refl refl ← LifttT≈LifttT′
           rewrite 𝕌-wf-gen k (Li≤′ j k refl)
           with record { A∈𝕌 = T∈𝕌 ; rel = Trel } ← T∼⟦T⟧
              | record { A∈𝕌 = T′∈𝕌 ; rel = T′rel } ← T′∼⟦T′⟧
              with T≈T″ ← ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T′∈𝕌 (®-transport T∈𝕌 T′∈𝕌 T≈T′ Trel) T′rel))))  = refl , (refl , (refl , T≈T″))

mutual
  unique-typ : ∀ {i j} →
    Γ ⊢ t ∶[ i ] T →
    Γ ⊢ t ∶[ j ] T′ →
    i ≡ j × Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i
  unique-typ (N-wf ⊢Γ) (N-wf _)                    = refl , ≈-refl (Se-wf 0 ⊢Γ)
  unique-typ (conv ⊢t S≈T) ⊢t′
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , ≈-trans (≈-sym S≈T) T≈T′
  unique-typ ⊢t (conv ⊢t′ S≈T′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈S                                = refl , ≈-trans T≈S S≈T′
  unique-typ (Se-wf i ⊢Γ) (Se-wf .i _)             = refl , ≈-refl (Se-wf (1 + i) ⊢Γ)
  unique-typ (Liftt-wf n ⊢T) (Liftt-wf .n ⊢T′)     = refl , ≈-refl (Se-wf (n + _) (proj₁ (presup-tm ⊢T)))
  unique-typ (Π-wf {k = k} ⊢S ⊢T refl) (Π-wf ⊢S′ ⊢T′ refl) = refl , ≈-refl (Se-wf k (proj₁ (presup-tm ⊢S)))
  unique-typ (vlookup ⊢Γ T∈Γ) (vlookup _ T′∈Γ)
    with same-lookup T∈Γ T′∈Γ
  ...  | refl , refl                               = refl , ≈-refl (∈⇒ty-wf ⊢Γ T∈Γ)
  unique-typ (ze-I ⊢Γ) (ze-I _)                    = refl , ≈-refl (N-wf ⊢Γ)
  unique-typ (su-I ⊢t) (su-I ⊢t′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , T≈T′
  unique-typ (N-E ⊢T _ _ ⊢t) (N-E _ _ _ _)
    with presup-tm ⊢T
  ...  | ⊢∷ ⊢Γ _ , _                               = refl , ≈-refl (t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t))
  unique-typ (Λ-I ⊢S ⊢t refl) (Λ-I _ ⊢t′ refl)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , Π-cong ⊢S (≈-refl ⊢S) T≈T′ refl
  unique-typ (Λ-E ⊢S ⊢T ⊢t ⊢s refl) (Λ-E ⊢S′ ⊢T′ ⊢t′ ⊢s′ refl)
    with ⊢Γ , _ ← presup-tm ⊢S
    with unique-typ ⊢t ⊢t′
  ...  | _ , Π≈
    with refl , refl , k≡maxij , S≈ , T≈ ← Π-≈-inj Π≈ = refl , []-cong-Se T≈ (s-, (s-I ⊢Γ) ⊢S ⊢s∶S[I]) (,-cong (I-≈ ⊢Γ) ⊢S S≈ (≈-refl ⊢s∶S[I]))
    where ⊢s∶S[I] = conv ⊢s (≈-sym ([I] ⊢S))
  unique-typ (L-I n ⊢t) (L-I .n ⊢t′)
    with unique-typ ⊢t ⊢t′
  ...  | refl , T≈T′                               = refl , Liftt-cong n T≈T′
  unique-typ (L-E n ⊢T ⊢t) (L-E n′ ⊢T′ ⊢t′)
    with ⊢Γ , _ ← presup-tm ⊢T
    with unique-typ ⊢t ⊢t′
  ...  | _ , Li≈
    with refl , refl , _ , T≈ ← Liftt-≈-inj Li≈ = refl , T≈
  unique-typ (t[σ] ⊢t ⊢σ) (t[σ] ⊢t′ ⊢σ′)
    with unique-typ ⊢t (ctxeq-tm (unique-ctx ⊢σ′ ⊢σ) ⊢t′)
  ...  | refl , T≈T′                               = refl , []-cong-Se′ T≈T′ ⊢σ

  unique-ctx : Γ ⊢s σ ∶ Δ → Γ ⊢s σ ∶ Δ′ → ⊢ Δ ≈ Δ′
  unique-ctx (s-I ⊢Γ) (s-I _)              = ≈-Ctx-refl ⊢Γ
  unique-ctx (s-conv ⊢σ Δ′≈Δ) ⊢σ′          = ⊢≈-trans (⊢≈-sym Δ′≈Δ) (unique-ctx ⊢σ ⊢σ′)
  unique-ctx ⊢σ (s-conv ⊢σ′ Δ≈Δ′)          = ⊢≈-trans (unique-ctx ⊢σ ⊢σ′) Δ≈Δ′
  unique-ctx (s-wk (⊢∷ ⊢Γ _)) (s-wk _)     = ≈-Ctx-refl ⊢Γ
  unique-ctx (s-∘ ⊢σ ⊢τ) (s-∘ ⊢σ′ ⊢τ′)     = unique-ctx ⊢τ (ctxeq-s (⊢≈-sym (unique-ctx ⊢σ ⊢σ′)) ⊢τ′)
  unique-ctx (s-, ⊢σ ⊢T _) (s-, ⊢σ′ ⊢T′ _) = ∷-cong (unique-ctx ⊢σ ⊢σ′) ⊢T ⊢T′ (≈-refl ⊢T) (≈-refl ⊢T′)