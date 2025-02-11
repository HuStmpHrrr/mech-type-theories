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
open import NonCumulative.Statics.Ascribed.Simpl
open import NonCumulative.Statics.Ascribed.Inversion
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties.Subst
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
Π-≈-inj {Γ} {S} {T} {S′} {T′} {i} {j} {j′} {k} {k′}  Π≈
  with ⊢Γ , ⊢ΠST , ⊢ΠS′T′ , _ ← presup-≈ Π≈
  with i≡maxjk , ⊢S , ⊢T ← Π-inv ⊢ΠST
     | i≡maxj′k′ , ⊢S′ , ⊢T′ ← Π-inv ⊢ΠS′T′
  with ⊨Γ , rel ← fundamental-t≈t′ Π≈
     | ⊨SΓ₁@(∷-cong ⊨Γ₁ Srel₁ _) , rel₁ ← fundamental-⊢t ⊢T
     | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t ⊢S
     | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t ⊢S′
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
        with record { ⊩Γ = ⊩SΓ ; krip = Tkrip } ← fundamental-⊢t⇒⊩t ⊢T
           | record { ⊩Γ = ⊩SΓ₁ ; krip = T′krip } ← fundamental-⊢t⇒⊩t (ctxeq-tm (∷-cong″ (≈-sym S≈S′′)) ⊢T′)
           with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← Trel s∈₁
              | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U 1+k≡1+k _ ; t∼⟦t⟧ = T∼⟦T⟧ } ← Tkrip (InitEnvs⇒s®I ⊩SΓ ρ′init)
              | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T′⟧′ ; T∈𝕌 = U 1+k≡′1+k _ ; t∼⟦t⟧ = T′∼⟦T′⟧ } ← T′krip (InitEnvs⇒s®I ⊩SΓ₁ ρ′init)
              rewrite Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡1+k))
                    | Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡′1+k))
                    | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                    | ⟦⟧-det ↘⟦T′⟧′ ↘⟦T′⟧
                    with record { A∈𝕌 = T∈𝕌 ; rel = Trel } ← T∼⟦T⟧
                       | record { A∈𝕌 = T′∈𝕌 ; rel = T′rel } ← T′∼⟦T′⟧ = ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ T′∈𝕌 (®-transport T∈𝕌 T′∈𝕌 T≈T′ Trel) T′rel))))

Λ-inv-gen : ∀ {i i′ j′ k R} →
         Γ ⊢ Λ (S ↙ i) t ∶[ k ] R → 
         Γ ⊢ R ≈ Π (S′ ↙ i′) (T′ ↙ j′) ∶[ 1 + k ] Se k →
         i ≡ i′ × k ≡ max i′ j′ × Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i × (S ↙ i) ∷ Γ ⊢ t ∶[ j′ ] T′
Λ-inv-gen (Λ-I ⊢S ⊢t _) T≈Π with Π-≈-inj T≈Π
... | refl , refl , refl , S≈S′ , T≈T′ = refl , refl , S≈S′ , conv ⊢t T≈T′
Λ-inv-gen (conv ⊢t x) T≈Π = Λ-inv-gen ⊢t (≈-trans x T≈Π)

Λ-inv :  ∀ {i i′ j′ k} →
         Γ ⊢ Λ (S ↙ i) t ∶[ k ] Π (S′ ↙ i′) (T′ ↙ j′) → 
         i ≡ i′ × k ≡ max i′ j′ × Γ ⊢ S ≈ S′ ∶[ 1 + i ] Se i × (S ↙ i) ∷ Γ ⊢ t ∶[ j′ ] T′
Λ-inv ⊢t 
  with presup-tm ⊢t 
... | ⊢Γ , ⊢Π 
  with Π-inv ⊢Π
... | k≡maxi′j′ , ⊢S′ , ⊢T′  = Λ-inv-gen ⊢t (Π-cong ⊢S′ (≈-refl ⊢S′) (≈-refl ⊢T′) k≡maxi′j′)

Liftt-≈-inj : ∀ {i j j′ k k′} →
          Γ ⊢ Liftt j (T ↙ k) ≈ Liftt j′ (T′ ↙ k′) ∶[ 1 + i ] Se i →
          j ≡ j′ × k ≡ k′ × i ≡ j + k × Γ ⊢ T ≈ T′ ∶[ 1 + k ] Se k
Liftt-≈-inj {Γ} {T} {T′} {i} {j} {j′} {k} {k′} Liftt≈
  with ⊢Γ , ⊢LifttT , ⊢LifttT′ , _ ← presup-≈ Liftt≈
  with i≡j+k , ⊢T ← Liftt-inv ⊢LifttT
  with i≡j′+k′ , ⊢T′ ← Liftt-inv ⊢LifttT′
  with ⊨Γ , rel ← fundamental-t≈t′ Liftt≈
     | ⊨Γ₁ , rel₁ ← fundamental-⊢t ⊢T
     | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t ⊢T
     | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t ⊢T′
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


-----------------------
-- canonical form of N

data IsND : D → Set where
  ze : IsND ze
  su : IsND a → IsND (su a)


data IsN : Nf → Set where
  ze : IsN ze
  su : IsN w → IsN (su w)


closed-®Nat : [] ⊢ t ∶N® a ∈Nat →
              IsND a
closed-®Nat (ze _)      = ze
closed-®Nat (su _ t∼a)  = su (closed-®Nat t∼a)
closed-®Nat (ne c∈ rel)
  with ≈u ← rel (⊢wI ⊢[])
    with _ , _ , ⊢u , _ ← presup-≈ ≈u = ⊥-elim (no-closed-Ne ⊢u)

closed-NbE-N : [] ⊢ t ∶[ 0 ] N →
               NbE [] t 0 N w →
               IsN w
closed-NbE-N ⊢t record { envs = envs ; nbe = record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } }
  with record { ⊩Γ = ⊩[] ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧′ ; T∈𝕌 = N′ ; t∼⟦t⟧ = t∼⟦t⟧ , _ } ← krip {ρ = envs} (s-I ⊢[])
      rewrite ⟦⟧-det ↘⟦t⟧′ ↘⟦t⟧ = helper (closed-®Nat t∼⟦t⟧) ↓⟦t⟧
  where helper : IsND a → Rf 0 - ↓ 0 N a ↘ w → IsN w
        helper ze     (Rze .0)    = ze
        helper (su a) (Rsu .0 ↘w) = su (helper a ↘w)

canonicity-N : [] ⊢ t ∶[ 0 ] N →
               ∃ λ w → [] ⊢ t ≈ Nf⇒Exp w ∶[ 0 ] N × IsN w
canonicity-N ⊢t
  with w , nbe , ≈w ← soundness ⊢t = w , ≈w , closed-NbE-N ⊢t nbe

no-neutral-Se-gen : ∀ {i j k k′ k″ k‴} →
                    t ≡ Ne⇒Exp u →
                    Γ ⊢ t ∶[ j ] T →
                    Γ ≡ (Se i ↙ (1 + i)) ∷ [] →
                    Γ ⊢ T ≈ T′ ∶[ 1 + j ] Se j →
                    T′ ∈ v 0 ∷ N ∷ Π (S ↙ k) (S′ ↙ k′) ∷ Liftt k″ (S″ ↙ k‴) ∷ [] →
                    ----------------
                    ⊥
no-neutral-Se-gen {_} {v .0} refl (vlookup ⊢Γ here) refl T≈ T′∈ = not-Se-≈-bundle (s≤s z≤n) (≈-trans (≈-sym (Se-[] _ (s-wk ⊢Γ))) T≈) T′∈
no-neutral-Se-gen {_} {rec T z s u} refl (N-E _ _ _ t∶T) refl T≈ T′∈ = no-neutral-Se-gen {S = N} {S′ = N} {S″ = N} {k = 0} {k′ = 0} {k″ = 0} {k‴ = 0} refl t∶T refl (≈-refl (N-wf (proj₁ (presup-tm t∶T)))) (there (here refl))
no-neutral-Se-gen {_} {u $ n} refl (Λ-E _ _ t∶T _ _) refl T≈ T′∈ = no-neutral-Se-gen {S″ = N} {k″ = 0} {k‴ = 0} refl t∶T refl (≈-refl (proj₂ (presup-tm t∶T))) (there (there (here refl)))
no-neutral-Se-gen {_} {unlift u} refl (L-E _ _ t∶T) refl T≈ T′∈ = no-neutral-Se-gen {S = N} {S′ = N} {k = 0} {k′ = 0} refl t∶T refl (≈-refl (proj₂ (presup-tm t∶T))) (there (there (there (here refl))))
no-neutral-Se-gen {_} {_} refl (conv ⊢t ≈T) refl T≈ T′∈ = no-neutral-Se-gen refl ⊢t refl (≈-trans ≈T T≈) T′∈


no-neutral-Se : ∀ {i} →
                (Se i ↙ (1 + i)) ∷ [] ⊢ Ne⇒Exp u ∶[ i ] v 0 →
                ----------------
                ⊥
no-neutral-Se ⊢u = no-neutral-Se-gen {S = N} {S′ = N} {S″ = N} {k = 0} {k′ = 0} {k″ = 0} {k‴ = 0} 
                                     refl ⊢u refl
                                     (≈-refl (conv (vlookup (⊢∷ ⊢[] (Se-wf _ ⊢[])) here)
                                                   (Se-[] _ (s-wk (⊢∷ ⊢[] (Se-wf _ ⊢[]))))))
                                     (here refl)

consistency : ∀ {i} → [] ⊢ t ∶[ 1 + i ] Π ((Se i) ↙ (1 + i)) ((v 0) ↙ i) → ⊥
consistency {_} {i} ⊢t  with fundamental-⊢t⇒⊩t ⊢t
... | record { ⊩Γ = ⊩[] ; krip = krip } 
    with krip {ρ = emp} (s-I ⊢[])
...    | record { ⟦T⟧ = .(Π (ℕ.suc i) _ (v 0 ↙ i) (λ n → ze)) ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦Π⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ 
             ; T∈𝕌 = Π i≡maxjk jA RT _ _ ; t∼⟦t⟧ = record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } } 
       rewrite 𝕌-wf-gen (1 + i) (ΠI≤′ (1 + i) i i≡maxjk)
             | 𝕌-wf-gen i (ΠO≤′ (1 + i) i i≡maxjk)
             | Glu-wf-gen (1 + i) (ΠI≤′ (1 + i) i i≡maxjk)
             | Glu-wf-gen i (ΠO≤′ (1 + i) i i≡maxjk)
             with krip (⊢wI ⊢[]) 
                | krip (⊢wwk (⊢∷ ⊢[] (t[σ]-Se ⊢IT (s-I ⊢[]))))
                | Bot⊆El jA (Bot-l 0)
...             | record { IT-rel = IT-rel }  
                | record { ap-rel = ap-rel }
                | l∈A 
                with RT l∈A 
                   | ap-rel (®El-resp-T≈ jA (v0®x jA IT-rel) ([]-cong-Se′ ([I] ⊢IT) (s-wk (⊢∷ ⊢[] (t[σ]-Se ⊢IT (s-I ⊢[])))))) l∈A 
...                | record { ↘⟦T⟧ = ⟦v⟧ .0 ; ↘⟦T′⟧ = ⟦v⟧ .0 ; T≈T′ = ne C≈C′ _ _ } 
                   | record { fa = .(↑ _ _ _) ; ↘fa = ↘fa ; ®fa = ne fa≈ refl _ , record { krip = krip } } = no-neutral-Se ⊢u′
    where
      ⊢u : (IT ↙ (1 + i)) ∷ [] ⊢ Ne⇒Exp (proj₁ (fa≈ 1)) ∶[ i ] OT
      ⊢u = conv (ctxeq-tm (∷-cong″ ([I] ⊢IT)) (proj₁ (proj₂ (proj₂ (presup-≈ (proj₂ (krip (⊢wI (⊢∷ ⊢[] (t[σ]-Se ⊢IT (s-I ⊢[]))))))))))) 
                (≈-trans ([]-cong-Se′ (≈-trans ([]-cong-Se‴ ⊢OT (wk,v0≈I (⊢∷ ⊢[] ⊢IT))) ([I] ⊢OT)) (s-I (⊢∷ ⊢[] ⊢IT))) ([I] ⊢OT))

      ⊢Se = Se-wf i ⊢[]
      ⊢[Se] = ⊢∷ ⊢[] ⊢Se

      T≈′ : [] ⊢ Π ((Se i) ↙ (1 + i)) ((v 0) ↙ i) ≈ Π (IT ↙ (1 + i)) (OT ↙ i) ∶[ 2 + i ] Se (1 + i)
      T≈′ = ≈-trans (≈-sym ([I] (Π-wf ⊢Se (conv (vlookup ⊢[Se] here) (Se-[] _ (s-wk ⊢[Se]))) (sym (trans (⊔-comm (1 + i) i) (m≤n⇒m⊔n≡n (n≤1+n _))))))) T≈

      IT≈ : [] ⊢ IT ≈ Se i ∶[ 2 + i ] Se (1 + i)
      IT≈ = ≈-sym (proj₁ (proj₂ (proj₂ (proj₂ (Π-≈-inj T≈′)))))

      OT≈ : (Se i ↙ (1 + i)) ∷ [] ⊢ OT ≈ v 0 ∶[ 1 + i ] Se i
      OT≈ = ≈-sym (proj₂ (proj₂ (proj₂ (proj₂ (Π-≈-inj T≈′)))))

      ⊢u′ : (Se i ↙ (1 + i)) ∷ [] ⊢ Ne⇒Exp (proj₁ (fa≈ 1)) ∶[ i ] v 0
      ⊢u′ = conv (ctxeq-tm (∷-cong″ IT≈) ⊢u) OT≈    

,-inv′ : ∀ {i Σ} → 
  Γ ⊢s (σ , t ∶ T ↙ i) ∶ Δ →
  Γ ⊢s σ ∶ Σ →
  Γ ⊢ t ∶[ i ] sub T σ × ⊢ (T ↙ i) ∷ Σ ≈ Δ 
,-inv′ ⊢σ,t ⊢σ
  with ,-inv ⊢σ,t
... | Σ′ , ⊢σ′ , ⊢t , T∷Σ′≈ 
  with presup-⊢≈ T∷Σ′≈ 
... | ⊢∷ ⊢Σ ⊢T , _
  with unique-ctx ⊢σ ⊢σ′
... | Σ≈Σ′ = ⊢t , ⊢≈-trans (∷-cong-simp Σ≈Σ′ (≈-refl (ctxeq-tm (⊢≈-sym Σ≈Σ′) ⊢T))) T∷Σ′≈

t[σ]-inv′ : ∀ {i} →
           Γ ⊢ t [ σ ] ∶[ i ] T →
           Γ ⊢s σ ∶ Δ → 
           ∃ λ S → Δ ⊢ t ∶[ i ] S × Γ ⊢ T ≈ S [ σ ] ∶[ 1 + i ] Se i
t[σ]-inv′ ⊢t[σ] ⊢σ 
  with t[σ]-inv ⊢t[σ]
... | Δ′ , S , ⊢σ′ , ⊢t , T≈ = S , ctxeq-tm (unique-ctx ⊢σ′ ⊢σ) ⊢t , T≈