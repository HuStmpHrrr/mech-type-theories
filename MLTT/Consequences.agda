{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Some consequences of fundamental theorems of completeness and soundness
module MLTT.Consequences (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib

open import MLTT.Statics.Properties
open import MLTT.Semantics.PER
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Semantics.Realizability fext
open import MLTT.Completeness fext
open import MLTT.Completeness.LogRel
open import MLTT.Completeness.Fundamental fext
open import MLTT.Completeness.Consequences fext
open import MLTT.Soundness fext
open import MLTT.Soundness.LogRel
open import MLTT.Soundness.Properties.LogRel fext
open import MLTT.Soundness.Properties.Substitutions fext
open import MLTT.Soundness.Cumulativity fext
open import MLTT.Soundness.Realizability fext
open import MLTT.Soundness.Fundamental fext



-- Equivalence of Π types is injective.
Π-≈-inj : ∀ {i} →
          Γ ⊢ Π S T ≈ Π S′ T′ ∶ Se i →
          Γ ⊢ S ≈ S′ ∶ Se i × S ∷ Γ ⊢ T ≈ T′ ∶ Se i
Π-≈-inj {Γ} {S} {T} {S′} {T′} {i} Π≈
  with ⊢Γ , ⊢ΠST , ⊢ΠS′T′ , _ ← presup-≈ Π≈
    with ⊢S  , ⊢T  ← Π-inv ⊢ΠST
       | ⊢S′ , ⊢T′ ← Π-inv ⊢ΠS′T′
      with ⊨Γ , _ , rel ← fundamental-t≈t′ Π≈
         | ⊨SΓ₁@(∷-cong ⊨Γ₁ Srel₁) , _ , rel₁ ← fundamental-⊢t ⊢T
         | record { ⊩Γ = ⊩Γ ; krip = Skrip } ← fundamental-⊢t⇒⊩t ⊢S
         | record { ⊩Γ = ⊩Γ₁ ; krip = S′krip } ← fundamental-⊢t⇒⊩t ⊢S′
        with ρ′ , _ , ρ′init , ρ′init₁ , ρ′∈ ← InitEnvs-related ⊨SΓ₁
          rewrite InitEnvs-det ρ′init₁ ρ′init
            with s-∷ {ρ = ρ} {A = A} ρinit S↘ ← ρ′init
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
                    | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                    | ⟦⟧-det ↘⟦S′⟧′ ↘⟦S′⟧
                with Π S≈S′ Trel ← ΠST≈ΠS′T′
                   | record { A∈𝕌 = S∈𝕌 ; rel = Srel } ← S∼⟦S⟧
                   | record { A∈𝕌 = S′∈𝕌 ; rel = S′rel } ← S′∼⟦S′⟧
                   with S≈S′′ ← ≈-sym ([I]-≈ˡ-Se (≈-sym ([I]-≈ˡ-Se (®⇒≈ S′∈𝕌 (®-transport S∈𝕌 S′∈𝕌 S≈S′ Srel) S′rel)))) = S≈S′′ , T≈T′-helper
  where
    s∈₁ : l′ A (len Γ) ∈′ El _ S≈S′
    s∈₁
      with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← Srel₁ ρ∈
        rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧ = El-one-sided S≈S′₁ S≈S′ s∈

    T≈T′-helper : S ∷ Γ ⊢ T ≈ T′ ∶ Se i
    T≈T′-helper
      with record { ⊩Γ = ⊩SΓ ; krip = Tkrip } ← fundamental-⊢t⇒⊩t ⊢T
         | record { ⊩Γ = ⊩SΓ₁ ; krip = T′krip } ← fundamental-⊢t⇒⊩t (ctxeq-tm (∷-cong (⊢≈-refl ⊢Γ) (≈-sym S≈S′′)) ⊢T′)
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


closed-®Nat : [] ⊢ t ∶N® a ∈Nat →
              IsND a
closed-®Nat (ze _)      = ze
closed-®Nat (su _ t∼a)  = su (closed-®Nat t∼a)
closed-®Nat (ne c∈ rel)
  with ≈u ← rel (⊢wI ⊢[])
    with _ , _ , ⊢u , _ ← presup-≈ ≈u = ⊥-elim (no-closed-Ne ⊢u)


closed-NbE-N : [] ⊢ t ∶ N →
               NbE [] t N w →
               IsN w
closed-NbE-N ⊢t record { envs = envs ; nbe = record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } }
  with record { ⊩Γ = ⊩[] ; krip = krip } ← fundamental-⊢t⇒⊩t ⊢t
    with record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧′ ; T∈𝕌 = N ; t∼⟦t⟧ = t∼⟦t⟧ , _ } ← krip {ρ = envs} (s-I ⊢[])
      rewrite ⟦⟧-det ↘⟦t⟧′ ↘⟦t⟧ = helper (closed-®Nat t∼⟦t⟧) ↓⟦t⟧
  where helper : IsND a → Rf 0 - ↓ N a ↘ w → IsN w
        helper ze     (Rze .0)    = ze
        helper (su a) (Rsu .0 ↘w) = su (helper a ↘w)


canonicity-N : [] ⊢ t ∶ N →
               ∃ λ w → [] ⊢ t ≈ Nf⇒Exp w ∶ N × IsN w
canonicity-N ⊢t
  with w , nbe , ≈w ← soundness ⊢t = w , ≈w , closed-NbE-N ⊢t nbe

no-neutral-Se-gen : ∀ {i j} →
                    t ≡ Ne⇒Exp u →
                    Γ ⊢ t ∶ T →
                    Γ ≡ Se i ∷ [] →
                    Γ ⊢ T ≈ T′ ∶ Se j →
                    T′ ∈ v 0 ∷ N ∷ Π S S′ ∷ [] →
                    ----------------
                    ⊥
no-neutral-Se-gen {_} {v .0} {j = j} refl (vlookup ⊢Γ here) refl T≈ T′∈ = not-Se-≈-bundle (s≤s z≤n) (≈-trans (lift-⊢≈-Se-max {j = j} (≈-sym (Se-[] _ (s-wk ⊢Γ)))) (lift-⊢≈-Se-max′ T≈)) T′∈
no-neutral-Se-gen {_} {rec T z s u} refl (N-E _ _ _ ⊢t) eq T≈ T′∈       = no-neutral-Se-gen {S = N} {S′ = N} refl ⊢t eq (≈-refl (N-wf 0 (proj₁ (presup-tm ⊢t)))) (there (here refl))
no-neutral-Se-gen {_} {u $ n} refl (Λ-E ⊢t _) eq T≈ T′∈                 = no-neutral-Se-gen refl ⊢t eq (≈-refl (proj₂ (proj₂ (presup-tm ⊢t)))) (there (there (here refl)))
no-neutral-Se-gen {_} {_} refl (cumu ⊢t) refl T≈ T′∈                    = not-Se-≈-bundle (s≤s z≤n) T≈ T′∈
no-neutral-Se-gen {_} {_} refl (conv ⊢t ≈T) eq T≈ T′∈                   = no-neutral-Se-gen refl ⊢t eq (≈-trans (lift-⊢≈-Se-max ≈T) (lift-⊢≈-Se-max′ T≈)) T′∈

no-neutral-Se : ∀ {i} →
                Se i ∷ [] ⊢ Ne⇒Exp u ∶ v 0 →
                ----------------
                ⊥
no-neutral-Se ⊢u = no-neutral-Se-gen {S = N} {S′ = N} refl ⊢u refl (≈-refl (conv (vlookup (⊢∷ ⊢[] (Se-wf _ ⊢[])) here) (Se-[] _ (s-wk (⊢∷ ⊢[] (Se-wf _ ⊢[])))))) (here refl)


consistency : ∀ {i} → [] ⊢ t ∶ Π (Se i) (v 0) → ⊥
consistency {_} {i} ⊢t
  with fundamental-⊢t⇒⊩t ⊢t
... | record { ⊩Γ = ⊩[] ; lvl = lvl ; krip = krip }
    with krip {ρ = emp} (s-I ⊢[])
...    | record { ↘⟦T⟧ = ⟦Π⟧ (⟦Se⟧ ._) ; T∈𝕌 = T∈𝕌@(Π iA@(U 0<l _) RT) ; t∼⟦t⟧ = t∼⟦t⟧@record { IT = IT ; OT = OT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } }
        with ®Π-wf iA RT (®El⇒® T∈𝕌 t∼⟦t⟧)
           | krip (⊢wI ⊢[])
           | krip (⊢wwk (⊢∷ ⊢[] (t[σ]-Se (®Π-wf iA RT (®El⇒® T∈𝕌 t∼⟦t⟧)) (s-I ⊢[]))))
           | Bot⊆El iA (Bot-l 0)
...        | ⊢IT
           | record { IT-rel = IT-rel }
           | record { ap-rel = ap-rel }
           | l∈A
           with RT l∈A
              | ap-rel (®El-resp-T≈ iA (v0®x iA IT-rel) ([]-cong-Se′ ([I] ⊢IT) (s-wk (⊢∷ ⊢[] (t[σ]-Se ⊢IT (s-I ⊢[])))))) l∈A
...           | record { ↘⟦T⟧ = ⟦v⟧ .0 ; ↘⟦T′⟧ = ⟦v⟧ .0 ; T≈T′ = ne C≈C′ }
              | record { fa = .(↑ _ _) ; ®fa = ne fa≈ , record { krip = krip } } = no-neutral-Se ⊢u′
  where ⊢u : IT ∷ [] ⊢ Ne⇒Exp (proj₁ (fa≈ 1)) ∶ OT
        ⊢u = conv (ctxeq-tm (∷-cong []-≈ ([I] ⊢IT)) (proj₁ (proj₂ (proj₂ (presup-≈ (proj₂ (krip (⊢wI (⊢∷ ⊢[] (t[σ]-Se ⊢IT (s-I ⊢[])))))))))))
                  (≈-trans ([]-cong-Se′ (≈-trans ([]-cong-Se″ ⊢OT (wk,v0≈I (⊢∷ ⊢[] ⊢IT))) ([I] ⊢OT)) (s-I (⊢∷ ⊢[] ⊢IT))) ([I] ⊢OT))

        ⊢[Se] = ⊢∷ ⊢[] (Se-wf i ⊢[])

        T≈′ : [] ⊢ Π (Se i) (v 0) ≈ Π IT OT ∶ Se _
        T≈′ = ≈-trans (lift-⊢≈-Se-max {j = lvl} (≈-sym ([I] (Π-wf (Se-wf i ⊢[]) (cumu (conv (vlookup ⊢[Se] here) (Se-[] i (s-wk ⊢[Se])))))))) (lift-⊢≈-Se-max′ T≈)

        IT≈ : [] ⊢ IT ≈ Se i ∶ Se _
        IT≈ = ≈-sym (proj₁ (Π-≈-inj T≈′))

        OT≈ : Se i ∷ [] ⊢ OT ≈ v 0 ∶ Se _
        OT≈ = ≈-sym (proj₂ (Π-≈-inj T≈′))

        ⊢u′ : Se i ∷ [] ⊢ Ne⇒Exp (proj₁ (fa≈ 1)) ∶ v 0
        ⊢u′ = conv (ctxeq-tm (∷-cong []-≈ IT≈) ⊢u) OT≈
