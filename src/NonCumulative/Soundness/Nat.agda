{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Nat
module NonCumulative.Soundness.Nat (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties

open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties.Subst
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Semantics.Evaluation
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Realizability fext
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Completeness.LogRel
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Contexts fext
open import NonCumulative.Soundness.Realizability fext
open import NonCumulative.Soundness.ToSyntax fext
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Substitutions fext

N-wf′ : ⊩ Γ →
        -------------
        Γ ⊩ N ∶[ 1 ] Se 0
N-wf′ ⊩Γ = record
    { ⊩Γ = ⊩Γ ; krip = helper }
    where
      helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp 1 Δ N (Se 0) σ ρ
      helper σ®ρ = record {
        ⟦T⟧ = U 0 ;
        ⟦t⟧ = N ;
        ↘⟦T⟧ = ⟦Se⟧ 0 ;
        ↘⟦t⟧ = ⟦N⟧ ;
        T∈𝕌 = U′ ;
        t∼⟦t⟧ = record
          { t∶T = t[σ] (N-wf (⊩⇒⊢ ⊩Γ)) ⊢σ
          ; T≈ = Se-[] 0 ⊢σ
          ; A∈𝕌 = N refl
          ; rel = N-[] ⊢σ
          }
        }
        where ⊢σ = s®⇒⊢s ⊩Γ σ®ρ

ze-I′ : ⊩ Γ →
        -----------
        Γ ⊩ ze ∶[ 0 ] N
ze-I′ ⊩Γ = record
    { ⊩Γ = ⊩Γ ;
      krip = helper
    }
    where
      helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp 0 Δ ze N σ ρ
      helper σ®ρ = record {
        ⟦T⟧ = N ;
        ⟦t⟧ = ze ;
        ↘⟦T⟧ = ⟦N⟧ ;
        ↘⟦t⟧ = ⟦ze⟧ ;
        T∈𝕌 = N refl ;
        t∼⟦t⟧ = (ze (ze-[] ⊢σ)) , N-[] ⊢σ
        }
        where ⊢σ = s®⇒⊢s ⊩Γ σ®ρ

su-I′ : Γ ⊩ t ∶[ 0 ] N →
        -------------
        Γ ⊩ su t ∶[ 0 ] N
su-I′ {t = t} ⊩t = record { ⊩Γ = ⊩Γ ; krip = helper }
    where
      open _⊩_∶[_]_ ⊩t
      helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp 0 Δ (su t) N σ ρ
      helper σ®ρ with krip σ®ρ
      ... | record { ⟦T⟧ = .N ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = N′ ; t∼⟦t⟧ = t∼⟦t⟧ , _ } =
        record { ⟦T⟧ = N ; ⟦t⟧ = su ⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ⟦su⟧ ↘⟦t⟧ ; T∈𝕌 = N refl ; t∼⟦t⟧ = (su (su-[] ⊢σ (⊩⇒⊢-tm ⊩t)) t∼⟦t⟧) , N-[]  ⊢σ }
        where ⊢σ = s®⇒⊢s ⊩Γ σ®ρ

----------------------------------------
-- Semantic judgment for recursor of Nat
--
-- The proof is complicated because we must embed the recursor in Agda. This embedding
-- is done by N-E-helper, which recurses on the gluing judgment for Nat. Its type is
-- given by N-E-helper-type.  We explain its type in details:
--
--     -- The type is done by pattern matching on a semantic judgment of context stack T ∷ N ∷ Γ.
--     N-E-helper-type {T} {Γ} ⊩TNΓ@(⊩∷ {i = i} ⊩NΓ@(⊩∷ ⊩Γ _ _) _ gT) =
--       ∀ {Δ s r σ ρ t a} →

--       -- The following three judgments are given by the assumptions of the judgment
--       N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
--       Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
--       (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →

--       -- Assuming any related substitution σ and environment ρ,
--       (σ®ρ : Δ ⊢s σ ∶ ⊩Γ ® ρ) →
--
--       -- if s[σ] and its evaluation ⟦s⟧(ρ) are related,
--       (glus : GluExp i Δ s (T [| ze ∶ N₀ ]) σ ρ) →
--
--       -- further if any related substitution σ′ and ρ′, r[σ′] and its evaluation ⟦r⟧(ρ′) are related,
--       (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩TNΓ ® ρ → GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ∶ N₀]) σ ρ) →
--
--       -- given a related t and a by Nat,
--       (t®a : Δ ⊢ t ∶N® a ∈Nat) →
--
--       -- we can derive a semantic value ra that is the result of the recursion on a
--       -- and the syntactic recursion and ra are related.
--       let open GluExp gs hiding (T∈𝕌)
--           open GluTyp (gT (cons-N ⊩NΓ σ®ρ t∼a))
--       in ∃ λ ra →   rec∙ T , ⟦t⟧ , r , ρ , a ↘ ra
--                    × Δ ⊢ rec (T [ q N₀ σ ]) (s [ σ ]) (r [ q (T ↙ i) (q N₀ σ) ]) t ∶[ i ] T [ σ , t ∶ N₀ ] ®[ i ] ra ∈El T∈𝕌

cons-N-type : ⊩ N₀ ∷ Γ → Set
cons-N-type ⊩NΓ@(⊩∷ ⊩Γ _ _) =
  ∀ {Δ σ ρ t a} →
  Δ ⊢s σ ∶ ⊩Γ ® ρ →
  Δ ⊢ t ∶N® a ∈Nat →
  Δ ⊢s σ , t ∶ N₀ ∶ ⊩NΓ ® ρ ↦ a

cons-N : (⊩NΓ : ⊩ N₀ ∷ Γ) → cons-N-type ⊩NΓ
cons-N ⊩NΓ@(⊩∷ ⊩Γ ⊢N _) {_} {σ} {_} {t} σ®ρ t®a
  with s®⇒⊢s ⊩Γ σ®ρ
...  | ⊢σ
     with presup-s ⊢σ
...     | ⊢Δ , _ = record
  { ⊢σ   = s-, ⊢σ ⊢N ⊢t′
  ; pσ   = σ
  ; v0σ  = t
  ; ⟦T⟧  = N
  ; ≈pσ  = p-, ⊢σ ⊢N ⊢t′
  ; ≈v0σ = [,]-v-ze ⊢σ ⊢N ⊢t′
  ; ↘⟦T⟧ = ⟦N⟧
  ; T∈𝕌  = N refl
  ; t∼ρ0 = t®a , ≈N
  ; step = σ®ρ
  }
  where
    ⊢t  = ®Nat⇒∶Nat t®a ⊢Δ
    ≈N  = N-[] ⊢σ
    ⊢t′ = conv ⊢t (≈-sym ≈N)

N-E-helper-type : ∀ {i} → ⊩ (T ↙ i) ∷ N₀ ∷ Γ → Set
N-E-helper-type {T} {Γ} ⊩TNΓ@(⊩∷ {i = i} ⊩NΓ@(⊩∷ ⊩Γ _ _) _ gluT) =
  ∀ {Δ s r σ ρ t a} →
  N₀ ∷ Γ ⊢ T ∶[ 1 + i ] Se i →
  Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] →
  (T ↙ i) ∷ N₀ ∷ Γ ⊢ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
  (σ®ρ : Δ ⊢s σ ∶ ⊩Γ ® ρ) →
  (glus : GluExp i Δ s (T [| ze ∶ N₀ ]) σ ρ) →
  (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩TNΓ ® ρ → GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ∶ N₀ ]) σ ρ) →
  (t®a : Δ ⊢ t ∶N® a ∈Nat) →
  let open GluExp glus hiding (T∈𝕌)
      open GluTyp (gluT (cons-N ⊩NΓ σ®ρ t®a))
  in ∃ λ ra →   rec∙ (T ↙ i) , ⟦t⟧ , r , ρ , a ↘ ra
               × Δ ⊢ rec (T [ q ( N₀ ) σ ] ↙ i) (s [ σ ]) (r [ q ( T ↙ i ) (q ( N₀ ) σ) ]) t ∶ T [ σ , t ∶ N₀ ] ®[ i ] ra ∈El T∈𝕌

N-E-helper : ∀ {i} → (⊩TNΓ : ⊩ (T ↙ i) ∷ N₀ ∷ Γ) →
             N-E-helper-type ⊩TNΓ
N-E-helper {T} {Γ} ⊩TNΓ@(⊩∷ {i = i} ⊩NΓ@(⊩∷ ⊩Γ _ _) _ gluT′) {Δ} {s} {r} {σ} {ρ} {_} {_}
           ⊢T ⊢s ⊢w σ®ρ
           glus@record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } glur′ t®a = recurse t®a
  where
    open ER
    rec′ : Exp → Exp
    rec′ t = rec (T [ q ( N₀ ) σ ] ↙ i) (s [ σ ]) (r [ q ( T ↙ i ) (q ( N₀ ) σ) ]) t
    ⊢σ   = s®⇒⊢s ⊩Γ σ®ρ
    open NatTyping ⊢T ⊢σ
    ≈N   = ≈-sym (N-[] ⊢σ)
    ⊢ze′ = conv (ze-I ⊢Δ) ≈N

    gluT : Δ ⊢ t ∶N® a ∈Nat → GluTyp i Δ T (σ , t ∶ N₀) (ρ ↦ a)
    gluT t®a′ = gluT′ (cons-N ⊩NΓ σ®ρ t®a′)

    glur : (t®a : Δ ⊢ t ∶N® a ∈Nat) →
           (let open GluTyp (gluT t®a) renaming (T∈𝕌 to T∈𝕌′) in Δ ⊢ t′ ∶ T [ σ , t ∶ N₀ ] ®[ i ] b ∈El T∈𝕌′) →
           GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ∶ N₀  ]) ((σ , t ∶ N₀) , t′ ∶ T ↙ i) (ρ ↦ a ↦ b)
    glur t®a t′®b = glur′ (s®-cons ⊩TNΓ (cons-N ⊩NΓ σ®ρ t®a) t′®b)

    T[σ,ze]≈T[|ze][σ] : Δ ⊢ T [ σ , ze ∶ N₀ ] ≈ T [| ze ∶ N₀ ] [ σ ] ∶[ 1 + i ] Se i
    T[σ,ze]≈T[|ze][σ] = ≈-sym ([]-I,ze-∘ ⊢T ⊢σ)

    T[σ,t]≈T[qσ][|t]′ : Δ ⊢ t ∶[ 0 ] N → Δ ⊢ T [ σ , t ∶ N₀ ] ≈ T [ q N₀ σ ] [| t ∶ N [ σ ] ↙ 0 ] ∶[ 1 + i ] Se i
    T[σ,t]≈T[qσ][|t]′ ⊢t = []-q-∘-,′ ⊢T ⊢σ (conv ⊢t ≈N)

    T[σ,t]≈T[qσ][|t] : Δ ⊢ t ∶[ 0 ] N → Δ ⊢ T [ σ , t ∶ N₀ ] ≈ T [ q N₀ σ ] [| t ∶ N₀ ] ∶[ 1 + i ] Se i
    T[σ,t]≈T[qσ][|t] ⊢t = ≈-trans (T[σ,t]≈T[qσ][|t]′ ⊢t) ([]-cong-Se‴ ⊢Tqσ
                                                                      (s-≈-sym (,-cong (I-≈ ⊢Δ) Δ⊢N ≈N
                                                                               (≈-conv-N-[]-sym (≈-refl ⊢t) (s-I ⊢Δ)))))

    T[σ,ze]≈T[qσ][|ze] : Δ ⊢ T [ σ , ze ∶ N₀ ] ≈ T [ q N₀ σ ] [| ze ∶ N₀ ] ∶[ 1 + i ] Se i
    T[σ,ze]≈T[qσ][|ze] = T[σ,t]≈T[qσ][|t] (ze-I ⊢Δ)

    ⊢sσ   = conv (t[σ] ⊢s ⊢σ) (≈-trans (≈-sym T[σ,ze]≈T[|ze][σ]) T[σ,ze]≈T[qσ][|ze])
    ⊢wqqσ = conv (t[σ] ⊢w ⊢qqσ) (rec-β-su-T-swap ⊢Δ ⊢TNΓ ⊢σ)

    rec-cong′ : Δ ⊢ t ≈ t′ ∶[ 0 ] N →
                Δ ⊢ rec′ t ≈ rec′ t′ ∶[ i ] T [ q N₀ σ ] [| t ∶ N₀ ]
    rec-cong′ = rec-cong ⊢Tqσ (≈-refl ⊢Tqσ) (≈-refl ⊢sσ) (≈-refl ⊢wqqσ)

    N-E′ : Δ ⊢ t ∶[ 0 ] N →
           Δ ⊢ rec′ t ∶[ i ] T [ q N₀ σ ] [| t ∶ N₀ ]
    N-E′ = N-E ⊢Tqσ ⊢sσ ⊢wqqσ

    recurse : (t®a : Δ ⊢ t ∶N® a ∈Nat) →
          let open GluTyp (gluT t®a) renaming (T∈𝕌 to T∈𝕌′)
          in ∃ λ ra →   rec∙ (T ↙ i) , ⟦t⟧ , r , ρ , a ↘ ra
                       × Δ ⊢ rec′ t ∶ T [ σ , t ∶ N₀ ] ®[ i ] ra ∈El T∈𝕌′
    recurse {t} {.ze} (ze ≈ze)
      with gluT (ze ≈ze)
    ...  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ }
        rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ⟦t⟧ , (ze↘ , ®El-one-sided _ _ (®El-resp-T≈ _ (®El-resp-≈ _ t∼⟦t⟧ s[σ]=rec′t) T[|ze][σ]≈T[σ,t]))
      where
        T[|ze][σ]≈T[σ,t] : Δ ⊢ T [| ze ∶ N₀ ] [ σ ] ≈ T [ σ , t ∶ N₀ ] ∶[ 1 + i ] Se i
        T[|ze][σ]≈T[σ,t] =
          begin
            T [| ze ∶ N₀ ] [ σ ] ≈⟨ []-I,ze-∘ ⊢T ⊢σ ⟩
            T [ σ , ze ∶ N₀ ] ≈⟨ []-cong-Se‴ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-refl Γ⊢N) (≈-sym (≈-conv ≈ze ≈N))) ⟩
            T [ σ , t ∶ N₀ ]
          ∎

        s[σ]=rec′t : Δ ⊢ s [ σ ] ≈ rec′ t ∶[ i ] T [| ze ∶ N₀ ] [ σ ]
        s[σ]=rec′t = ≈-conv (
            begin
              s [ σ ] ≈˘⟨ ≈-conv (rec-β-ze ⊢Tqσ ⊢sσ ⊢wqqσ) (≈-sym T[σ,ze]≈T[qσ][|ze]) ⟩
              rec′ ze ≈˘⟨ ≈-conv (rec-cong′ ≈ze) (≈-trans ([]-cong-Se‴ ⊢Tqσ (,-cong (I-≈ ⊢Δ) Δ⊢N (≈-refl Δ⊢N) (≈-conv ≈ze (≈-sym (N-[] (s-I ⊢Δ)))))) (≈-sym T[σ,ze]≈T[qσ][|ze])) ⟩
              rec′ t
            ∎ )
            T[σ,ze]≈T[|ze][σ]
    recurse {t} {.(su _)} t®a@(su {t′ = t′} ≈sut′ t′®a)
      with recurse t′®a
    ...  | ra , ↘ra , rect′®ra
        with gluT t®a
           | glur t′®a rect′®ra
    ...    | record { ⟦T⟧ = ⟦T⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; T∈𝕌 = T∈𝕌₁ ; T∼⟦T⟧ = T∼⟦T⟧ }
           | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
           rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = ⟦t⟧ , ((su↘ ↘ra ↘⟦t⟧) , ®El-one-sided _ _ (®El-resp-≈ _ (®El-resp-T≈ _ t∼⟦t⟧ T[wkwk,suv1][σ,t′,rec′t′]≈T[σ,t]) r[σ,t′,rec′t′]≈rec′t))
      where
        ⊢t      = ®Nat⇒∶Nat t®a ⊢Δ
        ⊢t′     = ®Nat⇒∶Nat t′®a ⊢Δ
        ⊢t′₁    = conv ⊢t′ ≈N
        ⊢I,t′   = ⊢I,t ⊢Δ Δ⊢N ⊢t′
        ⊢v1     = ⊢vn∶N L.[ T ↙ i ] ⊢TNΓ refl
        ⊢suv1   = conv (su-I ⊢v1) (≈-sym (N-[] ⊢wkwk))
        ⊢σ,t′   = s-, ⊢σ Γ⊢N (conv ⊢t′ ≈N)
        ⊢wect′  = conv (N-E′ ⊢t′) (≈-sym (T[σ,t]≈T[qσ][|t] ⊢t′))
        ⊢σt′rec = s-, ⊢σ,t′ ⊢T ⊢wect′

        T[wkwk,suv1][σ,t′,rec′t′]≈T[σ,t] : Δ ⊢ T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ (σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i ] ≈ T [ σ , t ∶ N₀ ] ∶[ 1 + i ] Se i
        T[wkwk,suv1][σ,t′,rec′t′]≈T[σ,t] =
          begin
            T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ (σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i ] ≈⟨ [∘]-Se ⊢T (s-, ⊢wkwk Γ⊢N ⊢suv1) ⊢σt′rec ⟩
            T [ ((wk ∘ wk) , su (v 1) ∶ N₀) ∘ ((σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i) ] ≈⟨ []-cong-Se‴ ⊢T (,-∘ ⊢wkwk Γ⊢N ⊢suv1 ⊢σt′rec) ⟩
            T [ ((wk ∘ wk) ∘ ((σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i)) , (su (v 1) [ ((σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i) ]) ∶ N₀ ] ≈⟨ []-cong-Se‴ ⊢T
                  (,-cong (wk∘wk∘,, ⊢Γ ⊢σ Γ⊢N ⊢T ⊢t′₁ ⊢wect′)
                          Γ⊢N (≈-refl Γ⊢N)
                          (≈-conv (≈-trans (su-[] ⊢σt′rec ⊢v1)
                                           (≈-trans (su-cong (≈-conv ([,]-v-su ⊢σ,t′ ⊢T ⊢wect′ here)
                                                                     (≈-trans ([]-cong-Se′ (N-[] ⊢wk) ⊢σ,t′)
                                                                     (N-[] ⊢σ,t′))))
                                                    (≈-trans (su-cong (≈-conv ([,]-v-ze ⊢σ Γ⊢N ⊢t′₁) (N-[] ⊢σ)))
                                                             (≈-sym ≈sut′))))
                                  (≈-sym (N-[] (s-∘ ⊢σt′rec ⊢wkwk))))) ⟩
            T [ σ , t ∶ N₀ ]
          ∎

        qσ∘[|t'],rec′t′≈σ,t′,rec′t′ : Δ ⊢s (q N₀ σ ∘ (I , t′ ∶ N₀)) , rec′ t′ ∶ T ↙ i ≈ (σ , t′ ∶ N₀ ) , rec′ t′ ∶ T ↙ i ∶ (T ↙ i) ∷ N₀ ∷ Γ
        qσ∘[|t'],rec′t′≈σ,t′,rec′t′ = s-≈-sym (,-cong (s-≈-sym (s-≈-trans (∘-cong (,-cong (I-≈ ⊢Δ) Δ⊢N ≈N (≈-refl (conv ⊢t′ (≈-sym (N-[] (s-I ⊢Δ)))))) (s-≈-refl ⊢qσ))
                                                                          (qσ∘[I,t]≈σ,t ⊢Δ Γ⊢N ⊢σ ⊢t′₁)))
                                                      ⊢T (≈-refl ⊢T) (≈-refl ⊢wect′))

        r[σ,t′,rec′t′]≈rec′t : Δ ⊢ r [ (σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i ] ≈ rec′ t ∶[ i ] T [ σ , t ∶ N₀ ]
        r[σ,t′,rec′t′]≈rec′t =
          begin
            r [ (σ , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i ] ≈⟨ ≈-conv ([]-cong (≈-refl ⊢w) (s-≈-sym qσ∘[|t'],rec′t′≈σ,t′,rec′t′)) T[wkwk,suv1][σ,t′,rec′t′]≈T[σ,t] ⟩
            r [ (q N₀ σ ∘ I , t′ ∶ N₀) , rec′ t′ ∶ T ↙ i ] ≈˘⟨ ≈-conv ([]-q-, ⊢qσ ⊢T ⊢I,t′ (N-E′ ⊢t′) ⊢w)
                                                                       (≈-trans ([]-cong-Se‴ (t[σ]-Se ⊢T (s-, ⊢wkwk Γ⊢N ⊢suv1)) qσ∘[|t'],rec′t′≈σ,t′,rec′t′)
                                                                                T[wkwk,suv1][σ,t′,rec′t′]≈T[σ,t]) ⟩
            r [ q (T ↙ i) (q N₀ σ) ] [ (I , t′ ∶ N₀) ,  rec′ t′ ∶ T [ q N₀ σ ] ↙ i ] ≈˘⟨ ≈-conv (rec-β-su ⊢Tqσ ⊢sσ ⊢wqqσ ⊢t′)
                                                                                                  (≈-trans (≈-sym (T[σ,t]≈T[qσ][|t] (su-I ⊢t′)))
                                                                                                           ([]-cong-Se‴ ⊢T (,-cong (s-≈-refl ⊢σ) Γ⊢N (≈-refl Γ⊢N) (≈-sym (≈-conv ≈sut′ ≈N))) )) ⟩
            rec′ (su t′) ≈˘⟨ ≈-conv (rec-cong′ ≈sut′) (≈-sym (T[σ,t]≈T[qσ][|t] ⊢t)) ⟩
            rec′ t
          ∎
    recurse {t} {↑ j A c} t®a@(ne c∈ rel)
      with gluT t®a
    ...  | record { ⟦T⟧ = ⟦T⟧′ ; ↘⟦T⟧ = ↘⟦T⟧′ ; T∈𝕌 = T∈𝕌′ ; T∼⟦T⟧ = T∼⟦T⟧′ }
         with s®⇒⟦⟧ρ ⊩Γ σ®ρ
    ...     | ⊨Γ , ρ∈ = ↑ i ⟦T⟧′ (rec (T ↙ i) ⟦t⟧ r ρ c) , (rec∙ ↘⟦T⟧′) , ®↓El⇒®El _ (record
              { t∶T = conv (N-E′ ⊢t) (≈-sym (T[σ,t]≈T[qσ][|t] ⊢t))
              ; T∼A = T∼⟦T⟧′
          ; c∈⊥ = rec∈⊥-helper
          ; krip = krip-helper
          })
      where
        ⊢t  = ®Nat⇒∶Nat t®a ⊢Δ
        ⊢t′ = conv ⊢t ≈N

        module TRty where
          T-eval : ∀ n → ∃₂ λ A W → ⟦ T ⟧ ρ ↦ l′ 0 N n ↘ A × Rty 1 + n - A at i ↘ W
          T-eval n
            with fundamental-⊢t ⊢T
          ... | ⊨NΓ@(∷-cong ⊨Γ₁ evN _) , Trel = helper′
            where
              ρ∈′ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ∈

              ρl∈ : ρ ↦ l′ 0 N n ∈′ ⟦ ⊨NΓ ⟧ρ
              ρl∈ = ρ∈′ , l∈ (evN ρ∈′)
                where
                  l∈ : (rt : RelTyp _ N _ N _) → l′ 0 N n ∈′ El _ (RelTyp.T≈T′ rt)
                  l∈ record { ⟦T⟧ = .N ; ⟦T′⟧ = .N ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = N′ } = ne (Bot-l n)

              helper′ : ∃₂ λ A W → ⟦ T ⟧ ρ ↦ l′ 0 N n ↘ A × Rty 1 + n - A at i ↘ W
              helper′
                with Trel {_ ↦ _} {_ ↦ _} ρl∈
              ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; T≈T′ = U 1+i≡1+i _ }
                   , record { ⟦t⟧ = ⟦T⟧₁ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; t≈t′ = T≈T′₁ }
                   rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+i≡1+i))
                   with 𝕌⊆TopT T≈T′₁ (1 + n)
              ...     | W , ↘W , _ = ⟦T⟧₁ , W , ↘⟦T⟧₁ , ↘W

        module sRf where
          open _⊢_∶_®↑[_]_∈El_≈_ (®El⇒®↑El T∈𝕌 t∼⟦t⟧) public

        module rRf where
          r-eval : ∀ n →
            let A , _ = TRty.T-eval n in
            ∃₂ λ a A′ →
              ∃ λ w → ⟦ r ⟧ ρ ↦ l′ 0 N n ↦ l′ i A (1 + n) ↘ a
                       × ⟦ T ⟧ ρ ↦ su (l′ 0 N n) ↘ A′
                       × Rf (2 + n) - ↓ i A′ a ↘ w
          r-eval n
            with fundamental-⊢t ⊢w | TRty.T-eval n
          ...  | ⊨TNΓ@(∷-cong ⊨NΓ@(∷-cong ⊨Γ₁ evN _) evT _) , rrel
               | A , _ , ↘A , _ = helper′
            where
              ρ∈′ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ∈

              ρl∈ : ρ ↦ l′ 0 N n ∈′ ⟦ ⊨NΓ ⟧ρ
              ρl∈ = ρ∈′ , l∈ (evN ρ∈′)
                where
                  l∈ : (rt : RelTyp _ N _ N _) → l′ 0 N n ∈′ El _ (RelTyp.T≈T′ rt)
                  l∈ record { ⟦T⟧ = .N ; ⟦T′⟧ = .N ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = N′ } = ne (Bot-l n)

              ρll∈ : ρ ↦ l′ 0 N n ↦ l′ i A (1 + n) ∈′ ⟦ ⊨TNΓ ⟧ρ
              ρll∈ = ρl∈ , l∈ (evT ρl∈)
                where
                  l∈ : (rt : RelTyp _ T _ T _) → l′ i A (1 + n) ∈′ El _ (RelTyp.T≈T′ rt)
                  l∈ record { ⟦T⟧ = ⟦T⟧₁ ; ⟦T′⟧ = ⟦T′⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
                    rewrite ⟦⟧-det ↘⟦T⟧₁ ↘A
                          | ⟦⟧-det ↘⟦T′⟧₁ ↘A = Bot⊆El T≈T′₁ (Bot-l (1 + n))

              helper′ : ∃₂ λ a A′ →
                          ∃ λ w → ⟦ r ⟧ ρ ↦ l′ 0 N n ↦ l′ i A (1 + n) ↘ a
                                   × ⟦ T ⟧ ρ ↦ su (l′ 0 N n) ↘ A′
                                   × Rf (2 + n) - ↓ i A′ a ↘ w
              helper′
                with rrel {_ ↦ _} {_ ↦ _} ρll∈
              ...  | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                   , record { ⟦t⟧ = ⟦t⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; t≈t′ = t≈t′ }
                   with El⊆Top T≈T′ t≈t′ (2 + n)
              ...     | w , ↘w , _ = ⟦t⟧ , ⟦T⟧ , w , ↘⟦t⟧ , ↘⟦T⟧ , ↘w


        rec∈⊥-helper : rec (T ↙ i) ⟦t⟧ r ρ c ∈′ Bot
        rec∈⊥-helper n
          with TRty.T-eval n
             | sRf.a∈⊤ n
             | rRf.r-eval n
             | c∈ n
        ...  | A , W , ↘A , ↘W
             | sw , ↘sw , _
             | a , A′ , w , ↘a , ↘A′ , ↘w
             | cu , ↘cu , _ = recne , ↘recne , ↘recne
          where
            recne = rec (W ↙ i) sw w cu
            ↘recne : Re n - rec (T ↙ i) (⟦t⟧) r (ρ) (c) ↘ recne
            ↘recne = Rr n ↘A ↘W ↘⟦T⟧ ↘sw ↘a ↘A′ ↘w ↘cu

        krip-helper : Δ′ ⊢w τ ∶ Δ → let u , _ = rec∈⊥-helper (len Δ′) in Δ′ ⊢ rec′ t [ τ ] ≈ Ne⇒Exp u ∶[ i ] T [ σ , t ∶ N₀ ] [ τ ]
        krip-helper {Δ′} {τ} ⊢τ
          with presup-s (⊢w⇒⊢s ⊢τ)
        ...  | ⊢Δ′ , _
          -- abstraction for the neutral term
            with TRty.T-eval (len Δ′)
                | sRf.a∈⊤ (len Δ′)
                | rRf.r-eval (len Δ′)
                | c∈ (len Δ′)
                | sRf.krip ⊢τ
                | rel ⊢τ
        ...     | A , W , ↘A , ↘W
                | sw , ↘sw , _
                | a , A′ , w , ↘a , ↘A′ , ↘w
                | cu , ↘cu , _
                | ≈s
                | ≈c = eq
          where
            ⊢τ′      = ⊢w⇒⊢s ⊢τ
            open NatTyping ⊢Tqσ ⊢τ′
              using ()
              renaming ( ⊢NΔ     to ⊢NΔ′
                        ; ⊢qσ    to ⊢qτ
                        ; ⊢qqσ   to ⊢qqτ
                        ; ⊢Tqσ   to ⊢Tqσqτ
                        ; ⊢TqσNΔ to ⊢TqστNΔ′
                        ; Δ⊢N    to Δ′⊢N
                        )

            ⊢qτqσ     = s-∘ ⊢qτ ⊢qσ
            ⊢Tqσqτ′   = t[σ]-Se ⊢T ⊢qτqσ
            ⊢TqσqτNΔ′ = ⊢∷ ⊢NΔ′ ⊢Tqσqτ′
            ⊢TqqNΔ′   = ⊢∷ ⊢NΔ′ ⊢Tqσqτ
            ⊢tτ′      = t[σ] ⊢t′ ⊢τ′
            ⊢στ       = s-∘ ⊢τ′ ⊢σ
            N[στ]≈N   : Δ′ ⊢ N [ σ ∘ τ ] ≈ N ∶[ 1 ] Se 0
            N[στ]≈N   = N-[] ⊢στ

            T[qσ][qτ]≈T[qσ∘qτ] : N₀ ∷ Δ′ ⊢ T [ q N₀ σ ] [ q N₀ τ ] ≈ T [ q N₀ σ ∘ q N₀ τ ] ∶[ 1 + i ] Se i
            T[qσ][qτ]≈T[qσ∘qτ] = [∘]-Se ⊢T ⊢qσ ⊢qτ

            T[qσ∘τ]≈T[qσ][qτ] : N₀ ∷ Δ′ ⊢ T [ q N₀ ( σ ∘ τ ) ] ≈ T [ q N₀ σ ] [ q N₀ τ ] ∶[ 1 + i ] Se i
            T[qσ∘τ]≈T[qσ][qτ] = begin
              T [ q N₀ ( σ ∘ τ ) ] ≈⟨ []-cong-Se‴ ⊢T (s-≈-sym (q∘q-N ⊢σ ⊢τ′)) ⟩
              T [ q N₀ σ ∘ q N₀ τ ] ≈˘⟨ T[qσ][qτ]≈T[qσ∘qτ] ⟩
              T [ q N₀ σ ] [ q N₀ τ ] ∎

            TqqNΔ′≈ : ⊢ ((T [ q N₀ σ ] [ q N₀ τ ]) ↙ i) ∷ N₀ ∷ Δ′ ≈ ((T [ q N₀ σ ∘ q N₀ τ ]) ↙ i) ∷ N₀ ∷ Δ′
            TqqNΔ′≈ = ∷-cong (⊢≈-refl ⊢NΔ′) ⊢Tqσqτ ⊢Tqσqτ′ T[qσ][qτ]≈T[qσ∘qτ] T[qσ][qτ]≈T[qσ∘qτ]

            T[|ze][σ][τ]≈T[qσ][qτ][|ze] : Δ′ ⊢ T [| ze ∶ N₀ ] [ σ ] [ τ ] ≈ T [ q N₀ σ ] [ q N₀ τ ] [| ze ∶ N₀ ] ∶[ 1 + i ] Se i
            T[|ze][σ][τ]≈T[qσ][qτ][|ze] = begin
               T [| ze ∶ N₀ ] [ σ ] [ τ ] ≈⟨ [∘]-Se (t[σ]-Se ⊢T (⊢I,ze ⊢Γ)) ⊢σ ⊢τ′ ⟩
               T [| ze ∶ N₀ ] [ σ ∘ τ ] ≈⟨ []-I,ze-∘ ⊢T ⊢στ ⟩
               T [ (σ ∘ τ) , ze ∶ N₀ ] ≈⟨ []-q-∘-,′ ⊢T ⊢στ (conv (ze-I ⊢Δ′) (≈-sym N[στ]≈N)) ⟩
               T [ q N₀ (σ ∘ τ) ] [| ze ∶ N [ σ ∘ τ ] ↙ 0 ] ≈⟨ []-cong-Se T[qσ∘τ]≈T[qσ][qτ] (s-conv (s-, (s-I ⊢Δ′) Δ′⊢N[στ] ze∶N[σ∘τ][I]) (∷-cong″ N[στ]≈N))
                    (s-≈-conv (,-cong (I-≈ ⊢Δ′) Δ′⊢N[στ] N[στ]≈N (≈-refl ze∶N[σ∘τ][I])) ( ∷-cong″ N[στ]≈N )) ⟩
               T [ q N₀ σ ] [ q N₀ τ ] [| ze ∶ N₀ ]
              ∎
              where
                Δ′⊢N[στ] = t[σ]-Se Γ⊢N ⊢στ
                ze∶N[σ∘τ][I] = conv (ze-I ⊢Δ′) (≈-sym (≈-trans ([I] Δ′⊢N[στ]) N[στ]≈N))

            TqστNΔ′≈ : ⊢ (T [ q N₀ (σ ∘ τ) ] ↙ i) ∷ N₀ ∷ Δ′ ≈ (T [ q N₀ σ ] [ q N₀ τ ] ↙ i) ∷ N₀ ∷ Δ′
            TqστNΔ′≈ = ∷-cong″ T[qσ∘τ]≈T[qσ][qτ]

            T[wkwksuv1][qqσ∘qqτ]≈T[qσ][qτ][wkwksuv1] : (T [ q N₀ σ ] [ q N₀ τ ] ↙ i) ∷ N₀ ∷ Δ′ ⊢ T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ q (T ↙ i) (q N₀ σ) ∘ q ((T [ q N₀ σ ]) ↙ i) (q N₀ τ) ] ≈ T [ q N₀ σ ] [ q N₀ τ ] [ (wk ∘ wk) , su (v 1) ∶ N₀ ] ∶[ 1 + i ] Se i
            T[wkwksuv1][qqσ∘qqτ]≈T[qσ][qτ][wkwksuv1] = begin
                T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ q (T ↙ i) (q N₀ σ) ∘ q ((T [ q N₀ σ ]) ↙ i) (q N₀ τ) ] ≈⟨ []-cong-Se‴ ⊢T′ (ctxeq-s-≈ (⊢≈-sym TqqNΔ′≈) (q∘q ⊢qσ ⊢qτ ⊢T)) ⟩
                T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ q (T ↙ i) (q N₀ σ ∘ q N₀ τ) ] ≈⟨ []-cong-Se‴ ⊢T′ (ctxeq-s-≈ (⊢≈-sym TqqNΔ′≈) (q-cong (q∘q-N ⊢σ ⊢τ′) ⊢T)) ⟩
                T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ q (T ↙ i) (q N₀ (σ ∘ τ)) ] ≈⟨ ctxeq-≈ TqστNΔ′≈ (rec-β-su-T-swap ⊢Δ′ (⊢∷ (⊢∷ ⊢Γ Γ⊢N) ⊢T) ⊢στ) ⟩
                T [ q N₀ (σ ∘ τ) ] [ (wk ∘ wk) , su (v 1) ∶ N₀ ] ≈⟨ []-cong-Se′ T[qσ∘τ]≈T[qσ][qτ] ⊢wkwksuv1 ⟩
                T [ q N₀ σ ] [ q N₀ τ ] [ (wk ∘ wk) , su (v 1) ∶ N₀ ]
              ∎
              where
                ⊢wkwksuv1 = ⊢[wk∘wk],su[v1] ⊢TqqNΔ′
                ⊢wkwksuv1′ = ⊢[wk∘wk],su[v1] ⊢TNΓ
                ⊢T′ = t[σ]-Se ⊢T ⊢wkwksuv1′

            qσqτ∼ρτl : N₀ ∷ Δ′ ⊢s q N₀ σ ∘ q N₀ τ ∶ ⊩NΓ ® ρ ↦ l′ 0 N (len Δ′)
            qσqτ∼ρτl
              with v0®x N′ (≈-refl (N-wf ⊢Δ′)) | s®-mon ⊩Γ ⊢τ σ®ρ
            ... | v0∼l , _
                | στ®ρτ
                with s®-mon ⊩Γ (⊢wwk ⊢NΔ′) στ®ρτ
            ...    | qστ®ρτl  = s®-resp-s≈ ⊩NΓ (cons-N ⊩NΓ qστ®ρτl v0∼l) (s-≈-sym (q∘q-N ⊢σ ⊢τ′))

            qqσqqτ∼ρτll : ((T [ q N₀ σ ∘ q N₀ τ ]) ↙ i) ∷ N₀ ∷ Δ′ ⊢s q (T ↙ i) (q N₀ σ) ∘ q ((T [ q N₀ σ ]) ↙ i) (q N₀ τ) ∶ ⊩TNΓ ® ρ ↦ l′ 0 N (len Δ′) ↦ l′ i (GluTyp.⟦T⟧ (gluT′ qσqτ∼ρτl)) (1 + (len Δ′))
            qqσqqτ∼ρτll
              with s®-mon ⊩NΓ (⊢wwk ⊢TqσqτNΔ′) qσqτ∼ρτl
            ...  | qσqτwk∼ρτl
                 with  gluT′ qσqτwk∼ρτl | gluT′ qσqτ∼ρτl | s®-cons ⊩TNΓ {a = l′ i (GluTyp.⟦T⟧ (gluT′ qσqτ∼ρτl)) (1 + (len Δ′)) } qσqτwk∼ρτl
            ...     | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T∈𝕌 = T∈𝕌₁ ; T∼⟦T⟧ = T∼⟦T⟧₁ }
                    | record { ↘⟦T⟧ = ↘⟦T⟧  ; T∈𝕌 = T∈𝕌  ; T∼⟦T⟧ = T∼⟦T⟧ }
                    | cons
                    rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = s®-resp-s≈ ⊩TNΓ (cons (®El-one-sided _ _ (®El-resp-T≈ _ (v0®x _ T∼⟦T⟧) ([∘]-Se ⊢T ⊢qτqσ (s-wk ⊢TqσqτNΔ′))))) (s-≈-sym (q∘q ⊢qσ ⊢qτ ⊢T))

            T[qσ][τ,t[τ]]≈T[qσ][qτ][|t[τ]] : Δ′ ⊢ T [ q N₀ σ ] [ τ , t [ τ ] ∶ N [ σ ] ↙ 0 ] ≈ T [ q N₀ σ ] [ q N₀ τ ] [| t [ τ ] ∶ N₀ ] ∶[ ℕ.suc i ] Se i
            T[qσ][τ,t[τ]]≈T[qσ][qτ][|t[τ]] = begin
                T [ q N₀ σ ] [ τ , t [ τ ] ∶ N [ σ ] ↙ 0 ] ≈⟨ []-cong-Se‴ ⊢Tqσ (s-≈-conv (,-cong (s-≈-refl ⊢τ′) (t[σ]-Se Γ⊢N ⊢σ) (≈-sym ≈N) (≈-refl (t[σ] ⊢t′ ⊢τ′))) (∷-cong″ (≈-sym ≈N))) ⟩
                T [ q N₀ σ ] [ τ , t [ τ ] ∶ N₀ ] ≈⟨ []-q-∘-,′ ⊢Tqσ ⊢τ′ (t[σ] ⊢t ⊢τ′) ⟩
                T [ q N₀ σ ] [ q N₀ τ ] [| t [ τ ] ∶ N [ τ ] ↙ 0 ]  ≈⟨ []-cong-Se‴ ⊢Tqσqτ
                                                                                  (s-≈-conv (,-cong (I-≈ ⊢Δ′) (t[σ]-Se Δ⊢N ⊢τ′) (N-[] ⊢τ′) (≈-refl (conv (t[σ] ⊢t ⊢τ′) (≈-sym ([I] (t[σ]-Se Δ⊢N ⊢τ′))))))
                                                                                  (∷-cong″ (≈-sym (≈-sym (N-[] ⊢τ′))))) ⟩
                T [ q N₀ σ ] [ q N₀ τ ] [| t [ τ ] ∶ N₀ ]
              ∎

            eq : Δ′ ⊢ rec′ t [ τ ] ≈ rec (Nf⇒Exp W ↙ i) (Nf⇒Exp sw) (Nf⇒Exp w) (Ne⇒Exp cu) ∶[ i ] T [ σ , t ∶ N₀ ] [ τ ]
            eq
              with gluT′ qσqτ∼ρτl | glur′ qqσqqτ∼ρτll
            ...  | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
                 | record { ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧′ ; ↘⟦t⟧ = ↘⟦t⟧′ ; T∈𝕌 = T∈𝕌′ ; t∼⟦t⟧ = t∼⟦t⟧ }
                 rewrite ⟦⟧-det ↘⟦T⟧′ ↘A′
                       | ⟦⟧-det ↘⟦T⟧ ↘A
                       | ⟦⟧-det ↘⟦t⟧′ ↘a
                       with ®⇒®↑ T∈𝕌 T∼⟦T⟧ | ®El⇒®↑El T∈𝕌′ t∼⟦t⟧
            ...           | record { A∈⊤ = A∈⊤ ; krip = krip }
                          | record { T∼A = T∼A ; a∈⊤ = a∈⊤ ; krip = krip′ }
                          with A∈⊤ (1 + (len Δ′)) | [I]-≈ˡ-Se (krip (⊢wI ⊢NΔ′))
                             | a∈⊤ (2 + (len Δ′)) | [I]-≈ˡ (krip′ (⊢wI ⊢TqσqτNΔ′))
            ...              | _ , ↘B , _ | ≈T
                             | _ , ↘w′ , _ | ≈r
                             rewrite Rty-det ↘B ↘W
                                   | Rf-det ↘w′ ↘w
                       = ≈-conv ( begin
                           rec′ t [ τ ] ≈⟨ ≈-conv (rec-[] ⊢τ′ ⊢Tqσ ⊢sσ ⊢wqqσ ⊢t) ([]-cong-Se‴ ⊢Tqσ (,-cong (s-≈-refl ⊢τ′) Δ⊢N ≈N (≈-refl (t[σ] ⊢t ⊢τ′)))) ⟩
                        rec (T [ q N₀ σ ] [ q N₀ τ ] ↙ i) (s [ σ ] [ τ ]) (r [ q (T ↙ i) (q N₀ σ) ] [ q ((T [ q N₀ σ ]) ↙ i) (q N₀ τ) ]) (t [ τ ]) ≈⟨
                              ≈-conv (rec-cong ⊢Tqσqτ
                                               (≈-trans T[qσ][qτ]≈T[qσ∘qτ] ≈T)
                                               (≈-conv ≈s T[|ze][σ][τ]≈T[qσ][qτ][|ze])
                                               (≈-conv (≈-trans (≈-sym ([∘] ⊢qqτ ⊢qqσ ⊢w)) (ctxeq-≈ (⊢≈-sym TqqNΔ′≈) ≈r)) T[wkwksuv1][qqσ∘qqτ]≈T[qσ][qτ][wkwksuv1])
                                               ≈c)
                                     (≈-sym T[qσ][τ,t[τ]]≈T[qσ][qτ][|t[τ]]) ⟩
                           rec ((Nf⇒Exp W) ↙ i) (Nf⇒Exp sw) (Nf⇒Exp w) (Ne⇒Exp cu)
                         ∎)
                         (begin
                            T [ q N₀ σ ] [ τ , t [ τ ] ∶ N [ σ ] ↙ 0 ] ≈˘⟨  []-q-∘-, ⊢T ⊢σ ⊢τ′ ⊢tτ′  ⟩
                            T [ (σ ∘ τ) , t [ τ ] ∶ N₀ ] ≈˘⟨ []-,-∘ ⊢T ⊢σ ⊢t′ ⊢τ′ ⟩
                            T [ σ , t ∶ N₀ ] [ τ ]
                          ∎)

N-E′ : ∀ {i} →
       N₀ ∷ Γ ⊩ T ∶[ 1 + i ] Se i →
       Γ ⊩ s ∶[ i ] T [| ze ∶ N₀ ] →
       (T ↙ i) ∷ N₀ ∷ Γ ⊩ r ∶[ i ] T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] →
       Γ ⊩ t ∶[ 0 ] N →
       --------------------------
       Γ ⊩ rec (T ↙ i) s r t ∶[ i ] T [| t ∶ N₀ ]
N-E′ {_} {T} {s} {r} {t} {i} ⊩T@record { ⊩Γ = ⊩NΓ@(⊩∷ ⊩Γ _ _) ; krip = krip } ⊩s ⊩r ⊩t = record
  { ⊩Γ   = ⊩Γ
  ; krip = helper
  }
  where
    module s = _⊩_∶[_]_ ⊩s
    module r = _⊩_∶[_]_ ⊩r
    module t = _⊩_∶[_]_ ⊩t

    ⊩TNΓ = ⊢∷′ ⊩T
    ⊢T   = ⊩⇒⊢-tm ⊩T
    ⊢s   = ⊩⇒⊢-tm ⊩s
    ⊢w   = ⊩⇒⊢-tm ⊩r
    ⊢t   = ⊩⇒⊢-tm ⊩t
    ⊢Γ   = proj₁ (presup-tm ⊢t)
    Γ⊢N  = N-wf ⊢Γ
    ⊢NΓ  = ⊢∷ ⊢Γ Γ⊢N
    ⊢TNΓ = ⊢∷ ⊢NΓ ⊢T
    ⊢wk  = s-wk ⊢NΓ
    ⊢wk′ = s-wk ⊢TNΓ

    glur : Δ ⊢s σ ∶ ⊩TNΓ ® ρ → GluExp i Δ r (T [ (wk ∘ wk) , su (v 1) ∶ N₀ ]) σ ρ
    glur {Δ} {σ} {ρ} σ®ρ
      with s®⇒⊢s ⊩TNΓ σ®ρ | Glu∷.step σ®ρ
    ... | ⊢σ | record { pσ = pσ ; ≈pσ = ≈pσ ; ≈v0σ = ≈v0σ ; ↘⟦T⟧ = ⟦N⟧ ; T∈𝕌 = N′ ; t∼ρ0 = t∼ρ0 , ≈N ; step = step }
        with presup-s ⊢σ
    ...    | ⊢Δ , _
           with krip (cons-N ⊩NΓ step (su (su-cong (≈-conv ≈v0σ ≈N)) t∼ρ0)) | r.krip (s®-irrel ⊩TNΓ r.⊩Γ σ®ρ)
    ...       | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧₁ ; T∈𝕌 = U 1+i≡1+i _ ; t∼⟦t⟧ = T∼⟦T⟧ }
              | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
              rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁ = record
                { ⟦T⟧ = _
                ; ⟦t⟧ = _
                ; ↘⟦T⟧ = ⟦[[wk∘wk],su[v1]]⟧ ↘⟦T⟧₁
                ; ↘⟦t⟧ = ↘⟦t⟧
                ; T∈𝕌 = A∈𝕌
                ; t∼⟦t⟧ = ®El-≡ T∈𝕌 A∈𝕌 t∼⟦t⟧ refl
                }
                where
                  open GluU T∼⟦T⟧

    glus : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp i Δ s (T [| ze ∶ N₀ ]) σ ρ
    glus {Δ} {σ} {ρ} σ®ρ
      with s®⇒⊢s ⊩Γ σ®ρ
    ...  | ⊢σ
      with presup-s ⊢σ
    ...     | ⊢Δ , _
      with krip (cons-N ⊩NΓ σ®ρ (ze (ze-≈ ⊢Δ))) | s.krip (s®-irrel ⊩Γ s.⊩Γ σ®ρ)
    ...  | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧₁ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = T∼⟦T⟧ }
         | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
         rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁ = record
          { ⟦T⟧ = _
          ; ⟦t⟧ = _
          ; ↘⟦T⟧ = ⟦[|ze]⟧ ↘⟦T⟧₁
          ; ↘⟦t⟧ = ↘⟦t⟧
          ; T∈𝕌 = A∈𝕌
          ; t∼⟦t⟧ = ®El-≡ T∈𝕌 A∈𝕌 t∼⟦t⟧ refl
          }
          where
            open GluU T∼⟦T⟧

    helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp i Δ (rec (T ↙ i) s r t) (T [| t ∶ N₀ ]) σ ρ
    helper {Δ} {σ} {ρ} σ®ρ
      with s®⇒⊢s ⊩Γ σ®ρ
    ...  | ⊢σ
         with presup-s ⊢σ | t.krip (s®-irrel ⊩Γ t.⊩Γ σ®ρ)
    ...     | ⊢Δ , _
            | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = N′ ; t∼⟦t⟧ = t∼⟦t⟧ , ≈N }
            with ⊢∷′-helper ⊩T (cons-N ⊩NΓ σ®ρ t∼⟦t⟧) | glus σ®ρ | N-E-helper ⊩TNΓ ⊢T ⊢s ⊢w σ®ρ (glus σ®ρ) glur t∼⟦t⟧
    ...        | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; T∼⟦T⟧ = T∼⟦T⟧ }
               | record { ⟦t⟧ = ⟦s⟧ ; ↘⟦t⟧ = ↘⟦s⟧ }
               | ra , ↘ra , rec∼ra = record
                { ⟦T⟧ = _
                ; ⟦t⟧ = _
                ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧) ↘⟦T⟧
                ; ↘⟦t⟧ = ⟦rec⟧ ↘⟦s⟧ ↘⟦t⟧ ↘ra
                ; T∈𝕌 = T∈𝕌
                ; t∼⟦t⟧ = ®El-resp-T≈ _ (®El-resp-≈ _ rec∼ra (≈-sym (rec-[] ⊢σ ⊢T ⊢s ⊢w ⊢t))) (≈-sym ([]-I,-∘ ⊢T ⊢σ ⊢t))
                }