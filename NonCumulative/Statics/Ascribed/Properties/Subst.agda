{-# OPTIONS --without-K --safe #-}

-- Properties of substitutions about their static equivalence.
module NonCumulative.Statics.Ascribed.Properties.Subst where

open import Lib
open import Function.Base using ( flip )
open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.PER


q-resp-≈ : ∀ {i} →
           ⊢ Γ →
           Δ ⊢ T ∶[ suc i ] Se i →
           Δ ⊢ T ≈ T′ ∶[ suc i ] Se i →
           Γ ⊢s σ ∶ Δ →
           (T [ σ ] ↙ i) ∷ Γ ⊢s q (T ↙ i) σ ≈ q (T′ ↙ i) σ ∶ (T ↙ i) ∷ Δ
q-resp-≈ ⊢Γ ⊢T T≈T′ ⊢σ = ,-cong (s-≈-refl (s-∘ (s-wk ⊢TσΓ) ⊢σ)) ⊢T T≈T′ (≈-refl (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΓ))))
  where ⊢TσΓ = ⊢∷ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

wk,v0≈I : ∀ {i} →
          ⊢ (T ↙ i) ∷ Γ →
          --------------------------------
          (T ↙ i) ∷ Γ ⊢s wk , v 0 ∶ T ↙ i ≈ I ∶ (T ↙ i) ∷ Γ
wk,v0≈I ⊢TΓ@(⊢∷ ⊢Γ ⊢T) = s-≈-sym (s-≈-trans (,-ext (s-I ⊢TΓ)) (,-cong (∘-I (s-wk ⊢TΓ)) ⊢T (≈-refl ⊢T) (≈-conv ([I] (vlookup ⊢TΓ here)) ([]-cong-Se″ ⊢T (s-wk ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ)))))))

qI≈I : ∀ {i} →
       ⊢ (T ↙ i) ∷ Γ →
       --------------------------
       (T ↙ i) ∷ Γ ⊢s q (T ↙ i) I ≈ I ∶ (T ↙ i) ∷ Γ
qI≈I {T} {_} {i} ⊢TΓ@(⊢∷ ⊢Γ ⊢T) =
  begin
    q (T ↙ i) I
  ≈⟨ ,-cong (I-∘ (s-wk ⊢TΓ)) ⊢T (≈-refl ⊢T) (≈-refl (conv (vlookup ⊢TΓ here) ([]-cong-Se″ ⊢T (s-wk ⊢TΓ) (s-≈-sym (I-∘ (s-wk ⊢TΓ)))))) ⟩
    (wk , v 0 ∶ T ↙ i)
  ≈⟨ wk,v0≈I ⊢TΓ ⟩
    I
  ∎
  where
    open SR

wk∘qσ≈σ∘wk : ∀ {i} →
             ⊢ Γ →
             Δ ⊢ T ∶[ suc i ] Se i →
             Γ ⊢s σ ∶ Δ →
             ---------------------------------------
             (T [ σ ] ↙ i) ∷ Γ ⊢s p (q (T ↙ i) σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk {σ = σ} ⊢Γ ⊢T ⊢σ = p-, (s-∘ (s-wk ⊢T[σ]Γ) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ)))
  where
    ⊢T[σ]Γ = ⊢∷ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

wk∘[σ,t]≈σ : ∀ {i} →
             ⊢ (T ↙ i) ∷ Δ →
             Γ ⊢s σ ∶ Δ →
             Γ ⊢ t ∶[ i ] T [ σ ] →
             ---------------------------
             Γ ⊢s wk ∘ (σ , t ∶ T ↙ i) ≈ σ ∶ Δ
wk∘[σ,t]≈σ {T} {σ = σ} {t = t} {i} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ ⊢t =
  begin
    wk ∘ (σ , t ∶ T ↙ i)
  ≈⟨ p-, ⊢σ ⊢T ⊢t ⟩
    σ
  ∎
  where
    open SR

wk∘wk∘,, : ∀ {i j} →
           ⊢ Δ →
           Γ ⊢s σ ∶ Δ →
           Δ ⊢ T ∶[ 1 + i ] Se i →
           (T ↙ i) ∷ Δ ⊢ S ∶[ 1 + j ] Se j →
           Γ ⊢ t ∶[ i ] T [ σ ] →
           Γ ⊢ s ∶[ j ] S [ σ , t ∶ T ↙ i ] →
           --------------------------------------
           Γ ⊢s wk ∘ wk ∘ ((σ , t ∶ T ↙ i) , s ∶ S ↙ j) ≈ σ ∶ Δ
wk∘wk∘,, ⊢Δ ⊢σ ⊢T ⊢S ⊢t ⊢s = s-≈-trans (∘-assoc ⊢wk ⊢wk′ (s-, ⊢σ,t ⊢S ⊢s))
                             (s-≈-trans (∘-cong (p-, ⊢σ,t ⊢S ⊢s) (s-≈-refl ⊢wk))
                                        (p-, ⊢σ ⊢T ⊢t))
  where ⊢TΔ  = ⊢∷ ⊢Δ ⊢T
        ⊢STΔ = ⊢∷ ⊢TΔ ⊢S
        ⊢wk  = s-wk ⊢TΔ
        ⊢wk′ = s-wk ⊢STΔ
        ⊢σ,t = s-, ⊢σ ⊢T ⊢t

module _ {i} (⊢Γ : ⊢ Γ) (⊢TNΔ : ⊢ (T ↙ i) ∷ N₀ ∷ Δ) (⊢σ : Γ ⊢s σ ∶ Δ) where

  private
    ⊢-split : ∀ {i T Γ} → ⊢ (T ↙ i) ∷ Γ → Γ ⊢ T ∶[ suc i ] Se i × ⊢ Γ
    ⊢-split (⊢∷ ⊢Γ ⊢T) = ⊢T , ⊢Γ

    ⊢T  = proj₁ (⊢-split ⊢TNΔ)
    ⊢Δ  = proj₂ (⊢-split (proj₂ (⊢-split ⊢TNΔ)))
    ⊢N  = N-wf ⊢Δ
    ⊢NΔ = ⊢∷ ⊢Δ ⊢N

    ⊢NΓ = ⊢∷ ⊢Γ (N-wf ⊢Γ)

    ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
    ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T

    ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
    ⊢T[qσ]NΓ = ⊢∷ ⊢NΓ ⊢T[qσ]

    ⊢Nσwk = t[σ]-Se (N-wf ⊢Δ) (s-∘ (s-wk ⊢NΓ) ⊢σ)

    ⊢wk∘wk = (s-∘ (s-wk ⊢TNΔ) (s-wk ⊢NΔ))
    ⊢wk∘wk′ = (s-∘ (s-wk ⊢T[qσ]NΓ) (s-wk ⊢NΓ))
    ⊢v1 = ⊢vn∶N L.[ T ↙ i ] ⊢TNΔ refl
    ⊢v1′ = ⊢vn∶N L.[ T [ q N₀ σ ] ↙ i ] ⊢T[qσ]NΓ refl
    ⊢su[v1] = conv-N-[]-sym (su-I ⊢v1) ⊢wk∘wk
    ⊢su[v1]′ = conv-N-[]-sym (su-I ⊢v1′) ⊢wk∘wk′
    ⊢[wk∘wk],su[v1]′ = ⊢[wk∘wk],su[v1] ⊢TNΔ
    ⊢[wk∘wk],su[v1]′′ = ⊢[wk∘wk],su[v1] ⊢T[qσ]NΓ
    ⊢qσ∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢qσ
    ⊢σ∘wk = s-∘ (s-wk ⊢NΓ) ⊢σ
    ⊢σ∘wk∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢σ∘wk

  [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN : (T [ q N₀ σ ] ↙ i) ∷ N₀ ∷ Γ ⊢s wk ∘ wk ∘ q (T ↙ i) (q N₀ σ) ≈ σ ∘ (wk ∘ wk) ∶ Δ
  [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN =
    begin
      wk ∘ wk ∘ q (T ↙ i) (q N₀ σ)
    ≈⟨ ∘-assoc (s-wk ⊢NΔ) (s-wk ⊢TNΔ) ⊢q[qσ] ⟩
      wk ∘ (wk ∘ q (T ↙ i) (q N₀ σ))
    ≈⟨ ∘-cong (wk∘qσ≈σ∘wk ⊢NΓ ⊢T ⊢qσ) (s-≈-refl (s-wk ⊢NΔ)) ⟩
      wk ∘ ((q N₀ σ) ∘ wk)
    ≈˘⟨ ∘-assoc (s-wk ⊢NΔ) ⊢qσ (s-wk ⊢T[qσ]NΓ) ⟩
      wk ∘ (q N₀ σ) ∘ wk
    ≈⟨ ∘-cong (s-≈-refl (s-conv (s-wk ⊢T[qσ]NΓ) (∷-cong′ ⊢Γ (N-wf ⊢Γ) (t[σ]-Se (N-wf ⊢Δ) ⊢σ) (≈-sym (N-[] ⊢σ))))) (wk∘qσ≈σ∘wk ⊢Γ ⊢N ⊢σ) ⟩
      σ ∘ wk ∘ wk
    ≈⟨ ∘-assoc ⊢σ (s-wk ⊢NΓ) (s-wk ⊢T[qσ]NΓ) ⟩
      σ ∘ (wk ∘ wk)
    ∎
    where open SR

  wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] : (T [ q N₀ σ ] ↙ i) ∷ N₀ ∷ Γ ⊢s wk ∘ wk ∘ q (T ↙ i) (q N₀ σ) ≈ σ ∘ wk ∘ ((wk ∘ wk) , su (v 1) ∶ N₀) ∶ Δ
  wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] =
    begin
      wk ∘ wk ∘ q (T ↙ i) (q N₀ σ)
    ≈⟨ [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN ⟩
      σ ∘ (wk ∘ wk)
    ≈˘⟨ ∘-cong (wk∘[σ,t]≈σ ⊢NΓ ⊢wk∘wk′ ⊢su[v1]′) (s-≈-refl ⊢σ) ⟩
      σ ∘ (wk ∘ ((wk ∘ wk), su (v 1) ∶ N₀))
    ≈˘⟨ ∘-assoc ⊢σ (s-wk ⊢NΓ) ⊢[wk∘wk],su[v1]′′ ⟩
      (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)  ∶ N₀))
    ∎
    where open SR

  suv1[qqσ]≈v0[wkwk,suv1] : (T [ q N₀ σ ] ↙ i) ∷ N₀ ∷ Γ ⊢ su (v 1) [ q (T ↙ i) (q N₀ σ) ] ≈ v 0 [ (wk ∘ wk) , su (v 1) ∶ N₀ ] ∶[ 0 ] N
  suv1[qqσ]≈v0[wkwk,suv1] =
    begin
      su (v 1) [ q (T ↙ i) (q N₀ σ) ]
    ≈⟨ su-[] ⊢q[qσ] ⊢v1 ⟩
      su (v 1 [ q (T ↙ i) (q N₀ σ) ])
    ≈⟨ su-cong (≈-conv ([,]-v-su ⊢qσ∘wk ⊢T (conv (vlookup ⊢T[qσ]NΓ here) ([∘]-Se ⊢T ⊢qσ (s-wk ⊢T[qσ]NΓ))) here) (N-[][] (s-wk ⊢NΔ) ⊢qσ∘wk)) ⟩
      su (v 0 [ q N₀ σ ∘ wk ])
    ≈⟨ su-cong ([]-cong-N″ (⊢vn∶N [] ⊢NΔ refl) ⊢qσ∘wk (,-∘ ⊢σ∘wk (N-wf ⊢Δ) (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ))) ⟩
      su (v 0 [ (σ ∘ wk ∘ wk) , v 0 [ wk ] ∶ N₀ ])
    ≈⟨ su-cong (≈-conv-N-[] ([,]-v-ze ⊢σ∘wk∘wk (N-wf ⊢Δ) (conv (t[σ] (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ)) ([∘]-Se (N-wf ⊢Δ) ⊢σ∘wk (s-wk ⊢T[qσ]NΓ)))) ⊢σ∘wk∘wk) ⟩
      su (v 0 [ wk ])
    ≈⟨ su-cong (≈-conv (≈-trans ([wk] ⊢NΓ ⊢T[qσ] here) (≈-sym ([I] (⊢vn∶T[wk]suc[n] {Δ = L.[ T [ q N₀ σ ] ↙ i ]} ⊢T[qσ]NΓ refl)))) (N-[][] (s-wk ⊢NΓ) (s-wk ⊢T[qσ]NΓ))) ⟩
      su (v 1 [ I ])
    ≈⟨ su-cong ([I] ⊢v1′) ⟩
      su (v 1)
    ≈˘⟨ ≈-conv-N-[] ([,]-v-ze ⊢wk∘wk′ (N-wf ⊢Γ) ⊢su[v1]′) ⊢wk∘wk′ ⟩
      v 0 [ (wk ∘ wk) , su (v 1) ∶ N₀ ]
    ∎
    where open ER

  [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1] : (T [ q N₀ σ ] ↙ i) ∷ N₀ ∷ Γ ⊢s ((wk ∘ wk) , su (v 1) ∶ N₀) ∘ q (T ↙ i) (q N₀ σ) ≈ q N₀ σ ∘ ((wk ∘ wk) , su (v 1) ∶ N₀) ∶ N₀ ∷ Δ
  [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1] =
    begin
      ((wk ∘ wk) , su (v 1) ∶ N₀) ∘ q (T ↙ i) (q N₀ σ)
    ≈⟨ ,-∘ ⊢wk∘wk (N-wf ⊢Δ) ⊢su[v1] ⊢q[qσ] ⟩
      (wk ∘ wk ∘ q (T ↙ i) (q N₀ σ)) , su (v 1) [ q (T ↙ i) (q N₀ σ) ] ∶ N₀
    ≈⟨ ,-cong wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] (N-wf ⊢Δ) (≈-refl (N-wf ⊢Δ)) (≈-conv-N-[]-sym suv1[qqσ]≈v0[wkwk,suv1] (s-∘ ⊢q[qσ] ⊢wk∘wk)) ⟩
      (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1) ∶ N₀)) , v 0 [ (wk ∘ wk) , su (v 1) ∶ N₀ ] ∶ N₀
    ≈˘⟨ ,-∘ ⊢σ∘wk (N-wf ⊢Δ) (conv (⊢vn∶N [] ⊢NΓ refl) (≈-sym (N-[] ⊢σ∘wk))) ⊢[wk∘wk],su[v1]′′ ⟩
      q N₀ σ ∘ ((wk ∘ wk) , su (v 1) ∶ N₀)
    ∎
    where open SR

  rec-β-su-T-swap : (T [ q N₀ σ ] ↙ i) ∷ N₀ ∷ Γ ⊢ T [ (wk ∘ wk) , su (v 1) ∶ N₀ ] [ q (T ↙ i) (q N₀ σ) ] ≈ T [ q N₀ σ ] [ (wk ∘ wk) , su (v 1) ∶ N₀ ] ∶[ 1 + i ] Se i
  rec-β-su-T-swap = ≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢q[qσ])
                    (≈-trans ([]-cong-Se″ ⊢T (s-∘ ⊢q[qσ] (s-, ⊢wk∘wk ⊢N ⊢su[v1])) [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1])
                             (≈-sym ([∘]-Se ⊢T ⊢qσ ⊢[wk∘wk],su[v1]′′)))

[I,t]∘σ≈σ,t[σ] : ∀ {i} →
                 ⊢ (T ↙ i) ∷ Δ →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶[ i ] T →
                 ---------------------------------------
                 Γ ⊢s (I , t ∶ T ↙ i) ∘ σ ≈ σ , t [ σ ] ∶ T ↙ i ∶ (T ↙ i) ∷ Δ
[I,t]∘σ≈σ,t[σ] {T} {σ = σ} {t = t} (⊢∷ ⊢Δ ⊢T) ⊢σ ⊢t =
  begin
    (I , t ∶ T ↙ _) ∘ σ
  ≈⟨ ,-∘ (s-I ⊢Δ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T))) ⊢σ ⟩
    (I ∘ σ) , t [ σ ] ∶ T ↙ _
  ≈⟨ ,-cong (I-∘ ⊢σ) ⊢T (≈-refl ⊢T) (≈-refl (conv (t[σ] ⊢t ⊢σ) ([]-cong-Se″ ⊢T ⊢σ (s-≈-sym (I-∘ ⊢σ))))) ⟩
    σ , t [ σ ] ∶ T ↙ _
  ∎
  where
    open SR

[I,ze]∘σ≈σ,ze : ⊢ Δ →
                Γ ⊢s σ ∶ Δ →
                -------------------------------------
                Γ ⊢s (I , ze ∶ N₀) ∘ σ ≈ σ , ze ∶ N₀ ∶ N₀ ∷ Δ
[I,ze]∘σ≈σ,ze {σ = σ} ⊢Δ ⊢σ =
  begin
    (I , ze ∶ N₀) ∘ σ
  ≈⟨ [I,t]∘σ≈σ,t[σ] (⊢∷ ⊢Δ (N-wf ⊢Δ)) ⊢σ (ze-I ⊢Δ) ⟩
    σ , ze [ σ ] ∶ N₀
  ≈⟨ ,-cong (s-≈-refl ⊢σ) (N-wf ⊢Δ) (≈-refl (N-wf ⊢Δ)) (≈-conv-N-[]-sym (ze-[] ⊢σ) ⊢σ) ⟩
    σ , ze ∶ _ ↙ 0
  ∎
  where
    open SR

qσ∘[I,t]≈σ,t : ∀ {i} →
               ⊢ Γ →
               Δ ⊢ T ∶[ suc i ] Se i →
               Γ ⊢s σ ∶ Δ →
               Γ ⊢ t ∶[ i ] T [ σ ] →
               -------------------------------------
               Γ ⊢s q (T ↙ i) σ ∘ (I , t ∶ T [ σ ] ↙ i) ≈ σ , t ∶ T ↙ i ∶ (T ↙ i) ∷ Δ
qσ∘[I,t]≈σ,t {Γ} {Δ} {T} {σ} {t} ⊢Γ ⊢T ⊢σ ⊢t =
  begin
    q (T ↙ _) σ ∘ (I , t ∶ T [ σ ] ↙ _)
  ≈⟨ ,-∘ (s-∘ (s-wk (⊢∷ ⊢Γ (conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)))) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ))) (⊢I,t ⊢Γ ⊢T[σ] ⊢t) ⟩
    (σ ∘ wk ∘ (I , t ∶ T [ σ ] ↙ _)) , v 0 [| t ∶ T [ σ ] ↙ _ ] ∶ T ↙ _
  ≈⟨ ,-cong σ∘wk∘[I,s] ⊢T (≈-refl ⊢T)
            (≈-refl (conv (t[σ] (vlookup ⊢T[σ]Γ here) (⊢I,t ⊢Γ ⊢T[σ] ⊢t)) (≈-trans ([]-cong-Se′ ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ)) (⊢I,t ⊢Γ ⊢T[σ] ⊢t)) ([∘]-Se ⊢T (s-∘ (s-wk ⊢T[σ]Γ) ⊢σ) (⊢I,t ⊢Γ ⊢T[σ] ⊢t))))) ⟩
    σ , v 0 [| t ∶ T [ σ ] ↙ _ ] ∶ T ↙ _
  ≈⟨ ,-cong (s-≈-refl ⊢σ) ⊢T (≈-refl ⊢T) (≈-conv ([,]-v-ze (s-I ⊢Γ) ⊢T[σ] ⊢t′) ([I] ⊢T[σ])) ⟩
    σ , t ∶ T ↙ _
  ∎
  where
    open SR

    ⊢T[σ] = t[σ]-Se ⊢T ⊢σ
    ⊢T[σ]Γ = ⊢∷ ⊢Γ ⊢T[σ]
    ⊢t′ = conv ⊢t (≈-sym ([I] ⊢T[σ]))

    σ∘wk∘[I,s] : Γ ⊢s σ ∘ wk ∘ (I , t ∶ T [ σ ] ↙ _) ≈ σ ∶ Δ
    σ∘wk∘[I,s] =
      begin
        σ ∘ wk ∘ (I , t ∶ T [ σ ] ↙ _)
      ≈⟨ ∘-assoc ⊢σ (s-wk ⊢T[σ]Γ) (⊢I,t ⊢Γ ⊢T[σ] ⊢t) ⟩
        σ ∘ (wk ∘ (I , t ∶ T [ σ ] ↙ _))
      ≈⟨ ∘-cong (wk∘[σ,t]≈σ ⊢T[σ]Γ (s-I ⊢Γ) ⊢t′) (s-≈-refl ⊢σ) ⟩
        σ ∘ I
      ≈⟨ ∘-I ⊢σ ⟩
        σ
      ∎

qσ∘[I,t]≈σ,t-N : ⊢ Γ →
                 ⊢ Δ →
                 Γ ⊢ t ∶[ 0 ] N →
                 Γ ⊢s σ ∶ Δ →
                 --------------------------------------
                 Γ ⊢s q N₀ σ ∘ (I , t ∶ N₀) ≈ σ , t ∶ N₀ ∶ N₀ ∷ Δ
qσ∘[I,t]≈σ,t-N {Γ} {Δ} {t} {σ} ⊢Γ ⊢Δ ⊢t ⊢σ =
  begin
    q N₀ σ ∘ (I , t ∶ N₀)
  ≈⟨ ∘-cong (,-cong (I-≈ ⊢Γ) (N-wf ⊢Γ) (≈-sym (N-[] ⊢σ)) (≈-refl (conv ⊢t (≈-sym (N-[] (s-I ⊢Γ)))))) (s-≈-refl (⊢q-N ⊢Γ ⊢Δ ⊢σ)) ⟩
    q N₀ σ ∘ (I , t ∶ N [ σ ] ↙ 0)
  ≈⟨ qσ∘[I,t]≈σ,t ⊢Γ (N-wf ⊢Δ) ⊢σ (conv-N-[]-sym ⊢t ⊢σ) ⟩
    σ , t ∶ N₀
  ∎
  where
    open SR

qσ∘[I,ze]≈σ,ze : ⊢ Γ →
                 ⊢ Δ →
                 Γ ⊢s σ ∶ Δ →
                 --------------------------------------
                 Γ ⊢s q N₀ σ ∘ (I , ze ∶ N₀) ≈ σ , ze ∶ N₀ ∶ N₀ ∷ Δ
qσ∘[I,ze]≈σ,ze ⊢Γ ⊢Δ ⊢σ = qσ∘[I,t]≈σ,t-N ⊢Γ ⊢Δ (ze-I ⊢Γ) ⊢σ

-- q[wk]∘[σ,v0[σ]]≈σ : ⊢ T ∷ Δ →
--                     Γ ⊢s σ ∶ T ∷ Δ →
--                     -----------------------------------------
--                     Γ ⊢s q wk ∘ (σ , v 0 [ σ ]) ≈ σ ∶ T ∷ Δ
-- q[wk]∘[σ,v0[σ]]≈σ {σ = σ} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ =
--   begin
--     q wk ∘ (σ , v 0 [ σ ])
--   ≈˘⟨ ∘-cong ([I,t]∘σ≈σ,t[σ] (⊢∷ ⊢TΔ ⊢T[wk]) ⊢σ ⊢v0) (s-≈-refl ⊢q[wk]) ⟩
--     q wk ∘ ((I , v 0) ∘ σ)
--   ≈˘⟨ ∘-assoc ⊢q[wk] (s-, (s-I ⊢TΔ) ⊢T[wk] (conv ⊢v0 (≈-sym ([I] ⊢T[wk])))) ⊢σ ⟩
--     (q wk ∘ (I , v 0)) ∘ σ
--   ≈⟨ ∘-cong (s-≈-refl ⊢σ) (qσ∘[I,t]≈σ,t ⊢TΔ ⊢T ⊢wk′ ⊢v0) ⟩
--     (wk , v 0) ∘ σ
--   ≈⟨ ∘-cong (s-≈-refl ⊢σ) (wk,v0≈I ⊢TΔ) ⟩
--     I ∘ σ
--   ≈⟨ I-∘ ⊢σ ⟩
--     σ
--   ∎
--   where
--     open SR

--     ⊢v0 = vlookup ⊢TΔ here
--     ⊢wk′ = s-wk ⊢TΔ
--     ⊢T[wk] = t[σ]-Se ⊢T ⊢wk′
--     ⊢q[wk] = ⊢q ⊢TΔ ⊢wk′ ⊢T

q[wk]∘[I,v0]≈I : ∀ {i} →
                 ⊢ (T ↙ i) ∷ Γ →
                 --------------------------------------
                 (T ↙ i) ∷ Γ ⊢s q (T ↙ i) wk ∘ (I , v 0 ∶ T [ wk ] ↙ i) ≈ I ∶ (T ↙ i) ∷ Γ
q[wk]∘[I,v0]≈I {T} ⊢TΓ@(⊢∷ ⊢Γ ⊢T) =
  begin
    q (T ↙ _) wk ∘ (I , v 0 ∶ T [ wk ] ↙ _)
  ≈⟨ qσ∘[I,t]≈σ,t ⊢TΓ ⊢T ⊢wk′ ⊢v0 ⟩
    (wk , v 0 ∶ _ ↙ _)
  ≈⟨ wk,v0≈I ⊢TΓ ⟩
    I
  ∎
  where
    open SR

    ⊢wk′ = s-wk ⊢TΓ
    ⊢v0 = vlookup ⊢TΓ here
