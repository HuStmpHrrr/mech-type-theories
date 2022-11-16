{-# OPTIONS --without-K --safe #-}

-- Properties of substitutions about their static equivalence.
module Mint.Statics.Properties.Substs where

open import Lib
open import Function.Base using ( flip )
open import Mint.Statics.Full
open import Mint.Statics.Misc
open import Mint.Statics.Refl
open import Mint.Statics.PER

wk,v0≈I : ⊢ T ∺ Γ →
          --------------------------------
          T ∺ Γ ⊢s wk , v 0 ≈ I ∶ T ∺ Γ
wk,v0≈I ⊢TΓ@(⊢∺ _ ⊢T) = s-≈-sym (s-≈-trans (,-ext (s-I ⊢TΓ)) (,-cong (∘-I (s-wk ⊢TΓ)) ⊢T (≈-conv ([I] (vlookup ⊢TΓ here)) ([]-cong-Se″ ⊢T (s-wk ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ)))))))

qI≈I : ⊢ T ∺ Γ →
       --------------------------
       T ∺ Γ ⊢s q I ≈ I ∶ T ∺ Γ
qI≈I ⊢TΓ@(⊢∺ _ ⊢T) =
  begin
    q I
  ≈⟨ ,-cong (I-∘ (s-wk ⊢TΓ)) ⊢T (≈-refl (conv (vlookup ⊢TΓ here) ([]-cong-Se″ ⊢T (s-wk ⊢TΓ) (s-≈-sym (I-∘ (s-wk ⊢TΓ)))))) ⟩
    (wk , v 0)
  ≈⟨ wk,v0≈I ⊢TΓ ⟩
    I
  ∎
  where
    open SR

wk∘qσ≈σ∘wk : ∀ {i} →
             ⊢ Γ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢s σ ∶ Δ →
             ---------------------------------------
             (T [ σ ]) ∺ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk {σ = σ} ⊢Γ ⊢T ⊢σ = p-, (s-∘ (s-wk ⊢T[σ]Γ) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ)))
  where
    ⊢T[σ]Γ = ⊢∺ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

wk∘[σ,t]≈σ : ⊢ T ∺ Δ →
             Γ ⊢s σ ∶ Δ →
             Γ ⊢ t ∶ T [ σ ] →
             ---------------------------
             Γ ⊢s wk ∘ (σ , t) ≈ σ ∶ Δ
wk∘[σ,t]≈σ {σ = σ} {t = t} ⊢TΔ@(⊢∺ _ ⊢T) ⊢σ ⊢t =
  begin
    wk ∘ (σ , t)
  ≈⟨ p-, ⊢σ ⊢T ⊢t ⟩
    σ
  ∎
  where
    open SR

wk∘wk∘,, : ∀ {i j} →
           ⊢ Δ →
           Γ ⊢s σ ∶ Δ →
           Δ ⊢ T ∶ Se i →
           T ∺ Δ ⊢ S ∶ Se j →
           Γ ⊢ t ∶ T [ σ ] →
           Γ ⊢ s ∶ S [ σ , t ] →
           --------------------------------------
           Γ ⊢s wk ∘ wk ∘ ((σ , t) , s) ≈ σ ∶ Δ
wk∘wk∘,, ⊢Δ ⊢σ ⊢T ⊢S ⊢t ⊢s = s-≈-trans (∘-assoc ⊢wk ⊢wk′ (s-, ⊢σ,t ⊢S ⊢s))
                             (s-≈-trans (∘-cong (p-, ⊢σ,t ⊢S ⊢s) (s-≈-refl ⊢wk))
                                        (p-, ⊢σ ⊢T ⊢t))
  where ⊢TΔ  = ⊢∺ ⊢Δ ⊢T
        ⊢STΔ = ⊢∺ ⊢TΔ ⊢S
        ⊢wk  = s-wk ⊢TΔ
        ⊢wk′ = s-wk ⊢STΔ
        ⊢σ,t = s-, ⊢σ ⊢T ⊢t

module _ (⊢Γ : ⊢ Γ) (⊢TNΔ : ⊢ T ∺ N ∺ Δ) (⊢σ : Γ ⊢s σ ∶ Δ) where

  private
    ⊢-split : ∀ {T Γ} → ⊢ T ∺ Γ → Γ ⊢ T × ⊢ Γ
    ⊢-split (⊢∺ ⊢Γ ⊢T) = (-, ⊢T) , ⊢Γ

    lvl = proj₁ (proj₁ (⊢-split ⊢TNΔ))
    ⊢T  = proj₂ (proj₁ (⊢-split ⊢TNΔ))
    ⊢NΔ = proj₂ (⊢-split ⊢TNΔ)
    ⊢N  = proj₂ (proj₁ (⊢-split ⊢NΔ))
    ⊢Δ  = proj₂ (⊢-split ⊢NΔ)

    ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)

    ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
    ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T

    ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
    ⊢T[qσ]NΓ = ⊢∺ ⊢NΓ ⊢T[qσ]

    ⊢wk∘wk = (s-∘ (s-wk ⊢TNΔ) (s-wk ⊢NΔ))
    ⊢wk∘wk′ = (s-∘ (s-wk ⊢T[qσ]NΓ) (s-wk ⊢NΓ))
    ⊢v1 = ⊢vn∶N L.[ T ] ⊢TNΔ refl
    ⊢v1′ = ⊢vn∶N L.[ T [ q σ ] ] ⊢T[qσ]NΓ refl
    ⊢su[v1] = conv-N-[]-sym (su-I ⊢v1) ⊢wk∘wk
    ⊢su[v1]′ = conv-N-[]-sym (su-I ⊢v1′) ⊢wk∘wk′
    ⊢[wk∘wk],su[v1]′ = ⊢[wk∘wk],su[v1] ⊢TNΔ
    ⊢[wk∘wk],su[v1]′′ = ⊢[wk∘wk],su[v1] ⊢T[qσ]NΓ
    ⊢qσ∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢qσ
    ⊢σ∘wk = s-∘ (s-wk ⊢NΓ) ⊢σ
    ⊢σ∘wk∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢σ∘wk

  [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN : (T [ q σ ]) ∺ N ∺ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ (wk ∘ wk) ∶ Δ
  [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN =
    begin
      wk ∘ wk ∘ q (q σ)
    ≈⟨ ∘-assoc (s-wk ⊢NΔ) (s-wk ⊢TNΔ) ⊢q[qσ] ⟩
      wk ∘ (wk ∘ q (q σ))
    ≈⟨ ∘-cong (wk∘qσ≈σ∘wk ⊢NΓ ⊢T ⊢qσ) (s-≈-refl (s-wk ⊢NΔ)) ⟩
      wk ∘ ((q σ) ∘ wk)
    ≈˘⟨ ∘-assoc (s-wk ⊢NΔ) ⊢qσ (s-wk ⊢T[qσ]NΓ) ⟩
      wk ∘ (q σ) ∘ wk
    ≈⟨ ∘-cong (s-≈-refl (s-conv (s-wk ⊢T[qσ]NΓ) (∺-cong′ ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-Se (N-wf 0 ⊢Δ) ⊢σ) (≈-sym (N-[] 0 ⊢σ))))) (wk∘qσ≈σ∘wk ⊢Γ ⊢N ⊢σ) ⟩
      σ ∘ wk ∘ wk
    ≈⟨ ∘-assoc ⊢σ (s-wk ⊢NΓ) (s-wk ⊢T[qσ]NΓ) ⟩
      σ ∘ (wk ∘ wk)
    ∎
    where open SR

  wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] : (T [ q σ ]) ∺ N ∺ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)) ∶ Δ
  wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] =
    begin
      wk ∘ wk ∘ q (q σ)
    ≈⟨ [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN ⟩
      σ ∘ (wk ∘ wk)
    ≈˘⟨ ∘-cong (wk∘[σ,t]≈σ ⊢NΓ ⊢wk∘wk′ ⊢su[v1]′) (s-≈-refl ⊢σ) ⟩
      σ ∘ (wk ∘ ((wk ∘ wk), su (v 1)))
    ≈˘⟨ ∘-assoc ⊢σ (s-wk ⊢NΓ) ⊢[wk∘wk],su[v1]′′ ⟩
      (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)))
    ∎
    where open SR

  suv1[qqσ]≈v0[wkwk,suv1] : (T [ q σ ]) ∺ N ∺ Γ ⊢ su (v 1) [ q (q σ) ] ≈ v 0 [ (wk ∘ wk) , su (v 1) ] ∶ N
  suv1[qqσ]≈v0[wkwk,suv1] =
    begin
      su (v 1) [ q (q σ) ]
    ≈⟨ su-[] ⊢q[qσ] ⊢v1 ⟩
      su (v 1 [ q (q σ) ])
    ≈⟨ su-cong (≈-conv ([,]-v-su ⊢qσ∘wk ⊢T (conv (vlookup ⊢T[qσ]NΓ here) ([∘]-Se ⊢T ⊢qσ (s-wk ⊢T[qσ]NΓ))) here) (N-[][] 0 (s-wk ⊢NΔ) ⊢qσ∘wk)) ⟩
      su (v 0 [ q σ ∘ wk ])
    ≈⟨ su-cong ([]-cong-N″ (⊢vn∶N [] ⊢NΔ refl) ⊢qσ∘wk (,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ))) ⟩
      su (v 0 [ (σ ∘ wk ∘ wk) , v 0 [ wk ] ])
    ≈⟨ su-cong (≈-conv-N-[] ([,]-v-ze ⊢σ∘wk∘wk (N-wf 0 ⊢Δ) (conv (t[σ] (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ)) ([∘]-Se (N-wf 0 ⊢Δ) ⊢σ∘wk (s-wk ⊢T[qσ]NΓ)))) ⊢σ∘wk∘wk) ⟩
      su (v 0 [ wk ])
    ≈⟨ su-cong (≈-conv (≈-trans ([wk] ⊢T[qσ]NΓ here) (≈-sym ([I] (⊢vn∶T[wk]suc[n] {Ψ = L.[ T [ q σ ] ]} ⊢T[qσ]NΓ refl)))) (N-[][] 0 (s-wk ⊢NΓ) (s-wk ⊢T[qσ]NΓ))) ⟩
      su (v 1 [ I ])
    ≈⟨ su-cong ([I] ⊢v1′) ⟩
      su (v 1)
    ≈˘⟨ ≈-conv-N-[] ([,]-v-ze ⊢wk∘wk′ (N-wf 0 ⊢Γ) ⊢su[v1]′) ⊢wk∘wk′ ⟩
      v 0 [ (wk ∘ wk) , su (v 1) ]
    ∎
    where open ER

  [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1] : (T [ q σ ]) ∺ N ∺ Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ q (q σ) ≈ q σ ∘ ((wk ∘ wk) , su (v 1)) ∶ N ∺ Δ
  [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1] =
    begin
      ((wk ∘ wk) , su (v 1)) ∘ q (q σ)
    ≈⟨ ,-∘ ⊢wk∘wk (N-wf 0 ⊢Δ) ⊢su[v1] ⊢q[qσ] ⟩
      (wk ∘ wk ∘ q (q σ)) , su (v 1) [ q (q σ) ]
    ≈⟨ ,-cong wk∘wk∘qqσ≈σ∘wk∘[wkwk,suv1] (N-wf 0 ⊢Δ) (≈-conv-N-[]-sym suv1[qqσ]≈v0[wkwk,suv1] (s-∘ ⊢q[qσ] ⊢wk∘wk)) ⟩
      (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1))) , v 0 [ (wk ∘ wk) , su (v 1) ]
    ≈˘⟨ ,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (⊢vn∶N [] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) ⊢[wk∘wk],su[v1]′′ ⟩
      q σ ∘ ((wk ∘ wk) , su (v 1))
    ∎
    where open SR

  rec-β-su-T-swap : (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ ((wk ∘ wk) , su (v 1)) ] [ q (q σ) ] ≈ T [ q σ ] [ ((wk ∘ wk) , su (v 1)) ] ∶ Se lvl
  rec-β-su-T-swap = ≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢q[qσ])
                    (≈-trans ([]-cong-Se″ ⊢T (s-∘ ⊢q[qσ] (s-, ⊢wk∘wk ⊢N ⊢su[v1])) [wkwk,suv1]∘qqσ≈qσ∘[wkwk,suv1])
                             (≈-sym ([∘]-Se ⊢T ⊢qσ ⊢[wk∘wk],su[v1]′′)))

[I,t]∘σ≈σ,t[σ] : ⊢ T ∺ Δ →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ T →
                 ---------------------------------------
                 Γ ⊢s (I , t) ∘ σ ≈ σ , t [ σ ] ∶ T ∺ Δ
[I,t]∘σ≈σ,t[σ] {σ = σ} {t = t} (⊢∺ ⊢Δ ⊢T) ⊢σ ⊢t =
  begin
    (I , t) ∘ σ
  ≈⟨ ,-∘ (s-I ⊢Δ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T))) ⊢σ ⟩
    (I ∘ σ) , t [ σ ]
  ≈⟨ ,-cong (I-∘ ⊢σ) ⊢T (≈-refl (conv (t[σ] ⊢t ⊢σ) ([]-cong-Se″ ⊢T ⊢σ (s-≈-sym (I-∘ ⊢σ))))) ⟩
    σ , t [ σ ]
  ∎
  where
    open SR

[I,ze]∘σ≈σ,ze : ⊢ Δ →
                Γ ⊢s σ ∶ Δ →
                -------------------------------------
                Γ ⊢s (I , ze) ∘ σ ≈ σ , ze ∶ N ∺ Δ
[I,ze]∘σ≈σ,ze {σ = σ} ⊢Δ ⊢σ =
  begin
    (I , ze) ∘ σ
  ≈⟨ [I,t]∘σ≈σ,t[σ] (⊢∺ ⊢Δ (N-wf 0 ⊢Δ)) ⊢σ (ze-I ⊢Δ) ⟩
    σ , ze [ σ ]
  ≈⟨ ,-cong (s-≈-refl ⊢σ) (N-wf 0 ⊢Δ) (≈-conv-N-[]-sym (ze-[] ⊢σ) ⊢σ) ⟩
    σ , ze
  ∎
  where
    open SR

qσ∘[I,t]≈σ,t : ∀ {i} →
               ⊢ Γ →
               Δ ⊢ T ∶ Se i →
               Γ ⊢s σ ∶ Δ →
               Γ ⊢ t ∶ T [ σ ] →
               -------------------------------------
               Γ ⊢s q σ ∘ (I , t) ≈ σ , t ∶ T ∺ Δ
qσ∘[I,t]≈σ,t {Γ = Γ} {Δ = Δ} {σ = σ} {t = t} ⊢Γ ⊢T ⊢σ ⊢t =
  begin
    ((σ ∘ wk) , v 0) ∘ (I , t)
  ≈⟨ ,-∘ (s-∘ (s-wk (⊢∺ ⊢Γ (conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)))) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ))) (⊢I,t ⊢Γ ⊢T[σ] ⊢t) ⟩
    (σ ∘ wk ∘ (I , t)) , v 0 [ I , t ]
  ≈⟨ ,-cong σ∘wk∘[I,s] ⊢T (≈-refl (conv (t[σ] (vlookup ⊢T[σ]Γ here) (⊢I,t ⊢Γ ⊢T[σ] ⊢t)) (≈-trans ([]-cong-Se′ ([∘]-Se ⊢T ⊢σ (s-wk ⊢T[σ]Γ)) (⊢I,t ⊢Γ ⊢T[σ] ⊢t)) ([∘]-Se ⊢T (s-∘ (s-wk ⊢T[σ]Γ) ⊢σ) (⊢I,t ⊢Γ ⊢T[σ] ⊢t))))) ⟩
    σ , v 0 [ I , t ]
  ≈⟨ ,-cong (s-≈-refl ⊢σ) ⊢T (≈-conv ([,]-v-ze (s-I ⊢Γ) ⊢T[σ] ⊢t′) ([I] ⊢T[σ])) ⟩
    σ , t
  ∎
  where
    open SR

    ⊢T[σ] = t[σ]-Se ⊢T ⊢σ
    ⊢T[σ]Γ = ⊢∺ ⊢Γ ⊢T[σ]
    ⊢t′ = conv ⊢t (≈-sym ([I] ⊢T[σ]))

    σ∘wk∘[I,s] : Γ ⊢s σ ∘ wk ∘ (I , t) ≈ σ ∶ Δ
    σ∘wk∘[I,s] =
      begin
        σ ∘ wk ∘ (I , t)
      ≈⟨ ∘-assoc ⊢σ (s-wk ⊢T[σ]Γ) (⊢I,t ⊢Γ ⊢T[σ] ⊢t) ⟩
        σ ∘ (wk ∘ (I , t))
      ≈⟨ ∘-cong (wk∘[σ,t]≈σ ⊢T[σ]Γ (s-I ⊢Γ) ⊢t′) (s-≈-refl ⊢σ) ⟩
        σ ∘ I
      ≈⟨ ∘-I ⊢σ ⟩
        σ
      ∎

qσ∘[I,ze]≈σ,ze : ⊢ Γ →
                 ⊢ Δ →
                 Γ ⊢s σ ∶ Δ →
                 --------------------------------------
                 Γ ⊢s q σ ∘ (I , ze) ≈ σ , ze ∶ N ∺ Δ
qσ∘[I,ze]≈σ,ze {Γ = Γ} {Δ = Δ} {σ = σ} ⊢Γ ⊢Δ ⊢σ =
  begin
    q σ ∘ (I , ze)
  ≈⟨ qσ∘[I,t]≈σ,t ⊢Γ (N-wf 0 ⊢Δ) ⊢σ (conv-N-[]-sym (ze-I ⊢Γ) ⊢σ) ⟩
    σ , ze
  ∎
  where
    open SR

q[wk]∘[σ,v0[σ]]≈σ : ⊢ T ∺ Δ →
                    Γ ⊢s σ ∶ T ∺ Δ →
                    -----------------------------------------
                    Γ ⊢s q wk ∘ (σ , v 0 [ σ ]) ≈ σ ∶ T ∺ Δ
q[wk]∘[σ,v0[σ]]≈σ {σ = σ} ⊢TΔ@(⊢∺ _ ⊢T) ⊢σ =
  begin
    q wk ∘ (σ , v 0 [ σ ])
  ≈˘⟨ ∘-cong ([I,t]∘σ≈σ,t[σ] (⊢∺ ⊢TΔ ⊢T[wk]) ⊢σ ⊢v0) (s-≈-refl ⊢q[wk]) ⟩
    q wk ∘ ((I , v 0) ∘ σ)
  ≈˘⟨ ∘-assoc ⊢q[wk] (s-, (s-I ⊢TΔ) ⊢T[wk] (conv ⊢v0 (≈-sym ([I] ⊢T[wk])))) ⊢σ ⟩
    (q wk ∘ (I , v 0)) ∘ σ
  ≈⟨ ∘-cong (s-≈-refl ⊢σ) (qσ∘[I,t]≈σ,t ⊢TΔ ⊢T ⊢wk′ ⊢v0) ⟩
    (wk , v 0) ∘ σ
  ≈⟨ ∘-cong (s-≈-refl ⊢σ) (wk,v0≈I ⊢TΔ) ⟩
    I ∘ σ
  ≈⟨ I-∘ ⊢σ ⟩
    σ
  ∎
  where
    open SR

    ⊢v0 = vlookup ⊢TΔ here
    ⊢wk′ = s-wk ⊢TΔ
    ⊢T[wk] = t[σ]-Se ⊢T ⊢wk′
    ⊢q[wk] = ⊢q ⊢TΔ ⊢wk′ ⊢T

q[wk]∘[I,v0]≈I : ⊢ T ∺ Γ →
                 --------------------------------------
                 T ∺ Γ ⊢s q wk ∘ (I , v 0) ≈ I ∶ T ∺ Γ
q[wk]∘[I,v0]≈I ⊢TΓ@(⊢∺ _ ⊢T) =
  begin
    q wk ∘ (I , v 0)
  ≈⟨ qσ∘[I,t]≈σ,t ⊢TΓ ⊢T ⊢wk′ ⊢v0 ⟩
    (wk , v 0)
  ≈⟨ wk,v0≈I ⊢TΓ ⟩
    I
  ∎
  where
    open SR

    ⊢wk′ = s-wk ⊢TΓ
    ⊢v0 = vlookup ⊢TΓ here
