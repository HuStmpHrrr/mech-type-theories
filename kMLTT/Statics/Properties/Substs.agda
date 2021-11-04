{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Substs where

open import Lib
open import Function.Base using ( flip )
open import kMLTT.Statics.Full
open import kMLTT.Statics.Misc
open import kMLTT.Statics.Refl
open import kMLTT.Statics.PER

wk∘σ≈pσ : ⊢ T ∺ Δ →
          Γ ⊢s σ ∶ T ∺ Δ →
          Γ ⊢s wk ∘ σ ≈ p σ ∶ Δ
wk∘σ≈pσ ⊢TΔ ⊢σ = s-≈-trans (p-∘ (s-I ⊢TΔ) ⊢σ) (p-cong (I-∘ ⊢σ))

wk∘[σ,t]≈σ : ⊢ T ∺ Δ →
             Γ ⊢s σ ∶ Δ →
             Γ ⊢ t ∶ T [ σ ] →
             Γ ⊢s wk ∘ (σ , t) ≈ σ ∶ Δ
wk∘[σ,t]≈σ {σ = σ} {t = t} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ ⊢t =
  begin
    wk ∘ (σ , t)
  ≈⟨ p-∘ (s-I ⊢TΔ) ⊢σ,t ⟩
    p (I ∘ (σ , t))
  ≈⟨ p-cong (I-∘ ⊢σ,t) ⟩
    p (σ , t)
  ≈⟨ p-, ⊢σ ⊢T ⊢t ⟩
    σ
  ∎
  where
    open SR

    ⊢σ,t = s-, ⊢σ ⊢T ⊢t

q[pI]∘[σ,v0[σ]]≈σ : ⊢ T ∺ Δ →
                    Γ ⊢s σ ∶ T ∺ Δ →
                    Γ ⊢s q (p I) ∘ (σ , v 0 [ σ ]) ≈ σ ∶ T ∺ Δ
q[pI]∘[σ,v0[σ]]≈σ {σ = σ} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ =
  begin
    q (p I) ∘ (σ , v 0 [ σ ])
  ≈⟨ ,-∘ (s-∘ ⊢pI′ ⊢pI) ⊢T (conv ⊢v0 ([∘]-Se ⊢T ⊢pI ⊢pI′)) ⊢σ,v0[σ] ⟩
    (p I ∘ p I ∘ (σ , v 0 [ σ ])) , v 0 [ σ , v 0 [ σ ] ]
  ≈⟨ ,-cong pI∘pI∘[σ,v0[σ]]≈pσ ⊢T (≈-refl (conv (t[σ] ⊢v0 ⊢σ,v0[σ]) (≈-trans (≈-conv-Se ([∘]-Se ⊢T ⊢pI ⊢pI′) ⊢σ,v0[σ] (s-≈-refl ⊢σ,v0[σ])) ([∘]-Se ⊢T (s-∘ ⊢pI′ ⊢pI) ⊢σ,v0[σ])))) ⟩
    p σ , v 0 [ σ , v 0 [ σ ] ]
  ≈⟨ ,-cong (s-≈-refl (s-p ⊢σ)) ⊢T (≈-conv ([,]-v-ze ⊢σ ⊢T[wk] ⊢v0[σ]) (≈-trans ([∘]-Se ⊢T ⊢pI ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ ⊢pI) (wk∘σ≈pσ ⊢TΔ ⊢σ)))) ⟩
    p σ , v 0 [ σ ]
  ≈˘⟨ ,-ext ⊢σ ⟩
    σ
  ∎
  where
    open SR

    ⊢v0[σ] = t[σ] (vlookup ⊢TΔ here) ⊢σ
    ⊢pI = ⊢wk ⊢TΔ
    ⊢T[wk] = conv-Se ⊢T ⊢pI
    ⊢T[wk]TΔ = ⊢∷ ⊢TΔ ⊢T[wk]
    ⊢pI′ = ⊢wk ⊢T[wk]TΔ
    ⊢σ,v0[σ] = s-, ⊢σ ⊢T[wk] ⊢v0[σ]
    ⊢v0 = vlookup ⊢T[wk]TΔ here

    pI∘pI∘[σ,v0[σ]]≈pσ =
      begin
        p I ∘ p I ∘ (σ , v 0 [ σ ])
      ≈⟨ ∘-assoc ⊢pI ⊢pI′ ⊢σ,v0[σ] ⟩
        p I ∘ (p I ∘ (σ , v 0 [ σ ]))
      ≈⟨ ∘-cong (wk∘σ≈pσ ⊢T[wk]TΔ ⊢σ,v0[σ]) (s-≈-refl ⊢pI) ⟩
        p I ∘ p (σ , v 0 [ σ ])
      ≈⟨ ∘-cong (p-, ⊢σ ⊢T[wk] ⊢v0[σ]) (s-≈-refl ⊢pI) ⟩
        p I ∘ σ
      -- ≈⟨ (∘-cong (s-≈-refl ⊢σ,v0[σ]) (p-∘ (s-I ⊢TΔ) ⊢pI′)) ⟩
      --   p (I ∘ p I) ∘ (σ , v 0 [ σ ])
      ≈⟨ wk∘σ≈pσ ⊢TΔ ⊢σ ⟩
        p σ
      ∎

q[pI]∘[I,v0]≈I : ⊢ T ∺ Γ →
                 T ∺ Γ ⊢s q (p I) ∘ (I , v 0) ≈ I ∶ T ∺ Γ
q[pI]∘[I,v0]≈I ⊢TΓ@(⊢∷ _ ⊢T) =
  begin
    q (p I) ∘ (I , v 0)
  ≈⟨ ∘-cong (,-cong (I-≈ ⊢TΓ) ⊢T[wk] ((≈-sym ([I] (conv ⊢v0 (≈-sym ([I] ⊢T[wk]))))))) (s-≈-refl (⊢q ⊢TΓ ⊢pI ⊢T)) ⟩
    q (p I) ∘ (I , v 0 [ I ])
  ≈⟨ q[pI]∘[σ,v0[σ]]≈σ ⊢TΓ (s-I ⊢TΓ) ⟩
    I
  ∎
  where
    open SR

    ⊢v0[I] = t[σ] (vlookup ⊢TΓ here) (s-I ⊢TΓ)
    ⊢pI = ⊢wk ⊢TΓ
    ⊢T[wk] = conv-Se ⊢T ⊢pI
    ⊢T[wk]TΓ = ⊢∷ ⊢TΓ ⊢T[wk]
    ⊢pI′ = ⊢wk ⊢T[wk]TΓ
    ⊢v0 = vlookup ⊢TΓ here
    ⊢v0′ = vlookup ⊢T[wk]TΓ here
