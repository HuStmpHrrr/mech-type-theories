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

p[qσ]≈σ∘wk : ∀ {i} →
             ⊢ Γ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢s σ ∶ Δ →
             (T [ σ ]) ∺ Γ ⊢s p (q σ) ≈ σ ∘ wk ∶ Δ
p[qσ]≈σ∘wk {σ = σ} ⊢Γ ⊢T ⊢σ =
  begin
    p ((σ ∘ wk) , v 0)
  ≈⟨ p-, (s-∘ (⊢wk ⊢T[σ]Γ) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (⊢wk ⊢T[σ]Γ))) ⟩
    σ ∘ wk
  ∎
  where
    open SR

    ⊢T[σ]Γ = ⊢∷ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

wk∘[σ,t]≈σ : ⊢ T ∺ Δ →
             Γ ⊢s σ ∶ Δ →
             Γ ⊢ t ∶ T [ σ ] →
             Γ ⊢s wk ∘ (σ , t) ≈ σ ∶ Δ
wk∘[σ,t]≈σ {σ = σ} {t = t} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ ⊢t =
  begin
    wk ∘ (σ , t)
  ≈⟨ wk∘σ≈pσ ⊢TΔ (s-, ⊢σ ⊢T ⊢t) ⟩
    p (σ , t)
  ≈⟨ p-, ⊢σ ⊢T ⊢t ⟩
    σ
  ∎
  where
    open SR

wk∘qσ≈σ∘wk : ⊢ Γ →
             ⊢ T ∺ Δ →
             Γ ⊢s σ ∶ Δ →
             (T [ σ ]) ∺ Γ ⊢s wk ∘ q σ ≈ σ ∘ wk ∶ Δ
wk∘qσ≈σ∘wk {σ = σ} ⊢Γ ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ =
  begin
    wk ∘ q σ
  ≈⟨ wk∘σ≈pσ ⊢TΔ ⊢qσ ⟩
    p (q σ)
  ≈⟨ p[qσ]≈σ∘wk ⊢Γ ⊢T ⊢σ ⟩
    σ ∘ wk
  ∎
  where
    open SR

    ⊢qσ = ⊢q ⊢Γ ⊢σ ⊢T

[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN : ⊢ Γ →
                             ⊢ T ∺ N ∺ Δ →
                             Γ ⊢s σ ∶ Δ →
                             (T [ q σ ]) ∺ N ∺ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ (wk ∘ wk) ∶ Δ
[wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN {σ = σ} ⊢Γ ⊢TNΔ@(⊢∷ ⊢NΔ@(⊢∷ ⊢Δ _) ⊢T) ⊢σ =
  begin
    wk ∘ wk ∘ q (q σ)
  ≈⟨ ∘-assoc (⊢wk ⊢NΔ) (⊢wk ⊢TNΔ) ⊢q[qσ] ⟩
    wk ∘ (wk ∘ q (q σ))
  ≈⟨ ∘-cong (wk∘qσ≈σ∘wk ⊢NΓ ⊢TNΔ ⊢qσ) (s-≈-refl (⊢wk ⊢NΔ)) ⟩
    wk ∘ ((q σ) ∘ wk)
  ≈˘⟨ ∘-assoc (⊢wk ⊢NΔ) ⊢qσ (⊢wk ⊢T[qσ]NΓ) ⟩
    wk ∘ (q σ) ∘ wk
  ≈⟨ ∘-cong (s-≈-refl (s-conv (⊢wk ⊢T[qσ]NΓ) (∷-cong′ ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-Se (N-wf 0 ⊢Δ) ⊢σ) (≈-sym (N-[] 0 ⊢σ))))) (wk∘qσ≈σ∘wk ⊢Γ ⊢NΔ ⊢σ) ⟩
    σ ∘ wk ∘ wk
  ≈⟨ ∘-assoc ⊢σ (⊢wk ⊢NΓ) (⊢wk ⊢T[qσ]NΓ) ⟩
    σ ∘ (wk ∘ wk)
  ∎
  where
    open SR

    ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ

    ⊢NΓ = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
    ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
    ⊢T[qσ]NΓ = ⊢∷ ⊢NΓ ⊢T[qσ]

    ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T

[I,t]∘σ≈σ,t[σ] : ⊢ Γ →
                 ⊢ T ∺ Δ →
                 Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ T →
                 Γ ⊢s (I , t) ∘ σ ≈ σ , t [ σ ] ∶ T ∺ Δ
[I,t]∘σ≈σ,t[σ] {σ = σ} {t = t} ⊢Γ (⊢∷ ⊢Δ ⊢T) ⊢σ ⊢t =
  begin
    (I , t) ∘ σ
  ≈⟨ ,-∘ (s-I ⊢Δ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T))) ⊢σ ⟩
    (I ∘ σ) , t [ σ ]
  ≈⟨ ,-cong (I-∘ ⊢σ) ⊢T (≈-refl (conv (t[σ] ⊢t ⊢σ) ([]-cong-Se (≈-refl ⊢T) ⊢σ (s-≈-sym (I-∘ ⊢σ))))) ⟩
    σ , t [ σ ]
  ∎
  where
    open SR

qσ∘[I,t]≈σ,t : ∀ {i} →
               ⊢ Γ →
               Δ ⊢ T ∶ Se i →
               Γ ⊢s σ ∶ Δ →
               Γ ⊢ t ∶ T [ σ ] →
               Γ ⊢s q σ ∘ (I , t) ≈ σ , t ∶ T ∺ Δ
qσ∘[I,t]≈σ,t {Γ = Γ} {Δ = Δ} {σ = σ} {t = t} ⊢Γ ⊢T ⊢σ ⊢t =
  begin
    ((σ ∘ wk) , v 0) ∘ (I , t)
  ≈⟨ ,-∘ (s-∘ (s-p (s-I ⊢T[σ]Γ)) ⊢σ) ⊢T (conv (vlookup ⊢T[σ]Γ here) ([∘]-Se ⊢T ⊢σ (⊢wk ⊢T[σ]Γ))) (s-, (s-I ⊢Γ) ⊢T[σ] ⊢t′) ⟩
    (σ ∘ wk ∘ (I , t)) , v 0 [ I , t ]
  ≈⟨ ,-cong σ∘wk∘[I,s] ⊢T (≈-refl (conv (t[σ] (vlookup ⊢T[σ]Γ here) (s-, (s-I ⊢Γ) ⊢T[σ] ⊢t′)) (≈-trans ([]-cong-Se′ ([∘]-Se ⊢T ⊢σ (⊢wk ⊢T[σ]Γ)) (s-, (s-I ⊢Γ) ⊢T[σ] ⊢t′)) ([∘]-Se ⊢T (s-∘ (⊢wk ⊢T[σ]Γ) ⊢σ) (s-, (s-I ⊢Γ) ⊢T[σ] ⊢t′))))) ⟩
    σ , v 0 [ I , t ]
  ≈⟨ ,-cong (s-≈-refl ⊢σ) ⊢T (≈-conv ([,]-v-ze (s-I ⊢Γ) ⊢T[σ] ⊢t′) ([I] ⊢T[σ])) ⟩
    σ , t
  ∎
  where
    open SR

    ⊢T[σ] = t[σ]-Se ⊢T ⊢σ
    ⊢T[σ]Γ = ⊢∷ ⊢Γ ⊢T[σ]
    ⊢t′ = conv ⊢t (≈-sym ([I] ⊢T[σ]))

    σ∘wk∘[I,s] : Γ ⊢s σ ∘ wk ∘ (I , t) ≈ σ ∶ Δ
    σ∘wk∘[I,s] =
      begin
        σ ∘ wk ∘ (I , t)
      ≈⟨ ∘-assoc ⊢σ (⊢wk ⊢T[σ]Γ) (s-, (s-I ⊢Γ) ⊢T[σ] ⊢t′) ⟩
        σ ∘ (wk ∘ (I , t))
      ≈⟨ ∘-cong (wk∘[σ,t]≈σ ⊢T[σ]Γ (s-I ⊢Γ) ⊢t′) (s-≈-refl ⊢σ) ⟩
        σ ∘ I
      ≈⟨ ∘-I ⊢σ ⟩
        σ
      ∎

q[wk]∘[σ,v0[σ]]≈σ : ⊢ T ∺ Δ →
                    Γ ⊢s σ ∶ T ∺ Δ →
                    Γ ⊢s q wk ∘ (σ , v 0 [ σ ]) ≈ σ ∶ T ∺ Δ
q[wk]∘[σ,v0[σ]]≈σ {σ = σ} ⊢TΔ@(⊢∷ _ ⊢T) ⊢σ =
  begin
    q wk ∘ (σ , v 0 [ σ ])
  ≈⟨ ,-∘ (s-∘ ⊢wk′′ ⊢wk′) ⊢T (conv ⊢v0 ([∘]-Se ⊢T ⊢wk′ ⊢wk′′)) ⊢σ,v0[σ] ⟩
    (wk ∘ wk ∘ (σ , v 0 [ σ ])) , v 0 [ σ , v 0 [ σ ] ]
  ≈⟨ ,-cong wk∘wk∘[σ,v0[σ]]≈pσ ⊢T (≈-refl (conv (t[σ] ⊢v0 ⊢σ,v0[σ]) (≈-trans ([]-cong-Se ([∘]-Se ⊢T ⊢wk′ ⊢wk′′) ⊢σ,v0[σ] (s-≈-refl ⊢σ,v0[σ])) ([∘]-Se ⊢T (s-∘ ⊢wk′′ ⊢wk′) ⊢σ,v0[σ])))) ⟩
    p σ , v 0 [ σ , v 0 [ σ ] ]
  ≈⟨ ,-cong (s-≈-refl (s-p ⊢σ)) ⊢T (≈-conv ([,]-v-ze ⊢σ ⊢T[wk] ⊢v0[σ]) (≈-trans ([∘]-Se ⊢T ⊢wk′ ⊢σ) ([]-cong-Se (≈-refl ⊢T) (s-∘ ⊢σ ⊢wk′) (wk∘σ≈pσ ⊢TΔ ⊢σ)))) ⟩
    p σ , v 0 [ σ ]
  ≈˘⟨ ,-ext ⊢σ ⟩
    σ
  ∎
  where
    open SR

    ⊢v0[σ] = t[σ] (vlookup ⊢TΔ here) ⊢σ
    ⊢wk′ = ⊢wk ⊢TΔ
    ⊢T[wk] = t[σ]-Se ⊢T ⊢wk′
    ⊢T[wk]TΔ = ⊢∷ ⊢TΔ ⊢T[wk]
    ⊢wk′′ = ⊢wk ⊢T[wk]TΔ
    ⊢σ,v0[σ] = s-, ⊢σ ⊢T[wk] ⊢v0[σ]
    ⊢v0 = vlookup ⊢T[wk]TΔ here

    wk∘wk∘[σ,v0[σ]]≈pσ =
      begin
        wk ∘ wk ∘ (σ , v 0 [ σ ])
      ≈⟨ ∘-assoc ⊢wk′ ⊢wk′′ ⊢σ,v0[σ] ⟩
        wk ∘ (wk ∘ (σ , v 0 [ σ ]))
      ≈⟨ ∘-cong (wk∘σ≈pσ ⊢T[wk]TΔ ⊢σ,v0[σ]) (s-≈-refl ⊢wk′) ⟩
        wk ∘ p (σ , v 0 [ σ ])
      ≈⟨ ∘-cong (p-, ⊢σ ⊢T[wk] ⊢v0[σ]) (s-≈-refl ⊢wk′) ⟩
        wk ∘ σ
      ≈⟨ wk∘σ≈pσ ⊢TΔ ⊢σ ⟩
        p σ
      ∎

q[wk]∘[I,v0]≈I : ⊢ T ∺ Γ →
                 T ∺ Γ ⊢s q wk ∘ (I , v 0) ≈ I ∶ T ∺ Γ
q[wk]∘[I,v0]≈I ⊢TΓ@(⊢∷ _ ⊢T) =
  begin
    q wk ∘ (I , v 0)
  ≈⟨ ∘-cong (,-cong (I-≈ ⊢TΓ) ⊢T[wk] ((≈-sym ([I] (conv ⊢v0 (≈-sym ([I] ⊢T[wk]))))))) (s-≈-refl (⊢q ⊢TΓ ⊢wk′ ⊢T)) ⟩
    q wk ∘ (I , v 0 [ I ])
  ≈⟨ q[wk]∘[σ,v0[σ]]≈σ ⊢TΓ (s-I ⊢TΓ) ⟩
    I
  ∎
  where
    open SR

    ⊢v0[I] = t[σ] (vlookup ⊢TΓ here) (s-I ⊢TΓ)
    ⊢wk′ = ⊢wk ⊢TΓ
    ⊢T[wk] = t[σ]-Se ⊢T ⊢wk′
    ⊢T[wk]TΓ = ⊢∷ ⊢TΓ ⊢T[wk]
    ⊢wk′′ = ⊢wk ⊢T[wk]TΓ
    ⊢v0 = vlookup ⊢TΓ here
    ⊢v0′ = vlookup ⊢T[wk]TΓ here
