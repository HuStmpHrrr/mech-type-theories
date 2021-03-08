{-# OPTIONS --without-K --safe #-}

-- complementary rules
module PTT.Statics.Complement where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc

import Data.Nat.Properties as ℕₚ

v0-lookup : ⊢ Γ →
            Γ ⊢ S →
            ---------------------
            S ∷ Γ ⊢ v 0 ∶ S [ ↑ ]
v0-lookup ⊢Γ (_ , ⊢S) = vlookup (⊢∷ ⊢Γ ⊢S) here

vsuc-lookup : ∀ {x} →
              Γ ⊢ v x ∶ T →
              ⊢ S ∷ Γ →
              ---------------------------
              S ∷ Γ ⊢ v (suc x) ∶ T [ ↑ ]
vsuc-lookup ⊢x ⊢SΓ
  with vlookup-inv ⊢x
...  | _ , T∈Γ , T≲T′ = conv-* ⊢SΓ (vlookup ⊢SΓ (there T∈Γ)) (S-↑ ⊢SΓ) T≲T′

⊢T⇒⊢Tσ : ∀ {i} →
         Δ ⊢ S ∶ Se i →
         Γ ⊢s σ ∶ Δ →
         Γ ⊢ S [ σ ] ∶ Se i
⊢T⇒⊢Tσ ⊢S ⊢σ = conv (t[σ] ⊢S ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))

⊢qσ : ∀ {i} →
      ⊢ Γ →
      Δ ⊢ S ∶ Se i →
      Γ ⊢s σ ∶ Δ →
      S [ σ ] ∷ Γ ⊢s q σ ∶ S ∷ Δ
⊢qσ ⊢Γ ⊢S ⊢σ = S-, ⊢σ↑ ⊢S (conv (vlookup ⊢SσΓ here) (≈-≲ (≈-sym (≈-conv ([∘] (S-↑ ⊢SσΓ) ⊢σ ⊢S) (≈-≲ (Se-[] ⊢σ↑ ℕₚ.≤-refl))))))
  where ⊢SσΓ = ⊢∷ ⊢Γ (⊢T⇒⊢Tσ ⊢S ⊢σ)
        ⊢σ↑  = S-∘ (S-↑ ⊢SσΓ) ⊢σ

⊢∈⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           Γ ⊢ T
⊢∈⇒ty-wf (⊢∷ ⊢Γ ⊢T) here = _ , ⊢T⇒⊢Tσ ⊢T (S-↑ (⊢∷ ⊢Γ ⊢T))
⊢∈⇒ty-wf (⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ⊢∈⇒ty-wf ⊢Γ T∈Γ
...  | _ , ⊢T            = _ , ⊢T⇒⊢Tσ ⊢T (S-↑ (⊢∷ ⊢Γ ⊢S))

I-, : ∀ {i} →
      ⊢ Γ →
      Γ ⊢ T ∶ Se i →
      Γ ⊢ t ∶ T →
      Γ ⊢s I , t ∶ T ∷ Γ
I-, ⊢Γ ⊢T ⊢t = S-, (S-I ⊢Γ) ⊢T (conv ⊢t (≈-≲ (≈-sym ([I] ⊢T))))

⊢[I] : ∀ {i} →
       ⊢ Γ →
       Γ ⊢ T ∶ Se i →
       Γ ⊢ t ∶ T →
       Γ ⊢ t [ I ] ∶ T
⊢[I] ⊢Γ ⊢T ⊢t = conv (t[σ] ⊢t (S-I ⊢Γ)) (≈-≲ ([I] ⊢T))

[]-Π : ∀ {i} →
       Δ ⊢ t ∶ Π S T →
       Γ ⊢s σ ∶ Δ →
       Δ ⊢ Π S T ∶ Se i →
       Γ ⊢ t [ σ ] ∶ Π (S [ σ ]) (T [ q σ ])
[]-Π ⊢t ⊢σ ⊢Π
  with inv-Π-wf ⊢Π | inv-Π-wf′ ⊢Π
...  | _ , ⊢T      | _ , ⊢S = conv (t[σ] ⊢t ⊢σ) (≈-≲ (Π-[] ⊢σ ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)))

ΠSe-$ : ∀ {i j} →
        ⊢ Γ →
        Γ ⊢ S ∶ Se j →
        Γ ⊢ T ∶ Π S (Se i) →
        Γ ⊢ s ∶ S →
        Γ ⊢ T $ s ∶ Se i
ΠSe-$ ⊢Γ ⊢S ⊢T ⊢s = conv (Λ-E ⊢T ⊢s) (≈-≲ (Se-[] (I-, ⊢Γ ⊢S ⊢s) ℕₚ.≤-refl))



T-[∘] : ∀ {i} →
        Γ ⊢s τ ∶ Γ′ →
        Γ′ ⊢s σ ∶ Γ″ →
        Γ″ ⊢ T ∶ Se i →
        ---------------------------------------
        Γ ⊢ T [ σ ∘ τ ] ≈ T [ σ ] [ τ ] ∶ Se i
T-[∘] ⊢τ ⊢σ ⊢T = ≈-conv ([∘] ⊢τ ⊢σ ⊢T)
                        (≈-≲ (Se-[] (S-∘ ⊢τ ⊢σ) ℕₚ.≤-refl))

[]-cong-Se : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ S ≈ S′ ∶ Se i →
             Γ ⊢s σ ≈ τ ∶ Δ →
             Γ ⊢ S [ σ ] ≈ S′ [ τ ] ∶ Se i
[]-cong-Se ⊢σ S≈S′ σ≈τ = ≈-conv ([]-cong σ≈τ S≈S′) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))

[,]-v-ze-∘ : ⊢ S ∷ Δ →
             Γ′ ⊢s σ ∶ Δ →
             Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢ s ∶ S [ σ ] →
             ---------------------------------------------------------
             Γ ⊢ v 0 [ (σ , s) ∘ τ ] ≈ s [ τ ] ∶ S [ ↑ ∘ (σ , s) ∘ τ ]
[,]-v-ze-∘ {S} {_} {_} {σ} {_} {τ} {s} (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢τ ⊢s =
  ≈-conv (let open TR in
         begin
           v 0 [ (σ , s) ∘ τ ]    ≈⟨ [∘] ⊢τ (S-, ⊢σ ⊢S ⊢s) (vlookup (⊢∷ ⊢Δ ⊢S) here) ⟩
           v 0 [ σ , s ] [ τ ]    ≈!⟨ ≈-conv ([]-cong (S-≈-refl ⊢τ) ([,]-v-ze ⊢σ ⊢S ⊢s))
                                             (≈-≲ helper) ⟩
           s [ τ ]                ∎)
         (≈-≲ (≈-sym helper′))
  where ⊢σ,s    = S-, ⊢σ ⊢S ⊢s
        ⊢σsτ    = S-∘ ⊢τ ⊢σ,s
        ⊢↑      = S-↑ (⊢∷ ⊢Δ ⊢S)
        helper  = begin
          S [ σ ] [ τ ]           ≈˘⟨ T-[∘] ⊢τ ⊢σ ⊢S ⟩
          S [ σ ∘ τ ]             ≈⟨ []-cong-Se (S-∘ ⊢τ ⊢σ) (≈-refl ⊢S) (∘-cong (S-≈-refl ⊢τ) (S-≈-sym (↑-∘-, ⊢σ ⊢S ⊢s))) ⟩
          S [ ↑ ∘ σ , s ∘ τ ]     ≈⟨ []-cong-Se (S-∘ ⊢τ (S-∘ ⊢σ,s ⊢↑)) (≈-refl ⊢S) (∘-assoc ⊢↑ ⊢σ,s ⊢τ) ⟩
          S [ ↑ ∘ ((σ , s) ∘ τ) ] ≈!⟨ T-[∘] ⊢σsτ ⊢↑ ⊢S ⟩
          S [ ↑ ] [ (σ , s) ∘ τ ] ∎
          where open TR
        helper′ = begin
          S [ ↑ ∘ (σ , s) ∘ τ ]   ≈⟨ []-cong-Se (S-∘ ⊢τ (S-∘ ⊢σ,s ⊢↑)) (≈-refl ⊢S) (∘-assoc ⊢↑ ⊢σ,s ⊢τ) ⟩
          S [ ↑ ∘ ((σ , s) ∘ τ) ] ≈!⟨ T-[∘] ⊢σsτ ⊢↑ ⊢S ⟩
          S [ ↑ ] [ (σ , s) ∘ τ ] ∎
          where open TR

,-ext′ : ⊢ S ∷ Δ →
         Γ′ ⊢s σ ∶ Δ →
         Γ ⊢s τ ∶ Γ′ →
         Γ′ ⊢ s ∶ S [ σ ] →
         -------------------------------------------
         Γ ⊢s (σ , s) ∘ τ ≈ (σ ∘ τ) , s [ τ ] ∶ S ∷ Δ
,-ext′ {_} {_} {_} {σ} {_} {τ} {s} (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢τ ⊢s = begin
  (σ , s) ∘ τ                                 ≈⟨ ,-ext ⊢σsτ ⟩
  (↑ ∘ ((σ , s) ∘ τ)) , (v 0 [ (σ , s) ∘ τ ]) ≈˘⟨ ,-cong ⊢S (∘-assoc (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢σ,s ⊢τ)
                                                            (≈-sym ([,]-v-ze-∘ (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢τ ⊢s)) ⟩
  ((↑ ∘ (σ , s) ∘ τ) , (s [ τ ]))             ≈!⟨ ,-cong ⊢S (∘-cong (S-≈-refl ⊢τ) (↑-∘-, ⊢σ ⊢S ⊢s)) (≈-refl (conv (t[σ] ⊢s ⊢τ) (≈-≲ (≈-sym helper)))) ⟩
  (σ ∘ τ) , (s [ τ ])                         ∎
  where open TRS
        ⊢σ,s = S-, ⊢σ ⊢S ⊢s
        ⊢σsτ = S-∘ ⊢τ ⊢σ,s
        helper = ≈-trans ([]-cong-Se (S-∘ ⊢τ (S-∘ ⊢σ,s (S-↑ (⊢∷ ⊢Δ ⊢S)))) (≈-refl ⊢S) (∘-cong (S-≈-refl ⊢τ) (↑-∘-, ⊢σ ⊢S ⊢s)))
                         (T-[∘] ⊢τ ⊢σ ⊢S)

[∘]-cong : ∀ {i} →
           ⊢ S ∷ Δ →
           Γ′ ⊢s σ ∶ Δ →
           Γ ⊢s τ ∶ Γ′ →
           Γ′ ⊢ s ∶ S [ σ ] →
           S ∷ Δ ⊢ T ∶ Se i →
           S ∷ Δ ⊢ T ≈ T′ ∶ Se i →
           -------------------------------------------------------
           Γ ⊢ T [ σ , s ] [ τ ] ≈ T′ [ (σ ∘ τ) , s [ τ ] ] ∶ Se i
[∘]-cong {_} {_} {_} {σ} {_} {τ} {s} {T} {T′} (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢τ ⊢s ⊢T T≈T′ = begin
  T [ σ , s ] [ τ ]          ≈˘⟨ T-[∘] ⊢τ (S-, ⊢σ ⊢S ⊢s) ⊢T ⟩
  T [ (σ , s) ∘ τ ]          ≈!⟨ []-cong-Se (S-∘ ⊢τ (S-, ⊢σ ⊢S ⊢s)) T≈T′ (,-ext′ (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢τ ⊢s) ⟩
  T′ [ (σ ∘ τ) , (s [ τ ]) ] ∎
  where open TR

[|∘]-cong : ∀ {i} →
            ⊢ S ∷ Δ →
            Γ ⊢s σ ∶ Δ →
            Δ ⊢ s ∶ S →
            S ∷ Δ ⊢ T ∶ Se i →
            -----------------------------------------------
            Γ ⊢ T [| s ] [ σ ] ≈ T [ σ , s [ σ ] ] ∶ Se i
[|∘]-cong (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s ⊢T = ≈-trans ([∘]-cong (⊢∷ ⊢Δ ⊢S) (S-I ⊢Δ) ⊢σ (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S)))) ⊢T (≈-refl ⊢T))
                                        ([]-cong-Se (S-, (S-∘ ⊢σ (S-I ⊢Δ)) ⊢S ⊢sσ)
                                                    (≈-refl ⊢T)
                                                    (,-cong ⊢S (I-∘ ⊢σ) (≈-refl ⊢sσ)))
  where helper = []-cong-Se ⊢σ (≈-refl ⊢S) (S-≈-sym (I-∘ ⊢σ))
        ⊢sσ    = conv (t[σ] ⊢s ⊢σ) (≈-≲ helper)

[q∘]-cong : ∀ {i} →
            ⊢ Γ →
            ⊢ S ∷ Δ →
            Γ ⊢s σ ∶ Δ →
            Γ ⊢ s ∶ S [ σ ] →
            S ∷ Δ ⊢ T ∶ Se i →
            -------------------------------------------------------
            Γ ⊢ T [ q σ ] [| s ] ≈ T [ σ , s ] ∶ Se i
[q∘]-cong {_} {_} {_} {σ} {s} ⊢Γ (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s ⊢T
  = ≈-trans ([∘]-cong (⊢∷ ⊢Δ ⊢S)
                      (S-∘ (S-↑ ⊢SσΓ) ⊢σ)
                      I,s
                      (conv (vlookup ⊢SσΓ here) (≈-≲ (≈-sym (T-[∘] (S-↑ ⊢SσΓ) ⊢σ ⊢S))))
                      ⊢T (≈-refl ⊢T))
                      (≈-sym ([]-cong-Se (S-, ⊢σ ⊢S ⊢s) (≈-refl ⊢T)
                                         (,-cong ⊢S (begin
                                             σ                   ≈˘⟨ ∘-I ⊢σ ⟩
                                             σ ∘ I               ≈˘⟨ ∘-cong (↑-∘-, (S-I ⊢Γ) ⊢S[σ] ⊢s′) (S-≈-refl ⊢σ) ⟩
                                             (σ ∘ (↑ ∘ (I , s))) ≈!⟨ S-≈-sym (∘-assoc ⊢σ (S-↑ ⊢SσΓ) I,s) ⟩
                                             σ ∘ ↑ ∘ (I , s)     ∎)
                                                    (≈-sym (≈-conv ([,]-v-ze (S-I ⊢Γ) ⊢S[σ] ⊢s′) (≈-≲ ([I] ⊢S[σ])))))))
  where ⊢S[σ] = ⊢T⇒⊢Tσ ⊢S ⊢σ
        ⊢SσΓ  = ⊢∷ ⊢Γ ⊢S[σ]
        I,s   = I-, ⊢Γ ⊢S[σ] ⊢s
        Sσ≲   = ≈-≲ (≈-sym ([I] ⊢S[σ]))
        ⊢s′   = conv ⊢s Sσ≲
        open TRS

I-ext : ⊢ S ∷ Γ →
        S ∷ Γ ⊢s I ≈ ↑ , v 0 ∶ S ∷ Γ
I-ext (⊢∷ ⊢Γ ⊢S) = begin
  I                       ≈⟨ ,-ext (S-I (⊢∷ ⊢Γ ⊢S)) ⟩
  ((↑ ∘ I) , (v 0 [ I ])) ≈!⟨ ,-cong ⊢S (∘-I (S-↑ (⊢∷ ⊢Γ ⊢S)))
                                     ([I] (conv (vlookup (⊢∷ ⊢Γ ⊢S) here)
                                                (≈-≲ ([]-cong-Se (S-↑ (⊢∷ ⊢Γ ⊢S)) (≈-refl ⊢S) (S-≈-sym (∘-I (S-↑ (⊢∷ ⊢Γ ⊢S)))))))) ⟩
  ↑ , v 0                 ∎
  where open TRS