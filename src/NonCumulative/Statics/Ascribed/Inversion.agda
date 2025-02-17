{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Inversion where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties.Subst

Λ-inv′ : ∀ {i k R} →
         Γ ⊢ Λ (S ↙ i) t ∶[ k ] R → 
         ∃₂ λ j T → Γ ⊢ R ≈ Π (S ↙ i) (T ↙ j) ∶[ 1 + k ] Se k × k ≡ max i j × (S ↙ i) ∷ Γ ⊢ t ∶[ j ] T
Λ-inv′ (Λ-I {T = T} {j = j} ⊢S ⊢t k≡maxij) = _ , _ , ≈-refl (Π-wf ⊢S (proj₂ (presup-tm ⊢t)) k≡maxij) , k≡maxij , ⊢t
Λ-inv′ (conv ⊢t x) 
  with Λ-inv′ ⊢t 
... | j , T , ≈R , k≡maxij , ⊢t = _ , _ , ≈-trans (≈-sym x) ≈R , k≡maxij , ⊢t 

ze-inv : ∀ {i} →
         Γ ⊢ ze ∶[ i ] T →
         i ≡ 0 × Γ ⊢ T ≈ N ∶[ 1 ] Se 0
ze-inv (ze-I ⊢Γ) = refl , ≈-refl (N-wf ⊢Γ)
ze-inv (conv ⊢ze T≈) 
  with ze-inv ⊢ze 
... | refl , ≈N = refl , (≈-trans (≈-sym T≈) ≈N)

su-inv : ∀ {i } →
         Γ ⊢ su t ∶[ i ] T →
         i ≡ 0 × Γ ⊢ T ≈ N ∶[ 1 ] Se 0 × Γ ⊢ t ∶[ 0 ] N
su-inv (su-I ⊢t) = refl , ≈-refl (N-wf (proj₁ (presup-tm ⊢t))) , ⊢t
su-inv (conv ⊢sut T≈) 
  with su-inv ⊢sut 
... | refl , ≈N , ⊢t = refl , ≈-trans (≈-sym T≈) ≈N , ⊢t

$-inv : ∀ {i R} →
         Γ ⊢ r $ s ∶[ i ] R →
         ∃₂ λ j k → ∃₂ λ S T → Γ ⊢ r ∶[ k ] Π (S ↙ j) (T ↙ i) × Γ ⊢ s ∶[ j ] S × k ≡ max j i × (Γ ⊢ R ≈ T [ I , s ∶ S ↙ j ] ∶[ 1 + i ] Se i)
$-inv (Λ-E ⊢S ⊢T ⊢r ⊢s x) = _ , _ , _ , _ , ⊢r , ⊢s , x , []-cong-Se′ (≈-refl ⊢T) (s-, (s-I (proj₁ (presup-tm ⊢S))) ⊢S (conv ⊢s (≈-sym ([I] ⊢S))))
$-inv (conv ⊢rs T≈) 
  with $-inv ⊢rs
... | j , k , S , T , ⊢r , ⊢s , refl , ≈Ts = _ , _ , _ , _ , ⊢r , ⊢s , refl , ≈-trans (≈-sym T≈) ≈Ts

liftt-inv : ∀ {i n} →
            Γ ⊢ liftt n t ∶[ i ] T →
            ∃₂ λ j S → i ≡ n + j × Γ ⊢ t ∶[ j ] S × Γ ⊢ T ≈ Liftt n (S ↙ j) ∶[ 1 + i ] Se i 
liftt-inv (L-I _ ⊢t) = _ , _ , refl , ⊢t , ≈-refl (Liftt-wf _ (proj₂ (presup-tm ⊢t))) 
liftt-inv (conv ⊢liftt T≈) 
  with liftt-inv ⊢liftt 
... | j , S , refl ,  ⊢t , ≈Liftt = _ , _ , refl , ⊢t , ≈-trans (≈-sym T≈) ≈Liftt

unlift-inv : ∀ {i} →
             Γ ⊢ unlift t ∶[ i ] T →
             ∃₂ λ j n → ∃ λ S → j ≡ n + i × Γ ⊢ t ∶[ j ] Liftt n (S ↙ i) × Γ ⊢ T ≈ S ∶[ 1 + i ] Se i  
unlift-inv (L-E {i = i} n ⊢T ⊢t) = _ , _ , _ , refl , ⊢t , ≈-refl ⊢T
unlift-inv (conv ⊢unliftt T≈) 
  with unlift-inv ⊢unliftt
... | j , n , S , refl , ⊢t , ≈S = _ , _ , _ , refl , ⊢t , ≈-trans (≈-sym T≈) ≈S

t[σ]-inv : ∀ {i} →
           Γ ⊢ t [ σ ] ∶[ i ] T →
           ∃₂ λ Δ S → Γ ⊢s σ ∶ Δ × Δ ⊢ t ∶[ i ] S × Γ ⊢ T ≈ S [ σ ] ∶[ 1 + i ] Se i
t[σ]-inv (t[σ] ⊢t ⊢σ) = _ , _ , ⊢σ , ⊢t , []-cong-Se′ (≈-refl (proj₂ (presup-tm ⊢t))) ⊢σ 
t[σ]-inv (conv ⊢t ≈T) 
  with t[σ]-inv ⊢t
... | Δ , S , ⊢σ , ⊢t , ≈S[σ] = _ , _ , ⊢σ , ⊢t , ≈-trans (≈-sym ≈T) ≈S[σ]        

I-inv : Γ ⊢s I ∶ Δ →
        ⊢ Γ ≈ Δ 
I-inv (s-I ⊢Γ) = ⊢≈-refl ⊢Γ
I-inv (s-conv ⊢I Δ≈) 
  with Γ≈ ← I-inv ⊢I = ⊢≈-trans Γ≈ Δ≈

,-inv : ∀ {i} → 
  Γ ⊢s (σ , t ∶ T ↙ i) ∶ Δ →
  ∃ λ Σ → Γ ⊢s σ ∶ Σ × Γ ⊢ t ∶[ i ] sub T σ × ⊢ (T ↙ i) ∷ Σ ≈ Δ 
,-inv (s-, ⊢σ ⊢T ⊢t) = _ , ⊢σ , ⊢t , ⊢≈-refl (⊢∷ (proj₁ (presup-tm ⊢T)) ⊢T)
,-inv (s-conv ⊢σ ≈Δ) 
  with ,-inv ⊢σ  
... | Δ , ⊢σ₁ , ⊢t , T∷Σ≈ = _ , ⊢σ₁ , ⊢t , ⊢≈-trans T∷Σ≈ ≈Δ

∘-inv : Γ ⊢s τ ∘ σ ∶ Δ →
        ∃ λ Ψ → Γ ⊢s σ ∶ Ψ × Ψ ⊢s τ ∶ Δ
∘-inv (s-∘ ⊢σ ⊢τ) = _ , ⊢σ , ⊢τ
∘-inv (s-conv ⊢τσ Δ≈) 
  with ∘-inv ⊢τσ 
... | Σ , ⊢σ , ⊢τ = _ , ⊢σ , s-conv ⊢τ Δ≈
 
wk-inv : ∀ {i} →
         (S ↙ i) ∷ Γ ⊢s wk ∶ Δ →
         ⊢ Γ ≈ Δ
wk-inv (s-wk (⊢∷ ⊢Γ _)) = ⊢≈-refl ⊢Γ
wk-inv (s-conv ⊢wk ≈Ψ) 
  with Γ≈Ψ ← wk-inv ⊢wk = ⊢≈-trans Γ≈Ψ ≈Ψ

wk-inv′ : Γ ⊢s wk ∶ Δ →
          ∃ λ Ψ → ∃₂ λ i T → ⊢ Γ ≈ (T ↙ i) ∷ Ψ × ⊢ Ψ ≈ Δ
wk-inv′ (s-wk ⊢S∷Γ@(⊢∷ ⊢Γ _)) = _ , _ , _ , ⊢≈-refl ⊢S∷Γ , ⊢≈-refl ⊢Γ
wk-inv′ (s-conv ⊢wk Δ≈) 
  with Ψ , i , T , Γ≈ , ≈Δ ← wk-inv′ ⊢wk = _ , _ , _ , Γ≈ , ⊢≈-trans ≈Δ Δ≈

rec-inv : ∀ {i j R} →
          Γ ⊢ rec (T ↙ i) s r t ∶[ j ] R →
          i ≡ j × 
          (N ↙ 0) ∷ Γ ⊢ T ∶[ 1 + i ] Se i × 
          Γ ⊢ s ∶[ i ] T [| ze ∶ N₀ ] × 
          (T ↙ i) L.∷ N₀ L.∷ Γ ⊢ r ∶[ i ] sub T ((wk ∘ wk) , su (v 1) ∶ N₀) × 
          Γ ⊢ t ∶[ 0 ] N ×
          Γ ⊢ R ≈ T [ I , t ∶ N₀ ] ∶[ 1 + i ] Se i
rec-inv (N-E ⊢T ⊢s ⊢r ⊢t) = refl , ⊢T , ⊢s , ⊢r , ⊢t , []-cong-Se‴ ⊢T (s-≈-refl (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t))
  where ⊢Γ = proj₁ (presup-tm ⊢t)
rec-inv (conv ⊢rect R≈) 
  with rec-inv ⊢rect
... | refl , ⊢T , ⊢s , ⊢r , ⊢t , ≈T[|t] = refl , ⊢T , ⊢s , ⊢r , ⊢t , ≈-trans (≈-sym R≈) ≈T[|t]

Π-inv-gen : ∀ {i j k} →
            Γ ⊢ Π (S ↙ j) (T ↙ k) ∶[ 1 + i ] T′ →
            Γ ⊢ T′ ≈ Se i ∶[ 2 + i ] Se (1 + i) →
            ---------------------------------
            i ≡ max j k  × Γ ⊢ S ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + k ] Se k
Π-inv-gen (Π-wf ⊢Π ⊢Π₁ i≡maxjk) T′≈ = i≡maxjk , ⊢Π , ⊢Π₁
Π-inv-gen (conv ⊢Π T″≈) T′≈ = Π-inv-gen ⊢Π (≈-trans T″≈ T′≈)

Π-inv : ∀ {i j k} →
          Γ ⊢ Π (S ↙ j) (T ↙ k) ∶[ 1 + i ] (Se i) →
          i ≡ max j k × Γ ⊢ S ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + k ] Se k
Π-inv ⊢Π
  with ⊢Γ ← proj₁ (presup-tm ⊢Π) = Π-inv-gen ⊢Π (≈-refl (Se-wf _ ⊢Γ))

Π-inv′ : ∀ {i j k R} →
         Γ ⊢ Π (S ↙ j) (T ↙ k) ∶[ i ] R →
         i ≡ 1 + max j k × Γ ⊢ R ≈ Se (max j k) ∶[ 2 + max j k ] Se (1 + max j k) × Γ ⊢ S ∶[ 1 + j ] Se j × (S ↙ j) ∷ Γ ⊢ T ∶[ 1 + k ] Se k
Π-inv′ (Π-wf ⊢S ⊢T refl) = refl , ≈-refl (Se-wf _ (proj₁ (presup-tm ⊢S))) , ⊢S , ⊢T
Π-inv′ (conv ⊢Π ≈R) 
  with Π-inv′ ⊢Π 
... | refl , ≈Se , ⊢S , ⊢T = refl , ≈-trans (≈-sym ≈R) ≈Se , ⊢S , ⊢T

Liftt-inv-gen : ∀ {i j k} →
                Γ ⊢ Liftt j (S ↙ k) ∶[ 1 + i ] T →
                Γ ⊢ T ≈ Se i ∶[ 2 + i ] Se (1 + i) →
                --------------------------------
                i ≡ j + k × Γ ⊢ S ∶[ 1 + k ] Se k
Liftt-inv-gen (Liftt-wf _ ⊢Liftt) T≈ = refl , ⊢Liftt
Liftt-inv-gen (conv ⊢Liftt T′≈) T≈ = Liftt-inv-gen ⊢Liftt (≈-trans T′≈ T≈)

Liftt-inv : ∀ {i j k} →
            Γ ⊢ Liftt j (S ↙ k) ∶[ 1 + i ] Se i →
            i ≡ j + k × Γ ⊢ S ∶[ 1 + k ] Se k
Liftt-inv ⊢Liftt  
  with ⊢Γ ← proj₁ (presup-tm ⊢Liftt) = Liftt-inv-gen ⊢Liftt (≈-refl (Se-wf _ ⊢Γ))

Liftt-inv′ : ∀ {i j k R} →
             Γ ⊢ Liftt j (S ↙ k) ∶[ i ] R →
             i ≡ 1 + j + k × Γ ⊢ S ∶[ 1 + k ] Se k × Γ ⊢ R ≈ Se (j + k) ∶[ 2 + j + k ] Se (1 + j + k) 
Liftt-inv′ (Liftt-wf _ ⊢T) = refl , ⊢T , ≈-refl (Se-wf _ (proj₁ (presup-tm ⊢T)))
Liftt-inv′ (conv ⊢LifttT ≈S) 
  with Liftt-inv′ ⊢LifttT    
... | refl , ⊢T , R≈ = refl , ⊢T , ≈-trans (≈-sym ≈S) R≈