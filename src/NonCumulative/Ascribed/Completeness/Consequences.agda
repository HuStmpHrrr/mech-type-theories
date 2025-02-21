{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Consequences of proving completeness theorem
module NonCumulative.Ascribed.Completeness.Consequences (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Ascribed.Statics.Full
open import NonCumulative.Ascribed.Statics.Properties
open import NonCumulative.Ascribed.Statics.Presup
open import NonCumulative.Ascribed.Statics.Refl
open import NonCumulative.Ascribed.Semantics.Readback
open import NonCumulative.Ascribed.Semantics.Properties.PER fext
open import NonCumulative.Ascribed.Completeness.LogRel
open import NonCumulative.Ascribed.Completeness.Fundamental fext

N≈⇒eq-lvl : ∀ {i} →
          Γ ⊢ N ≈ N ∶[ 1 + i ] Se i →
          i ≡ 0 
N≈⇒eq-lvl N≈ 
  with ⊨Γ , rel ← fundamental-t≈t′ N≈
    with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
      with rel ρ∈
... | record { ⟦T⟧ = .(U _) ; ⟦T′⟧ = .(U _) ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U 1+i≡1+i _ } 
    , record { ⟦t⟧ = .N ; ⟦t′⟧ = .N ; ↘⟦t⟧ = ⟦N⟧ ; ↘⟦t′⟧ = ⟦N⟧ ; t≈t′ = t≈t′ } 
    rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+i≡1+i)) 
    with N i≡0 ← t≈t′ = i≡0

⊢t∶N-lvl : ∀ {i} →
         Γ ⊢ t ∶[ i ] N →
         i ≡ 0
⊢t∶N-lvl ⊢t with presup-tm ⊢t
... | _ , ⊢N = N≈⇒eq-lvl (≈-refl ⊢N) 

⊢t≈s∶N-lvl : ∀ {i} →
            Γ ⊢ t ≈ s ∶[ i ] N →
            i ≡ 0
⊢t≈s∶N-lvl t≈s = ⊢t∶N-lvl (proj₁ (proj₂ (presup-≈ t≈s)))

-- If two Se's are equivalent, then they have the same universe level.
Se≈⇒eq-lvl : ∀ {i j k l} →
             Γ ⊢ Se i ≈ Se j ∶[ l ] Se k →
             --------------------------
             i ≡ j × k ≡ 1 + i × l ≡ 1 + k
Se≈⇒eq-lvl Se≈
  with ⊨Γ , rel ← fundamental-t≈t′ Se≈
    with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
      with rel ρ∈
...     | record { ⟦T⟧ = .(U _) ; ⟦T′⟧ = .(U _) ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = U 1+k≡1+k x₁ }
        , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = .(U _) ; ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Se⟧ _ ; t≈t′ = t≈t′ }
        rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+k≡1+k))
        with U k≡1+i i≡j ← t≈t′ = i≡j , k≡1+i , 1+k≡1+k

⊢T:Se-lvl : ∀ {i j} →
           Γ ⊢ T ∶[ i ] Se j →
           i ≡ 1 + j
⊢T:Se-lvl ⊢T with presup-tm ⊢T
... | _ , ⊢Se     
    with Se≈⇒eq-lvl (≈-refl ⊢Se) 
...    | _ , i≡1+j , _ = i≡1+j

⊢T≈S:Se-lvl : ∀ {i j} →
           Γ ⊢ T ≈ S ∶[ i ] Se j →
           i ≡ 1 + j
⊢T≈S:Se-lvl T≈S = ⊢T:Se-lvl (proj₁ (proj₂ (presup-≈ T≈S)))

InitEnvs-lookup : ∀ {x} →
                  x < len Γ →
                  InitEnvs Γ ρ →
                  ∃₂ λ i A → ∃ λ n → ρ x ≡ l′ i A n
InitEnvs-lookup {.(_ ↙ _) ∷ []} (s≤s z≤n) (s-∷ Γ~ρ x) = _ , _ , 0 , refl
InitEnvs-lookup {.(_ ↙ _) ∷ T′ ∷ Γ} {_} {ℕ.zero} (s≤s x<len) (s-∷ Γ~ρ x) = _ , _ , 1 + len Γ , refl
InitEnvs-lookup {.(_ ↙ _) ∷ T′ ∷ Γ} {_} {ℕ.suc x} (s≤s x<len) (s-∷ Γ~ρ x₁) = InitEnvs-lookup x<len Γ~ρ

not-Se-≈-v : ∀ {i x} →
             x < len Γ →
             Γ ⊢ Se i ≈ v x ∶[ 2 + i ] Se (1 + i) → ⊥
not-Se-≈-v {x = x} x<len Se≈ 
  with ⊨Γ , rel ← fundamental-t≈t′ Se≈ 
    with _ , ρ , _ , ρrel , ρ∈ ← InitEnvs-related ⊨Γ 
      with rel ρ∈ | InitEnvs-lookup x<len ρrel 
... | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U 2+i≡2+i _ } 
    , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
    | _ , _ , _ , eq 
    rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 2+i≡2+i)) | eq
    with t≈t′ 
...    | ()

not-Se-≈-N : ∀ {i} →
             Γ ⊢ Se i ≈ N ∶[ 2 + i ] Se (1 + i) → ⊥
not-Se-≈-N Se≈ 
   with ⊨Γ , rel ← fundamental-t≈t′ Se≈ 
      with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ 
          with rel ρ∈ 
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U 2+i≡2+i _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦N⟧ ; t≈t′ = t≈t′ } 
           rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 2+i≡2+i)) 
           with t≈t′ 
...           | ()

not-Se-≈-Π : ∀ {i j k} →
             Γ ⊢ Se i ≈ Π (S ↙ j) (T ↙ k) ∶[ 2 + i ] Se (1 + i) → ⊥
not-Se-≈-Π Se≈
  with ⊨Γ , rel ← fundamental-t≈t′ Se≈
     with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U 2+i≡2+i _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Π⟧ _ ; t≈t′ = t≈t′ } 
           rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 2+i≡2+i)) 
           with t≈t′ 
...           | ()

not-Se-≈-L : ∀ {i j k} →
             Γ ⊢ Se i ≈ Liftt j (T ↙ k) ∶[ 2 + i ] Se (1 + i) → ⊥
not-Se-≈-L Se≈
  with ⊨Γ , rel ← fundamental-t≈t′ Se≈
     with _ , _ , _ , _ , ρ∈ ← InitEnvs-related ⊨Γ
        with rel ρ∈
...        | record { ↘⟦T⟧ = ⟦Se⟧ _ ; T≈T′ = U 2+i≡2+i _ }
           , record { ↘⟦t⟧ = ⟦Se⟧ _ ; ↘⟦t′⟧ = ⟦Liftt⟧ _ ; t≈t′ = t≈t′ } 
           rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 2+i≡2+i)) 
           with t≈t′ 
...           | ()

not-Se-≈-bundle : ∀ {i k k′ k″ k‴ x} →
                  x < len Γ →
                  Γ ⊢ Se i ≈ T ∶[ 2 + i ] Se (1 + i) →
                  T ∈ v x ∷ N ∷ Π (S ↙ k) (S′ ↙ k′) ∷ Liftt k″ (S″ ↙ k‴) ∷ [] →
                  ⊥
not-Se-≈-bundle x<len Se≈ 0d = not-Se-≈-v x<len Se≈
not-Se-≈-bundle x<len Se≈ 1d = not-Se-≈-N Se≈
not-Se-≈-bundle x<len Se≈ 2d = not-Se-≈-Π Se≈
not-Se-≈-bundle x<len Se≈ 3d = not-Se-≈-L Se≈ 