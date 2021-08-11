{-# OPTIONS --without-K --safe #-}

module Unbox.StaticProps where

open import Lib
open import LibNonEmpty
open import Unbox.Statics

open import Data.Nat.Properties as ℕₚ
open import Data.List.Properties as Lₚ

mutual
  ≈-refl : Ψ ⊢ t ∶ T → Ψ ⊢ t ≈ t ∶ T
  ≈-refl (vlookup T∈Γ)  = v-≈ T∈Γ
  ≈-refl (⟶-I ⊢t)       = Λ-cong (≈-refl ⊢t)
  ≈-refl (⟶-E ⊢t ⊢s)    = $-cong (≈-refl ⊢t) (≈-refl ⊢s)
  ≈-refl (□-I ⊢t)       = box-cong (≈-refl ⊢t)
  ≈-refl (□-E Γs ⊢t eq) = unbox-cong Γs (≈-refl ⊢t) eq
  ≈-refl (t[σ] ⊢t ⊢σ)   = []-cong (≈-refl ⊢t) (s≈-refl ⊢σ)

  s≈-refl : Ψ ⊢s σ ∶ Ψ′ → Ψ ⊢s σ ≈ σ ∶ Ψ′
  s≈-refl S-I             = I-≈
  s≈-refl (S-p ⊢σ)        = p-cong (s≈-refl ⊢σ)
  s≈-refl (S-, ⊢σ ⊢t)     = ,-cong (s≈-refl ⊢σ) (≈-refl ⊢t)
  s≈-refl (S-； Γs ⊢σ eq) = ；-cong Γs (s≈-refl ⊢σ) eq
  s≈-refl (S-∘ ⊢σ ⊢δ)     = ∘-cong (s≈-refl ⊢σ) (s≈-refl ⊢δ)

L-I : ∀ n → L I n ≡ n
L-I zero    = refl
L-I (suc n) = refl

L-∘ : ∀ n σ δ → L (σ ∘ δ) n ≡ L δ (L σ n)
L-∘ 0 σ δ       = refl
L-∘ (suc n) σ δ = refl

L-p : ∀ n σ → L (p σ) n ≡ L σ n
L-p zero σ    = refl
L-p (suc n) σ = refl

L-, : ∀ n σ t → S-L (σ , t) n ≡ L σ n
L-, zero σ t    = refl
L-, (suc n) σ t = refl

L-+ : ∀ (σ : Substs) n m → L σ (n + m) ≡ L σ n + L (Tr σ n) m
L-+ I zero m                                       = refl
L-+ I (suc n) m
  rewrite L-I m                                    = refl
L-+ (p σ) zero m                                   = refl
L-+ (p σ) (suc n) m                                = L-+ σ (suc n) m
L-+ (σ , t) zero m                                 = refl
L-+ (σ , t) (suc n) m                              = L-+ σ (suc n) m
L-+ (σ ； k) zero m                                = refl
L-+ (σ ； k) (suc n) m
  rewrite L-+ σ n m                                = sym (+-assoc k (S-L σ n) (S-L (S-Tr σ n) m))
L-+ (σ ∘ δ) zero m                                 = refl
L-+ (σ ∘ δ) (suc n) m
  rewrite L-+ σ (suc n) m
        | L-+ δ (L σ (suc n)) (L (Tr σ (suc n)) m) = cong (L δ (L σ (suc n)) +_) (sym (L-∘ m (Tr σ (suc n)) (Tr δ (L σ (suc n)))))

Tr-I : ∀ n → Tr I n ≡ I
Tr-I zero    = refl
Tr-I (suc n) = refl

Tr-∘ : ∀ n σ δ → Tr (σ ∘ δ) n ≡ (Tr σ n ∘ Tr δ (L σ n))
Tr-∘ 0 σ δ       = refl
Tr-∘ (suc n) σ δ = refl

Tr-+ : ∀ (σ : Substs) n m → Tr σ (n + m) ≡ Tr (Tr σ n) m
Tr-+ I zero m                                = refl
Tr-+ I (suc n) m                             = sym (Tr-I m)
Tr-+ (p σ) zero m                            = refl
Tr-+ (p σ) (suc n) m                         = Tr-+ σ (suc n) m
Tr-+ (σ , x) zero m                          = refl
Tr-+ (σ , x) (suc n) m                       = Tr-+ σ (suc n) m
Tr-+ (σ ； x) zero m                         = refl
Tr-+ (σ ； x) (suc n) m                      = Tr-+ σ n m
Tr-+ (σ ∘ δ) zero m                          = refl
Tr-+ (σ ∘ δ) (suc n) m
 rewrite Tr-∘ m (Tr σ (suc n)) (Tr δ (L σ (suc n)))
       | Tr-+ σ (suc n) m
       | L-+ σ (suc n) m = cong (Tr (Tr σ (suc n)) m ∘_) (Tr-+ δ (L σ (suc n)) (L (Tr σ (suc n)) m))

L-<-len : ∀ n → Ψ ⊢s σ ∶ Ψ′ → n < len Ψ′ → L σ n < len Ψ
L-<-len n (S-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<
  rewrite L-∘ n δ σ           = L-<-len _ ⊢σ (L-<-len n ⊢δ n<)
L-<-len 0 ⊢σ n<               = s≤s z≤n
L-<-len (suc n) S-I n<        = n<
L-<-len (suc n) (S-p ⊢σ) n<   = L-<-len (suc n) ⊢σ n<
L-<-len (suc n) (S-, ⊢σ _) n< = L-<-len (suc n) ⊢σ n<
L-<-len (suc n) (S-； {Ψ} {_} {_} {m} Γs ⊢σ eq) (s≤s n<)
  rewrite length-++⁺′ Γs Ψ | eq
  with L-<-len n ⊢σ n<
...  | s≤s L<                 = s≤s (+-monoʳ-≤ m L<)

Tr-⊢s : ∀ n → Ψ ⊢s σ ∶ Ψ′ → n < len Ψ′ →
        ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × Ψ ≡ Φ₃ ++⁺ Φ₄ ×
          len Φ₁ ≡ n × len Φ₃ ≡ L σ n × Φ₄ ⊢s Tr σ n ∶ Φ₂
Tr-⊢s n (S-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<
  rewrite Tr-∘ n δ σ
  with Tr-⊢s n ⊢δ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
     , eq′ , eq , eql , eql′ , ⊢δ′
  with Tr-⊢s (L δ n) ⊢σ (L-<-len n ⊢δ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈
     , eq‴ , eq″ , eql″ , eql‴ , ⊢σ′
  rewrite ++⁺̂ˡ-cancel Φ₃ Φ₅
                      (trans (sym eq) eq‴)
                      (trans eql′ (sym eql″)) = Φ₁ , Φ₂ , Φ₇ , Φ₈
                                              , eq′ , eq″ , eql , trans eql‴ (sym (L-∘ n δ σ))
                                              , S-∘ ⊢σ′ ⊢δ′
Tr-⊢s zero ⊢σ n<                              = [] , _ , [] , _ , refl , refl , refl , refl , ⊢σ
Tr-⊢s (suc n) (S-I {Ψ}) n<
  with chop Ψ n<
...  | Φ₁ , Φ₂ , eq , eq′                     = Φ₁ , Φ₂ , Φ₁ , Φ₂ , eq , eq , eq′ , eq′ , S-I
Tr-⊢s (suc n) (S-p ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | (T ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
     , refl , eq , eql , eql′ , ⊢σ′           = Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq , eql , eql′ , ⊢σ′
Tr-⊢s (suc n) (S-, ⊢σ ⊢t) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄
     , refl , eq , eql , eql′ , ⊢σ′           = (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq , eql , eql′ , ⊢σ′
Tr-⊢s (suc n) (S-； Γs ⊢σ eq″) (s≤s n<)
  with Tr-⊢s n ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
     , eq′ , refl , eql , eql′ , ⊢σ′          = [] ∷ Φ₁ , Φ₂ , Γs ++ Φ₃ , Φ₄
                                              , cong ([] ∷_) (cong toList eq′) , sym (++-++⁺ Γs) , cong suc eql , trans (length-++ Γs) (cong₂ _+_ eq″ eql′)
                                              , ⊢σ′

Tr-⊢s′ : ∀ Γs → Ψ ⊢s σ ∶ Γs ++⁺ Ψ′ →
         ∃₂ λ Φ₁ Φ₂ → Ψ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ L σ (len Γs) × Φ₂ ⊢s Tr σ (len Γs) ∶ Ψ′
Tr-⊢s′ Γs ⊢σ with Tr-⊢s (len Γs) ⊢σ (length-<-++⁺ Γs)
... | Φ₁ , Φ₂ , Φ₃ , Φ₄
    , eq′ , eq , eql , eql′ , ⊢σ′
    rewrite ++⁺̂ˡ-cancel Γs Φ₁ eq′ (sym eql) = Φ₃ , Φ₄ , eq , eql′ , ⊢σ′


mutual
  presup : Ψ ⊢ t ≈ t′ ∶ T → Ψ ⊢ t ∶ T × Ψ ⊢ t′ ∶ T
  presup (v-≈ T∈Γ)                  = vlookup T∈Γ , vlookup T∈Γ
  presup (Λ-cong t≈t′)
    with presup t≈t′
  ...  | ⊢t , ⊢t′                   = ⟶-I ⊢t , ⟶-I ⊢t′
  presup ($-cong t≈t′ s≈s′)
    with presup t≈t′ | presup s≈s′
  ...  | ⊢t , ⊢t′    | ⊢s , ⊢s′     = ⟶-E ⊢t ⊢s , ⟶-E ⊢t′ ⊢s′
  presup (box-cong t≈t′)
    with presup t≈t′
  ...  | ⊢t , ⊢t′                   = □-I ⊢t , □-I ⊢t′
  presup (unbox-cong Γs t≈t′ eq)
    with presup t≈t′
  ...  | ⊢t , ⊢t′                   = □-E Γs ⊢t eq , □-E Γs ⊢t′ eq
  presup ([]-cong t≈t′ σ≈σ′)
    with presup t≈t′ | presup-s σ≈σ′
  ...  | ⊢t , ⊢t′    | ⊢σ , ⊢σ′     = t[σ] ⊢t ⊢σ , t[σ] ⊢t′ ⊢σ′
  presup (v-ze ⊢σ ⊢t)               = t[σ] (vlookup here) (S-, ⊢σ ⊢t) , ⊢t
  presup (v-su ⊢σ ⊢t T∈Γ)           = t[σ] (vlookup (there T∈Γ)) (S-, ⊢σ ⊢t) , t[σ] (vlookup T∈Γ) ⊢σ
  presup (Λ-[] ⊢σ ⊢t)               = t[σ] (⟶-I ⊢t) ⊢σ , ⟶-I (t[σ] ⊢t (⊢q ⊢σ _))
  presup ($-[] ⊢σ ⊢t ⊢s)            = t[σ] (⟶-E ⊢t ⊢s) ⊢σ , (⟶-E (t[σ] ⊢t ⊢σ) (t[σ] ⊢s ⊢σ))
  presup (box-[] ⊢σ ⊢t)             = t[σ] (□-I ⊢t) ⊢σ , □-I (t[σ] ⊢t (S-； ([] ∷ []) ⊢σ refl))
  presup (unbox-[] Γs ⊢σ ⊢t refl)
    with Tr-⊢s′ Γs ⊢σ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢σ′ = (t[σ] (□-E Γs ⊢t refl) ⊢σ) , □-E Φ₁ (t[σ] ⊢t ⊢σ′) eql
  presup (⟶-β ⊢t ⊢s)                = ⟶-E (⟶-I ⊢t) ⊢s , t[σ] ⊢t (S-, S-I ⊢s)
  presup (□-β Γs ⊢t eq)             = □-E Γs (□-I ⊢t) eq , t[σ] ⊢t (S-； Γs S-I eq)
  presup (⟶-η ⊢t)                   = ⊢t , ⟶-I (⟶-E (t[σ] ⊢t (S-p S-I)) (vlookup here))
  presup (□-η ⊢t)                   = ⊢t , (□-I (□-E ([] ∷ []) ⊢t refl))
  presup (≈-sym t′≈t)
    with presup t′≈t
  ...  | ⊢t′ , ⊢t                   = ⊢t , ⊢t′
  presup (≈-trans t≈t″ t″≈t′)
    with presup t≈t″ | presup t″≈t′
  ...  | ⊢t , _      | _ , ⊢t′      = ⊢t , ⊢t′

  presup-s : Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → Ψ ⊢s σ ∶ Ψ′ × Ψ ⊢s σ′ ∶ Ψ′
  presup-s I-≈                      = S-I , S-I
  presup-s (p-cong σ≈σ′)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = S-p ⊢σ , S-p ⊢σ′
  presup-s (,-cong σ≈σ′ t≈t′)
    with presup-s σ≈σ′ | presup t≈t′
  ...  | ⊢σ , ⊢σ′      | ⊢t , ⊢t′   = S-, ⊢σ ⊢t , S-, ⊢σ′ ⊢t′
  presup-s (；-cong Γs σ≈σ′ eq)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = S-； Γs ⊢σ eq , S-； Γs ⊢σ′ eq
  presup-s (∘-cong σ≈σ′ δ≈δ′)
    with presup-s σ≈σ′ | presup-s δ≈δ′
  ...  | ⊢σ , ⊢σ′      | ⊢δ , ⊢δ′   = S-∘ ⊢σ ⊢δ , S-∘ ⊢σ′ ⊢δ′
  presup-s (∘-I ⊢σ)                 = S-∘ S-I ⊢σ , ⊢σ
  presup-s (I-∘ ⊢σ)                 = S-∘ ⊢σ S-I , ⊢σ
  presup-s (∘-assoc ⊢σ ⊢σ′ ⊢σ″)     = S-∘ ⊢σ (S-∘ ⊢σ′ ⊢σ″) , S-∘ (S-∘ ⊢σ ⊢σ′) ⊢σ″
  presup-s (,-∘ ⊢σ ⊢t ⊢δ)           = S-∘ ⊢δ (S-, ⊢σ ⊢t) , S-, (S-∘ ⊢δ ⊢σ) (t[σ] ⊢t ⊢δ)
  presup-s (p-∘ ⊢σ ⊢δ)              = S-∘ ⊢δ (S-p ⊢σ) , S-p (S-∘ ⊢δ ⊢σ)
  presup-s (；-∘ Γs ⊢σ ⊢δ refl)
    with Tr-⊢s′ Γs ⊢δ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢δ′ = S-∘ ⊢δ (S-； Γs ⊢σ refl) , S-； Φ₁ (S-∘ ⊢δ′ ⊢σ) eql
  presup-s (p-, ⊢σ ⊢t)              = S-p (S-, ⊢σ ⊢t) , ⊢σ
  presup-s (,-ext ⊢σ)               = ⊢σ , S-, (S-p ⊢σ) (t[σ] (vlookup here) ⊢σ)
  presup-s (；-ext ⊢σ)
    with Tr-⊢s′ ([] ∷ []) ⊢σ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢σ′ = ⊢σ , S-； Φ₁ ⊢σ′ eql


L-resp-≈ : ∀ n → Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → n < len Ψ′ → L σ n ≡ L σ′ n
L-resp-≈ n I-≈ n<                             = refl
L-resp-≈ n (p-cong {_} {σ} {σ′} σ≈σ′) n<
  rewrite L-p n σ | L-p n σ′                  = L-resp-≈ n σ≈σ′ n<
L-resp-≈ n (,-cong {_} {σ} {σ′} {_} {_} {t} {t′} σ≈σ′ t≈t′) n<
  rewrite L-, n σ t | L-, n σ′ t′             = L-resp-≈ n σ≈σ′ n<
L-resp-≈ 0 (；-cong Γs σ≈σ′ eq) n<            = refl
L-resp-≈ (suc n) (；-cong {_} {_} {_} {_} {m} Γs σ≈σ′ eq) (s≤s n<)
                                              = cong (m +_) (L-resp-≈ n σ≈σ′ n<)
L-resp-≈ n (∘-cong {_} {δ} {δ′} {_} {σ} {σ′} δ≈δ′ σ≈σ′) n<
  rewrite L-∘ n σ δ | L-∘ n σ′ δ′
        | L-resp-≈ n σ≈σ′ n<
  with presup-s σ≈σ′
...  | _ , ⊢σ′                                = L-resp-≈ (L σ′ n) δ≈δ′ (L-<-len n ⊢σ′ n<)
L-resp-≈ n (∘-I {_} {σ} ⊢σ) n<
  rewrite L-∘ n σ I | L-I (L σ n)             = refl
L-resp-≈ n (I-∘ {_} {σ} ⊢σ) n<
  rewrite L-∘ n I σ | L-I n                   = refl
L-resp-≈ n (∘-assoc {_} {σ} {_} {σ′} {_} {σ″} ⊢σ ⊢σ′ ⊢σ″) n<
  rewrite L-∘ n (σ″ ∘ σ′) σ | L-∘ n σ″ σ′
        | L-∘ n σ″ (σ′ ∘ σ)                   = sym (L-∘ (L σ″ n) σ′ σ)
L-resp-≈ n (,-∘ {_} {σ} {_} {_} {t} {_} {_} {δ} ⊢σ ⊢t ⊢δ) n<
  rewrite L-∘ n (σ , t) δ | L-, n σ t
        | L-, n (σ ∘ δ) (t [ δ ])             = sym (L-∘ n σ δ)
L-resp-≈ n (p-∘ {_} {σ} {_} {_} {_} {_} {δ} ⊢σ ⊢δ) n<
  rewrite L-∘ n (p σ) δ | L-p n σ
        | L-p n (σ ∘ δ)                       = sym (L-∘ n σ δ)
L-resp-≈ 0 (；-∘ Γs ⊢σ ⊢δ eq) n<              = refl
L-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {m} Γs ⊢σ ⊢δ eq) n<
  rewrite L-∘ n σ (Tr δ m)                    = L-+ δ m (L σ n)
L-resp-≈ n (p-, {_} {σ} {_} {_} {t} ⊢σ ⊢t) n< = trans (L-p n (σ , t)) (L-, n σ t)
L-resp-≈ n (,-ext {_} {σ} ⊢σ) n<              = sym (trans (L-, n (p σ) (v 0 [ σ ])) (L-p n σ))
L-resp-≈ zero (；-ext ⊢σ) n<                  = refl
L-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ) n<       = L-+ σ 1 n


Tr-resp-≈ : ∀ n → Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → n < len Ψ′ →
            ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × Ψ ≡ Φ₃ ++⁺ Φ₄ ×
              len Φ₁ ≡ n × len Φ₃ ≡ L σ n × Φ₄ ⊢s Tr σ n ≈ Tr σ′ n ∶ Φ₂
Tr-resp-≈ n (I-≈ {Ψ}) n<
  with chop Ψ n<
...  | Φ₁ , Φ₂ , eq , eql
  rewrite L-I n | Tr-I n                                           = Φ₁ , Φ₂ , Φ₁ , Φ₂ , eq , eq , eql , eql , I-≈
Tr-resp-≈ n (∘-assoc {_} {σ} {_} {σ′} {_} {σ″} ⊢σ ⊢σ′ ⊢σ″) n<
  rewrite Tr-∘ n (σ″ ∘ σ′) σ | Tr-∘ n σ″ (σ′ ∘ σ)
        | Tr-∘ n σ″ σ′ | Tr-∘ (L σ″ n) σ′ σ
        | L-∘ n σ″ σ′
  with Tr-⊢s n ⊢σ″ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ″₁
  with Tr-⊢s (L σ″ n) ⊢σ′ (L-<-len n ⊢σ″ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , ⊢σ′₁
  with Tr-⊢s (L σ′ (L σ″ n)) ⊢σ (L-<-len (L σ″ n) ⊢σ′ (L-<-len n ⊢σ″ n<))
...  | Φ₉ , Φ₁₀ , Φ₁₁ , Φ₁₂ , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ₁
  rewrite L-∘ n (σ″ ∘ σ′) σ | L-∘ n σ″ σ′
        | ++⁺̂ˡ-cancel Φ₃ Φ₅ (trans (sym eq′) eq″) (trans eql′ (sym eql″))
        | ++⁺̂ˡ-cancel Φ₇ Φ₉
                      (trans (sym eq‴) eq₁)
                      (trans eql‴ (sym eql₁))                      = Φ₁ , Φ₂ , Φ₁₁ , Φ₁₂ , eq , eq₂ , eql , eql₂ , ∘-assoc ⊢σ₁ ⊢σ′₁ ⊢σ″₁
Tr-resp-≈ {Ψ} {_} {_} {Ψ′} 0 σ≈σ′ n<                               = [] , Ψ′ , [] , Ψ , refl , refl , refl , refl , σ≈σ′
Tr-resp-≈ (suc n) (p-cong σ≈σ′) n<
  with Tr-resp-≈ (suc n) σ≈σ′ n<
... | (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , σ≈σ″ = Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , σ≈σ″
Tr-resp-≈ (suc n) (,-cong σ≈σ′ t≈t′) n<
  with Tr-resp-≈ (suc n) σ≈σ′ n<
... | Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , σ≈σ″       = (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , σ≈σ″
Tr-resp-≈ (suc n) (；-cong Γs σ≈σ′ e) (s≤s n<)
  with Tr-resp-≈ n σ≈σ′ n<
... | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″             = [] ∷ Φ₁ , Φ₂ , Γs ++ Φ₃ , Φ₄
                                                                   , cong ([] ∷_) (cong toList eq) , trans (cong (Γs ++⁺_) eq′) (sym (++-++⁺ Γs))
                                                                   , cong suc eql , trans (length-++ Γs) (cong₂ _+_ e eql′) , σ≈σ″
Tr-resp-≈ (suc n) (∘-cong {σ = σ} δ≈δ′ σ≈σ′) n<
  with Tr-resp-≈ (suc n) σ≈σ′ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″
  with Tr-resp-≈ (L σ (suc n)) δ≈δ′ (L-<-len (suc n) (proj₁ (presup-s σ≈σ′)) n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , δ≈δ″
  rewrite ++⁺̂ˡ-cancel Φ₃ Φ₅ (trans (sym eq′) eq″) (trans eql′ (sym eql″))
        | L-resp-≈ (suc n) σ≈σ′ n<                                 = Φ₁ , Φ₂ , Φ₇ , Φ₈ , eq , eq‴ , eql , eql‴ , ∘-cong δ≈δ″ σ≈σ″
Tr-resp-≈ (suc n) (∘-I {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  rewrite L-I (L σ (suc n)) | Tr-I (L σ (suc n))                   = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ∘-I ⊢σ′
Tr-resp-≈ (suc n) (I-∘ {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , I-∘ ⊢σ′
Tr-resp-≈ (suc n) (,-∘ {_} {σ} {δ = δ} ⊢σ ⊢t ⊢δ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , ⊢σ′
  with Tr-⊢s (L σ (suc n)) ⊢δ (L-<-len (suc n) ⊢σ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , ⊢δ′
  rewrite ++⁺̂ˡ-cancel Φ₃ Φ₅
                       (trans (sym eq′) eq″)
                       (trans eql′ (sym eql″))                     = (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₇ , Φ₈ , refl , eq‴ , eql , eql‴ , ∘-cong (s≈-refl ⊢δ′) (s≈-refl ⊢σ′)
Tr-resp-≈ (suc n) (p-∘ {_} {σ} ⊢σ ⊢δ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , ⊢σ′
  with Tr-⊢s (L σ (suc n)) ⊢δ (L-<-len (suc n) ⊢σ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , ⊢δ′
  rewrite ++⁺̂ˡ-cancel Φ₃ Φ₅
                       (trans (sym eq′) eq″)
                       (trans eql′ (sym eql″))                     = Γ ∷ Φ₁ , Φ₂ , Φ₇ , Φ₈ , refl , eq‴ , eql , eql‴ , ∘-cong (s≈-refl ⊢δ′) (s≈-refl ⊢σ′)
Tr-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {m} Γs ⊢σ ⊢δ refl) (s≤s n<)
  rewrite Tr-∘ n σ (Tr δ m) | Tr-+ δ m (L σ n)
  with Tr-⊢s n ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  with Tr-⊢s′ Γs ⊢δ
...  | Φ₅ , Φ₆ , eq″ , eql″ , ⊢δ′
  with Tr-⊢s (L σ n) ⊢δ′ (L-<-len n ⊢σ n<)
...  | Φ₇ , Φ₈ , Φ₉ , Φ₀ , eq‴ , refl , eql‴ , eql⁗ , ⊢δ″
  rewrite ++⁺̂ˡ-cancel Φ₃ Φ₇
                      (trans (sym eq′) eq‴)
                      (trans eql′ (sym eql‴))                      = [] ∷ Φ₁ , Φ₂ , Φ₅ ++ Φ₉ , Φ₀
                                                                   , cong ([] ∷_) (cong toList eq) , trans eq″ (sym (++-++⁺ Φ₅))
                                                                   , cong suc eql , trans (length-++ Φ₅) (trans (cong₂ _+_ eql″ eql⁗) (sym (L-+ δ (len Γs) (L σ n))))
                                                                   , ∘-cong (s≈-refl ⊢δ″) (s≈-refl ⊢σ′)
Tr-resp-≈ (suc n) (p-, ⊢σ ⊢t) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , s≈-refl ⊢σ′
Tr-resp-≈ (suc n) (,-ext ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , s≈-refl ⊢σ′
Tr-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  rewrite sym (Tr-+ σ 1 n)                                         = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , s≈-refl ⊢σ′


Tr-resp-≈′ : ∀ Γs → Ψ ⊢s σ ≈ σ′ ∶ Γs ++⁺ Ψ′ →
             ∃₂ λ Φ₁ Φ₂ → Ψ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ L σ (len Γs) × Φ₂ ⊢s Tr σ (len Γs) ≈ Tr σ′ (len Γs) ∶ Ψ′
Tr-resp-≈′ Γs σ≈σ′
  with Tr-resp-≈ (len Γs) σ≈σ′ (length-<-++⁺ Γs)
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″
  rewrite ++⁺̂ˡ-cancel Γs Φ₁ eq (sym eql) = Φ₃ , Φ₄ , eq′ , eql′ , σ≈σ″
