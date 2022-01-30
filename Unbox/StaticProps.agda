{-# OPTIONS --without-K --safe #-}

module Unbox.StaticProps where

open import Lib
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
  s≈-refl S-p             = p-≈
  s≈-refl (S-, ⊢σ ⊢t)     = ,-cong (s≈-refl ⊢σ) (≈-refl ⊢t)
  s≈-refl (S-； Γs ⊢σ eq) = ；-cong Γs (s≈-refl ⊢σ) eq
  s≈-refl (S-∘ ⊢σ ⊢δ)     = ∘-cong (s≈-refl ⊢σ) (s≈-refl ⊢δ)

⊢q∘I, : Ψ ⊢s σ ∶ Δ ∷ Δs → Ψ ⊢ t ∶ T → Ψ ⊢s q σ ∘ (I , t) ≈ σ , t ∶ (T ∷ Δ) ∷ Δs
⊢q∘I, ⊢σ ⊢t = s-≈-trans (,-∘ (S-∘ S-p ⊢σ) (vlookup here) (S-, S-I ⊢t))
                        (,-cong (s-≈-trans (∘-assoc (S-, S-I ⊢t) S-p ⊢σ)
                                (s-≈-trans (∘-cong (p-, S-I ⊢t) (s≈-refl ⊢σ))
                                           (∘-I ⊢σ)))
                                (v-ze S-I ⊢t))

O-I : ∀ n → O I n ≡ n
O-I zero    = refl
O-I (suc n) = refl

O-∘ : ∀ n σ δ → O (σ ∘ δ) n ≡ O δ (O σ n)
O-∘ 0 σ δ       = refl
O-∘ (suc n) σ δ = refl

O-p : ∀ n → O p n ≡ n
O-p zero    = refl
O-p (suc n) = refl

O-, : ∀ n σ t → S-O (σ , t) n ≡ O σ n
O-, zero σ t    = refl
O-, (suc n) σ t = refl

O-+ : ∀ (σ : Substs) n m → O σ (n + m) ≡ O σ n + O (Tr σ n) m
O-+ I zero m                                       = refl
O-+ I (suc n) m
  rewrite O-I m                                    = refl
O-+ p zero m                                       = refl
O-+ p (suc n) m
  rewrite O-I m                                    = refl
O-+ (σ , t) zero m                                 = refl
O-+ (σ , t) (suc n) m                              = O-+ σ (suc n) m
O-+ (σ ； k) zero m                                = refl
O-+ (σ ； k) (suc n) m
  rewrite O-+ σ n m                                = sym (+-assoc k (O σ n) (O (S-Tr σ n) m))
O-+ (σ ∘ δ) zero m                                 = refl
O-+ (σ ∘ δ) (suc n) m
  rewrite O-+ σ (suc n) m
        | O-+ δ (O σ (suc n)) (O (Tr σ (suc n)) m) = cong (O δ (O σ (suc n)) +_) (sym (O-∘ m (Tr σ (suc n)) (Tr δ (O σ (suc n)))))

Tr-I : ∀ n → Tr I n ≡ I
Tr-I zero    = refl
Tr-I (suc n) = refl

Tr-∘ : ∀ n σ δ → Tr (σ ∘ δ) n ≡ (Tr σ n ∘ Tr δ (O σ n))
Tr-∘ 0 σ δ       = refl
Tr-∘ (suc n) σ δ = refl

Tr-+ : ∀ (σ : Substs) n m → Tr σ (n + m) ≡ Tr (Tr σ n) m
Tr-+ I zero m            = refl
Tr-+ I (suc n) m         = sym (Tr-I m)
Tr-+ p zero m            = refl
Tr-+ p (suc n) m
  rewrite Tr-I m         = refl
Tr-+ (σ , x) zero m      = refl
Tr-+ (σ , x) (suc n) m   = Tr-+ σ (suc n) m
Tr-+ (σ ； x) zero m     = refl
Tr-+ (σ ； x) (suc n) m  = Tr-+ σ n m
Tr-+ (σ ∘ δ) zero m      = refl
Tr-+ (σ ∘ δ) (suc n) m
 rewrite Tr-∘ m (Tr σ (suc n)) (Tr δ (O σ (suc n)))
       | Tr-+ σ (suc n) m
       | O-+ σ (suc n) m = cong (Tr (Tr σ (suc n)) m ∘_) (Tr-+ δ (O σ (suc n)) (O (Tr σ (suc n)) m))

O-<-len : ∀ n → Ψ ⊢s σ ∶ Ψ′ → n < len Ψ′ → O σ n < len Ψ
O-<-len n (S-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<
  rewrite O-∘ n δ σ           = O-<-len _ ⊢σ (O-<-len n ⊢δ n<)
O-<-len 0 ⊢σ n<               = s≤s z≤n
O-<-len (suc n) S-I n<        = n<
O-<-len (suc n) S-p n<        = n<
O-<-len (suc n) (S-, ⊢σ _) n< = O-<-len (suc n) ⊢σ n<
O-<-len (suc n) (S-； {Ψ} {_} {_} {m} Γs ⊢σ eq) (s≤s n<)
  rewrite length-++⁺-tail Γs Ψ | eq
  with O-<-len n ⊢σ n<
...  | s≤s L<                 = s≤s (+-monoʳ-≤ m L<)

Tr-⊢s : ∀ n → Ψ ⊢s σ ∶ Ψ′ → n < len Ψ′ →
        ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × Ψ ≡ Φ₃ ++⁺ Φ₄ ×
          len Φ₁ ≡ n × len Φ₃ ≡ O σ n × Φ₄ ⊢s Tr σ n ∶ Φ₂
Tr-⊢s n (S-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<
  rewrite Tr-∘ n δ σ
  with Tr-⊢s n ⊢δ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄
     , eq′ , eq , eql , eql′ , ⊢δ′
  with Tr-⊢s (O δ n) ⊢σ (O-<-len n ⊢δ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈
     , eq‴ , eq″ , eql″ , eql‴ , ⊢σ′
  rewrite ++⁺-cancelˡ′ Φ₃ Φ₅
                      (trans (sym eq) eq‴)
                      (trans eql′ (sym eql″)) = Φ₁ , Φ₂ , Φ₇ , Φ₈
                                              , eq′ , eq″ , eql , trans eql‴ (sym (O-∘ n δ σ))
                                              , S-∘ ⊢σ′ ⊢δ′
Tr-⊢s zero ⊢σ n<                              = [] , _ , [] , _ , refl , refl , refl , refl , ⊢σ
Tr-⊢s (suc n) (S-I {Ψ}) n<
  with chop Ψ n<
...  | Φ₁ , Φ₂ , eq , eq′                     = Φ₁ , Φ₂ , Φ₁ , Φ₂ , eq , eq , eq′ , eq′ , S-I
Tr-⊢s (suc n) (S-p {T} {Γ} {Γs}) n<
  with chop (Γ ∷ Γs) n<
...  | Γ′ ∷ Φ₁ , Φ₂ , refl , eq′              = Γ′ ∷ Φ₁ , Φ₂ , (T ∷ Γ′) ∷ Φ₁ , Φ₂ , refl , refl , eq′ , eq′ , S-I
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
         ∃₂ λ Φ₁ Φ₂ → Ψ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ O σ (len Γs) × Φ₂ ⊢s Tr σ (len Γs) ∶ Ψ′
Tr-⊢s′ Γs ⊢σ with Tr-⊢s (len Γs) ⊢σ (length-<-++⁺ Γs)
... | Φ₁ , Φ₂ , Φ₃ , Φ₄
    , eq′ , eq , eql , eql′ , ⊢σ′
    rewrite ++⁺-cancelˡ′ Γs Φ₁ eq′ (sym eql) = Φ₃ , Φ₄ , eq , eql′ , ⊢σ′


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
  presup (Λ-[] ⊢σ ⊢t)               = t[σ] (⟶-I ⊢t) ⊢σ , ⟶-I (t[σ] ⊢t (⊢q ⊢σ _))
  presup ($-[] ⊢σ ⊢t ⊢s)            = t[σ] (⟶-E ⊢t ⊢s) ⊢σ , (⟶-E (t[σ] ⊢t ⊢σ) (t[σ] ⊢s ⊢σ))
  presup (box-[] ⊢σ ⊢t)             = t[σ] (□-I ⊢t) ⊢σ , □-I (t[σ] ⊢t (S-； ([] ∷ []) ⊢σ refl))
  presup (unbox-[] Γs ⊢σ ⊢t refl)
    with Tr-⊢s′ Γs ⊢σ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢σ′ = (t[σ] (□-E Γs ⊢t refl) ⊢σ) , □-E Φ₁ (t[σ] ⊢t ⊢σ′) eql
  presup (⟶-β ⊢t ⊢s)                = ⟶-E (⟶-I ⊢t) ⊢s , t[σ] ⊢t (S-, S-I ⊢s)
  presup (□-β Γs ⊢t eq)             = □-E Γs (□-I ⊢t) eq , t[σ] ⊢t (S-； Γs S-I eq)
  presup (⟶-η ⊢t)                   = ⊢t , ⟶-I (⟶-E (t[σ] ⊢t S-p) (vlookup here))
  presup (□-η ⊢t)                   = ⊢t , (□-I (□-E ([] ∷ []) ⊢t refl))
  presup ([I] ⊢t)                   = t[σ] ⊢t S-I , ⊢t
  presup ([∘] ⊢σ ⊢σ′ ⊢t)            = t[σ] ⊢t (S-∘ ⊢σ ⊢σ′) , t[σ] (t[σ] ⊢t ⊢σ′) ⊢σ
  presup (v-ze ⊢σ ⊢t)               = t[σ] (vlookup here) (S-, ⊢σ ⊢t) , ⊢t
  presup (v-su ⊢σ ⊢t T∈Γ)           = t[σ] (vlookup (there T∈Γ)) (S-, ⊢σ ⊢t) , t[σ] (vlookup T∈Γ) ⊢σ
  presup ([p] T∈Γ)                  = t[σ] (vlookup T∈Γ) S-p , vlookup (there T∈Γ)
  presup (≈-sym t′≈t)
    with presup t′≈t
  ...  | ⊢t′ , ⊢t                   = ⊢t , ⊢t′
  presup (≈-trans t≈t″ t″≈t′)
    with presup t≈t″ | presup t″≈t′
  ...  | ⊢t , _      | _ , ⊢t′      = ⊢t , ⊢t′

  presup-s : Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → Ψ ⊢s σ ∶ Ψ′ × Ψ ⊢s σ′ ∶ Ψ′
  presup-s I-≈                      = S-I , S-I
  presup-s p-≈                      = S-p , S-p
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
  presup-s (；-∘ Γs ⊢σ ⊢δ refl)
    with Tr-⊢s′ Γs ⊢δ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢δ′ = S-∘ ⊢δ (S-； Γs ⊢σ refl) , S-； Φ₁ (S-∘ ⊢δ′ ⊢σ) eql
  presup-s (p-, ⊢σ ⊢t)              = S-∘ (S-, ⊢σ ⊢t) S-p , ⊢σ
  presup-s (,-ext ⊢σ)               = ⊢σ , S-, (S-∘ ⊢σ S-p) (t[σ] (vlookup here) ⊢σ)
  presup-s (；-ext ⊢σ)
    with Tr-⊢s′ ([] ∷ []) ⊢σ
  ...  | Φ₁ , Φ₂ , refl , eql , ⊢σ′ = ⊢σ , S-； Φ₁ ⊢σ′ eql
  presup-s (s-≈-sym σ≈σ′)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = ⊢σ′ , ⊢σ
  presup-s (s-≈-trans σ≈σ′ σ′≈σ″)
    with presup-s σ≈σ′ | presup-s σ′≈σ″
  ...  | ⊢σ , _ | _ , ⊢σ″           = ⊢σ , ⊢σ″

O-resp-≈ : ∀ n → Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → O σ n ≡ O σ′ n
O-resp-≈ n I-≈                                = refl
O-resp-≈ n p-≈                                = refl
O-resp-≈ n (,-cong {_} {σ} {σ′} {_} {_} {t} {t′} σ≈σ′ t≈t′)
  rewrite O-, n σ t | O-, n σ′ t′             = O-resp-≈ n σ≈σ′
O-resp-≈ n (s-≈-sym σ≈σ′)                     = sym (O-resp-≈ n σ≈σ′)
O-resp-≈ n (s-≈-trans σ≈σ′ σ′≈σ″)             = trans (O-resp-≈ n σ≈σ′) (O-resp-≈ n σ′≈σ″)
O-resp-≈ 0 (；-cong Γs σ≈σ′ eq)               = refl
O-resp-≈ (suc n) (；-cong {_} {_} {_} {_} {m} Γs σ≈σ′ eq)
                                              = cong (m +_) (O-resp-≈ n σ≈σ′)
O-resp-≈ n (∘-cong {_} {δ} {δ′} {_} {σ} {σ′} δ≈δ′ σ≈σ′)
  rewrite O-∘ n σ δ | O-∘ n σ′ δ′
        | O-resp-≈ n σ≈σ′
  with presup-s σ≈σ′
...  | _ , ⊢σ′                                = O-resp-≈ (O σ′ n) δ≈δ′
O-resp-≈ n (∘-I {_} {σ} ⊢σ)
  rewrite O-∘ n σ I | O-I (O σ n)             = refl
O-resp-≈ n (I-∘ {_} {σ} ⊢σ)
  rewrite O-∘ n I σ | O-I n                   = refl
O-resp-≈ n (∘-assoc {_} {σ} {_} {σ′} {_} {σ″} ⊢σ ⊢σ′ ⊢σ″)
  rewrite O-∘ n (σ″ ∘ σ′) σ | O-∘ n σ″ σ′
        | O-∘ n σ″ (σ′ ∘ σ)                   = sym (O-∘ (O σ″ n) σ′ σ)
O-resp-≈ n (,-∘ {_} {σ} {_} {_} {t} {_} {_} {δ} ⊢σ ⊢t ⊢δ)
  rewrite O-∘ n (σ , t) δ | O-, n σ t
        | O-, n (σ ∘ δ) (t [ δ ])             = sym (O-∘ n σ δ)
O-resp-≈ 0 (；-∘ Γs ⊢σ ⊢δ eq)                 = refl
O-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {m} Γs ⊢σ ⊢δ eq)
  rewrite O-∘ n σ (Tr δ m)                    = O-+ δ m (O σ n)
O-resp-≈ n (p-, {_} {σ} {_} {_} {t} ⊢σ ⊢t)    = trans (O-∘ n p (σ , t)) (trans (O-, (O p n) σ t) (cong (O σ) (O-p n)))
O-resp-≈ n (,-ext {_} {σ} ⊢σ)                 = sym (trans (O-, n (p ∘ σ) (v 0 [ σ ])) (trans (O-∘ n p σ) (cong (O σ) (O-p n))))
O-resp-≈ zero (；-ext ⊢σ)                     = refl
O-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ)          = O-+ σ 1 n


Tr-resp-≈ : ∀ n → Ψ ⊢s σ ≈ σ′ ∶ Ψ′ → n < len Ψ′ →
            ∃₂ λ Φ₁ Φ₂ → ∃₂ λ Φ₃ Φ₄ → Ψ′ ≡ Φ₁ ++⁺ Φ₂ × Ψ ≡ Φ₃ ++⁺ Φ₄ ×
              len Φ₁ ≡ n × len Φ₃ ≡ O σ n × Φ₄ ⊢s Tr σ n ≈ Tr σ′ n ∶ Φ₂
Tr-resp-≈ n (I-≈ {Ψ}) n<
  with chop Ψ n<
...  | Φ₁ , Φ₂ , eq , eql
  rewrite O-I n | Tr-I n                                           = Φ₁ , Φ₂ , Φ₁ , Φ₂ , eq , eq , eql , eql , I-≈
Tr-resp-≈ n (∘-assoc {_} {σ} {_} {σ′} {_} {σ″} ⊢σ ⊢σ′ ⊢σ″) n<
  rewrite Tr-∘ n (σ″ ∘ σ′) σ | Tr-∘ n σ″ (σ′ ∘ σ)
        | Tr-∘ n σ″ σ′ | Tr-∘ (O σ″ n) σ′ σ
        | O-∘ n σ″ σ′
  with Tr-⊢s n ⊢σ″ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ″₁
  with Tr-⊢s (O σ″ n) ⊢σ′ (O-<-len n ⊢σ″ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , ⊢σ′₁
  with Tr-⊢s (O σ′ (O σ″ n)) ⊢σ (O-<-len (O σ″ n) ⊢σ′ (O-<-len n ⊢σ″ n<))
...  | Φ₉ , Φ₁₀ , Φ₁₁ , Φ₁₂ , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ₁
  rewrite O-∘ n (σ″ ∘ σ′) σ | O-∘ n σ″ σ′
        | ++⁺-cancelˡ′ Φ₃ Φ₅ (trans (sym eq′) eq″) (trans eql′ (sym eql″))
        | ++⁺-cancelˡ′ Φ₇ Φ₉
                      (trans (sym eq‴) eq₁)
                      (trans eql‴ (sym eql₁))                      = Φ₁ , Φ₂ , Φ₁₁ , Φ₁₂ , eq , eq₂ , eql , eql₂ , ∘-assoc ⊢σ₁ ⊢σ′₁ ⊢σ″₁
Tr-resp-≈ {Ψ} {_} {_} {Ψ′} 0 σ≈σ′ n<                               = [] , Ψ′ , [] , Ψ , refl , refl , refl , refl , σ≈σ′
Tr-resp-≈ (suc n) (p-≈ {T} {Γ} {Γs}) n<
  with chop (Γ ∷ Γs) n<
...  | Γ′ ∷ Φ₁ , Φ₂ , refl , eql                                   = Γ′ ∷ Φ₁ , Φ₂ , (T ∷ Γ′) ∷ Φ₁ , Φ₂ , refl , refl , eql , eql , I-≈
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
  with Tr-resp-≈ (O σ (suc n)) δ≈δ′ (O-<-len (suc n) (proj₁ (presup-s σ≈σ′)) n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , δ≈δ″
  rewrite ++⁺-cancelˡ′ Φ₃ Φ₅ (trans (sym eq′) eq″) (trans eql′ (sym eql″))
        | O-resp-≈ (suc n) σ≈σ′                                    = Φ₁ , Φ₂ , Φ₇ , Φ₈ , eq , eq‴ , eql , eql‴ , ∘-cong δ≈δ″ σ≈σ″
Tr-resp-≈ (suc n) (∘-I {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  rewrite O-I (O σ (suc n)) | Tr-I (O σ (suc n))                   = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ∘-I ⊢σ′
Tr-resp-≈ (suc n) (I-∘ {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , I-∘ ⊢σ′
Tr-resp-≈ (suc n) (,-∘ {_} {σ} {δ = δ} ⊢σ ⊢t ⊢δ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Γ ∷ Φ₁ , Φ₂ , Φ₃ , Φ₄ , refl , eq′ , eql , eql′ , ⊢σ′
  with Tr-⊢s (O σ (suc n)) ⊢δ (O-<-len (suc n) ⊢σ n<)
...  | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , ⊢δ′
  rewrite ++⁺-cancelˡ′ Φ₃ Φ₅
                       (trans (sym eq′) eq″)
                       (trans eql′ (sym eql″))                     = (_ ∷ Γ) ∷ Φ₁ , Φ₂ , Φ₇ , Φ₈ , refl , eq‴ , eql , eql‴ , ∘-cong (s≈-refl ⊢δ′) (s≈-refl ⊢σ′)
Tr-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {m} Γs ⊢σ ⊢δ refl) (s≤s n<)
  rewrite Tr-∘ n σ (Tr δ m) | Tr-+ δ m (O σ n)
  with Tr-⊢s n ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  with Tr-⊢s′ Γs ⊢δ
...  | Φ₅ , Φ₆ , eq″ , eql″ , ⊢δ′
  with Tr-⊢s (O σ n) ⊢δ′ (O-<-len n ⊢σ n<)
...  | Φ₇ , Φ₈ , Φ₉ , Φ₀ , eq‴ , refl , eql‴ , eql⁗ , ⊢δ″
  rewrite ++⁺-cancelˡ′ Φ₃ Φ₇
                      (trans (sym eq′) eq‴)
                      (trans eql′ (sym eql‴))                      = [] ∷ Φ₁ , Φ₂ , Φ₅ ++ Φ₉ , Φ₀
                                                                   , cong ([] ∷_) (cong toList eq) , trans eq″ (sym (++-++⁺ Φ₅))
                                                                   , cong suc eql , trans (length-++ Φ₅) (trans (cong₂ _+_ eql″ eql⁗) (sym (O-+ δ (len Γs) (O σ n))))
                                                                   , ∘-cong (s≈-refl ⊢δ″) (s≈-refl ⊢σ′)
Tr-resp-≈ (suc n) (p-, ⊢σ ⊢t) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , I-∘ ⊢σ′
Tr-resp-≈ (suc n) (,-ext ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′             = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , s-≈-sym (I-∘ ⊢σ′)
Tr-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ) n<
  with Tr-⊢s (suc n) ⊢σ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , ⊢σ′
  rewrite sym (Tr-+ σ 1 n)                                         = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , s≈-refl ⊢σ′

Tr-resp-≈ n (s-≈-sym σ≈σ′) n<
  with Tr-resp-≈ n σ≈σ′ n<
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″            = Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , trans eql′ (O-resp-≈ n σ≈σ′) , s-≈-sym σ≈σ″
Tr-resp-≈ n (s-≈-trans σ≈σ′ σ′≈σ″) n<
  with Tr-resp-≈ n σ≈σ′ n< | Tr-resp-≈ n σ′≈σ″ n< | O-resp-≈ n σ≈σ′
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″
     | Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , eql‴ , σ′≈σ‴
     | Leq
     rewrite ++⁺-cancelˡ′ Φ₁ Φ₅ (trans (sym eq) eq″)
                               (trans eql (sym eql″))
           | ++⁺-cancelˡ′ Φ₃ Φ₇ (trans (sym eq′) eq‴)
                                (trans eql′ (trans Leq (sym eql‴))) = Φ₅ , Φ₆ , Φ₇ , Φ₈ , eq″ , eq‴ , eql″ , trans eql‴ (sym (O-resp-≈ n σ≈σ′)) , s-≈-trans σ≈σ″ σ′≈σ‴

Tr-resp-≈′ : ∀ Γs → Ψ ⊢s σ ≈ σ′ ∶ Γs ++⁺ Ψ′ →
             ∃₂ λ Φ₁ Φ₂ → Ψ ≡ Φ₁ ++⁺ Φ₂ × len Φ₁ ≡ O σ (len Γs) × Φ₂ ⊢s Tr σ (len Γs) ≈ Tr σ′ (len Γs) ∶ Ψ′
Tr-resp-≈′ Γs σ≈σ′
  with Tr-resp-≈ (len Γs) σ≈σ′ (length-<-++⁺ Γs)
...  | Φ₁ , Φ₂ , Φ₃ , Φ₄ , eq , eq′ , eql , eql′ , σ≈σ″
  rewrite ++⁺-cancelˡ′ Γs Φ₁ eq (sym eql) = Φ₃ , Φ₄ , eq′ , eql′ , σ≈σ″
