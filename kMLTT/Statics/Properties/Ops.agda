{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Ops where

open import Data.Nat.Properties as Nₚ
open import Data.List.Properties as Lₚ

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Properties.Contexts


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

L-+ : ∀ (σ : Substs) n m → L σ (n + m) ≡ L σ n + L (σ ∥ n) m
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
        | L-+ δ (L σ (suc n)) (L (σ ∥ suc n) m) = cong (L δ (L σ (suc n)) +_) (sym (L-∘ m (σ ∥ suc n) (δ ∥ L σ (suc n))))

I-∥ : ∀ n → (I ∥ n) ≡ I
I-∥ zero    = refl
I-∥ (suc n) = refl

∘-∥ : ∀ n σ δ → ((σ ∘ δ) ∥ n) ≡ (σ ∥ n ∘ δ ∥ L σ n)
∘-∥ zero σ δ    = refl
∘-∥ (suc n) σ δ = refl

+-∥ : ∀ (σ : Substs) n m → (σ ∥ n + m) ≡ (σ ∥ n ∥ m)
+-∥ σ zero m              = refl
+-∥ I (suc n) m           = sym (I-∥ m)
+-∥ (p σ) (suc n) m       = +-∥ σ (suc n) m
+-∥ (σ ∘ δ) (suc n) m
  rewrite ∘-∥ m (σ ∥ suc n) (δ ∥ L σ (suc n))
        | +-∥ σ (suc n) m
        | sym (+-∥ δ (L σ (suc n)) (L (σ ∥ suc n) m))
        | L-+ σ (suc n) m = refl
+-∥ (σ , _) (suc n) m     = +-∥ σ (suc n) m
+-∥ (σ ； _) (suc n) m    = +-∥ σ n m

L-<-len : Γ ⊢s σ ∶ Δ →
        ∀ n →
        n < len Δ →
        --------------
        L σ n < len Γ
L-<-len ⊢σ zero n<l              = s≤s z≤n
L-<-len (s-I x) (suc n) n<l      = n<l
L-<-len (s-p ⊢σ) (suc n) n<l     = L-<-len ⊢σ (suc n) n<l
L-<-len (s-∘ ⊢σ ⊢δ) (suc n) n<l  = L-<-len ⊢σ _ (L-<-len ⊢δ (suc n) n<l)
L-<-len (s-, ⊢σ _ _) (suc n) n<l = L-<-len ⊢σ (suc n) n<l
L-<-len (s-； {Γ} {n = m} Ψs ⊢σ _ eq) (suc n) (s≤s n<l)
  rewrite length-++⁺′ Ψs Γ | eq
  with L-<-len ⊢σ n n<l
...  | s≤s L<l                   = s≤s (+-monoʳ-≤ m L<l)
L-<-len (s-conv ⊢σ Δ′≈Δ) (suc n) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)      = L-<-len ⊢σ (suc n) n<l

∥-⊢s : Γ ⊢s σ ∶ Δ →
       ∀ n →
       n < len Δ →
       --------------------------------------------------
       ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
          Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
          len Ψs ≡ L σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ∶ Δ′
∥-⊢s ⊢σ zero n<l                                   = [] , [] , -, -, refl , refl , refl , refl , ⊢σ
∥-⊢s {Γ} (s-I ⊢Γ) (suc n) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                          = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , s-I (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-⊢s (s-p ⊢σ) (suc n) n<l
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , (T ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (s-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) (suc n) n<l
  with ∥-⊢s ⊢δ (suc n) n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , ⊢δ∥
     with ∥-⊢s ⊢σ (L δ (suc n)) (L-<-len ⊢δ (suc n) n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , ⊢σ∥
        rewrite ++⁺ˡ-cancel Ψs Ψs‴
                            (trans (sym eq) eq‴)
                            (trans eql (sym eql‴)) = Ψs″ , Ψs′ , Δ′ , Γ′ , eq″ , eq′ , eql″ , eql′ , s-∘ ⊢σ∥ ⊢δ∥
∥-⊢s (s-, ⊢σ _ _) (suc n) n<l
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , (_ ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (s-； Ψs ⊢σ _ eq) (suc n) (s≤s n<l)
  with ∥-⊢s ⊢σ n n<l
...  | Ψs′ , Ψs″ , Γ′ , Δ′
     , refl , eq″ , eql′ , eql″ , ⊢σ∥              = Ψs ++ Ψs′ , [] ∷ Ψs″ , Γ′ , Δ′
                                                   , sym (++-++⁺ Ψs) , cong ([] ∷⁺_) eq″
                                                   , trans (length-++ Ψs) (cong₂ _+_ eq eql′) , cong suc eql″ , ⊢σ∥
∥-⊢s (s-conv ⊢σ Δ′≈Δ) (suc n) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)
  with ∥-⊢s ⊢σ (suc n) n<l
...  | Ψs , Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥
     with ≈⇒∥⇒∥ Ψs′ Δ′≈Δ
...    | Ψs″ , Δ″ , eq″ , eql″ , Δ′≈Δ∥             = Ψs , Ψs″ , Γ′ , Δ″ , eq , eq″ , eql , trans (sym eql″) eql′ , s-conv ⊢σ∥ Δ′≈Δ∥

L-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           -----------------
           L σ n ≡ L σ′ n
L-resp-≈ n (I-≈ _)                     = refl
L-resp-≈ n (p-cong {_} {σ} {σ′} σ≈σ′)
   rewrite L-p n σ
         | L-p n σ′                    = L-resp-≈ n σ≈σ′
L-resp-≈ n (∘-cong {_} {σ} {δ} {_} {σ′} {δ′} σ≈δ σ′≈δ′)
  rewrite L-∘ n σ′ σ
        | L-∘ n δ′ δ
        | L-resp-≈ n σ′≈δ′             = L-resp-≈ (L δ′ n) σ≈δ
L-resp-≈ n (,-cong {_} {σ} {σ′} {_} {_} {t} {t′} σ≈σ′ _ _)
  rewrite L-, n σ t
        | L-, n σ′ t′                  = L-resp-≈ n σ≈σ′
L-resp-≈ zero (；-cong Ψs σ≈σ′ _ _)    = refl
L-resp-≈ (suc n) (；-cong Ψs σ≈σ′ _ _) = cong (_ +_) (L-resp-≈ n σ≈σ′)
L-resp-≈ n (I-∘ {_} {σ} _)
  rewrite L-∘ n I σ
        | L-I n                        = refl
L-resp-≈ n (∘-I {_} {σ} _)
  rewrite L-∘ n σ I                    = L-I (L σ n)
L-resp-≈ n (∘-assoc {_} {σ} {_} {_} {σ′} {σ″} _ _ _)
  rewrite L-∘ n (σ ∘ σ′) σ″
        | L-∘ n σ σ′
        | L-∘ n σ (σ′ ∘ σ″)
        | L-∘ (L σ n) σ′ σ″            = refl
L-resp-≈ n (,-∘ {_} {σ} {_} {_} {t} {_} {δ} _ _ _ _)
  rewrite L-∘ n (σ , t) δ
        | L-, n σ t
        | L-, n (σ ∘ δ) (t [ δ ])      = sym (L-∘ n σ δ)
L-resp-≈ n (p-∘ {_} {σ} {_} {_} {_} {δ} _ _)
  rewrite L-∘ n (p σ) δ
        | L-p n σ
        | L-p n (σ ∘ δ)                = sym (L-∘ n σ δ)
L-resp-≈ zero (；-∘ Ψs _ _ _)          = refl
L-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {n = m} Ψs _ _ _)
  rewrite L-+ δ m (L σ n)              = cong (_ +_) (sym (L-∘ n σ (δ ∥ m)))
L-resp-≈ n (p-, {_} {σ} {_} {_} {t} _ _ _)
  rewrite L-p n (σ , t)
        | L-, n σ t                    = refl
L-resp-≈ n (,-ext {_} {σ} _)
  rewrite L-, n (p σ) (v 0 [ σ ])      = sym (L-p n σ)
L-resp-≈ zero (；-ext _)               = refl
L-resp-≈ (suc n) (；-ext {_} {σ} _)    = L-+ σ 1 n
L-resp-≈ n (s-≈-sym σ≈σ′)              = sym (L-resp-≈ n σ≈σ′)
L-resp-≈ n (s-≈-trans σ≈σ″ σ″≈σ′)      = trans (L-resp-≈ n σ≈σ″) (L-resp-≈ n σ″≈σ′)
L-resp-≈ n (s-conv σ≈σ′ _)             = L-resp-≈ n σ≈σ′
