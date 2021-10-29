{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Ops where

open import Data.Nat.Properties as Nₚ
open import Data.List.Properties as Lₚ

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Refl
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
L-+ I zero m                                    = refl
L-+ I (suc n) m
  rewrite L-I m                                 = refl
L-+ (p σ) zero m                                = refl
L-+ (p σ) (suc n) m                             = L-+ σ (suc n) m
L-+ (σ , t) zero m                              = refl
L-+ (σ , t) (suc n) m                           = L-+ σ (suc n) m
L-+ (σ ； k) zero m                             = refl
L-+ (σ ； k) (suc n) m
  rewrite L-+ σ n m                             = sym (+-assoc k (S-L σ n) (S-L (S-Tr σ n) m))
L-+ (σ ∘ δ) zero m                              = refl
L-+ (σ ∘ δ) (suc n) m
  rewrite L-+ σ (suc n) m
        | L-+ δ (L σ (suc n)) (L (σ ∥ suc n) m) = cong (L δ (L σ (suc n)) +_) (sym (L-∘ m (σ ∥ suc n) (δ ∥ L σ (suc n))))

I-∥ : ∀ n → (I ∥ n) ≡ I
I-∥ zero    = refl
I-∥ (suc n) = refl

∘-∥ : ∀ n σ δ → ((σ ∘ δ) ∥ n) ≡ (σ ∥ n ∘ δ ∥ L σ n)
∘-∥ zero σ δ    = refl
∘-∥ (suc n) σ δ = refl

∥-+ : ∀ (σ : Substs) n m → (σ ∥ n + m) ≡ (σ ∥ n ∥ m)
∥-+ σ zero m              = refl
∥-+ I (suc n) m           = sym (I-∥ m)
∥-+ (p σ) (suc n) m       = ∥-+ σ (suc n) m
∥-+ (σ ∘ δ) (suc n) m
  rewrite ∘-∥ m (σ ∥ suc n) (δ ∥ L σ (suc n))
        | ∥-+ σ (suc n) m
        | sym (∥-+ δ (L σ (suc n)) (L (σ ∥ suc n) m))
        | L-+ σ (suc n) m = refl
∥-+ (σ , _) (suc n) m     = ∥-+ σ (suc n) m
∥-+ (σ ； _) (suc n) m    = ∥-+ σ n m

L-<-len : ∀ n →
          Γ ⊢s σ ∶ Δ →
          n < len Δ →
          --------------
          L σ n < len Γ
L-<-len zero ⊢σ n<l              = s≤s z≤n
L-<-len (suc n) (s-I _) n<l      = n<l
L-<-len (suc n) (s-p ⊢σ) n<l     = L-<-len (suc n) ⊢σ n<l
L-<-len (suc n) (s-∘ ⊢σ ⊢δ) n<l  = L-<-len _ ⊢σ (L-<-len (suc n) ⊢δ n<l)
L-<-len (suc n) (s-, ⊢σ _ _) n<l = L-<-len (suc n) ⊢σ n<l
L-<-len (suc n) (s-； {Γ} {n = m} Ψs ⊢σ _ eq) (s≤s n<l)
  rewrite length-++⁺′ Ψs Γ | eq
  with L-<-len n ⊢σ n<l
...  | s≤s L<l                   = s≤s (+-monoʳ-≤ m L<l)
L-<-len (suc n) (s-conv ⊢σ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)      = L-<-len (suc n) ⊢σ n<l

∥-⊢s : ∀ n →
       Γ ⊢s σ ∶ Δ →
       n < len Δ →
       --------------------------------------------------
       ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
          Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
          len Ψs ≡ L σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ∶ Δ′
∥-⊢s zero ⊢σ n<l                                   = [] , [] , -, -, refl , refl , refl , refl , ⊢σ
∥-⊢s {Γ} (suc n) (s-I ⊢Γ) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                          = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , s-I (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-⊢s (suc n)  (s-p ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs , (T ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (suc n) (s-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<l
  with ∥-⊢s (suc n) ⊢δ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , ⊢δ∥
     with ∥-⊢s (L δ (suc n)) ⊢σ (L-<-len (suc n) ⊢δ n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , ⊢σ∥
        rewrite ++⁺ˡ-cancel Ψs Ψs‴
                            (trans (sym eq) eq‴)
                            (trans eql (sym eql‴)) = Ψs″ , Ψs′ , Δ′ , Γ′ , eq″ , eq′ , eql″ , eql′ , s-∘ ⊢σ∥ ⊢δ∥
∥-⊢s (suc n) (s-, ⊢σ _ _) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                = Ψs , (_ ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-⊢s (suc n) (s-； Ψs ⊢σ _ eq) (s≤s n<l)
  with ∥-⊢s n ⊢σ n<l
...  | Ψs′ , Ψs″ , Γ′ , Δ′
     , refl , eq″ , eql′ , eql″ , ⊢σ∥              = Ψs ++ Ψs′ , [] ∷ Ψs″ , Γ′ , Δ′
                                                   , sym (++-++⁺ Ψs) , cong ([] ∷⁺_) eq″
                                                   , trans (length-++ Ψs) (cong₂ _+_ eq eql′) , cong suc eql″ , ⊢σ∥
∥-⊢s (suc n) (s-conv ⊢σ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs , Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥
     with ≈⇒∥⇒∥ Ψs′ Δ′≈Δ
...     | Ψs″ , Δ″ , eq″ , eql″ , Δ′≈Δ∥            = Ψs , Ψs″ , Γ′ , Δ″ , eq , eq″ , eql , trans (sym eql″) eql′ , s-conv ⊢σ∥ Δ′≈Δ∥


∥-⊢s′ : ∀ Ψs →
        Γ ⊢s σ ∶ Ψs ++⁺ Δ →
        ---------------------
        ∃₂ λ Ψs′ Γ′ → Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ L σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ∶ Δ
∥-⊢s′ Ψs ⊢σ
  with ∥-⊢s (len Ψs) ⊢σ (length-<-++⁺ Ψs)
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥
     rewrite ++⁺ˡ-cancel Ψs Ψs₂ eq₂ (sym eql₂) = Ψs₁ , Γ₁ , eq₁ , eql₁ , ⊢σ∥


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
L-resp-≈ zero (；-∘ Ψs _ _ _ _)          = refl
L-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {n = m} Ψs _ _ _ _)
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
L-resp-≈ n (s-≈-conv σ≈σ′ _)           = L-resp-≈ n σ≈σ′


≈L-<-len : ∀ n →
           Γ ⊢s σ ≈ τ ∶ Δ →
           n < len Δ →
           --------------
           L σ n < len Γ
≈L-<-len zero σ≈τ n<l                           = s≤s z≤n
≈L-<-len (suc n) (I-≈ _) n<l                    = n<l
≈L-<-len (suc n) (p-cong σ≈τ) n<l               = ≈L-<-len (suc n) σ≈τ n<l
≈L-<-len (suc n) (∘-cong {σ = σ} σ≈τ σ′≈τ′) n<l = ≈L-<-len (S-L σ (suc n)) σ≈τ (≈L-<-len (suc n) σ′≈τ′ n<l)
≈L-<-len (suc n) (,-cong σ≈τ _ _) n<l           = ≈L-<-len (suc n) σ≈τ n<l
≈L-<-len (suc n) (；-cong {Γ} Ψs σ≈τ _ eq) (s≤s n<l)
  rewrite length-++⁺′ Ψs Γ | eq
  with ≈L-<-len n σ≈τ n<l
...  | s≤s L<l                                  = s≤s (+-monoʳ-≤ _ L<l)
≈L-<-len (suc n) (I-∘ ⊢σ) n<l                   = L-<-len (suc n) ⊢σ n<l
≈L-<-len (suc n) (∘-I {_} {σ} ⊢σ) n<l
  rewrite L-I (L σ (suc n))                     = L-<-len (suc n) ⊢σ n<l
≈L-<-len (suc n) (∘-assoc ⊢σ ⊢σ′ ⊢σ″) n<l       = L-<-len (suc n) (s-∘ ⊢σ″ (s-∘ ⊢σ′ ⊢σ)) n<l
≈L-<-len (suc n) (,-∘ ⊢σ ⊢T ⊢t ⊢δ) n<l          = L-<-len (suc n) (s-∘ ⊢δ (s-, ⊢σ ⊢T ⊢t)) n<l
≈L-<-len (suc n) (p-∘ ⊢σ ⊢δ) n<l                = L-<-len (suc n) (s-∘ ⊢δ (s-p ⊢σ)) n<l
≈L-<-len (suc n) (；-∘ Ψs ⊢σ ⊢δ ⊢ΨsΓ eq) n<l    = L-<-len (suc n) (s-∘ ⊢δ (s-； Ψs ⊢σ ⊢ΨsΓ eq)) n<l
≈L-<-len (suc n) (p-, ⊢σ _ _) n<l               = L-<-len (suc n) ⊢σ n<l
≈L-<-len (suc n) (,-ext ⊢σ) n<l                 = L-<-len (suc n) ⊢σ n<l
≈L-<-len (suc n) (；-ext ⊢σ) n<l                = L-<-len (suc n) ⊢σ n<l
≈L-<-len (suc n) (s-≈-sym σ≈τ) n<l
  rewrite sym (L-resp-≈ (suc n) σ≈τ)            = ≈L-<-len (suc n) σ≈τ n<l
≈L-<-len (suc n) (s-≈-trans σ≈τ _) n<l          = ≈L-<-len (suc n) σ≈τ n<l
≈L-<-len (suc n) (s-≈-conv σ≈τ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)                     = ≈L-<-len (suc n) σ≈τ n<l


∥-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           n < len Δ →
           --------------------------------------------------
           ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
             Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
             len Ψs ≡ L σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ≈ σ′ ∥ n ∶ Δ′
∥-resp-≈ zero σ≈σ′ n<l                                 = [] , [] , -, -, refl , refl , refl , refl , σ≈σ′
∥-resp-≈ {Γ} (suc n) (I-≈ ⊢Γ) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                              = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , I-≈ (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-resp-≈ (suc n) (p-cong σ≈σ′) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l
...  | Ψs , (T ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , σ≈σ′∥                  = Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , σ≈σ′∥
∥-resp-≈ (suc n) (∘-cong {σ = σ′} σ≈δ σ′≈δ′) n<l
  with ∥-resp-≈ (suc n) σ′≈δ′ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , σ′≈δ′∥
     with ∥-resp-≈ (L σ′ (suc n)) σ≈δ (≈L-<-len (suc n) σ′≈δ′ n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , σ≈δ∥
        rewrite ++⁺ˡ-cancel Ψs Ψs‴
                            (trans (sym eq) eq‴)
                            (trans eql (sym eql‴))
              | L-resp-≈ (suc n) σ′≈δ′                 = Ψs″ , Ψs′ , Δ′ , Γ′ , eq″ , eq′ , eql″ , eql′ , ∘-cong σ≈δ∥ σ′≈δ′∥
∥-resp-≈ (suc n) (,-cong σ≈σ′ ⊢T t≈t′) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l
...  | Ψs , Ψ ∷ Ψs′ , Γ′ , Δ′
     , eq , refl , eql , eql′ , ⊢σ∥                    = Ψs , (_ ∷ Ψ) ∷ Ψs′ , Γ′ , Δ′ , eq , refl , eql , eql′ , ⊢σ∥
∥-resp-≈ (suc n) (；-cong Ψs σ≈σ′ _ eq) (s≤s n<l)
  with ∥-resp-≈ n σ≈σ′ n<l
...  | Ψs′ , Ψs″ , Γ′ , Δ′
     , refl , eq″ , eql′ , eql″ , ⊢σ∥                  = Ψs ++ Ψs′ , [] ∷ Ψs″ , Γ′ , Δ′
                                                       , sym (++-++⁺ Ψs) , cong ([] ∷⁺_) eq″
                                                       , trans (length-++ Ψs) (cong₂ _+_ eq eql′) , cong suc eql″ , ⊢σ∥
∥-resp-≈ (suc n) (I-∘ ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs , Ψs′ , Γ′ , Δ′
     , eq , eq′ , eql , eql′ , ⊢σ∥                     = Ψs , Ψs′ , Γ′ , Δ′ , eq , eq′ , eql , eql′ , I-∘ ⊢σ∥
∥-resp-≈ (suc n) (∘-I {_} {σ} ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs , Ψs′ , Γ′ , Δ′
     , eq , eq′ , eql , eql′ , ⊢σ∥                     = Ψs , Ψs′ , Γ′ , Δ′ , eq , eq′
                                                       , trans eql (sym (L-I _)) , eql′
                                                       , subst (λ δ → _ ⊢s σ ∥ suc n ∘ δ ≈ σ ∥ suc n ∶ _) (sym (I-∥ (L σ (suc n)))) (∘-I ⊢σ∥)
∥-resp-≈ (suc n) (∘-assoc {_} {σ} {_} {_} {σ′} {σ″} ⊢σ ⊢σ′ ⊢σ″) n<l
  with ∥-⊢s (suc n) ⊢σ n<l | L-<-len (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥ | Lσ<l
     with ∥-⊢s (L σ (suc n)) ⊢σ′ Lσ<l
...     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
        , eq₃ , eq₄ , eql₃ , eql₄ , ⊢σ′∥
        with ∥-⊢s (L σ′ (L σ (suc n))) ⊢σ″ (L-<-len (L σ (suc n)) ⊢σ′ Lσ<l)
...        | Ψs₅ , Ψs₆ , Γ₅ , Γ₆
           , eq₅ , eq₆ , eql₅ , eql₆ , ⊢σ″∥
           rewrite ++⁺ˡ-cancel Ψs₁ Ψs₄
                               (trans (sym eq₁) eq₄)
                               (trans eql₁ (sym eql₄))
                 | ++⁺ˡ-cancel Ψs₃ Ψs₆
                               (trans (sym eq₃) eq₆)
                               (trans eql₃ (sym eql₆))
                 | ∘-∥ (L σ (suc n)) σ′ σ″             = Ψs₅ , Ψs₂ , Γ₅ , Γ₂ , eq₅ , eq₂ , eql₅ , eql₂ , ∘-assoc ⊢σ∥ ⊢σ′∥ ⊢σ″∥
∥-resp-≈ (suc n) (,-∘ {_} {σ} ⊢σ ⊢T ⊢t ⊢δ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l | ∥-⊢s (L σ (suc n)) ⊢δ (L-<-len (suc n) ⊢σ n<l)
...  | Ψs₁ , Γ ∷ Ψs₂ , Γ₁ , Γ₂
     , eq₁ , refl , eql₁ , eql₂ , ⊢σ∥
     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
     , eq₃ , eq₄ , eql₃ , eql₄ , ⊢δ∥
     rewrite ++⁺ˡ-cancel Ψs₁ Ψs₄
                         (trans (sym eq₁) eq₄)
                         (trans eql₁ (sym eql₄))       = Ψs₃ , (_ ∷ Γ) ∷ Ψs₂ , Γ₃ , Γ₂ , eq₃ , refl , eql₃ , eql₂ , s-≈-refl (s-∘ ⊢δ∥ ⊢σ∥)
∥-resp-≈ (suc n) (p-∘ {_} {σ} ⊢σ ⊢δ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l | ∥-⊢s (L σ (suc n)) ⊢δ (L-<-len (suc n) ⊢σ n<l)
...  | Ψs₁ , (T ∷ Γ) ∷ Ψs₂ , Γ₁ , Γ₂
     , eq₁ , refl , eql₁ , eql₂ , ⊢σ∥
     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
     , eq₃ , eq₄ , eql₃ , eql₄ , ⊢δ∥
     rewrite ++⁺ˡ-cancel Ψs₁ Ψs₄
                         (trans (sym eq₁) eq₄)
                         (trans eql₁ (sym eql₄))       = Ψs₃ , Γ ∷ Ψs₂ , Γ₃ , Γ₂ , eq₃ , refl , eql₃ , eql₂ , s-≈-refl (s-∘ ⊢δ∥ ⊢σ∥)
∥-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} Ψs ⊢σ ⊢δ ⊢ΨsΓ refl) (s≤s n<l)
  rewrite ∘-∥ n σ (δ ∥ len Ψs) | ∥-+ δ (len Ψs) (L σ n)
  with ∥-⊢s n ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , refl , eq₂ , eql₁ , eql₂ , ⊢σ∥
     with ∥-⊢s′ Ψs ⊢δ
...     | Ψs₃ , Γ₃ , eq₃ , eql₃ , ⊢δ∥
        with ∥-⊢s (L σ n) ⊢δ∥ (L-<-len n ⊢σ n<l)
...        | Ψs₄ , Ψs₅ , Γ₄ , Γ₅
           , refl , eq₅ , eql₄ , eql₅ , ⊢δ∥′
           rewrite ++⁺ˡ-cancel Ψs₁ Ψs₅ eq₅
                               (trans eql₁ (sym eql₅)) = Ψs₃ ++ Ψs₄ , [] ∷ Ψs₂ , Γ₄ , Γ₂
                                                       , trans eq₃ (sym (++-++⁺ Ψs₃)) , cong ([] ∷⁺_) eq₂
                                                       , trans (length-++ Ψs₃) (trans (cong₂ _+_ eql₃ eql₄) (sym (L-+ δ (len Ψs) (L σ n)))) , cong suc eql₂
                                                       , s-≈-refl (s-∘ ⊢δ∥′ ⊢σ∥)
∥-resp-≈ (suc n) (p-, ⊢σ ⊢T ⊢t) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥                   = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , s-≈-refl ⊢σ∥
∥-resp-≈ (suc n) (,-ext ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥                   = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , s-≈-refl ⊢σ∥
∥-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥
     rewrite sym (∥-+ σ 1 n)                           = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , s-≈-refl ⊢σ∥
∥-resp-≈ (suc n) (s-≈-sym σ≈σ′) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , σ≈σ′∥                   = Ψs , Ψs′ , Γ₁ , Γ′ , eq , eq′ , trans eql (L-resp-≈ (suc n) σ≈σ′) , eql′ , s-≈-sym σ≈σ′∥
∥-resp-≈ (suc n) (s-≈-trans σ≈σ′ σ′≈σ″) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l | ∥-resp-≈ (suc n) σ′≈σ″ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , σ≈σ′∥
     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
     , eq₃ , eq₄ , eql₃ , eql₄ , σ′≈σ″∥
     rewrite L-resp-≈ (suc n) σ≈σ′
           | L-resp-≈ (suc n) σ′≈σ″
           | ++⁺ˡ-cancel Ψs₁ Ψs₃
                         (trans (sym eq₁) eq₃)
                         (trans eql₁ (sym eql₃))
           | ++⁺ˡ-cancel Ψs₂ Ψs₄
                         (trans (sym eq₂) eq₄)
                         (trans eql₂ (sym eql₄))       = Ψs₃ , Ψs₄ , Γ₃ , Γ₄ , eq₃ , eq₄ , eql₃ , eql₄ , s-≈-trans σ≈σ′∥ σ′≈σ″∥
∥-resp-≈ (suc n) (s-≈-conv σ≈σ′ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)
  with ∥-resp-≈ (suc n) σ≈σ′ n<l
...  | Ψs , Ψs′ , Γ′ , Δ″
     , eq , refl , eql , eql′ , σ≈σ′∥
     with ≈⇒∥⇒∥ Ψs′ Δ′≈Δ
...     | Ψs″ , Δ″ , eq″ , eql″ , Δ′≈Δ∥                = Ψs , Ψs″ , Γ′ , Δ″ , eq , eq″ , eql , trans (sym eql″) eql′ , s-≈-conv σ≈σ′∥ Δ′≈Δ∥

∥-resp-≈′ : ∀ Ψs →
            Γ ⊢s σ ≈ σ′ ∶ Ψs ++⁺ Δ →
            --------------------------------------------------
            ∃₂ λ Ψs′ Γ′ →
              Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ L σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ≈ σ′ ∥ len Ψs ∶ Δ
∥-resp-≈′ Ψs σ≈σ′
  with ∥-resp-≈ (len Ψs) σ≈σ′ (length-<-++⁺ Ψs)
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , σ≈σ′∥
     rewrite ++⁺ˡ-cancel Ψs Ψs₂ eq₂ (sym eql₂) = Ψs₁ , Γ₁ , eq₁ , eql₁ , σ≈σ′∥
