{-# OPTIONS --without-K --safe #-}

-- Properties of operations
--
-- e.g. truncation offset (O) and truncation
module Mint.Statics.Properties.Ops where

open import Data.Nat.Properties as Nₚ
open import Data.List.Properties as Lₚ

open import Lib
open import Mint.Statics.Full
open import Mint.Statics.Refl
open import Mint.Statics.Properties.Contexts


O-I : ∀ n → O I n ≡ n
O-I zero    = refl
O-I (suc n) = refl

O-wk : ∀ n → O wk n ≡ n
O-wk zero    = refl
O-wk (suc n) = refl

O-∘ : ∀ n σ δ → O (σ ∘ δ) n ≡ O δ (O σ n)
O-∘ 0 σ δ       = refl
O-∘ (suc n) σ δ = refl

O-p : ∀ n σ → O (p σ) n ≡ O σ n
O-p zero    σ = refl
O-p (suc n) σ = refl

O-, : ∀ n σ t → S-O (σ , t) n ≡ O σ n
O-, zero σ t    = refl
O-, (suc n) σ t = refl

-- distributivity of + over O
O-+ : ∀ (σ : Substs) n m → O σ (n + m) ≡ O σ n + O (σ ∥ n) m
O-+ I zero m                                    = refl
O-+ I (suc n) m
  rewrite O-I m                                 = refl
O-+ wk zero m                                   = refl
O-+ wk (suc n) m
  rewrite O-I m                                 = refl
O-+ (σ , t) zero m                              = refl
O-+ (σ , t) (suc n) m                           = O-+ σ (suc n) m
O-+ (σ ； k) zero m                             = refl
O-+ (σ ； k) (suc n) m
  rewrite O-+ σ n m                             = sym (+-assoc k (S-O σ n) (S-O (S-Tr σ n) m))
O-+ (σ ∘ δ) zero m                              = refl
O-+ (σ ∘ δ) (suc n) m
  rewrite O-+ σ (suc n) m
        | O-+ δ (O σ (suc n)) (O (σ ∥ suc n) m) = cong (O δ (O σ (suc n)) +_) (sym (O-∘ m (σ ∥ suc n) (δ ∥ O σ (suc n))))

I-∥ : ∀ n → (I ∥ n) ≡ I
I-∥ zero    = refl
I-∥ (suc n) = refl

-- distributivity of composition over truncation
∘-∥ : ∀ n σ δ → ((σ ∘ δ) ∥ n) ≡ (σ ∥ n ∘ δ ∥ O σ n)
∘-∥ zero σ δ    = refl
∘-∥ (suc n) σ δ = refl

-- distributivity of + over truncation
∥-+ : ∀ (σ : Substs) n m → (σ ∥ n + m) ≡ (σ ∥ n ∥ m)
∥-+ σ zero m              = refl
∥-+ I (suc n) m           = sym (I-∥ m)
∥-+ wk (suc n) m          = sym (I-∥ m)
∥-+ (σ ∘ δ) (suc n) m
  rewrite ∘-∥ m (σ ∥ suc n) (δ ∥ O σ (suc n))
        | ∥-+ σ (suc n) m
        | sym (∥-+ δ (O σ (suc n)) (O (σ ∥ suc n) m))
        | O-+ σ (suc n) m = refl
∥-+ (σ , _) (suc n) m     = ∥-+ σ (suc n) m
∥-+ (σ ； _) (suc n) m    = ∥-+ σ n m

-- O respects length of context stacks
O-<-len : ∀ n →
          Γ ⊢s σ ∶ Δ →
          n < len Δ →
          --------------
          O σ n < len Γ
O-<-len zero ⊢σ n<l              = s≤s z≤n
O-<-len (suc n) (s-I _) n<l      = n<l
O-<-len (suc n) (s-wk _) n<l     = n<l
O-<-len (suc n) (s-∘ ⊢σ ⊢δ) n<l  = O-<-len _ ⊢σ (O-<-len (suc n) ⊢δ n<l)
O-<-len (suc n) (s-, ⊢σ _ _) n<l = O-<-len (suc n) ⊢σ n<l
O-<-len (suc n) (s-； {Γ} {n = m} Ψs ⊢σ _ eq) (s≤s n<l)
  rewrite length-++⁺-tail Ψs Γ | eq
  with O-<-len n ⊢σ n<l
...  | s≤s L<l                   = s≤s (+-monoʳ-≤ m L<l)
O-<-len (suc n) (s-conv ⊢σ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)      = O-<-len (suc n) ⊢σ n<l

-- typing of a truncated substitution
∥-⊢s : ∀ n →
       Γ ⊢s σ ∶ Δ →
       n < len Δ →
       --------------------------------------------------
       ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
          Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
          len Ψs ≡ O σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ∶ Δ′
∥-⊢s zero ⊢σ n<l                                   = [] , [] , -, -, refl , refl , refl , refl , ⊢σ
∥-⊢s {Γ} (suc n) (s-I ⊢Γ) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                          = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , s-I (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-⊢s {(T ∷ Ψ) ∷ Γ} (suc n)  (s-wk (⊢∺ ⊢Γ _)) n<l
  with chop (Ψ ∷ Γ) n<l
...  | (Ψ′ ∷ Ψs′) , Γ′ , refl , refl                 = (T ∷ Ψ′) ∷ Ψs′ , Ψ′ ∷ Ψs′ , Γ′ , _ , refl , refl , refl , refl , s-I (⊢⇒∥⊢ (Ψ′ ∷ Ψs′) ⊢Γ)
∥-⊢s (suc n) (s-∘ {_} {σ} {_} {δ} ⊢σ ⊢δ) n<l
  with ∥-⊢s (suc n) ⊢δ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , ⊢δ∥
     with ∥-⊢s (O δ (suc n)) ⊢σ (O-<-len (suc n) ⊢δ n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , ⊢σ∥
        rewrite ++⁺-cancelˡ′ Ψs Ψs‴
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
        ∃₂ λ Ψs′ Γ′ → Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ O σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ∶ Δ
∥-⊢s′ Ψs ⊢σ
  with ∥-⊢s (len Ψs) ⊢σ (length-<-++⁺ Ψs)
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥
     rewrite ++⁺-cancelˡ′ Ψs Ψs₂ eq₂ (sym eql₂) = Ψs₁ , Γ₁ , eq₁ , eql₁ , ⊢σ∥


-- O respects substitution equivalence
O-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           -----------------
           O σ n ≡ O σ′ n
O-resp-≈ n (I-≈ _)                     = refl
O-resp-≈ n (wk-≈ _)                    = refl
   -- rewrite O-wk n σ
   --       | O-wk n σ′                   = O-resp-≈ n σ≈σ′
O-resp-≈ n (∘-cong {_} {σ} {δ} {_} {σ′} {δ′} σ≈δ σ′≈δ′)
  rewrite O-∘ n σ′ σ
        | O-∘ n δ′ δ
        | O-resp-≈ n σ′≈δ′             = O-resp-≈ (O δ′ n) σ≈δ
O-resp-≈ n (,-cong {_} {σ} {σ′} {_} {_} {t} {t′} σ≈σ′ _ _)
  rewrite O-, n σ t
        | O-, n σ′ t′                  = O-resp-≈ n σ≈σ′
O-resp-≈ zero (；-cong Ψs σ≈σ′ _ _)    = refl
O-resp-≈ (suc n) (；-cong Ψs σ≈σ′ _ _) = cong (_ +_) (O-resp-≈ n σ≈σ′)
O-resp-≈ n (I-∘ {_} {σ} _)
  rewrite O-∘ n I σ
        | O-I n                        = refl
O-resp-≈ n (∘-I {_} {σ} _)
  rewrite O-∘ n σ I                    = O-I (O σ n)
O-resp-≈ n (∘-assoc {_} {σ} {_} {_} {σ′} {σ″} _ _ _)
  rewrite O-∘ n (σ ∘ σ′) σ″
        | O-∘ n σ σ′
        | O-∘ n σ (σ′ ∘ σ″)
        | O-∘ (O σ n) σ′ σ″            = refl
O-resp-≈ n (,-∘ {_} {σ} {_} {_} {t} {_} {δ} _ _ _ _)
  rewrite O-∘ n (σ , t) δ
        | O-, n σ t
        | O-, n (σ ∘ δ) (t [ δ ])      = sym (O-∘ n σ δ)
O-resp-≈ zero (；-∘ Ψs _ _ _ _)         = refl
O-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} {n = m} Ψs _ _ _ _)
  rewrite O-+ δ m (O σ n)              = cong (_ +_) (sym (O-∘ n σ (δ ∥ m)))
O-resp-≈ n (p-, {_} {σ} {_} {_} {t} _ _ _)
  rewrite O-p n (σ , t)
        | O-, n σ t                    = refl
O-resp-≈ n (,-ext {_} {σ} _)
  rewrite O-, n (p σ) (v 0 [ σ ])      = sym (trans (O-∘ n wk σ) (cong (O σ) (O-wk n)))
O-resp-≈ zero (；-ext _)               = refl
O-resp-≈ (suc n) (；-ext {_} {σ} _)    = O-+ σ 1 n
O-resp-≈ n (s-≈-sym σ≈σ′)              = sym (O-resp-≈ n σ≈σ′)
O-resp-≈ n (s-≈-trans σ≈σ″ σ″≈σ′)      = trans (O-resp-≈ n σ≈σ″) (O-resp-≈ n σ″≈σ′)
O-resp-≈ n (s-≈-conv σ≈σ′ _)           = O-resp-≈ n σ≈σ′


≈O-<-len : ∀ n →
           Γ ⊢s σ ≈ τ ∶ Δ →
           n < len Δ →
           --------------
           O σ n < len Γ
≈O-<-len zero σ≈τ n<l                           = s≤s z≤n
≈O-<-len (suc n) (I-≈ _) n<l                    = n<l
≈O-<-len (suc n) (wk-≈ _) n<l                   = n<l
≈O-<-len (suc n) (∘-cong {σ = σ} σ≈τ σ′≈τ′) n<l = ≈O-<-len (S-O σ (suc n)) σ≈τ (≈O-<-len (suc n) σ′≈τ′ n<l)
≈O-<-len (suc n) (,-cong σ≈τ _ _) n<l           = ≈O-<-len (suc n) σ≈τ n<l
≈O-<-len (suc n) (；-cong {Γ} Ψs σ≈τ _ eq) (s≤s n<l)
  rewrite length-++⁺-tail Ψs Γ | eq
  with ≈O-<-len n σ≈τ n<l
...  | s≤s L<l                                  = s≤s (+-monoʳ-≤ _ L<l)
≈O-<-len (suc n) (I-∘ ⊢σ) n<l                   = O-<-len (suc n) ⊢σ n<l
≈O-<-len (suc n) (∘-I {_} {σ} ⊢σ) n<l
  rewrite O-I (O σ (suc n))                     = O-<-len (suc n) ⊢σ n<l
≈O-<-len (suc n) (∘-assoc ⊢σ ⊢σ′ ⊢σ″) n<l       = O-<-len (suc n) (s-∘ ⊢σ″ (s-∘ ⊢σ′ ⊢σ)) n<l
≈O-<-len (suc n) (,-∘ ⊢σ ⊢T ⊢t ⊢δ) n<l          = O-<-len (suc n) (s-∘ ⊢δ (s-, ⊢σ ⊢T ⊢t)) n<l
≈O-<-len (suc n) (；-∘ Ψs ⊢σ ⊢δ ⊢ΨsΓ eq) n<l    = O-<-len (suc n) (s-∘ ⊢δ (s-； Ψs ⊢σ ⊢ΨsΓ eq)) n<l
≈O-<-len (suc n) (p-, ⊢σ _ _) n<l               = O-<-len (suc n) ⊢σ n<l
≈O-<-len (suc n) (,-ext ⊢σ) n<l                 = O-<-len (suc n) ⊢σ n<l
≈O-<-len (suc n) (；-ext ⊢σ) n<l                = O-<-len (suc n) ⊢σ n<l
≈O-<-len (suc n) (s-≈-sym σ≈τ) n<l
  rewrite sym (O-resp-≈ (suc n) σ≈τ)            = ≈O-<-len (suc n) σ≈τ n<l
≈O-<-len (suc n) (s-≈-trans σ≈τ _) n<l          = ≈O-<-len (suc n) σ≈τ n<l
≈O-<-len (suc n) (s-≈-conv σ≈τ Δ′≈Δ) n<l
  rewrite sym (≈⇒len≡ Δ′≈Δ)                     = ≈O-<-len (suc n) σ≈τ n<l


-- truncation respects substitution equivalence
∥-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           n < len Δ →
           --------------------------------------------------
           ∃₂ λ Ψs Ψs′ → ∃₂ λ Γ′ Δ′ →
             Γ ≡ Ψs ++⁺ Γ′ × Δ ≡ Ψs′ ++⁺ Δ′ ×
             len Ψs ≡ O σ n × len Ψs′ ≡ n × Γ′ ⊢s σ ∥ n ≈ σ′ ∥ n ∶ Δ′
∥-resp-≈ zero σ≈σ′ n<l                                 = [] , [] , -, -, refl , refl , refl , refl , σ≈σ′
∥-resp-≈ {Γ} (suc n) (I-≈ ⊢Γ) n<l
  with chop Γ n<l
...  | Ψs , Γ′ , eq , eql                              = Ψs , Ψs , Γ′ , Γ′ , eq , eq , eql , eql , I-≈ (⊢⇒∥⊢ Ψs (subst ⊢_ eq ⊢Γ))
∥-resp-≈ {(T ∷ Ψ) ∷ Γ}(suc n) (wk-≈ (⊢∺ ⊢Γ _)) n<l
  with chop (Ψ ∷ Γ) n<l
...  | (Ψ′ ∷ Ψs′) , Γ′ , refl , refl                      = (T ∷ Ψ′) ∷ Ψs′ , Ψ′ ∷ Ψs′ , Γ′ , Γ′ , refl , refl , refl , refl , I-≈ (⊢⇒∥⊢ (Ψ′ ∷ Ψs′) ⊢Γ)
∥-resp-≈ (suc n) (∘-cong {σ = σ′} σ≈δ σ′≈δ′) n<l
  with ∥-resp-≈ (suc n) σ′≈δ′ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , σ′≈δ′∥
     with ∥-resp-≈ (O σ′ (suc n)) σ≈δ (≈O-<-len (suc n) σ′≈δ′ n<l)
...     | Ψs″ , Ψs‴ , Δ′ , Γ₂
        , eq″ , eq‴ , eql″ , eql‴ , σ≈δ∥
        rewrite ++⁺-cancelˡ′ Ψs Ψs‴
                            (trans (sym eq) eq‴)
                            (trans eql (sym eql‴))
              | O-resp-≈ (suc n) σ′≈δ′                 = Ψs″ , Ψs′ , Δ′ , Γ′ , eq″ , eq′ , eql″ , eql′ , ∘-cong σ≈δ∥ σ′≈δ′∥
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
                                                       , trans eql (sym (O-I _)) , eql′
                                                       , subst (λ δ → _ ⊢s σ ∥ suc n ∘ δ ≈ σ ∥ suc n ∶ _) (sym (I-∥ (O σ (suc n)))) (∘-I ⊢σ∥)
∥-resp-≈ (suc n) (∘-assoc {_} {σ} {_} {_} {σ′} {σ″} ⊢σ ⊢σ′ ⊢σ″) n<l
  with ∥-⊢s (suc n) ⊢σ n<l | O-<-len (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥ | Lσ<l
     with ∥-⊢s (O σ (suc n)) ⊢σ′ Lσ<l
...     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
        , eq₃ , eq₄ , eql₃ , eql₄ , ⊢σ′∥
        with ∥-⊢s (O σ′ (O σ (suc n))) ⊢σ″ (O-<-len (O σ (suc n)) ⊢σ′ Lσ<l)
...        | Ψs₅ , Ψs₆ , Γ₅ , Γ₆
           , eq₅ , eq₆ , eql₅ , eql₆ , ⊢σ″∥
           rewrite ++⁺-cancelˡ′ Ψs₁ Ψs₄
                               (trans (sym eq₁) eq₄)
                               (trans eql₁ (sym eql₄))
                 | ++⁺-cancelˡ′ Ψs₃ Ψs₆
                               (trans (sym eq₃) eq₆)
                               (trans eql₃ (sym eql₆))
                 | ∘-∥ (O σ (suc n)) σ′ σ″             = Ψs₅ , Ψs₂ , Γ₅ , Γ₂ , eq₅ , eq₂ , eql₅ , eql₂ , ∘-assoc ⊢σ∥ ⊢σ′∥ ⊢σ″∥
∥-resp-≈ (suc n) (,-∘ {_} {σ} ⊢σ ⊢T ⊢t ⊢δ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l | ∥-⊢s (O σ (suc n)) ⊢δ (O-<-len (suc n) ⊢σ n<l)
...  | Ψs₁ , Γ ∷ Ψs₂ , Γ₁ , Γ₂
     , eq₁ , refl , eql₁ , eql₂ , ⊢σ∥
     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
     , eq₃ , eq₄ , eql₃ , eql₄ , ⊢δ∥
     rewrite ++⁺-cancelˡ′ Ψs₁ Ψs₄
                         (trans (sym eq₁) eq₄)
                         (trans eql₁ (sym eql₄))       = Ψs₃ , (_ ∷ Γ) ∷ Ψs₂ , Γ₃ , Γ₂ , eq₃ , refl , eql₃ , eql₂ , s-≈-refl (s-∘ ⊢δ∥ ⊢σ∥)
∥-resp-≈ (suc n) (；-∘ {_} {σ} {_} {_} {δ} Ψs ⊢σ ⊢δ ⊢ΨsΓ refl) (s≤s n<l)
  rewrite ∘-∥ n σ (δ ∥ len Ψs) | ∥-+ δ (len Ψs) (O σ n)
  with ∥-⊢s n ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , refl , eq₂ , eql₁ , eql₂ , ⊢σ∥
     with ∥-⊢s′ Ψs ⊢δ
...     | Ψs₃ , Γ₃ , eq₃ , eql₃ , ⊢δ∥
        with ∥-⊢s (O σ n) ⊢δ∥ (O-<-len n ⊢σ n<l)
...        | Ψs₄ , Ψs₅ , Γ₄ , Γ₅
           , refl , eq₅ , eql₄ , eql₅ , ⊢δ∥′
           rewrite ++⁺-cancelˡ′ Ψs₁ Ψs₅ eq₅
                               (trans eql₁ (sym eql₅)) = Ψs₃ ++ Ψs₄ , [] ∷ Ψs₂ , Γ₄ , Γ₂
                                                       , trans eq₃ (sym (++-++⁺ Ψs₃)) , cong ([] ∷⁺_) eq₂
                                                       , trans (length-++ Ψs₃) (trans (cong₂ _+_ eql₃ eql₄) (sym (O-+ δ (len Ψs) (O σ n)))) , cong suc eql₂
                                                       , s-≈-refl (s-∘ ⊢δ∥′ ⊢σ∥)
∥-resp-≈ (suc n) (p-, ⊢σ ⊢T ⊢t) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥                   = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , I-∘ ⊢σ∥
∥-resp-≈ (suc n) (,-ext ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥                   = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , s-≈-sym (I-∘ ⊢σ∥)
∥-resp-≈ (suc n) (；-ext {_} {σ} ⊢σ) n<l
  with ∥-⊢s (suc n) ⊢σ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , ⊢σ∥
     rewrite sym (∥-+ σ 1 n)                           = Ψs₁ , Ψs₂ , Γ₁ , Γ₂ , eq₁ , eq₂ , eql₁ , eql₂ , s-≈-refl ⊢σ∥
∥-resp-≈ (suc n) (s-≈-sym σ≈σ′) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l
...  | Ψs , Ψs′ , Γ₁ , Γ′
     , eq , eq′ , eql , eql′ , σ≈σ′∥                   = Ψs , Ψs′ , Γ₁ , Γ′ , eq , eq′ , trans eql (O-resp-≈ (suc n) σ≈σ′) , eql′ , s-≈-sym σ≈σ′∥
∥-resp-≈ (suc n) (s-≈-trans σ≈σ′ σ′≈σ″) n<l
  with ∥-resp-≈ (suc n) σ≈σ′ n<l | ∥-resp-≈ (suc n) σ′≈σ″ n<l
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , σ≈σ′∥
     | Ψs₃ , Ψs₄ , Γ₃ , Γ₄
     , eq₃ , eq₄ , eql₃ , eql₄ , σ′≈σ″∥
     rewrite O-resp-≈ (suc n) σ≈σ′
           | O-resp-≈ (suc n) σ′≈σ″
           | ++⁺-cancelˡ′ Ψs₁ Ψs₃
                         (trans (sym eq₁) eq₃)
                         (trans eql₁ (sym eql₃))
           | ++⁺-cancelˡ′ Ψs₂ Ψs₄
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
              Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ O σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ≈ σ′ ∥ len Ψs ∶ Δ
∥-resp-≈′ Ψs σ≈σ′
  with ∥-resp-≈ (len Ψs) σ≈σ′ (length-<-++⁺ Ψs)
...  | Ψs₁ , Ψs₂ , Γ₁ , Γ₂
     , eq₁ , eq₂ , eql₁ , eql₂ , σ≈σ′∥
     rewrite ++⁺-cancelˡ′ Ψs Ψs₂ eq₂ (sym eql₂) = Ψs₁ , Γ₁ , eq₁ , eql₁ , σ≈σ′∥
