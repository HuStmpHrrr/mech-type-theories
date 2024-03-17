{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

-- Various properties of domain-level operations
--
-- This modulke covers properties of domain-level operations including insertion,
-- composition, truncation and truncation offsets.
--
-- This module is one of the root sources that use functional extensionality.
module Mint.Semantics.Properties.Domain (fext : Extensionality 0ℓ 0ℓ) where

open import Data.Nat.Properties as Nₚ
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

open import Lib hiding (lookup)
open import Mint.Statics.Syntax
open import Mint.Semantics.Domain
open import Mint.Semantics.Properties.NoFunExt.Domain public

vone-stable : ins vone 1 ≡ vone
vone-stable = fext λ { zero    → refl
                     ; (suc n) → refl }

vone-∥ : ∀ n → (vone ∥ n) ≡ vone
vone-∥ n = fext λ m → refl

ins-ø : ∀ n κ κ′ → (ins κ n ø κ′) ≡ ins (κ ø κ′ ∥ n) (O κ′ n)
ins-ø n κ κ′ = fext λ { zero → refl
                      ; (suc m) → refl }

∥-+ : ∀ (κ : UMoT) n m → κ ∥ n + m ≡ κ ∥ n ∥ m
∥-+ κ n m = fext (λ i → cong κ (+-assoc n m i))

ø-∥ : ∀ κ κ′ n → (κ ø κ′) ∥ n ≡ (κ ∥ n ø (κ′ ∥ O κ n))
ø-∥ κ κ′ zero                      = refl
ø-∥ κ κ′ (suc n)
  rewrite ∥-+ κ′ (κ 0) (O (κ ∥ 1) n)
        | ø-∥ (κ ∥ 1) (κ′ ∥ κ 0) n = refl

ø-idx : ∀ κ κ′ n → (κ ø κ′) n ≡ O (κ′ ∥ O κ n) (κ n)
ø-idx κ κ′ zero    = refl
ø-idx κ κ′ (suc n) = trans (ø-idx (κ ∥ 1) (κ′ ∥ κ 0) n)
                           (cong (λ k → M-O k (κ (suc n))) (fext λ m → cong κ′ (sym (+-assoc (κ 0) (O (κ ∥ 1) n) m))))

-- monoidal structor of vone and ø
vone-ø : ∀ κ → (vone ø κ) ≡ κ
vone-ø κ = fext helper
  where helper : ∀ n → (vone ø κ) n ≡ κ n
        helper n
          rewrite ø-idx vone κ n
                | O-vone n
                | +-identityʳ n = +-identityʳ (κ n)

ø-vone : ∀ κ → (κ ø vone) ≡ κ
ø-vone κ = fext helper
  where helper : ∀ n → (κ ø vone) n ≡ κ n
        helper n
          rewrite ø-idx κ vone n = O-vone (κ n)

ins-vone-ø : ∀ n κ → (ins vone n ø κ) ≡ ins (κ ∥ n) (O κ n)
ins-vone-ø n κ
  rewrite ins-ø n vone κ
        | vone-ø (κ ∥ n) = refl

ins-1-ø-ins-n : ∀ κ κ′ n → (ins κ 1 ø ins κ′ n) ≡ ins (κ ø κ′) n
ins-1-ø-ins-n κ κ′ n
  rewrite ins-ø 1 κ (ins κ′ n)
        | +-identityʳ n = refl

ins-1-ø-ins-vone : ∀ κ n → (ins κ 1 ø ins vone n) ≡ ins κ n
ins-1-ø-ins-vone κ n
  rewrite ins-1-ø-ins-n κ vone n
        | ø-vone κ = refl

ø-assoc : ∀ κ κ′ κ″ → (κ ø κ′ ø κ″) ≡ (κ ø (κ′ ø κ″))
ø-assoc κ κ′ κ″        = fext (helper κ κ′ κ″)
  where helper : ∀ κ κ′ κ″ n → (κ ø κ′ ø κ″) n ≡ (κ ø (κ′ ø κ″)) n
        helper κ κ′ κ″ zero       = sym (O-ø κ′ κ″ (κ 0))
        helper κ κ′ κ″ (suc n)
          rewrite ø-∥ κ′ κ″ (κ 0) = helper (κ ∥ 1) (κ′ ∥ κ 0) (κ″ ∥ O κ′ (κ 0)) n

-- distributivity of O over UMoT application to an Envs
O-ρ-[] : ∀ (ρ : Envs) (κ : UMoT) n → O (ρ [ κ ]) n ≡ O κ (O ρ n)
O-ρ-[] ρ κ zero                                    = refl
O-ρ-[] ρ κ (suc n)
  rewrite O-+ κ (proj₁ (ρ 0)) (O (ρ ∥ 1) n)
        | sym (O-ρ-[] (ρ ∥ 1) (κ ∥ proj₁ (ρ 0)) n) = cong (O κ (proj₁ (ρ 0)) +_)
                                                          (cong (λ k → M-O k n) (fext (λ m →
                                                            cong (λ k → M-O k (proj₁ (ρ (suc m)))) (∥-+ κ (proj₁ (ρ 0)) (O (ρ ∥ 1) m)))))

-- composition of UMoT application
mutual
  D-comp : ∀ (a : D) κ κ′ → a [ κ ] [ κ′ ] ≡ a [ κ ø κ′ ]
  D-comp N κ κ′                        = refl
  D-comp (□ A) κ κ′
    rewrite sym (ins-ø 1 κ (ins κ′ 1)) = cong □ (D-comp A (ins κ 1) (ins κ′ 1))
  D-comp (Π A t ρ) κ κ′
    rewrite D-comp A κ κ′
          | ρ-comp ρ κ κ′              = refl
  D-comp (U i) κ κ′                    = refl
  D-comp ze κ κ′                       = refl
  D-comp (su a) κ κ′                   = cong su (D-comp a κ κ′)
  D-comp (Λ t ρ) κ κ′
    rewrite ρ-comp ρ κ κ′              = refl
  D-comp (box a) κ κ′
    rewrite sym (ins-ø 1 κ (ins κ′ 1)) = cong box (D-comp a (ins κ 1) (ins κ′ 1))
  D-comp (↑ A c) κ κ′                  = cong₂ ↑ (D-comp A κ κ′) (Dn-comp c κ κ′)

  Dn-comp : ∀ (c : Dn) κ κ′ → c [ κ ] [ κ′ ] ≡ c [ κ ø κ′ ]
  Dn-comp (l x) κ κ′       = refl
  Dn-comp (rec T a t ρ c) κ κ′
    rewrite D-comp a κ κ′
          | ρ-comp ρ κ κ′
          | Dn-comp c κ κ′ = refl
  Dn-comp (c $ d) κ κ′     = cong₂ _$_ (Dn-comp c κ κ′) (Df-comp d κ κ′)
  Dn-comp (unbox n c) κ κ′
    rewrite O-ø κ κ′ n
          | ø-∥ κ κ′ n     = cong (unbox (O κ′ (O κ n))) (Dn-comp c (κ ∥ n) (κ′ ∥ O κ n))

  Df-comp : ∀ (d : Df) κ κ′ → d [ κ ] [ κ′ ] ≡ d [ κ ø κ′ ]
  Df-comp (↓ A a) κ κ′ = cong₂ ↓ (D-comp A κ κ′) (D-comp a κ κ′)

  ρ-comp : ∀ (ρ : Envs) κ κ′ → ρ [ κ ] [ κ′ ] ≡ ρ [ κ ø κ′ ]
  ρ-comp ρ κ κ′ = fext λ n → ≡×≡⇒≡ (helper n , helper′ n)
    where helper : ∀ n → proj₁ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₁ ((ρ [ κ ø κ′ ]) n)
          helper n
            rewrite ø-∥ κ κ′ (O ρ n)
                  | O-ρ-[] ρ κ n = sym (O-ø (κ ∥ O ρ n) (κ′ ∥ O κ (O ρ n)) (proj₁ (ρ n)))
          helper′ : ∀ n → proj₂ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₂ ((ρ [ κ ø κ′ ]) n)
          helper′ n
            rewrite ø-∥ κ κ′ (O ρ n)
                  | O-ρ-[] ρ κ n = fext λ m → D-comp (proj₂ (ρ n) m) (κ ∥ O ρ n) (κ′ ∥ O κ (O ρ n))

-- distributivity of truncation over UMoT application to an Env
ρ-∥-[] : ∀ (ρ : Envs) (κ : UMoT) n → (ρ [ κ ]) ∥ n ≡ ρ ∥ n [ κ ∥ O ρ n ]
ρ-∥-[] ρ κ n = fext λ m → ≡×≡⇒≡ (helper m , helper′ m)
  where helper : ∀ m → proj₁ (((ρ [ κ ]) ∥ n) m) ≡ proj₁ ((ρ ∥ n [ κ ∥ O ρ n ]) m)
        helper m
          rewrite O-+ (toUMoT ρ) n m = cong (λ k → M-O k (proj₁ (ρ (n + m))))
                                             (fext λ i → cong κ (+-assoc (O ρ n) (O (ρ ∥ n) m) i))
        helper′ : ∀ m → proj₂ (((ρ [ κ ]) ∥ n) m) ≡ proj₂ ((ρ ∥ n [ κ ∥ O ρ n ]) m)
        helper′ m
          rewrite O-+ (toUMoT ρ) n m = fext λ i → cong (mtran (proj₂ (ρ (n + m)) i))
                                                        (fext λ i → cong κ (+-assoc (O ρ n) (O (ρ ∥ n) m) i))

-- identity of UMoT application
mutual
  D-ap-vone : ∀ (a : D) → a [ vone ] ≡ a
  D-ap-vone N           = refl
  D-ap-vone (□ A)
    rewrite vone-stable = cong □ (D-ap-vone A)
  D-ap-vone (Π A t ρ)
    rewrite D-ap-vone A
          | ρ-ap-vone ρ = refl
  D-ap-vone (U i)       = refl
  D-ap-vone ze          = refl
  D-ap-vone (su a)      = cong su (D-ap-vone a)
  D-ap-vone (Λ t ρ)     = cong (Λ t) (ρ-ap-vone ρ)
  D-ap-vone (box a)
    rewrite vone-stable = cong box (D-ap-vone a)
  D-ap-vone (↑ A c)     = cong₂ ↑ (D-ap-vone A) (Dn-ap-vone c)

  Dn-ap-vone : ∀ (c : Dn) → c [ vone ] ≡ c
  Dn-ap-vone (l x)       = refl
  Dn-ap-vone (rec T a t ρ c)
    rewrite D-ap-vone a
          | ρ-ap-vone ρ
          | Dn-ap-vone c = refl
  Dn-ap-vone (c $ d)     = cong₂ _$_ (Dn-ap-vone c) (Df-ap-vone d)
  Dn-ap-vone (unbox k c)
    rewrite O-vone k     = cong (unbox k) (Dn-ap-vone c)

  Df-ap-vone : ∀ (d : Df) → d [ vone ] ≡ d
  Df-ap-vone (↓ A a) = cong₂ ↓ (D-ap-vone A) (D-ap-vone a)

  ρ-ap-vone : ∀ (ρ : Envs) → ρ [ vone ] ≡ ρ
  ρ-ap-vone ρ = fext helper
    where helper : ∀ n → (ρ [ vone ]) n ≡ ρ n
          helper n = ≡×≡⇒≡ (O-vone (proj₁ (ρ n)) , fext λ m → D-ap-vone (proj₂ (ρ n) m))

-- monotonicity of various operations
↦-mon : ∀ ρ a (κ : UMoT) → (ρ ↦ a) [ κ ] ≡ ρ [ κ ] ↦ a [ κ ]
↦-mon ρ a κ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                       ; (suc m) → refl }))
                     ; (suc n) → refl }

ext1-mon-ins : ∀ ρ κ k → ext ρ 1 [ ins κ k ] ≡ ext (ρ [ κ ]) k
ext1-mon-ins ρ κ k = fext λ { 0       → ≡×≡⇒≡ (+-identityʳ _ , refl)
                            ; (suc n) → refl }

ext1-mon : ∀ ρ n → ext ρ 1 [ ins vone n ] ≡ ext ρ n
ext1-mon ρ n
  rewrite ext1-mon-ins ρ vone n
        | ρ-ap-vone ρ = refl

ext-mon : ∀ ρ k (κ : UMoT) → ext ρ k [ κ ] ≡ ext (ρ [ κ ∥ k ]) (O κ k)
ext-mon ρ k κ = fext λ { 0       → refl
                       ; (suc n) → ≡×≡⇒≡ ( cong (λ κ′ → O κ′ (proj₁ (ρ n))) (fext λ m → cong κ (+-assoc k (O ρ n) m))
                                         , fext λ m → cong (proj₂ (ρ n) m [_]) (fext λ l → cong κ (+-assoc k (O ρ n) l))) }

drop-mon : ∀ ρ (κ : UMoT) → drop ρ [ κ ] ≡ drop (ρ [ κ ])
drop-mon ρ κ = fext λ { 0       → refl
                      ; (suc n) → refl }

drop-↦ : ∀ ρ a → drop (ρ ↦ a) ≡ ρ
drop-↦ ρ a = fext λ { 0       → refl
                    ; (suc n) → refl }

drop-same : ∀ ρ → drop ρ ↦ lookup ρ 0 ≡ ρ
drop-same ρ = fext λ { zero    → ≡×≡⇒≡ (refl , fext λ { zero → refl
                                                      ; (suc x) → refl })
                     ; (suc n) → refl }

D-ins-ins : ∀ (a : D) κ n → a [ ins κ 1 ] [ ins vone n ] ≡ a [ ins κ n ]
D-ins-ins a κ n = trans (D-comp a (ins κ 1) (ins vone n)) (cong (a [_]) (ins-1-ø-ins-vone κ n))

D-ins-ins′ : ∀ (a : D) κ κ′ n → a [ ins κ 1 ] [ ins κ′ n ] ≡ a [ ins (κ ø κ′) n ]
D-ins-ins′ a κ κ′ n = trans (D-comp a (ins κ 1) (ins κ′ n)) (cong (a [_]) (ins-1-ø-ins-n κ κ′ n))
