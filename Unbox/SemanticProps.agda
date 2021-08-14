{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.SemanticProps (fext : Extensionality 0ℓ 0ℓ) where

open import Lib
open import LibNonEmpty
open import Unbox.Statics
open import Unbox.Semantics

open import Data.Nat.Properties as Nₚ
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

L-add-ρ : ∀ n m (ρ : Ctxs) → L ρ (n + m) ≡ L ρ n + L (Tr ρ n) m
L-add-ρ zero m ρ    = refl
L-add-ρ (suc n) m ρ = trans (cong (proj₁ (ρ 0) +_) (L-add-ρ n m (Tr ρ 1)))
                            (sym (+-assoc (proj₁ (ρ 0)) (L (Tr ρ 1) n) (L (Tr ρ (suc n)) m)))

vone-stable : ins vone 1 ≡ vone
vone-stable = fext λ { zero    → refl
                     ; (suc n) → refl }

Tr-vone : ∀ n → Tr vone n ≡ vone
Tr-vone n = fext λ m → refl

L-vone : ∀ n → L vone n ≡ n
L-vone zero    = refl
L-vone (suc n) = cong suc (L-vone n)

ins-ø : ∀ n κ κ′ → (ins κ n ø κ′) ≡ ins (κ ø Tr κ′ n) (L κ′ n)
ins-ø n κ κ′ = fext λ { zero → refl
                      ; (suc m) → refl }

L-+ : ∀ (κ : MTrans) n m → L κ (n + m) ≡ L κ n + L (Tr κ n) m
L-+ κ zero m               = refl
L-+ κ (suc n) m
  rewrite L-+ (Tr κ 1) n m = sym (+-assoc (κ 0) (L (Tr κ 1) n) (L (Tr κ (suc n)) m))

L-ø : ∀ κ κ′ n → L (κ ø κ′) n ≡ L κ′ (L κ n)
L-ø κ κ′ zero                         = refl
L-ø κ κ′ (suc n)
  rewrite L-ø (Tr κ 1) (Tr κ′ (κ 0)) n
        | L-+ κ′ (κ 0) (L (Tr κ 1) n) = refl

Tr-+ : ∀ (κ : MTrans) n m → Tr κ (n + m) ≡ Tr (Tr κ n) m
Tr-+ κ n m = fext (λ i → cong κ (+-assoc n m i))

ø-+ : ∀ κ κ′ n → Tr (κ ø κ′) n ≡ (Tr κ n ø Tr κ′ (L κ n))
ø-+ κ κ′ zero                          = refl
ø-+ κ κ′ (suc n)
  rewrite Tr-+ κ′ (κ 0) (L (Tr κ 1) n)
        | ø-+ (Tr κ 1) (Tr κ′ (κ 0)) n = refl

Tr-ø : ∀ κ κ′ n → Tr (κ ø κ′) n ≡ (Tr κ n ø Tr κ′ (L κ n))
Tr-ø κ κ′ zero                         = refl
Tr-ø κ κ′ (suc n)
  rewrite Tr-ø (Tr κ 1) (Tr κ′ (L κ 1)) n
        | ø-+ (Tr κ 1) (Tr κ′ (κ 0)) n
        | Tr-+ κ′ (κ 0) (L (Tr κ 1) n) = refl

ø-idx : ∀ κ κ′ n → (κ ø κ′) n ≡ L (Tr κ′ (L κ n)) (κ n)
ø-idx κ κ′ zero    = refl
ø-idx κ κ′ (suc n) = trans (ø-idx (Tr κ 1) (Tr κ′ (κ 0)) n)
                           (cong (λ k → M-L k (κ (suc n))) (fext λ m → cong κ′ (sym (+-assoc (κ 0) (L (Tr κ 1) n) m))))

vone-ø : ∀ κ → (vone ø κ) ≡ κ
vone-ø κ = fext helper
  where helper : ∀ n → (vone ø κ) n ≡ κ n
        helper n
          rewrite ø-idx vone κ n
                | L-vone n
                | +-identityʳ n = +-identityʳ (κ n)

ø-vone : ∀ κ → (κ ø vone) ≡ κ
ø-vone κ = fext helper
  where helper : ∀ n → (κ ø vone) n ≡ κ n
        helper n
          rewrite ø-idx κ vone n = L-vone (κ n)

L-ρ-[] : ∀ (ρ : Ctxs) (κ : MTrans) n → L (ρ [ κ ]) n ≡ L κ (L ρ n)
L-ρ-[] ρ κ zero                                        = refl
L-ρ-[] ρ κ (suc n)
  rewrite L-+ κ (proj₁ (ρ 0)) (L (toMTrans (Tr ρ 1)) n)
        | sym (L-ρ-[] (Tr ρ 1) (Tr κ (proj₁ (ρ 0))) n) = cong (L κ (proj₁ (ρ 0)) +_)
                                                              (cong (λ k → M-L k n) (fext (λ m →
                                                               cong (λ k → M-L k (proj₁ (ρ (suc m)))) (Tr-+ κ (proj₁ (ρ 0)) (L (toMTrans (Tr ρ 1)) m)))))

mutual
  D-comp : ∀ (a : D) κ κ′ → a [ κ ] [ κ′ ] ≡ a [ κ ø κ′ ]
  D-comp (Λ t ρ) κ κ′
    rewrite ρ-comp ρ κ κ′              = refl
  D-comp (box a) κ κ′
    rewrite sym (ins-ø 1 κ (ins κ′ 1)) = cong box (D-comp a (ins κ 1) (ins κ′ 1))
  D-comp (↑ T c) κ κ′                  = cong (↑ T) (Dn-comp c κ κ′)

  Dn-comp : ∀ (c : Dn) κ κ′ → c [ κ ] [ κ′ ] ≡ c [ κ ø κ′ ]
  Dn-comp (l x) κ κ′    = refl
  Dn-comp (c $ d) κ κ′  = cong₂ _$_ (Dn-comp c κ κ′) (Df-comp d κ κ′)
  Dn-comp (unbox n c) κ κ′
    rewrite L-ø κ κ′ n
          | Tr-ø κ κ′ n = cong (unbox (L κ′ (L κ n))) (Dn-comp c (Tr κ n) (Tr κ′ (L κ n)))

  Df-comp : ∀ (d : Df) κ κ′ → d [ κ ] [ κ′ ] ≡ d [ κ ø κ′ ]
  Df-comp (↓ T a) κ κ′ = cong (↓ T) (D-comp a κ κ′)

  ρ-comp : ∀ (ρ : Ctxs) κ κ′ → ρ [ κ ] [ κ′ ] ≡ ρ [ κ ø κ′ ]
  ρ-comp ρ κ κ′ = fext λ n → ≡×≡⇒≡ (helper n , helper′ n)
    where helper : ∀ n → proj₁ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₁ ((ρ [ κ ø κ′ ]) n)
          helper n
            rewrite Tr-ø κ κ′ (L ρ n)
                  | L-ρ-[] ρ κ n = sym (L-ø (Tr κ (L ρ n)) (Tr κ′ (L κ (L ρ n))) (proj₁ (ρ n)))
          helper′ : ∀ n → proj₂ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₂ ((ρ [ κ ø κ′ ]) n)
          helper′ n
            rewrite Tr-ø κ κ′ (L ρ n)
                  | L-ρ-[] ρ κ n = fext λ m → D-comp (proj₂ (ρ n) m) (Tr κ (L ρ n)) (Tr κ′ (L κ (L ρ n)))

Tr-ρ-[] : ∀ (ρ : Ctxs) (κ : MTrans) n → Tr (ρ [ κ ]) n ≡ Tr ρ n [ Tr κ (L ρ n) ]
Tr-ρ-[] ρ κ n = fext λ m → ≡×≡⇒≡ (helper m , helper′ m)
  where helper : ∀ m → proj₁ (Tr (ρ [ κ ]) n m) ≡ proj₁ ((Tr ρ n [ Tr κ (L ρ n) ]) m)
        helper m
          rewrite L-+ (toMTrans ρ) n m = cong (λ k → M-L k (proj₁ (ρ (n + m))))
                                              (fext λ i → cong κ (+-assoc (L ρ n) (L (Tr ρ n) m) i))
        helper′ : ∀ m → proj₂ (Tr (ρ [ κ ]) n m) ≡ proj₂ ((Tr ρ n [ Tr κ (L ρ n) ]) m)
        helper′ m
          rewrite L-+ (toMTrans ρ) n m = fext λ i → cong (mtran (proj₂ (ρ (n + m)) i))
                                                         (fext λ i → cong κ (+-assoc (L ρ n) (L (Tr ρ n) m) i))

unbox-mon : ∀ {n} (κ : MTrans) → unbox∙ n , a ↘ b → unbox∙ L κ n , a [ Tr κ n ] ↘ b′ → b [ κ ] ≡ b′
unbox-mon {box a} κ (box↘ n) (box↘ .(L κ n))
  rewrite D-comp a (ins vone n) κ
        | D-comp a (ins (Tr κ n) 1) (ins vone (L κ n))
        | ins-ø n vone κ
        | vone-ø (Tr κ n)
        | ins-ø 1 (Tr κ n) (ins vone (L κ n))
        | ø-vone (Tr κ n)
        | +-identityʳ (L κ n)            = refl
unbox-mon κ (unbox∙ n) (unbox∙ .(L κ n)) = refl

unbox-mon-⇒ : ∀ {n} (κ : MTrans) → unbox∙ n , a ↘ b → unbox∙ L κ n , a [ Tr κ n ] ↘ b [ κ ]
unbox-mon-⇒ {_} {_} {n} κ ↘b = let b′ , ↘b′ = helper κ ↘b
                               in subst (unbox∙ L κ n , _ [ Tr κ _ ] ↘_) (sym (unbox-mon κ ↘b ↘b′)) ↘b′
  where helper : ∀ {n} (κ : MTrans) → unbox∙ n , a ↘ b → ∃ λ b′ → unbox∙ L κ n , a [ Tr κ n ] ↘ b′
        helper {box a} κ (box↘ n)       = mtran (mtran a (ins (Tr κ n) 1)) (ins vone (L κ n))
                                        , box↘ (L κ n)
        helper {↑ (□ T) c} κ (unbox∙ n) = unbox′ T (L κ n) (mtran-c c (Tr κ n)) , unbox∙ (L κ n)

