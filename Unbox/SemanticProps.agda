{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.SemanticProps (fext : Extensionality 0ℓ 0ℓ) where

open import Lib
open import Unbox.Statics
open import Unbox.Semantics
import Unbox.StaticProps as Sₚ

open import Data.Nat.Properties as Nₚ
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)

L-add-ρ : ∀ n m (ρ : Envs) → L ρ (n + m) ≡ L ρ n + L (Tr ρ n) m
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

Tr-ø : ∀ κ κ′ n → Tr (κ ø κ′) n ≡ (Tr κ n ø Tr κ′ (L κ n))
Tr-ø κ κ′ zero                          = refl
Tr-ø κ κ′ (suc n)
  rewrite Tr-+ κ′ (κ 0) (L (Tr κ 1) n)
        | Tr-ø (Tr κ 1) (Tr κ′ (κ 0)) n = refl

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

ins-vone-ø : ∀ n κ → (ins vone n ø κ) ≡ ins (Tr κ n) (L κ n)
ins-vone-ø n κ
  rewrite ins-ø n vone κ
        | vone-ø (Tr κ n) = refl

ins-1-ø-ins-vone : ∀ κ n → (ins κ 1 ø ins vone n) ≡ ins κ n
ins-1-ø-ins-vone κ n
  rewrite ins-ø 1 κ (ins vone n)
        | ø-vone κ
        | +-identityʳ n = refl

ø-assoc : ∀ κ κ′ κ″ → (κ ø κ′ ø κ″) ≡ (κ ø (κ′ ø κ″))
ø-assoc κ κ′ κ″        = fext (helper κ κ′ κ″)
  where helper : ∀ κ κ′ κ″ n → (κ ø κ′ ø κ″) n ≡ (κ ø (κ′ ø κ″)) n
        helper κ κ′ κ″ zero        = sym (L-ø κ′ κ″ (κ 0))
        helper κ κ′ κ″ (suc n)
          rewrite Tr-ø κ′ κ″ (κ 0) = helper (Tr κ 1) (Tr κ′ (κ 0)) (Tr κ″ (L κ′ (κ 0))) n

L-ρ-[] : ∀ (ρ : Envs) (κ : MTrans) n → L (ρ [ κ ]) n ≡ L κ (L ρ n)
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

  ρ-comp : ∀ (ρ : Envs) κ κ′ → ρ [ κ ] [ κ′ ] ≡ ρ [ κ ø κ′ ]
  ρ-comp ρ κ κ′ = fext λ n → ≡×≡⇒≡ (helper n , helper′ n)
    where helper : ∀ n → proj₁ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₁ ((ρ [ κ ø κ′ ]) n)
          helper n
            rewrite Tr-ø κ κ′ (L ρ n)
                  | L-ρ-[] ρ κ n = sym (L-ø (Tr κ (L ρ n)) (Tr κ′ (L κ (L ρ n))) (proj₁ (ρ n)))
          helper′ : ∀ n → proj₂ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₂ ((ρ [ κ ø κ′ ]) n)
          helper′ n
            rewrite Tr-ø κ κ′ (L ρ n)
                  | L-ρ-[] ρ κ n = fext λ m → D-comp (proj₂ (ρ n) m) (Tr κ (L ρ n)) (Tr κ′ (L κ (L ρ n)))

Tr-ρ-[] : ∀ (ρ : Envs) (κ : MTrans) n → Tr (ρ [ κ ]) n ≡ Tr ρ n [ Tr κ (L ρ n) ]
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

unbox-mon-⇐ : ∀ {n} (κ : MTrans) → unbox∙ L κ n , a [ Tr κ n ] ↘ b′ → ∃ λ b → unbox∙ n , a ↘ b
unbox-mon-⇐ {box a} {_} {n} κ (box↘ .(L κ n))        = a [ ins vone n ] , box↘ n
unbox-mon-⇐ {↑ .(□ _) c} {_} {n} κ (unbox∙ .(L κ n)) = unbox′ _ n c , unbox∙ n

mutual

  ap-vone : ∀ (a : D) → a [ vone ] ≡ a
  ap-vone (Λ t ρ)       = cong (Λ t) (ρ-ap-vone ρ)
  ap-vone (box a)
    rewrite vone-stable = cong box (ap-vone a)
  ap-vone (↑ T c)       = cong (↑ T) (Dn-ap-vone c)

  Dn-ap-vone : ∀ (c : Dn) → c [ vone ] ≡ c
  Dn-ap-vone (l x)       = refl
  Dn-ap-vone (c $ d)     = cong₂ _$_ (Dn-ap-vone c) (Df-ap-vone d)
  Dn-ap-vone (unbox k c)
    rewrite L-vone k = cong (unbox k) (Dn-ap-vone c)

  Df-ap-vone : ∀ (d : Df) → d [ vone ] ≡ d
  Df-ap-vone (↓ T a) = cong (↓ T) (ap-vone a)

  ρ-ap-vone : ∀ (ρ : Envs) → ρ [ vone ] ≡ ρ
  ρ-ap-vone ρ = fext helper
    where helper : ∀ n → (ρ [ vone ]) n ≡ ρ n
          helper n = ≡×≡⇒≡ (L-vone (proj₁ (ρ n)) , fext λ m → ap-vone (proj₂ (ρ n) m))

↦-mon : ∀ ρ a (κ : MTrans) → (ρ ↦ a) [ κ ] ≡ (ρ [ κ ] ↦ a [ κ ])
↦-mon ρ a κ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                       ; (suc m) → refl }))
                     ; (suc n) → refl }

ext1-mon-ins : ∀ ρ κ k → ext ρ 1 [ ins κ k ] ≡ ext (ρ [ κ ]) k
ext1-mon-ins ρ κ k = fext λ { 0       → ≡×≡⇒≡ (+-identityʳ _ , refl)
                            ; (suc n) → refl }

ext-mon : ∀ ρ k (κ : MTrans) → ext ρ k [ κ ] ≡ ext (ρ [ Tr κ k ]) (L κ k)
ext-mon ρ k κ = fext λ { 0       → refl
                       ; (suc n) → ≡×≡⇒≡ ( cong (λ κ′ → L κ′ (proj₁ (ρ n))) (fext λ m → cong κ (+-assoc k (L ρ n) m))
                                         , fext λ m → cong (proj₂ (ρ n) m [_]) (fext λ l → cong κ (+-assoc k (L ρ n) l))) }

drop-mon : ∀ ρ (κ : MTrans) → drop ρ [ κ ] ≡ drop (ρ [ κ ])
drop-mon ρ κ = fext λ { 0       → refl
                      ; (suc n) → refl }

drop-↦ : ∀ ρ a → drop (ρ ↦ a) ≡ ρ
drop-↦ ρ a = fext λ { 0       → refl
                    ; (suc n) → refl }

L-drop : ∀ n ρ → L (drop ρ) n ≡ L ρ n
L-drop zero ρ    = refl
L-drop (suc n) ρ = refl

L-↦ : ∀ n ρ a → L (ρ ↦ a) n ≡ L ρ n
L-↦ zero ρ a    = refl
L-↦ (suc n) ρ a = refl

L-ρ-+ : ∀ (ρ : Envs) n m → L ρ (n + m) ≡ L ρ n + L (Tr ρ n) m
L-ρ-+ ρ zero m = refl
L-ρ-+ ρ (suc n) m = trans (cong (proj₁ (ρ 0) +_) (L-ρ-+ (Tr ρ 1) n m))
                          (sym (+-assoc (proj₁ (ρ 0)) (L (Tr ρ 1) n) (L (Tr ρ (suc n)) m)))

L-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → L ρ (L σ n) ≡ L ρ′ n
L-⟦⟧s n ⟦I⟧
  rewrite Sₚ.L-I n          = refl
L-⟦⟧s n (⟦p⟧ {σ} {_} {ρ′} ↘ρ′)
  rewrite Sₚ.L-p n σ
        | L-drop n ρ′       = L-⟦⟧s n ↘ρ′
L-⟦⟧s n (⟦,⟧ {σ} {_} {ρ′} {t} {a} ↘ρ′ ↘a)
  rewrite Sₚ.L-, n σ t
  rewrite L-↦ n ρ′ a        = L-⟦⟧s n ↘ρ′
L-⟦⟧s zero (⟦；⟧ ↘ρ′)       = refl
L-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)
  rewrite L-ρ-+ ρ m (L σ n) = cong (L ρ m +_) (L-⟦⟧s n ↘ρ′)
L-⟦⟧s n (⟦∘⟧ {δ} {_} {_} {σ} ↘ρ′ ↘ρ″)
  rewrite Sₚ.L-∘ n σ δ
        | L-⟦⟧s (L σ n) ↘ρ′ = L-⟦⟧s n ↘ρ″

Tr-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ Tr σ n ⟧s Tr ρ (L σ n) ↘ Tr ρ′ n
Tr-⟦⟧s n ⟦I⟧
  rewrite Sₚ.Tr-I n
        | Sₚ.L-I n                         = ⟦I⟧
Tr-⟦⟧s 0 ↘ρ′                               = ↘ρ′
Tr-⟦⟧s (suc n) (⟦p⟧ ↘ρ′)                   = Tr-⟦⟧s (suc n) ↘ρ′
Tr-⟦⟧s (suc n) (⟦,⟧ ↘ρ′ ↘a)                = Tr-⟦⟧s (suc n) ↘ρ′
Tr-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)  = subst (⟦ Tr σ n ⟧s_↘ Tr ρ′ n) (fext λ l → cong ρ (sym (+-assoc m (L σ n) l))) (Tr-⟦⟧s n ↘ρ′)
Tr-⟦⟧s (suc n) (⟦∘⟧ {σ = σ} ↘ρ′ ↘ρ″)       = ⟦∘⟧ (Tr-⟦⟧s (L σ (suc n)) ↘ρ′) (Tr-⟦⟧s (suc n) ↘ρ″)

↦-drop : ∀ ρ → drop ρ ↦ lookup ρ 0 ≡ ρ
↦-drop ρ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                    ; (suc m) → refl }))
                  ; (suc n) → refl }
