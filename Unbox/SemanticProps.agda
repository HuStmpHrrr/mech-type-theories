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

O-add-ρ : ∀ n m (ρ : Envs) → O ρ (n + m) ≡ O ρ n + O (Tr ρ n) m
O-add-ρ zero m ρ    = refl
O-add-ρ (suc n) m ρ = trans (cong (proj₁ (ρ 0) +_) (O-add-ρ n m (Tr ρ 1)))
                            (sym (+-assoc (proj₁ (ρ 0)) (O (Tr ρ 1) n) (O (Tr ρ (suc n)) m)))

vone-stable : ins vone 1 ≡ vone
vone-stable = fext λ { zero    → refl
                     ; (suc n) → refl }

Tr-vone : ∀ n → Tr vone n ≡ vone
Tr-vone n = fext λ m → refl

O-vone : ∀ n → O vone n ≡ n
O-vone zero    = refl
O-vone (suc n) = cong suc (O-vone n)

ins-ø : ∀ n κ κ′ → (ins κ n ø κ′) ≡ ins (κ ø Tr κ′ n) (O κ′ n)
ins-ø n κ κ′ = fext λ { zero → refl
                      ; (suc m) → refl }

O-+ : ∀ (κ : UMoT) n m → O κ (n + m) ≡ O κ n + O (Tr κ n) m
O-+ κ zero m               = refl
O-+ κ (suc n) m
  rewrite O-+ (Tr κ 1) n m = sym (+-assoc (κ 0) (O (Tr κ 1) n) (O (Tr κ (suc n)) m))

O-ø : ∀ κ κ′ n → O (κ ø κ′) n ≡ O κ′ (O κ n)
O-ø κ κ′ zero                         = refl
O-ø κ κ′ (suc n)
  rewrite O-ø (Tr κ 1) (Tr κ′ (κ 0)) n
        | O-+ κ′ (κ 0) (O (Tr κ 1) n) = refl

Tr-+ : ∀ (κ : UMoT) n m → Tr κ (n + m) ≡ Tr (Tr κ n) m
Tr-+ κ n m = fext (λ i → cong κ (+-assoc n m i))

Tr-ø : ∀ κ κ′ n → Tr (κ ø κ′) n ≡ (Tr κ n ø Tr κ′ (O κ n))
Tr-ø κ κ′ zero                          = refl
Tr-ø κ κ′ (suc n)
  rewrite Tr-+ κ′ (κ 0) (O (Tr κ 1) n)
        | Tr-ø (Tr κ 1) (Tr κ′ (κ 0)) n = refl

ø-idx : ∀ κ κ′ n → (κ ø κ′) n ≡ O (Tr κ′ (O κ n)) (κ n)
ø-idx κ κ′ zero    = refl
ø-idx κ κ′ (suc n) = trans (ø-idx (Tr κ 1) (Tr κ′ (κ 0)) n)
                           (cong (λ k → O k (κ (suc n))) (fext λ m → cong κ′ (sym (+-assoc (κ 0) (O (Tr κ 1) n) m))))

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

ins-vone-ø : ∀ n κ → (ins vone n ø κ) ≡ ins (Tr κ n) (O κ n)
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
        helper κ κ′ κ″ zero        = sym (O-ø κ′ κ″ (κ 0))
        helper κ κ′ κ″ (suc n)
          rewrite Tr-ø κ′ κ″ (κ 0) = helper (Tr κ 1) (Tr κ′ (κ 0)) (Tr κ″ (O κ′ (κ 0))) n

O-ρ-[] : ∀ (ρ : Envs) (κ : UMoT) n → O (ρ [ κ ]) n ≡ O κ (O ρ n)
O-ρ-[] ρ κ zero                                        = refl
O-ρ-[] ρ κ (suc n)
  rewrite O-+ κ (proj₁ (ρ 0)) (O (toUMoT (Tr ρ 1)) n)
        | sym (O-ρ-[] (Tr ρ 1) (Tr κ (proj₁ (ρ 0))) n) = cong (O κ (proj₁ (ρ 0)) +_)
                                                              (cong (λ k → O k n) (fext (λ m →
                                                               cong (λ k → O k (proj₁ (ρ (suc m)))) (Tr-+ κ (proj₁ (ρ 0)) (O (toUMoT (Tr ρ 1)) m)))))

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
    rewrite O-ø κ κ′ n
          | Tr-ø κ κ′ n = cong (unbox (O κ′ (O κ n))) (Dn-comp c (Tr κ n) (Tr κ′ (O κ n)))

  Df-comp : ∀ (d : Df) κ κ′ → d [ κ ] [ κ′ ] ≡ d [ κ ø κ′ ]
  Df-comp (↓ T a) κ κ′ = cong (↓ T) (D-comp a κ κ′)

  ρ-comp : ∀ (ρ : Envs) κ κ′ → ρ [ κ ] [ κ′ ] ≡ ρ [ κ ø κ′ ]
  ρ-comp ρ κ κ′ = fext λ n → ≡×≡⇒≡ (helper n , helper′ n)
    where helper : ∀ n → proj₁ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₁ ((ρ [ κ ø κ′ ]) n)
          helper n
            rewrite Tr-ø κ κ′ (O ρ n)
                  | O-ρ-[] ρ κ n = sym (O-ø (Tr κ (O ρ n)) (Tr κ′ (O κ (O ρ n))) (proj₁ (ρ n)))
          helper′ : ∀ n → proj₂ ((ρ [ κ ] [ κ′ ]) n) ≡ proj₂ ((ρ [ κ ø κ′ ]) n)
          helper′ n
            rewrite Tr-ø κ κ′ (O ρ n)
                  | O-ρ-[] ρ κ n = fext λ m → D-comp (proj₂ (ρ n) m) (Tr κ (O ρ n)) (Tr κ′ (O κ (O ρ n)))

Tr-ρ-[] : ∀ (ρ : Envs) (κ : UMoT) n → Tr (ρ [ κ ]) n ≡ Tr ρ n [ Tr κ (O ρ n) ]
Tr-ρ-[] ρ κ n = fext λ m → ≡×≡⇒≡ (helper m , helper′ m)
  where helper : ∀ m → proj₁ (Tr (ρ [ κ ]) n m) ≡ proj₁ ((Tr ρ n [ Tr κ (O ρ n) ]) m)
        helper m
          rewrite O-+ (toUMoT ρ) n m = cong (λ k → O k (proj₁ (ρ (n + m))))
                                              (fext λ i → cong κ (+-assoc (O ρ n) (O (Tr ρ n) m) i))
        helper′ : ∀ m → proj₂ (Tr (ρ [ κ ]) n m) ≡ proj₂ ((Tr ρ n [ Tr κ (O ρ n) ]) m)
        helper′ m
          rewrite O-+ (toUMoT ρ) n m = fext λ i → cong (mtran (proj₂ (ρ (n + m)) i))
                                                         (fext λ i → cong κ (+-assoc (O ρ n) (O (Tr ρ n) m) i))

unbox-mon : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → unbox∙ O κ n , a [ Tr κ n ] ↘ b′ → b [ κ ] ≡ b′
unbox-mon {box a} κ (box↘ n) (box↘ .(O κ n))
  rewrite D-comp a (ins vone n) κ
        | D-comp a (ins (Tr κ n) 1) (ins vone (O κ n))
        | ins-ø n vone κ
        | vone-ø (Tr κ n)
        | ins-ø 1 (Tr κ n) (ins vone (O κ n))
        | ø-vone (Tr κ n)
        | +-identityʳ (O κ n)            = refl
unbox-mon κ (unbox∙ n) (unbox∙ .(O κ n)) = refl

unbox-mon-⇒ : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → unbox∙ O κ n , a [ Tr κ n ] ↘ b [ κ ]
unbox-mon-⇒ {_} {_} {n} κ ↘b = let b′ , ↘b′ = helper κ ↘b
                               in subst (unbox∙ O κ n , _ [ Tr κ _ ] ↘_) (sym (unbox-mon κ ↘b ↘b′)) ↘b′
  where helper : ∀ {n} (κ : UMoT) → unbox∙ n , a ↘ b → ∃ λ b′ → unbox∙ O κ n , a [ Tr κ n ] ↘ b′
        helper {box a} κ (box↘ n)       = mtran (mtran a (ins (Tr κ n) 1)) (ins vone (O κ n))
                                        , box↘ (O κ n)
        helper {↑ (□ T) c} κ (unbox∙ n) = unbox′ T (O κ n) (mtran-c c (Tr κ n)) , unbox∙ (O κ n)

unbox-mon-⇐ : ∀ {n} (κ : UMoT) → unbox∙ O κ n , a [ Tr κ n ] ↘ b′ → ∃ λ b → unbox∙ n , a ↘ b
unbox-mon-⇐ {box a} {_} {n} κ (box↘ .(O κ n))        = a [ ins vone n ] , box↘ n
unbox-mon-⇐ {↑ .(□ _) c} {_} {n} κ (unbox∙ .(O κ n)) = unbox′ _ n c , unbox∙ n

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
    rewrite O-vone k = cong (unbox k) (Dn-ap-vone c)

  Df-ap-vone : ∀ (d : Df) → d [ vone ] ≡ d
  Df-ap-vone (↓ T a) = cong (↓ T) (ap-vone a)

  ρ-ap-vone : ∀ (ρ : Envs) → ρ [ vone ] ≡ ρ
  ρ-ap-vone ρ = fext helper
    where helper : ∀ n → (ρ [ vone ]) n ≡ ρ n
          helper n = ≡×≡⇒≡ (O-vone (proj₁ (ρ n)) , fext λ m → ap-vone (proj₂ (ρ n) m))

↦-mon : ∀ ρ a (κ : UMoT) → (ρ ↦ a) [ κ ] ≡ (ρ [ κ ] ↦ a [ κ ])
↦-mon ρ a κ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                       ; (suc m) → refl }))
                     ; (suc n) → refl }

ext1-mon-ins : ∀ ρ κ k → ext ρ 1 [ ins κ k ] ≡ ext (ρ [ κ ]) k
ext1-mon-ins ρ κ k = fext λ { 0       → ≡×≡⇒≡ (+-identityʳ _ , refl)
                            ; (suc n) → refl }

ext-mon : ∀ ρ k (κ : UMoT) → ext ρ k [ κ ] ≡ ext (ρ [ Tr κ k ]) (O κ k)
ext-mon ρ k κ = fext λ { 0       → refl
                       ; (suc n) → ≡×≡⇒≡ ( cong (λ κ′ → O κ′ (proj₁ (ρ n))) (fext λ m → cong κ (+-assoc k (O ρ n) m))
                                         , fext λ m → cong (proj₂ (ρ n) m [_]) (fext λ l → cong κ (+-assoc k (O ρ n) l))) }

drop-mon : ∀ ρ (κ : UMoT) → drop ρ [ κ ] ≡ drop (ρ [ κ ])
drop-mon ρ κ = fext λ { 0       → refl
                      ; (suc n) → refl }

drop-↦ : ∀ ρ a → drop (ρ ↦ a) ≡ ρ
drop-↦ ρ a = fext λ { 0       → refl
                    ; (suc n) → refl }

O-drop : ∀ n ρ → O (drop ρ) n ≡ O ρ n
O-drop zero ρ    = refl
O-drop (suc n) ρ = refl

O-↦ : ∀ n ρ a → O (ρ ↦ a) n ≡ O ρ n
O-↦ zero ρ a    = refl
O-↦ (suc n) ρ a = refl

O-ρ-+ : ∀ (ρ : Envs) n m → O ρ (n + m) ≡ O ρ n + O (Tr ρ n) m
O-ρ-+ ρ zero m = refl
O-ρ-+ ρ (suc n) m = trans (cong (proj₁ (ρ 0) +_) (O-ρ-+ (Tr ρ 1) n m))
                          (sym (+-assoc (proj₁ (ρ 0)) (O (Tr ρ 1) n) (O (Tr ρ (suc n)) m)))

O-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → O ρ (O σ n) ≡ O ρ′ n
O-⟦⟧s n ⟦I⟧
  rewrite Sₚ.O-I n          = refl
O-⟦⟧s n (⟦p⟧ {ρ})
  rewrite Sₚ.O-p n          = sym (O-drop n ρ)
O-⟦⟧s n (⟦,⟧ {σ} {_} {ρ′} {t} {a} ↘ρ′ ↘a)
  rewrite Sₚ.O-, n σ t
  rewrite O-↦ n ρ′ a        = O-⟦⟧s n ↘ρ′
O-⟦⟧s zero (⟦；⟧ ↘ρ′)       = refl
O-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)
  rewrite O-ρ-+ ρ m (O σ n) = cong (O ρ m +_) (O-⟦⟧s n ↘ρ′)
O-⟦⟧s n (⟦∘⟧ {δ} {_} {_} {σ} ↘ρ′ ↘ρ″)
  rewrite Sₚ.O-∘ n σ δ
        | O-⟦⟧s (O σ n) ↘ρ′ = O-⟦⟧s n ↘ρ″

Tr-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ Tr σ n ⟧s Tr ρ (O σ n) ↘ Tr ρ′ n
Tr-⟦⟧s n ⟦I⟧
  rewrite Sₚ.Tr-I n
        | Sₚ.O-I n                         = ⟦I⟧
Tr-⟦⟧s 0 ↘ρ′                               = ↘ρ′
Tr-⟦⟧s (suc n) ⟦p⟧                         = ⟦I⟧
Tr-⟦⟧s (suc n) (⟦,⟧ ↘ρ′ ↘a)                = Tr-⟦⟧s (suc n) ↘ρ′
Tr-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)  = subst (⟦ Tr σ n ⟧s_↘ Tr ρ′ n) (fext λ l → cong ρ (sym (+-assoc m (O σ n) l))) (Tr-⟦⟧s n ↘ρ′)
Tr-⟦⟧s (suc n) (⟦∘⟧ {σ = σ} ↘ρ′ ↘ρ″)       = ⟦∘⟧ (Tr-⟦⟧s (O σ (suc n)) ↘ρ′) (Tr-⟦⟧s (suc n) ↘ρ″)

↦-drop : ∀ ρ → drop ρ ↦ lookup ρ 0 ≡ ρ
↦-drop ρ = fext λ { 0       → ≡×≡⇒≡ (refl , (fext λ { 0       → refl
                                                    ; (suc m) → refl }))
                  ; (suc n) → refl }

mutual
  ⟦⟧-mon : (κ : UMoT) → ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ [ κ ] ↘ a [ κ ]
  ⟦⟧-mon κ (⟦v⟧ n)                                                = ⟦v⟧ n
  ⟦⟧-mon κ (⟦Λ⟧ t)                                                = ⟦Λ⟧ t
  ⟦⟧-mon κ (⟦$⟧ ↘f ↘b ↘a)                                         = ⟦$⟧ (⟦⟧-mon κ ↘f) (⟦⟧-mon κ ↘b) (∙-mon κ ↘a)
  ⟦⟧-mon {box t} {ρ} {box a} κ (⟦box⟧ ↘a)                         = ⟦box⟧ (subst (⟦ t ⟧_↘ a [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (⟦⟧-mon (ins κ 1) ↘a))
  ⟦⟧-mon {unbox .n t} {ρ} {a} κ (⟦unbox⟧ {_} {_} {b} n ↘b unbox↘) = ⟦unbox⟧ n
                                                                            (subst (⟦ t ⟧_↘ b [ Tr κ (O ρ n)]) (sym (Tr-ρ-[] ρ κ n)) (⟦⟧-mon (Tr κ (O ρ n)) ↘b))
                                                                            (subst (unbox∙_, b [ Tr κ (O ρ n) ] ↘ a [ κ ]) (sym (O-ρ-[] ρ κ n)) (unbox-mon-⇒ κ unbox↘))
  ⟦⟧-mon κ (⟦[]⟧ ↘ρ′ ↘a)                                          = ⟦[]⟧ (⟦⟧s-mon κ ↘ρ′) (⟦⟧-mon κ ↘a)

  ⟦⟧s-mon : (κ : UMoT) → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ [ κ ] ↘ ρ′ [ κ ]
  ⟦⟧s-mon κ ⟦I⟧                                  = ⟦I⟧
  ⟦⟧s-mon {_} {ρ} κ ⟦p⟧                          = subst (⟦ p ⟧s ρ [ κ ] ↘_) (sym (drop-mon ρ κ)) ⟦p⟧
  ⟦⟧s-mon {σ , t} {ρ} κ (⟦,⟧ ↘ρ′ ↘a)             = subst (⟦ σ , t ⟧s ρ [ κ ] ↘_) (sym (↦-mon _ _ κ)) (⟦,⟧ (⟦⟧s-mon κ ↘ρ′) (⟦⟧-mon κ ↘a))
  ⟦⟧s-mon {σ ； n} {ρ} κ (⟦；⟧ {_} {_} {ρ′} ↘ρ′) = subst (⟦ σ ； n ⟧s ρ [ κ ] ↘_)
                                                       (trans (cong (ext _) (O-ρ-[] ρ κ n)) (sym (ext-mon ρ′ (O ρ n) κ)))
                                                       (⟦；⟧ (subst (⟦ σ ⟧s_↘ ρ′ [ Tr κ (O ρ n) ]) (sym (Tr-ρ-[] ρ κ n)) (⟦⟧s-mon (Tr κ (O ρ n)) ↘ρ′)))
  ⟦⟧s-mon κ (⟦∘⟧ ↘ρ″ ↘ρ′)                        = ⟦∘⟧ (⟦⟧s-mon κ ↘ρ″) (⟦⟧s-mon κ ↘ρ′)

  ∙-mon : ∀ {fa} → (κ : UMoT) → f ∙ a ↘ fa → f [ κ ] ∙ a [ κ ] ↘ fa [ κ ]
  ∙-mon {_} {a} {fa} κ (Λ∙ {t} {ρ} ↘fa) = Λ∙ (subst (⟦ t ⟧_↘ fa [ κ ]) (↦-mon ρ a κ) (⟦⟧-mon κ ↘fa))
  ∙-mon κ ($∙ S T c a)                  = $∙ S T (c [ κ ]) (a [ κ ])
