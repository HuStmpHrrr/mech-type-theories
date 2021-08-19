{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module Unbox.PER (fext : Extensionality 0ℓ 0ℓ) where

open import Lib
open import LibNonEmpty
open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.SemanticProps fext

open import Relation.Binary
  using ( Rel
        ; IsPartialEquivalence
        ; PartialSetoid
        ; Symmetric
        ; Transitive)

Ty : Set₁
Ty = Rel D _

Evs : Set₁
Evs = Rel Ctxs _

_≈_∈_ : ∀ {i} {A : Set i} → A → A → Rel A i → Set i
a ≈ b ∈ P = P a b

Bot : Dn → Dn → Set
Bot c c′ = ∀ ns (κ : MTrans) → ∃ λ u → Re ns - c [ κ ] ↘ u × Re ns - c′ [ κ ] ↘ u

Top : Df → Df → Set
Top d d′ = ∀ ns (κ : MTrans) → ∃ λ w → Rf ns - d [ κ ] ↘ w × Rf ns - d′ [ κ ] ↘ w

-- Bot is a PER
Bot-sym : Symmetric Bot
Bot-sym ⊥ ns κ
  with ⊥ ns κ
...  | u , ↘u , ↘u′ = u , ↘u′ , ↘u

Bot-trans : Transitive Bot
Bot-trans ⊥₁ ⊥₂ ns κ
  with ⊥₁ ns κ | ⊥₂ ns κ
...  | u , ↘u , ↘u′ | u′ , ↘u₁ , ↘u₂
  rewrite Re-det ↘u′ ↘u₁ = u′ , ↘u , ↘u₂

BotIsPER : IsPartialEquivalence Bot
BotIsPER = record
  { sym   = Bot-sym
  ; trans = Bot-trans
  }

-- Top is a PER
Top-sym : Symmetric Top
Top-sym ⊤ ns κ
  with ⊤ ns κ
...  | w , ↘w , ↘w′ = w , ↘w′ , ↘w

Top-trans : Transitive Top
Top-trans ⊤₁ ⊤₂ ns κ
  with ⊤₁ ns κ | ⊤₂ ns κ
...  | w , ↘w , ↘w′ | w′ , ↘w₁ , ↘w₂
  rewrite Rf-det ↘w′ ↘w₁ = w′ , ↘w , ↘w₂

TopIsPER : IsPartialEquivalence Top
TopIsPER = record
  { sym   = Top-sym
  ; trans = Top-trans
  }

-- Setup for interpreting types
data BotT T : Ty where
  bne : c ≈ c′ ∈ Bot → ↑ T c ≈ ↑ T c′ ∈ BotT T

record ap-equiv (f a f′ a′ : D) (T : Ty) : Set where
  field
    fa fa′ : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    faTfa′ : T fa fa′

ap-mt : ∀ (κ : MTrans) (f a : D) → Set
ap-mt κ f a = {fa fa′ : D} → f ∙ a ↘ fa → f [ κ ] ∙ a [ κ ] ↘ fa′ → fa′ ≡ fa [ κ ]

record unbox-equiv k (a b : D) (T : Ty) : Set where
  field
    ua ub : D
    ↘ua   : unbox∙ k , a ↘ ua
    ↘ub   : unbox∙ k , b ↘ ub
    uaTub : T ua ub


-- interpretation of types to PERs
⟦_⟧T : Typ → Ty
⟦ B ⟧T         = BotT B
⟦ S ⟶ T ⟧T a b = ∀ {a′ b′} κ → a′ ≈ b′ ∈ ⟦ S ⟧T → ap-equiv (a [ κ ]) a′ (b [ κ ]) b′ ⟦ T ⟧T × ap-mt κ a a′ × ap-mt κ b b′
⟦ □ T ⟧T a b   = ∀ k (κ : MTrans) → unbox-equiv k (a [ κ ]) (b [ κ ]) ⟦ T ⟧T


-- ⟦ T ⟧ is a PER
⟦⟧-sym : ∀ T → Symmetric ⟦ T ⟧T
⟦⟧-sym B (bne c≈c′)  = bne (Bot-sym c≈c′)
⟦⟧-sym (S ⟶ T) f≈f′ κ a≈b
  with f≈f′ κ (⟦⟧-sym S a≈b)
...  | ae , am , am′ = record
                       { fa     = fa′
                       ; fa′    = fa
                       ; ↘fa    = ↘fa′
                       ; ↘fa′   = ↘fa
                       ; faTfa′ = ⟦⟧-sym T faTfa′
                       }
                     , am′ , am
  where open ap-equiv ae
⟦⟧-sym (□ T) a≈b k κ = record
  { ua    = ub
  ; ub    = ua
  ; ↘ua   = ↘ub
  ; ↘ub   = ↘ua
  ; uaTub = ⟦⟧-sym T uaTub
  }
  where open unbox-equiv (a≈b k κ)

⟦⟧-trans : ∀ T → Transitive ⟦ T ⟧T
⟦⟧-trans B (bne c≈c′) (bne c′≈c″)  = bne (Bot-trans c≈c′ c′≈c″)
⟦⟧-trans (S ⟶ T) f≈f′ f≈f″ κ a≈b
  with f≈f′ κ (⟦⟧-trans S a≈b (⟦⟧-sym S a≈b)) | f≈f″ κ a≈b
...  | ae , am , _ | ae′ , _ , am′ = record
                                     { fa     = ae.fa
                                     ; fa′    = ae′.fa′
                                     ; ↘fa    = ae.↘fa
                                     ; ↘fa′   = ae′.↘fa′
                                     ; faTfa′ = ⟦⟧-trans T ae.faTfa′ (subst (λ a′ → ⟦ T ⟧T a′ _) (ap-det ae′.↘fa ae.↘fa′) ae′.faTfa′)
                                     }
                                   , am , am′
  where module ae  = ap-equiv ae
        module ae′ = ap-equiv ae′
⟦⟧-trans (□ T) a≈a′ a′≈a″ k κ      = record
  { ua    = ue.ua
  ; ub    = ue′.ub
  ; ↘ua   = ue.↘ua
  ; ↘ub   = ue′.↘ub
  ; uaTub = ⟦⟧-trans T ue.uaTub (subst (λ a′ → ⟦ T ⟧T a′ _) (unbox-det ue′.↘ua ue.↘ub) ue′.uaTub)
  }
  where module ue  = unbox-equiv (a≈a′ k κ)
        module ue′ = unbox-equiv (a′≈a″ k κ)

⟦⟧-PER : ∀ T → IsPartialEquivalence ⟦ T ⟧T
⟦⟧-PER T = record
  { sym   = ⟦⟧-sym T
  ; trans = ⟦⟧-trans T
  }

⟦⟧-refl : ∀ T → a ≈ b ∈ ⟦ T ⟧T → a ≈ a ∈ ⟦ T ⟧T
⟦⟧-refl T a≈b = ⟦⟧-trans T a≈b (⟦⟧-sym T a≈b)


-- ⟦ T ⟧ is realizable
l∈Bot : ∀ x → l x ≈ l x ∈ Bot
l∈Bot x ns κ = v (sum⁺ ns ∸ x ∸ 1) , Rl ns x , Rl ns x

mutual

  Bot⊆⟦⟧ : ∀ T → c ≈ c′ ∈ Bot → ↑ T c ≈ ↑ T c′ ∈ ⟦ T ⟧T
  Bot⊆⟦⟧ B c≈c′             = bne c≈c′
  Bot⊆⟦⟧ (S ⟶ T) c≈c′ κ a≈b = record
                              { fa     = [ T ] _ $′ ↓ S _
                              ; fa′    = [ T ] _ $′ ↓ S _
                              ; ↘fa    = $∙ S T _ _
                              ; ↘fa′   = $∙ S T _ _
                              ; faTfa′ = Bot⊆⟦⟧ T λ ns κ′ → let u , ↘u , ↘u′ = c≈c′ ns (κ ø κ′)
                                                                w , ↘w , ↘w′ = ⟦⟧⊆Top S a≈b ns κ′
                                                            in u $ w
                                                             , R$ ns (subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u) ↘w
                                                             , R$ ns (subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u′) ↘w′
                              }
                            , (λ { ($∙ _ _ _ _) ($∙ _ _ _ _) → refl })
                            , λ { ($∙ _ _ _ _) ($∙ _ _ _ _) → refl }
  Bot⊆⟦⟧ (□ T) c≈c′ k κ     = record
    { ua    = unbox′ T k (mtran-c _ κ)
    ; ub    = unbox′ T k (mtran-c _ κ)
    ; ↘ua   = unbox∙ k
    ; ↘ub   = unbox∙ k
    ; uaTub = Bot⊆⟦⟧ T λ ns κ′ → let u , ↘u , ↘u′ = c≈c′ (truncate ns (L κ′ k)) (κ ø Tr κ′ k)
                                 in unbox (L κ′ k) u
                                  , Ru ns (L κ′ k) (subst (Re _ -_↘ _) (sym (Dn-comp _ κ (Tr κ′ k))) ↘u)
                                  , Ru ns (L κ′ k) (subst (Re _ -_↘ _) (sym (Dn-comp _ κ (Tr κ′ k))) ↘u′)
    }

  ⟦⟧⊆Top : ∀ T → a ≈ b ∈ ⟦ T ⟧T → ↓ T a ≈ ↓ T b ∈ Top
  ⟦⟧⊆Top B (bne c≈c′) ns κ
    with c≈c′ ns κ
  ...  | u , ↘u , ↘u′     = ne u , Rne ns ↘u , Rne ns ↘u′
  ⟦⟧⊆Top (S ⟶ T) a≈b ns κ = let w , ↘w , ↘w′ = ⟦⟧⊆Top T faTfa′ (inc ns) vone
                            in Λ w
                             , RΛ ns ↘fa (subst (λ a′ → Rf inc ns - ↓ T a′ ↘ w) (ap-vone _) ↘w)
                             , RΛ ns ↘fa′ (subst (λ a′ → Rf inc ns - ↓ T a′ ↘ w) (ap-vone _) ↘w′)
    where open ap-equiv (proj₁ (a≈b κ (Bot⊆⟦⟧ S (l∈Bot (sum⁺ ns)))))
  ⟦⟧⊆Top (□ T) a≈b ns κ   = let w , ↘w , ↘w′ = ⟦⟧⊆Top T uaTub ns vone
                            in box w
                             , R□ ns ↘ua (subst (Rf ns -_↘ w) (cong (↓ T) (ap-vone _)) ↘w)
                             , R□ ns ↘ub (subst (Rf ns -_↘ w) (cong (↓ T) (ap-vone _)) ↘w′)
    where open unbox-equiv (a≈b 1 κ)
