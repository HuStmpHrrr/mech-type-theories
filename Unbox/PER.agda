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

infix 1 _≈_∈_
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

ap-mt : ∀ (κ : MTrans) (f a : D) → Set
ap-mt κ f a = {fa fa′ : D} → f ∙ a ↘ fa → f [ κ ] ∙ a [ κ ] ↘ fa′ → fa′ ≡ fa [ κ ]

record ap-equiv (f a f′ a′ : D) (T : Ty) : Set where
  field
    fa fa′   : D
    ↘fa      : f ∙ a ↘ fa
    ↘fa′     : f′ ∙ a′ ↘ fa′
    faTfa′   : T fa fa′
    minv-fa  : ∀ κ → ap-mt κ f a
    minv-fa′ : ∀ κ → ap-mt κ f′ a′

record unbox-equiv k (a b : D) (T : Ty) : Set where
  field
    ua ub : D
    ↘ua   : unbox∙ k , a ↘ ua
    ↘ub   : unbox∙ k , b ↘ ub
    uaTub : T ua ub


-- interpretation of types to PERs
⟦_⟧T : Typ → Ty
⟦ B ⟧T         = BotT B
⟦ S ⟶ T ⟧T a b = ∀ {a′ b′} (κ : MTrans) → a′ ≈ b′ ∈ ⟦ S ⟧T → ap-equiv (a [ κ ]) a′ (b [ κ ]) b′ ⟦ T ⟧T
⟦ □ T ⟧T a b   = ∀ k (κ : MTrans) → unbox-equiv k (a [ κ ]) (b [ κ ]) ⟦ T ⟧T


-- ⟦ T ⟧ is a PER
⟦⟧-sym : ∀ T → Symmetric ⟦ T ⟧T
⟦⟧-sym B (bne c≈c′)       = bne (Bot-sym c≈c′)
⟦⟧-sym (S ⟶ T) f≈f′ κ a≈b = record
  { fa     = fa′
  ; fa′    = fa
  ; ↘fa    = ↘fa′
  ; ↘fa′   = ↘fa
  ; faTfa′ = ⟦⟧-sym T faTfa′
  ; minv-fa = λ κ′ → minv-fa′ κ′
  ; minv-fa′ = λ κ′ → minv-fa κ′
  }
  where open ap-equiv (f≈f′ κ (⟦⟧-sym S a≈b))
⟦⟧-sym (□ T) a≈b k κ      = record
  { ua    = ub
  ; ub    = ua
  ; ↘ua   = ↘ub
  ; ↘ub   = ↘ua
  ; uaTub = ⟦⟧-sym T uaTub
  }
  where open unbox-equiv (a≈b k κ)

⟦⟧-trans : ∀ T → Transitive ⟦ T ⟧T
⟦⟧-trans B (bne c≈c′) (bne c′≈c″) = bne (Bot-trans c≈c′ c′≈c″)
⟦⟧-trans (S ⟶ T) f≈f′ f≈f″ κ a≈b = record
  { fa       = ae.fa
  ; fa′      = ae′.fa′
  ; ↘fa      = ae.↘fa
  ; ↘fa′     = ae′.↘fa′
  ; faTfa′   = ⟦⟧-trans T ae.faTfa′ (subst (λ a′ → ⟦ T ⟧T a′ _) (ap-det ae′.↘fa ae.↘fa′) ae′.faTfa′)
  ; minv-fa  = ae.minv-fa
  ; minv-fa′ = ae′.minv-fa′
  }
  where module ae  = ap-equiv (f≈f′ κ (⟦⟧-trans S a≈b (⟦⟧-sym S a≈b)))
        module ae′ = ap-equiv (f≈f″ κ a≈b)
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
    { fa       = [ T ] _ $′ ↓ S _
    ; fa′      = [ T ] _ $′ ↓ S _
    ; ↘fa      = $∙ S T _ _
    ; ↘fa′     = $∙ S T _ _
    ; faTfa′   = Bot⊆⟦⟧ T λ ns κ′ → let u , ↘u , ↘u′ = c≈c′ ns (κ ø κ′)
                                        w , ↘w , ↘w′ = ⟦⟧⊆Top S a≈b ns κ′
                                    in u $ w
                                     , R$ ns (subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u) ↘w
                                     , R$ ns (subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u′) ↘w′
    ; minv-fa  = λ { κ′ ($∙ _ _ _ _) ($∙ _ _ _ _) → refl }
    ; minv-fa′ = λ { κ′ ($∙ _ _ _ _) ($∙ _ _ _ _) → refl }
    }
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
    where open ap-equiv (a≈b κ (Bot⊆⟦⟧ S (l∈Bot (sum⁺ ns))))
  ⟦⟧⊆Top (□ T) a≈b ns κ   = let w , ↘w , ↘w′ = ⟦⟧⊆Top T uaTub ns vone
                            in box w
                             , R□ ns ↘ua (subst (Rf ns -_↘ w) (cong (↓ T) (ap-vone _)) ↘w)
                             , R□ ns ↘ub (subst (Rf ns -_↘ w) (cong (↓ T) (ap-vone _)) ↘w′)
    where open unbox-equiv (a≈b 1 κ)


-- the modal internalizes Kripke structure
⟦⟧-mon : ∀ T (κ : MTrans) → a ≈ b ∈ ⟦ T ⟧T → a [ κ ] ≈ b [ κ ] ∈ ⟦ T ⟧T
⟦⟧-mon B κ (bne c≈c′)    = bne λ ns κ′ → let u , ↘u , ↘u′ = c≈c′ ns (κ ø κ′)
                                         in u
                                          , subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u
                                          , subst (Re _ -_↘ _) (sym (Dn-comp _ κ κ′)) ↘u′
⟦⟧-mon {f} {f′} (S ⟶ T) κ f≈f′ κ′ a≈b
  rewrite D-comp f κ κ′
        | D-comp f′ κ κ′ = f≈f′ (κ ø κ′) a≈b
⟦⟧-mon {a} {b} (□ T) κ a≈b k κ′
  rewrite D-comp a κ κ′
        | D-comp b κ κ′  = a≈b k (κ ø κ′)


-- interpretations of contexts and context stacks
⟦_⟧Γ : Env → Ctx → Ctx → Set
⟦ Γ ⟧Γ e e′ = ∀ {n T} → n ∶ T ∈ Γ → e n ≈ e′ n ∈ ⟦ T ⟧T

⟦_⟧Γs : List Env → Ctxs → Ctxs → Set
⟦ [] ⟧Γs ρ ρ′     = ⊤
⟦ Γ ∷ Γs ⟧Γs ρ ρ′ = ⟦ Γ ⟧Γ (proj₂ (ρ 0)) (proj₂ (ρ′ 0))
                  × proj₁ (ρ 0) ≡ proj₁ (ρ′ 0)
                  × ⟦ Γs ⟧Γs (Tr ρ 1) (Tr ρ′ 1)

⟦_⟧Ψ : Envs → Ctxs → Ctxs → Set
⟦ Γ ∷ Γs ⟧Ψ = ⟦ Γ ∷ Γs ⟧Γs

-- basic properties of interpreted context stacks
⟦⟧Γ-sym : ∀ Γ → Symmetric ⟦ Γ ⟧Γ
⟦⟧Γ-sym Γ e≈e′ T∈Γ = ⟦⟧-sym _ (e≈e′ T∈Γ)

⟦⟧Γ-trans : ∀ Γ → Transitive ⟦ Γ ⟧Γ
⟦⟧Γ-trans Γ e≈e′ e′≈e″ T∈Γ = ⟦⟧-trans _ (e≈e′ T∈Γ) (e′≈e″ T∈Γ)

⟦⟧Γ-PER : ∀ Γ → IsPartialEquivalence ⟦ Γ ⟧Γ
⟦⟧Γ-PER Γ = record
  { sym   = ⟦⟧Γ-sym Γ
  ; trans = ⟦⟧Γ-trans Γ
  }

⟦⟧Γs-sym : ∀ Γs → Symmetric ⟦ Γs ⟧Γs
⟦⟧Γs-sym []                        = _
⟦⟧Γs-sym (Γ ∷ Γs) (e≈e′ , eq , tl) = ⟦⟧Γ-sym Γ e≈e′ , sym eq , ⟦⟧Γs-sym Γs tl

⟦⟧Γs-trans : ∀ Γs → Transitive ⟦ Γs ⟧Γs
⟦⟧Γs-trans []                                            = _
⟦⟧Γs-trans (Γ ∷ Γs) (e≈e′ , eq , tl) (e′≈e″ , eq′ , tl′) = ⟦⟧Γ-trans Γ e≈e′ e′≈e″ , trans eq eq′ , ⟦⟧Γs-trans Γs tl tl′

⟦⟧Γs-PER : ∀ Γs → IsPartialEquivalence ⟦ Γs ⟧Γs
⟦⟧Γs-PER Γs = record
  { sym   = ⟦⟧Γs-sym Γs
  ; trans = ⟦⟧Γs-trans Γs
  }

⟦⟧Ψ-sym : ∀ Ψ → Symmetric ⟦ Ψ ⟧Ψ
⟦⟧Ψ-sym (Γ ∷ Γs) {ρ} {ρ′} = ⟦⟧Γs-sym (Γ ∷ Γs) {ρ} {ρ′}

⟦⟧Ψ-trans : ∀ Ψ → Transitive ⟦ Ψ ⟧Ψ
⟦⟧Ψ-trans (Γ ∷ Γs) {ρ} {ρ′} {ρ″} = ⟦⟧Γs-trans (Γ ∷ Γs) {ρ} {ρ′} {ρ″}

⟦⟧Ψ-PER : ∀ Ψ → IsPartialEquivalence ⟦ Ψ ⟧Ψ
⟦⟧Ψ-PER Ψ = record
  { sym   = λ {ρ} {ρ′} → ⟦⟧Ψ-sym Ψ {ρ} {ρ′}
  ; trans = λ {ρ} {ρ′} {ρ″} → ⟦⟧Ψ-trans Ψ {ρ} {ρ′} {ρ″}
  }

⟦⟧Ψ-refl : ∀ Ψ ρ ρ′ → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → ρ ≈ ρ ∈ ⟦ Ψ ⟧Ψ
⟦⟧Ψ-refl Ψ ρ ρ′ ρ≈ρ′ = ⟦⟧Ψ-trans Ψ {ρ} {ρ′} {ρ} ρ≈ρ′ (⟦⟧Ψ-sym Ψ {ρ} {ρ′} ρ≈ρ′)

⟦⟧Γs-L : ∀ n Γs → ρ ≈ ρ′ ∈ ⟦ Γs ⟧Γs → n < len Γs → L ρ n ≡ L ρ′ n
⟦⟧Γs-L zero Γs ρ≈ρ′ n<                           = refl
⟦⟧Γs-L (suc n) (Γ ∷ Γs) (_ , eq , ρ≈ρ′) (s≤s n<) = cong₂ _+_ eq (⟦⟧Γs-L n Γs ρ≈ρ′ n<)

⟦⟧Ψ-L : ∀ ρ ρ′ n → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → n < len Ψ → L ρ n ≡ L ρ′ n
⟦⟧Ψ-L {Γ ∷ Γs} ρ ρ′ n = ⟦⟧Γs-L {ρ} {ρ′} n (Γ ∷ Γs)

⟦⟧Γs-mon : ∀ Γs (κ : MTrans) → ρ ≈ ρ′ ∈ ⟦ Γs ⟧Γs → ρ [ κ ] ≈ ρ′ [ κ ] ∈ ⟦ Γs ⟧Γs
⟦⟧Γs-mon [] κ ρ≈ρ′ = tt
⟦⟧Γs-mon {ρ} {ρ′} (Γ ∷ Γs) κ (e≈e′ , eq , ρ≈ρ′)
 rewrite Tr-ρ-[] ρ κ 1
       | Tr-ρ-[] ρ′ κ 1
       | sym eq    = (λ T∈Γ → ⟦⟧-mon _ κ (e≈e′ T∈Γ)) , refl , ⟦⟧Γs-mon Γs (Tr κ (proj₁ (ρ 0) + 0)) ρ≈ρ′

⟦⟧Ψ-mon : ∀ ρ ρ′ (κ : MTrans) → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → ρ [ κ ] ≈ ρ′ [ κ ] ∈ ⟦ Ψ ⟧Ψ
⟦⟧Ψ-mon {Γ ∷ Γs} ρ ρ′ = ⟦⟧Γs-mon {ρ} {ρ′} (Γ ∷ Γs)

⟦⟧Ψ-Tr : ∀ n → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → n < len Ψ → ∃₂ λ Δs Ψ′ → Ψ ≡ Δs ++⁺ Ψ′ × len Δs ≡ n × (Tr ρ n ≈ Tr ρ′ n ∈ ⟦ Ψ′ ⟧Ψ)
⟦⟧Ψ-Tr {_} {_} {Ψ} zero ρ≈ρ′ n<  = [] , Ψ , refl , refl , ρ≈ρ′
⟦⟧Ψ-Tr {ρ} {ρ′} {Γ ∷ Γ′ ∷ Γs} (suc n) (e≈e′ , eq , ρ≈ρ′) (s≤s n<)
  with ⟦⟧Ψ-Tr {Tr ρ 1} {Tr ρ′ 1} {Γ′ ∷ Γs} n ρ≈ρ′ n<
...  | Δs , Ψ′ , eq′ , eql , rel = Γ ∷ Δs , Ψ′ , cong (Γ ∷_) (cong toList eq′) , cong suc eql , rel

⟦⟧Ψ-L′ : ∀ ρ ρ′ Δs → ρ ≈ ρ′ ∈ ⟦ Δs ++⁺ Ψ ⟧Ψ → L ρ (len Δs) ≡ L ρ′ (len Δs)
⟦⟧Ψ-L′ ρ ρ′ Δs ρ≈ρ′ = ⟦⟧Ψ-L ρ ρ′ (len Δs) ρ≈ρ′ (length-<-++⁺ Δs)

⟦⟧Ψ-Tr′ : ∀ ρ ρ′ Δs → ρ ≈ ρ′ ∈ ⟦ Δs ++⁺ Ψ ⟧Ψ → Tr ρ (len Δs) ≈ Tr ρ′ (len Δs) ∈ ⟦ Ψ ⟧Ψ
⟦⟧Ψ-Tr′ {Ψ} ρ ρ′ Δs ρ≈ρ′
  with ⟦⟧Ψ-Tr {ρ} {ρ′} (len Δs) ρ≈ρ′ (length-<-++⁺ Δs)
...  | Δs′ , Ψ′ , eq , eql , rel
     rewrite ++⁺̂ˡ-cancel Δs Δs′ eq (sym eql) = rel

ctx-↦ : ∀ {Γ Γs} ρ ρ′ → ρ ≈ ρ′ ∈ ⟦ Γ ∷ Γs ⟧Ψ → a ≈ b ∈ ⟦ T ⟧T → ρ ↦ a ≈ ρ′ ↦ b ∈ ⟦ (T ∷ Γ) ∷ Γs ⟧Ψ
ctx-↦ _ _ (e≈e′ , eq , ρ≈ρ′) a≈b = (λ { here → a≈b
                                      ; (there T∈Γ) → e≈e′ T∈Γ })
                                 , eq , ρ≈ρ′

ctx-ext : ∀ ρ ρ′ n → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → ext ρ n ≈ ext ρ′ n ∈ ⟦ [] ∷ toList Ψ ⟧Ψ
ctx-ext ρ ρ′ n ρ≈ρ′ = (λ { () }) , refl , ρ≈ρ′

ctx-drop : ∀ ρ ρ′ → ρ ≈ ρ′ ∈ ⟦ (T ∷ Γ) ∷ Γs ⟧Ψ → drop ρ ≈ drop ρ′ ∈ ⟦ Γ ∷ Γs ⟧Ψ
ctx-drop ρ ρ′ (e≈e′ , eq , ρ≈ρ′) = (λ T∈Γ → e≈e′ (there T∈Γ)) , eq , ρ≈ρ′

-- Definitions of semantic judgments
record ⟦_⟧_≈⟦_⟧_∈_ s ρ t ρ′ T : Set where
  field
    ⟦s⟧    : D
    ⟦t⟧    : D
    ↘⟦s⟧   : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ↘⟦t⟧   : ⟦ t ⟧ ρ′ ↘ ⟦t⟧
    sTt    : ⟦s⟧ ≈ ⟦t⟧ ∈ ⟦ T ⟧T
    minv-s : ∀ (κ : MTrans) → ⟦ s ⟧ ρ [ κ ] ↘ a → a ≡ ⟦s⟧ [ κ ]
    minv-t : ∀ (κ : MTrans) → ⟦ t ⟧ ρ′ [ κ ] ↘ a → a ≡ ⟦t⟧ [ κ ]

module Intp {s ρ u ρ′ T} (r : ⟦ s ⟧ ρ ≈⟦ u ⟧ ρ′ ∈ T) = ⟦_⟧_≈⟦_⟧_∈_ r

record ⟦_⟧_≈⟦_⟧_∈s_ σ ρ τ ρ′ Ψ : Set where
  field
    ⟦σ⟧    : Ctxs
    ⟦τ⟧    : Ctxs
    ↘⟦σ⟧   : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    σΨτ    : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ Ψ ⟧Ψ
    minv-σ : ∀ (κ : MTrans) → ⟦ σ ⟧s ρ [ κ ] ↘ ρ″ → ρ″ ≡ ⟦σ⟧ [ κ ]
    minv-τ : ∀ (κ : MTrans) → ⟦ τ ⟧s ρ′ [ κ ] ↘ ρ″ → ρ″ ≡ ⟦τ⟧ [ κ ]

module Intps {σ ρ τ ρ′ Γ} (r : ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Γ) = ⟦_⟧_≈⟦_⟧_∈s_ r

infix 4 _⊨_≈_∶_ _⊨_∶_  _⊨s_≈_∶_ _⊨s_∶_
_⊨_≈_∶_ : Envs → Exp → Exp → Typ → Set
Ψ ⊨ t ≈ t′ ∶ T = ∀ ρ ρ′ → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → ⟦ t ⟧ ρ ≈⟦ t′ ⟧ ρ′ ∈ T

_⊨_∶_ : Envs → Exp → Typ → Set
Ψ ⊨ t ∶ T = Ψ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Envs → Substs → Substs → Envs → Set
Ψ ⊨s σ ≈ τ ∶ Ψ′ = ∀ ρ ρ′ → ρ ≈ ρ′ ∈ ⟦ Ψ ⟧Ψ → ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Ψ′

_⊨s_∶_ : Envs → Substs → Envs → Set
Ψ ⊨s σ ∶ Ψ′ = Ψ ⊨s σ ≈ σ ∶ Ψ′


-- Semantic judgments

≈-sym′ : Ψ ⊨ t ≈ t′ ∶ T →
         ----------------
         Ψ ⊨ t′ ≈ t ∶ T
≈-sym′ {Ψ} t≈t′ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = ⟦t⟧
  ; ⟦t⟧    = ⟦s⟧
  ; ↘⟦s⟧   = ↘⟦t⟧
  ; ↘⟦t⟧   = ↘⟦s⟧
  ; sTt    = ⟦⟧-sym _ sTt
  ; minv-s = minv-t
  ; minv-t = minv-s
  }
  where open Intp (t≈t′ ρ′ ρ (⟦⟧Ψ-sym _ {ρ} {ρ′} ρ≈ρ′))

≈-trans′ : Ψ ⊨ t ≈ t′ ∶ T →
           Ψ ⊨ t′ ≈ t″ ∶ T →
           -----------------
           Ψ ⊨ t ≈ t″ ∶ T
≈-trans′ {Ψ} {T = T} t≈t′ t′≈t″ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧  = i₁.⟦s⟧
  ; ⟦t⟧  = i₂.⟦t⟧
  ; ↘⟦s⟧ = i₁.↘⟦s⟧
  ; ↘⟦t⟧ = i₂.↘⟦t⟧
  ; sTt  = ⟦⟧-trans _ i₁.sTt (subst (_≈ i₂.⟦t⟧ ∈ ⟦ T ⟧T) (⟦⟧-det i₂.↘⟦s⟧ i₁.↘⟦t⟧) i₂.sTt)
  ; minv-s = i₁.minv-s
  ; minv-t = i₂.minv-t
  }
  where module i₁ = Intp (t≈t′ ρ ρ (⟦⟧Ψ-refl _ ρ ρ′ ρ≈ρ′))
        module i₂ = Intp (t′≈t″ ρ ρ′ ρ≈ρ′)

v-≈′ : ∀ {x} →
       x ∶ T ∈ Γ →
       ----------------------
       Γ ∷ Γs ⊨ v x ≈ v x ∶ T
v-≈′ {x = x} T∈Γ ρ ρ′ (e≈e′ , _) = record
  { ⟦s⟧    = lookup ρ x
  ; ⟦t⟧    = lookup ρ′ x
  ; ↘⟦s⟧   = ⟦v⟧ _
  ; ↘⟦t⟧   = ⟦v⟧ _
  ; sTt    = e≈e′ T∈Γ
  ; minv-s = λ { κ (⟦v⟧ .x) → refl }
  ; minv-t = λ { κ (⟦v⟧ .x) → refl }
  }

Λ-cong′ : (S ∷ Γ) ∷ Γs ⊨ t ≈ t′ ∶ T →
          ---------------------------
          Γ ∷ Γs ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
Λ-cong′ {_} {_} {_} {t} {t′} t≈t′ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = Λ _ _
  ; ⟦t⟧    = Λ _ _
  ; ↘⟦s⟧   = ⟦Λ⟧ _
  ; ↘⟦t⟧   = ⟦Λ⟧ _
  ; sTt    = λ {a} {b} κ a≈b →
             let ρκ,a        = ctx-↦ (ρ [ κ ]) (ρ′ [ κ ]) (⟦⟧Ψ-mon ρ ρ′ κ ρ≈ρ′) a≈b
                 intp        = t≈t′ (ρ [ κ ] ↦ a) (ρ′ [ κ ] ↦ b) ρκ,a
                 module intp = Intp intp
             in record
                { fa       = intp.⟦s⟧
                ; fa′      = intp.⟦t⟧
                ; ↘fa      = Λ∙ intp.↘⟦s⟧
                ; ↘fa′     = Λ∙ intp.↘⟦t⟧
                ; faTfa′   = intp.sTt
                ; minv-fa  = λ { κ′ (Λ∙ ↘fa) (Λ∙ {_} {_} {_} {fa′} ↘fa′) → trans (intp.minv-s κ′ (subst (⟦ t ⟧_↘ fa′) (sym (↦-mon _ _ _)) ↘fa′))
                                                                                 (cong _[ κ′ ] (⟦⟧-det intp.↘⟦s⟧ ↘fa)) }
                ; minv-fa′ = λ { κ′ (Λ∙ ↘fa) (Λ∙ {_} {_} {_} {fa′} ↘fa′) → trans (intp.minv-t κ′ (subst (⟦ t′ ⟧_↘ fa′) (sym (↦-mon _ _ _)) ↘fa′))
                                                                                 (cong _[ κ′ ] (⟦⟧-det intp.↘⟦t⟧ ↘fa)) }
                }
  ; minv-s = λ { κ′ (⟦Λ⟧ .t) → refl }
  ; minv-t = λ { κ′ (⟦Λ⟧ .t′) → refl }
  }

$-cong′ : Ψ ⊨ t ≈ t′ ∶ S ⟶ T →
          Ψ ⊨ s ≈ s′ ∶ S →
          -----------------------
          Ψ ⊨ t $ s ≈ t′ $ s′ ∶ T
$-cong′ t≈t′ s≈s′ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = ae.fa
  ; ⟦t⟧    = ae.fa′
  ; ↘⟦s⟧   = ⟦$⟧ i₁.↘⟦s⟧ i₂.↘⟦s⟧ ae.↘fa
  ; ↘⟦t⟧   = ⟦$⟧ i₁.↘⟦t⟧ i₂.↘⟦t⟧ ae.↘fa′
  ; sTt    = ae.faTfa′
  ; minv-s = λ { κ (⟦$⟧ ↘f′ ↘a′ ↘f′a′) → ae.minv-fa κ ae.↘fa (subst₂ (_∙_↘ _) (i₁.minv-s κ ↘f′) (i₂.minv-s κ ↘a′) ↘f′a′) }
  ; minv-t = λ { κ (⟦$⟧ ↘f′ ↘a′ ↘f′a′) → ae.minv-fa′ κ ae.↘fa′ (subst₂ (_∙_↘ _) (i₁.minv-t κ ↘f′) (i₂.minv-t κ ↘a′) ↘f′a′) }
  }
  where module i₁ = Intp (t≈t′ ρ ρ′ ρ≈ρ′)
        module i₂ = Intp (s≈s′ ρ ρ′ ρ≈ρ′)
        module ae = ap-equiv (subst₂ (λ a b → ap-equiv a _ b _ _) (ap-vone _) (ap-vone _) (i₁.sTt vone i₂.sTt))

box-cong′ : [] ∷⁺ Ψ ⊨ t ≈ t′ ∶ T →
            ------------------------
            Ψ ⊨ box t ≈ box t′ ∶ □ T
box-cong′ {_} {t} {t′} t≈t′ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = box ⟦s⟧
  ; ⟦t⟧    = box ⟦t⟧
  ; ↘⟦s⟧   = ⟦box⟧ ↘⟦s⟧
  ; ↘⟦t⟧   = ⟦box⟧ ↘⟦t⟧
  ; sTt    = λ k κ → record
    { ua    = ⟦s⟧ [ ins κ 1 ] [ ins vone k ]
    ; ub    = ⟦t⟧ [ ins κ 1 ] [ ins vone k ]
    ; ↘ua   = box↘ k
    ; ↘ub   = box↘ k
    ; uaTub = ⟦⟧-mon _ (ins vone k) (⟦⟧-mon _ (ins κ 1) sTt)
    }
  ; minv-s = λ { {box a} κ (⟦box⟧ ↘a) → cong box (minv-s (ins κ 1) (subst (⟦ t ⟧_↘ a) (sym (ext1-mon-ins _ _ 1)) ↘a)) }
  ; minv-t = λ { {box a} κ (⟦box⟧ ↘a) → cong box (minv-t (ins κ 1) (subst (⟦ t′ ⟧_↘ a) (sym (ext1-mon-ins _ _ 1)) ↘a)) }
  }
  where open Intp (t≈t′ (ext ρ 1) (ext ρ′ 1) (ctx-ext ρ ρ′ 1 ρ≈ρ′))

unbox-cong′ : ∀ {n} Γs →
              Ψ ⊨ t ≈ t′ ∶ □ T →
              len Γs ≡ n →
              --------------------------------------
              Γs ++⁺ Ψ ⊨ unbox n t ≈ unbox n t′ ∶ T
unbox-cong′ {_} {t} {t′} {_} {n} Γs t≈t′ refl ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = ua
  ; ⟦t⟧    = ub
  ; ↘⟦s⟧   = ⟦unbox⟧ n ↘⟦s⟧ ↘ua
  ; ↘⟦t⟧   = ⟦unbox⟧ n ↘⟦t⟧ (subst (unbox∙_, ⟦t⟧ ↘ ub) (⟦⟧Ψ-L′ ρ ρ′ Γs ρ≈ρ′) ↘ub)
  ; sTt    = uaTub
  ; minv-s = λ { κ (⟦unbox⟧ {a = a′} .(len Γs) ↘a′ ↘ua′) → sym (unbox-mon κ ↘ua
                                                                          (subst₂ (unbox∙_,_↘ _) (L-ρ-[] ρ κ (len Γs))
                                                                                                 (minv-s (Tr κ (L ρ (len Γs))) (subst (⟦ t ⟧_↘ a′) (Tr-ρ-[] ρ κ (len Γs)) ↘a′))
                                                                                  ↘ua′)) }
  ; minv-t = λ { κ (⟦unbox⟧ {a = a′} .(len Γs) ↘a′ ↘ua′) → sym (unbox-mon κ ↘ub
                                                                          (subst₂ (unbox∙_,_↘ _) (trans (L-ρ-[] ρ′ κ (len Γs)) (cong (L κ) (sym (⟦⟧Ψ-L′ ρ ρ′ Γs ρ≈ρ′))))
                                                                                                 (minv-t (Tr κ (L ρ (len Γs))) (subst (⟦ t′ ⟧_↘ a′) (trans (Tr-ρ-[] ρ′ κ (len Γs))
                                                                                                                                                           (cong (λ n → Tr ρ′ (len Γs) [ Tr κ n ]) (sym (⟦⟧Ψ-L′ ρ ρ′ Γs ρ≈ρ′)))) ↘a′))
                                                                                  ↘ua′)) }
  }
  where open Intp (t≈t′ (Tr ρ n) (Tr ρ′ n) (⟦⟧Ψ-Tr′ ρ ρ′ Γs ρ≈ρ′))
        open unbox-equiv (subst₂ (λ a b → unbox-equiv _ a b _) (ap-vone _) (ap-vone _) (sTt (L ρ n) vone))

[]-cong′ : Ψ ⊨ t ≈ t′ ∶ T →
           Ψ′ ⊨s σ ≈ σ′ ∶ Ψ →
           ------------------------------
           Ψ′ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶ T
[]-cong′ {_} {t} {t′} t≈t′ σ≈σ′ ρ ρ′ ρ≈ρ′ = record
  { ⟦s⟧    = ⟦s⟧
  ; ⟦t⟧    = ⟦t⟧
  ; ↘⟦s⟧   = ⟦[]⟧ ↘⟦σ⟧ ↘⟦s⟧
  ; ↘⟦t⟧   = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
  ; sTt    = sTt
  ; minv-s = λ { κ (⟦[]⟧ ↘ρ″ ↘a) → minv-s κ (subst (⟦ t ⟧_↘ _) (minv-σ κ ↘ρ″) ↘a) }
  ; minv-t = λ { κ (⟦[]⟧ ↘ρ″ ↘a) → minv-t κ (subst (⟦ t′ ⟧_↘ _) (minv-τ κ ↘ρ″) ↘a) }
  }
  where open Intps (σ≈σ′ ρ ρ′ ρ≈ρ′)
        open Intp (t≈t′ ⟦σ⟧ ⟦τ⟧ σΨτ)

s-≈-sym′ : Ψ ⊨s σ ≈ σ′ ∶ Ψ′ →
           ------------------
           Ψ ⊨s σ′ ≈ σ ∶ Ψ′
s-≈-sym′ σ≈σ′ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = ⟦τ⟧
  ; ⟦τ⟧    = ⟦σ⟧
  ; ↘⟦σ⟧   = ↘⟦τ⟧
  ; ↘⟦τ⟧   = ↘⟦σ⟧
  ; σΨτ    = ⟦⟧Ψ-sym _ {⟦σ⟧} {⟦τ⟧} σΨτ
  ; minv-σ = minv-τ
  ; minv-τ = minv-σ
  }
  where open Intps (σ≈σ′ ρ′ ρ (⟦⟧Ψ-sym _ {ρ} {ρ′} ρ≈ρ′))

s-≈-trans′ : Ψ ⊨s σ ≈ σ′ ∶ Ψ′ →
             Ψ ⊨s σ′ ≈ σ″ ∶ Ψ′ →
             --------------------
             Ψ ⊨s σ ≈ σ″ ∶ Ψ′
s-≈-trans′ {Ψ′ = Ψ′} σ≈σ′ σ′≈σ″ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = i₁.⟦σ⟧
  ; ⟦τ⟧    = i₂.⟦τ⟧
  ; ↘⟦σ⟧   = i₁.↘⟦σ⟧
  ; ↘⟦τ⟧   = i₂.↘⟦τ⟧
  ; σΨτ    = ⟦⟧Ψ-trans _ {i₁.⟦σ⟧} {i₁.⟦τ⟧} {i₂.⟦τ⟧} i₁.σΨτ (subst (_≈ i₂.⟦τ⟧ ∈ ⟦ Ψ′ ⟧Ψ) (⟦⟧s-det i₂.↘⟦σ⟧ i₁.↘⟦τ⟧) i₂.σΨτ)
  ; minv-σ = i₁.minv-σ
  ; minv-τ = i₂.minv-τ
  }
  where module i₁ = Intps (σ≈σ′ ρ ρ (⟦⟧Ψ-refl _ ρ ρ′ ρ≈ρ′))
        module i₂ = Intps (σ′≈σ″ ρ ρ′ ρ≈ρ′)

I-≈′ : Ψ ⊨s I ≈ I ∶ Ψ
I-≈′ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = ρ
  ; ⟦τ⟧    = ρ′
  ; ↘⟦σ⟧   = ⟦I⟧
  ; ↘⟦τ⟧   = ⟦I⟧
  ; σΨτ    = ρ≈ρ′
  ; minv-σ = λ { κ ⟦I⟧ → refl }
  ; minv-τ = λ { κ ⟦I⟧ → refl }
  }

p-cong′ : Ψ ⊨s σ ≈ σ′ ∶ (T ∷ Γ) ∷ Γs →
          ----------------------------
          Ψ ⊨s p σ ≈ p σ′ ∶ Γ ∷ Γs
p-cong′ σ≈σ′ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = drop ⟦σ⟧
  ; ⟦τ⟧    = drop ⟦τ⟧
  ; ↘⟦σ⟧   = ⟦p⟧ ↘⟦σ⟧
  ; ↘⟦τ⟧   = ⟦p⟧ ↘⟦τ⟧
  ; σΨτ    = ctx-drop ⟦σ⟧ ⟦τ⟧ σΨτ
  ; minv-σ = λ { κ (⟦p⟧ ↘ρ″) → trans (cong drop (minv-σ κ ↘ρ″)) (sym (drop-mon _ κ)) }
  ; minv-τ = λ { κ (⟦p⟧ ↘ρ″) → trans (cong drop (minv-τ κ ↘ρ″)) (sym (drop-mon _ κ)) }
  }
  where open Intps (σ≈σ′ ρ ρ′ ρ≈ρ′)

,-cong′ : Ψ ⊨s σ ≈ σ′ ∶ Γ ∷ Γs →
          Ψ ⊨ t ≈ t′ ∶ T →
          -----------------------------------
          Ψ ⊨s σ , t ≈ σ′ , t′ ∶ (T ∷ Γ) ∷ Γs
,-cong′ σ≈σ′ t≈t′ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = ⟦σ⟧ ↦ ⟦s⟧
  ; ⟦τ⟧    = ⟦τ⟧ ↦ ⟦t⟧
  ; ↘⟦σ⟧   = ⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧
  ; ↘⟦τ⟧   = ⟦,⟧ ↘⟦τ⟧ ↘⟦t⟧
  ; σΨτ    = ctx-↦ ⟦σ⟧ ⟦τ⟧ σΨτ sTt
  ; minv-σ = λ { κ (⟦,⟧ ↘ρ″ ↘a) → trans (cong₂ _↦_ (minv-σ κ ↘ρ″) (minv-s κ ↘a)) (sym (↦-mon _ _ κ)) }
  ; minv-τ = λ { κ (⟦,⟧ ↘ρ″ ↘a) → trans (cong₂ _↦_ (minv-τ κ ↘ρ″) (minv-t κ ↘a)) (sym (↦-mon _ _ κ)) }
  }
  where open Intps (σ≈σ′ ρ ρ′ ρ≈ρ′)
        open Intp (t≈t′ ρ ρ′ ρ≈ρ′)

；-cong′ : ∀ {n} Γs →
          Ψ ⊨s σ ≈ σ′ ∶ Ψ′ →
          len Γs ≡ n →
          --------------------------------------
          Γs ++⁺ Ψ ⊨s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Ψ′
；-cong′ {_} {σ} {σ′} {Ψ′} {n = n} Γs σ≈σ′ refl ρ ρ′ ρ≈ρ′ = record
   { ⟦σ⟧    = ext ⟦σ⟧ (L ρ n)
   ; ⟦τ⟧    = ext ⟦τ⟧ (L ρ′ n)
   ; ↘⟦σ⟧   = ⟦；⟧ ↘⟦σ⟧
   ; ↘⟦τ⟧   = ⟦；⟧ ↘⟦τ⟧
   ; σΨτ    = subst (λ m → ext ⟦σ⟧ (L ρ n) ≈ ext ⟦τ⟧ m ∈ ⟦ [] ∷⁺ Ψ′ ⟧Ψ) (⟦⟧Ψ-L′ ρ ρ′ Γs ρ≈ρ′) (ctx-ext ⟦σ⟧ ⟦τ⟧ (L ρ n) σΨτ)
   ; minv-σ = λ { κ (⟦；⟧ {_} {_} {ρ″} ↘ρ″) → trans (cong (λ ρ″ → ext ρ″ _) (minv-σ (Tr κ (L ρ n)) (subst (⟦ σ ⟧s_↘ ρ″) (Tr-ρ-[] ρ κ n) ↘ρ″)))
                                             (trans (cong (ext _) (L-ρ-[] ρ κ n))
                                                    (sym (ext-mon ⟦σ⟧ (L ρ n) κ))) }
   ; minv-τ = λ { κ (⟦；⟧ {_} {_} {ρ″} ↘ρ″) → trans (cong (λ ρ″ → ext ρ″ _) (minv-τ (Tr κ (L ρ′ n)) (subst (⟦ σ′ ⟧s_↘ ρ″) (Tr-ρ-[] ρ′ κ n) ↘ρ″)))
                                             (trans (cong (ext _) (L-ρ-[] ρ′ κ n))
                                                    (sym (ext-mon ⟦τ⟧ (L ρ′ n) κ))) }
   }
   where open Intps (σ≈σ′ (Tr ρ n) (Tr ρ′ n) (⟦⟧Ψ-Tr′ ρ ρ′ Γs ρ≈ρ′))

∘-cong′ : Ψ ⊨s δ ≈ δ′ ∶ Ψ′ →
          Ψ′ ⊨s σ ≈ σ′ ∶ Ψ″ →
          -------------------------
          Ψ ⊨s σ ∘ δ ≈ σ′ ∘ δ′ ∶ Ψ″
∘-cong′ {σ = σ} {σ′} δ≈δ′ σ≈σ′ ρ ρ′ ρ≈ρ′ = record
  { ⟦σ⟧    = i₂.⟦σ⟧
  ; ⟦τ⟧    = i₂.⟦τ⟧
  ; ↘⟦σ⟧   = ⟦∘⟧ i₁.↘⟦σ⟧ i₂.↘⟦σ⟧
  ; ↘⟦τ⟧   = ⟦∘⟧ i₁.↘⟦τ⟧ i₂.↘⟦τ⟧
  ; σΨτ    = i₂.σΨτ
  ; minv-σ = λ { κ (⟦∘⟧ {ρ″ = ρ‴} ↘ρ″ ↘ρ‴) → i₂.minv-σ κ (subst (⟦ σ ⟧s_↘ ρ‴) (i₁.minv-σ κ ↘ρ″) ↘ρ‴) }
  ; minv-τ = λ { κ (⟦∘⟧ {ρ″ = ρ‴} ↘ρ″ ↘ρ‴) → i₂.minv-τ κ (subst (⟦ σ′ ⟧s_↘ ρ‴) (i₁.minv-τ κ ↘ρ″) ↘ρ‴) }
  }
  where module i₁ = Intps (δ≈δ′ ρ ρ′ ρ≈ρ′)
        module i₂ = Intps (σ≈σ′ i₁.⟦σ⟧ i₁.⟦τ⟧ i₁.σΨτ)
