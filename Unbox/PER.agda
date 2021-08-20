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
⟦ S ⟶ T ⟧T a b = ∀ {a′ b′} (κ : MTrans) → a′ ≈ b′ ∈ ⟦ S ⟧T → ap-equiv (a [ κ ]) a′ (b [ κ ]) b′ ⟦ T ⟧T × ∀ κ′ → ap-mt κ′ (a [ κ ]) a′ × ap-mt κ′ (b [ κ ]) b′
⟦ □ T ⟧T a b   = ∀ k (κ : MTrans) → unbox-equiv k (a [ κ ]) (b [ κ ]) ⟦ T ⟧T


-- ⟦ T ⟧ is a PER
⟦⟧-sym : ∀ T → Symmetric ⟦ T ⟧T
⟦⟧-sym B (bne c≈c′)  = bne (Bot-sym c≈c′)
⟦⟧-sym (S ⟶ T) f≈f′ κ a≈b
  with f≈f′ κ (⟦⟧-sym S a≈b)
...  | ae , mt       = record
                       { fa     = fa′
                       ; fa′    = fa
                       ; ↘fa    = ↘fa′
                       ; ↘fa′   = ↘fa
                       ; faTfa′ = ⟦⟧-sym T faTfa′
                       }
                     , λ κ′ → let am , am′ = mt κ′ in am′ , am
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
⟦⟧-trans B (bne c≈c′) (bne c′≈c″) = bne (Bot-trans c≈c′ c′≈c″)
⟦⟧-trans (S ⟶ T) f≈f′ f≈f″ κ a≈b
  with f≈f′ κ (⟦⟧-trans S a≈b (⟦⟧-sym S a≈b)) | f≈f″ κ a≈b
...  | ae , mt | ae′ , mt′        = record
                                    { fa     = ae.fa
                                    ; fa′    = ae′.fa′
                                    ; ↘fa    = ae.↘fa
                                    ; ↘fa′   = ae′.↘fa′
                                    ; faTfa′ = ⟦⟧-trans T ae.faTfa′ (subst (λ a′ → ⟦ T ⟧T a′ _) (ap-det ae′.↘fa ae.↘fa′) ae′.faTfa′)
                                    }
                                  , λ κ′ → proj₁ (mt κ′) , proj₂ (mt′ κ′)
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
                            , λ κ′ → (λ { ($∙ _ _ _ _) ($∙ _ _ _ _) → refl })
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


-- Definitions of semantic judgments
record ⟦_⟧_≈⟦_⟧_∈_ s ρ u ρ′ T : Set where
  field
    ⟦s⟧  : D
    ⟦t⟧  : D
    ↘⟦s⟧ : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ↘⟦t⟧ : ⟦ u ⟧ ρ′ ↘ ⟦t⟧
    sTt  : ⟦s⟧ ≈ ⟦t⟧ ∈ ⟦ T ⟧T
    -- minv-s : ∀ (κ : MTrans) → ⟦ s ⟧ ρ [ κ ] ↘ a →

module Intp {s ρ u ρ′ T} (r : ⟦ s ⟧ ρ ≈⟦ u ⟧ ρ′ ∈ T) = ⟦_⟧_≈⟦_⟧_∈_ r

record ⟦_⟧_≈⟦_⟧_∈s_ σ ρ τ ρ′ Ψ : Set where
  field
    ⟦σ⟧  : Ctxs
    ⟦τ⟧  : Ctxs
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦τ⟧ : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    σΨτ  : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ Ψ ⟧Ψ

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


-- -- TODO: important property

-- infix 4 _⊨′_∶_ _⊨s′_∶_
-- mutual
--   data _⊨′_∶_ : Envs → Exp → Typ → Set where
--     vlookup : ∀ {x} →
--               x ∶ T ∈ Γ →
--               ----------------
--               Γ ∷ Γs ⊨′ v x ∶ T
--     ⟶-I     : (S ∷ Γ) ∷ Γs ⊨′ t ∶ T →
--               (S ∷ Γ) ∷ Γs ⊨ t ∶ T →
--               ----------------------
--               Γ ∷ Γs ⊨′ Λ t ∶ S ⟶ T
--     ⟶-E     : Ψ ⊨′ t ∶ S ⟶ T →
--               Ψ ⊨ t ∶ S ⟶ T →
--               Ψ ⊨′ s ∶ S →
--               Ψ ⊨ s ∶ S →
--               -------------
--               Ψ ⊨′ t $ s ∶ T
--     □-I     : [] ∷⁺ Ψ ⊨′ t ∶ T →
--               -----------------
--               Ψ ⊨′ box t ∶ □ T
--     □-E     : ∀ {n} Γs →
--               Ψ ⊨′ t ∶ □ T →
--               len Γs ≡ n →
--               -------------------------
--               Γs ++⁺ Ψ ⊨′ unbox n t ∶ T
--     t[σ]    : Ψ ⊨′ t ∶ T →
--               Ψ′ ⊨s′ σ ∶ Ψ →
--               Ψ′ ⊨s σ ∶ Ψ →
--               ----------------
--               Ψ′ ⊨′ t [ σ ] ∶ T

--   data _⊨s′_∶_ : Envs → Substs → Envs → Set where
--     S-I  : Ψ ⊨s′ I ∶ Ψ
--     S-p  : Ψ ⊨s′ σ ∶ (T ∷ Γ) ∷ Γs →
--            ------------------------
--            Ψ ⊨s′ p σ ∶ Γ ∷ Γs
--     S-,  : Ψ ⊨s′ σ ∶ Γ ∷ Γs →
--            Ψ ⊨′ t ∶ T →
--            --------------------------
--            Ψ ⊨s′ σ , t ∶ (T ∷ Γ) ∷ Γs
--     S-； : ∀ {n} Γs →
--            Ψ ⊨s′ σ ∶ Ψ′ →
--            len Γs ≡ n →
--            -------------------------------
--            Γs ++⁺ Ψ ⊨s′ σ ； n ∶ [] ∷⁺ Ψ′
--     S-∘  : Ψ ⊨s′ δ ∶ Ψ′ →
--            Ψ′ ⊨s′ σ ∶ Ψ″ →
--            -----------------
--            Ψ ⊨s′ σ ∘ δ ∶ Ψ″


-- mutual
--   ⟦⟧-κ-mon : ∀ ρ (κ : MTrans) → Ψ ⊨′ t ∶ T → ρ ≈ ρ ∈ ⟦ Ψ ⟧Ψ → ⟦ t ⟧ ρ [ κ ] ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b [ κ ]
--   ⟦⟧-κ-mon ρ κ (vlookup _) ρ≈ (⟦v⟧ _) (⟦v⟧ _)                            = refl
--   ⟦⟧-κ-mon ρ κ (⟶-I t∶T _) ρ≈ (⟦Λ⟧ _) (⟦Λ⟧ _)                            = refl
--   ⟦⟧-κ-mon ρ κ (⟶-E t∶F sF s∶S sS) ρ≈ (⟦$⟧ ↘f ↘a ↘fa) (⟦$⟧ ↘f′ ↘b ↘f′b)
--     rewrite ⟦⟧-κ-mon ρ κ t∶F ρ≈ ↘f ↘f′
--           | ⟦⟧-κ-mon ρ κ s∶S ρ≈ ↘a ↘b = proj₂ (proj₂ (sF.sTt vone sS.sTt) κ) helper helper′
--     where module sF = Intp (sF ρ ρ ρ≈)
--           module sS = Intp (sS ρ ρ ρ≈)
--           helper : mtran sF.⟦t⟧ vone ∙ sS.⟦t⟧ ↘ _
--           helper
--             rewrite ap-vone sF.⟦t⟧ = subst₂ (_∙_↘ _) (⟦⟧-det ↘f′ sF.↘⟦t⟧) (⟦⟧-det ↘b sS.↘⟦t⟧) ↘f′b
--           helper′ : mtran (mtran sF.⟦t⟧ vone) κ ∙ mtran sS.⟦t⟧ κ ↘ _
--           helper′
--             rewrite ap-vone sF.⟦t⟧ = subst₂ (λ f a → f [ κ ] ∙ a [ κ ] ↘ _) (⟦⟧-det ↘f′ sF.↘⟦t⟧) (⟦⟧-det ↘b sS.↘⟦t⟧) ↘fa
--   ⟦⟧-κ-mon ρ κ (□-I t∶T) ρ≈ (⟦box⟧ ↘a) (⟦box⟧ ↘b)        = cong box (⟦⟧-κ-mon (ext ρ 1) (ins κ 1) t∶T (ctx-ext ρ ρ 1 ρ≈) {!↘a!} ↘b)
--   ⟦⟧-κ-mon ρ κ (□-E Γs t∶T eq) ρ≈ (⟦unbox⟧ n ↘a ↘ub) (⟦unbox⟧ _ ↘b ↘ub′) = {!⟦⟧-κ-mon (Tr κ (L ρ n)) t∶T (⟦⟧Ψ-Tr′ Γs ρ≈) ? ↘b !}
--   ⟦⟧-κ-mon ρ κ (t[σ] t∶T σ∶Ψ′ sem) ρ≈ (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ {_} {_} {ρ″} ↘ρ″ ↘b)
--     rewrite ⟦⟧s-κ-mon ρ κ σ∶Ψ′ ρ≈ ↘ρ′ ↘ρ″ = ⟦⟧-κ-mon ⟦σ⟧ κ t∶T (⟦⟧Ψ-refl _ ⟦σ⟧ ⟦τ⟧ σΨτ) (subst (λ ρ‴ → ⟦ _ ⟧ ρ‴ [ κ ] ↘ _) eq ↘a) (subst (⟦ _ ⟧_↘ _) eq ↘b)
--       where open Intps (sem ρ ρ ρ≈)
--             eq = ⟦⟧s-det ↘ρ″ ↘⟦σ⟧

--   ⟦⟧s-κ-mon : ∀ ρ (κ : MTrans) → Ψ ⊨s′ σ ∶ Ψ′ → ρ ≈ ρ ∈ ⟦ Ψ ⟧Ψ → ⟦ σ ⟧s ρ [ κ ] ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″ [ κ ]
--   ⟦⟧s-κ-mon ρ κ S-I ρ≈ ⟦I⟧ ⟦I⟧ = refl
--   ⟦⟧s-κ-mon ρ κ (S-p σ∶Ψ′) ρ≈ (⟦p⟧ ↘ρ′) (⟦p⟧ ↘ρ″) = trans (cong drop (⟦⟧s-κ-mon _ κ σ∶Ψ′ ρ≈ ↘ρ′ ↘ρ″)) {!!}
--   ⟦⟧s-κ-mon ρ κ (S-, σ∶Ψ′ t∶T) ρ≈ (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
--     rewrite ⟦⟧s-κ-mon ρ κ σ∶Ψ′ ρ≈ ↘ρ′ ↘ρ″
--           | ⟦⟧-κ-mon ρ κ t∶T ρ≈ ↘a ↘b = {!!}
--   ⟦⟧s-κ-mon ρ κ (S-； Γs σ∶Ψ′ x) ρ≈ (⟦；⟧ ↘ρ′) (⟦；⟧ ↘ρ″) = {!!}
--   ⟦⟧s-κ-mon ρ κ (S-∘ σ∶Ψ′ σ∶Ψ′₁) ρ≈ (⟦∘⟧ ↘ρ′ ↘ρ′₁) (⟦∘⟧ ↘ρ″ ↘ρ″₁) = {!!}


-- -- -- mutual
-- -- --   ⟦⟧-κ-mon : Ψ ⊢ t ∶ T → Ψ ⊨ t ∶ T → ρ ≈ ρ ∈ ⟦ Ψ ⟧Ψ → ⟦ t ⟧ ρ [ κ ] ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b [ κ ]
-- -- --   ⟦⟧-κ-mon (vlookup T∈Γ) sem ρ≈ (⟦v⟧ _) (⟦v⟧ _)                      = refl
-- -- --   ⟦⟧-κ-mon (⟶-I t∶T) sem ρ≈ (⟦Λ⟧ _) (⟦Λ⟧ _)                          = refl
-- -- --   ⟦⟧-κ-mon (⟶-E t∶F s∶S) sem ρ≈ (⟦$⟧ ↘f ↘a ↘fa) (⟦$⟧ ↘f′ ↘b ↘f′b)    = {!!}
-- -- --   ⟦⟧-κ-mon (□-I t∶T) sem ρ≈ (⟦box⟧ ↘a) (⟦box⟧ ↘b)                    = {!!}
-- -- --   ⟦⟧-κ-mon (□-E Γs t∶T x) sem ρ≈ (⟦unbox⟧ _ ↘a x₁) (⟦unbox⟧ _ ↘b x₂) = {!!}
-- -- --   ⟦⟧-κ-mon (t[σ] t∶T x) sem ρ≈ (⟦[]⟧ x₁ ↘a) (⟦[]⟧ x₂ ↘b)             = {!!}


-- -- -- Semantic judgments

-- -- ≈-sym′ : Ψ ⊨ t ≈ t′ ∶ T →
-- --          ----------------
-- --          Ψ ⊨ t′ ≈ t ∶ T
-- -- ≈-sym′ {Ψ} t≈t′ {ρ} {ρ′} ρ≈ρ′ = record
-- --   { ⟦s⟧  = ⟦t⟧
-- --   ; ⟦t⟧  = ⟦s⟧
-- --   ; ↘⟦s⟧ = ↘⟦t⟧
-- --   ; ↘⟦t⟧ = ↘⟦s⟧
-- --   ; sTt  = ⟦⟧-sym _ sTt
-- --   }
-- --   where open Intp (t≈t′ {ρ′} {ρ} (⟦⟧Ψ-sym _ {ρ} {ρ′} ρ≈ρ′))


-- -- ≈-trans′ : Ψ ⊨ t ≈ t′ ∶ T →
-- --            Ψ ⊨ t′ ≈ t″ ∶ T →
-- --            -----------------
-- --            Ψ ⊨ t ≈ t″ ∶ T
-- -- ≈-trans′ {Ψ} {T = T} t≈t′ t′≈t″ {ρ} {ρ′} ρ≈ρ′ = record
-- --   { ⟦s⟧  = i₁.⟦s⟧
-- --   ; ⟦t⟧  = i₂.⟦t⟧
-- --   ; ↘⟦s⟧ = i₁.↘⟦s⟧
-- --   ; ↘⟦t⟧ = i₂.↘⟦t⟧
-- --   ; sTt  = ⟦⟧-trans _ i₁.sTt (subst (_≈ i₂.⟦t⟧ ∈ ⟦ T ⟧T) (⟦⟧-det i₂.↘⟦s⟧ i₁.↘⟦t⟧) i₂.sTt)
-- --   }
-- --   where module i₁ = Intp (t≈t′ {ρ} {ρ} (⟦⟧Ψ-refl {ρ} {ρ′} _ ρ≈ρ′))
-- --         module i₂ = Intp (t′≈t″ {ρ} {ρ′} ρ≈ρ′)

-- -- v-≈′ : ∀ {x} →
-- --        x ∶ T ∈ Γ →
-- --        ----------------------
-- --        Γ ∷ Γs ⊨ v x ≈ v x ∶ T
-- -- v-≈′ {x = x} T∈Γ {ρ} {ρ′} (e≈e′ , _) = record
-- --   { ⟦s⟧  = lookup ρ x
-- --   ; ⟦t⟧  = lookup ρ′ x
-- --   ; ↘⟦s⟧ = ⟦v⟧ _
-- --   ; ↘⟦t⟧ = ⟦v⟧ _
-- --   ; sTt  = e≈e′ T∈Γ
-- --   }

-- -- Λ-cong′ : (S ∷ Γ) ∷ Γs ⊨′ t ∶ T →
-- --           (S ∷ Γ) ∷ Γs ⊨′ t′ ∶ T →
-- --           (S ∷ Γ) ∷ Γs ⊨ t ≈ t′ ∶ T →
-- --           ---------------------------
-- --           Γ ∷ Γs ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
-- -- Λ-cong′ t∶T t′∶T t≈t′ {ρ} {ρ′} ρ≈ρ′ = record
-- --   { ⟦s⟧  = Λ _ _
-- --   ; ⟦t⟧  = Λ _ _
-- --   ; ↘⟦s⟧ = ⟦Λ⟧ _
-- --   ; ↘⟦t⟧ = ⟦Λ⟧ _
-- --   ; sTt  = λ {a} {b} κ a≈b → let ρκ,a        = ctx-↦ {ρ [ κ ]} {ρ′ [ κ ]} (⟦⟧Ψ-mon {ρ} {ρ′} κ ρ≈ρ′) a≈b
-- --                                  intp        = t≈t′ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ b} ρκ,a
-- --                                  module intp = Intp intp
-- --                              in record
-- --                                 { fa     = intp.⟦s⟧
-- --                                 ; fa′    = intp.⟦t⟧
-- --                                 ; ↘fa    = Λ∙ intp.↘⟦s⟧
-- --                                 ; ↘fa′   = Λ∙ intp.↘⟦t⟧
-- --                                 ; faTfa′ = intp.sTt
-- --                                 }
-- --                               , λ κ′ → (λ { (Λ∙ ↘fa) (Λ∙ ↘fa′) → ⟦⟧-κ-mon {ρ = ρ [ κ ] ↦ a} κ′ t∶T (⟦⟧Ψ-refl {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ b} _ ρκ,a) {!!} ↘fa })
-- --                                      , λ { (Λ∙ ↘fa) (Λ∙ ↘fa′) → ⟦⟧-κ-mon {ρ = ρ′ [ κ ] ↦ b} κ′ t′∶T (⟦⟧Ψ-refl {ρ′ [ κ ] ↦ b} {ρ [ κ ] ↦ a} _ (⟦⟧Ψ-sym _ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ b} ρκ,a)) {!!} ↘fa }
-- --   }

-- -- -- $-cong     : Ψ ⊨ t ≈ t′ ∶ S ⟶ T →
-- -- --              Ψ ⊨ s ≈ s′ ∶ S →
-- -- --              -----------------------
-- -- --              Ψ ⊨ t $ s ≈ t′ $ s′ ∶ T
-- -- -- box-cong   : [] ∷⁺ Ψ ⊨ t ≈ t′ ∶ T →
-- -- --              ------------------------
-- -- --              Ψ ⊨ box t ≈ box t′ ∶ □ T
-- -- -- unbox-cong : ∀ {n} Γs →
-- -- --              Ψ ⊨ t ≈ t′ ∶ □ T →
-- -- --              len Γs ≡ n →
-- -- --              --------------------------------------
-- -- --              Γs ++⁺ Ψ ⊨ unbox n t ≈ unbox n t′ ∶ T
-- -- -- []-cong    : Ψ ⊨ t ≈ t′ ∶ T →
-- -- --              Ψ′ ⊨s σ ≈ σ′ ∶ Ψ →
-- -- --              ------------------------------
-- -- --              Ψ′ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶ T
