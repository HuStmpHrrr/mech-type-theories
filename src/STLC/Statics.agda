{-# OPTIONS --without-K --safe #-}

module STLC.Statics where

open import Lib

open import Level renaming (suc to succ)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties


infixr 5 _⟶_
infixr 9 _X_

-- types
data Typ : Set where
  *   : Typ
  _X_ : Typ → Typ → Typ
  _⟶_ : Typ → Typ → Typ

Ctx : Set
Ctx = List Typ

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx

-- legal terms
infixl 10 _$_
data Trm : Ctx → Typ → Set where
  *   : Trm Γ *
  var : T ∈ Γ → Trm Γ T
  pr  : (s : Trm Γ S) (u : Trm Γ U) → Trm Γ (S X U)
  π₁  : (t : Trm Γ (S X U)) → Trm Γ S
  π₂  : (t : Trm Γ (S X U)) → Trm Γ U
  _$_ : Trm Γ (S ⟶ U) → Trm Γ S → Trm Γ U
  Λ   : Trm (S ∷ Γ) U → Trm Γ (S ⟶ U)

data Subst : Ctx → Ctx → Set where
  []  : Subst Γ []
  _∷_ : Trm Γ T → Subst Γ Γ′ → Subst Γ (T ∷ Γ′)

data Forall {a} (P : ∀ {T} → Trm Γ T → Set a) : Subst Γ Δ → Set (succ a) where
  []  : Forall P []
  _∷_ : {t : Trm Γ T} {σ : Subst Γ Δ} → P t → Forall P σ → Forall P (t ∷ σ)

-- shifting of de Bruijn indices based on OPE
shift : Trm Γ T → Γ ⊆ Γ′ → Trm Γ′ T
shift * Γ⊆Γ′         = *
shift (var T∈Γ) Γ⊆Γ′ = var (∈-⊆ T∈Γ Γ⊆Γ′)
shift (pr s u) Γ⊆Γ′  = pr (shift s Γ⊆Γ′) (shift u Γ⊆Γ′)
shift (π₁ t) Γ⊆Γ′    = π₁ (shift t Γ⊆Γ′)
shift (π₂ t) Γ⊆Γ′    = π₂ (shift t Γ⊆Γ′)
shift (s $ u) Γ⊆Γ′   = shift s Γ⊆Γ′ $ shift u Γ⊆Γ′
shift (Λ t) Γ⊆Γ′     = Λ (shift t (refl ∷ Γ⊆Γ′))

size : Trm Γ T → ℕ
size *        = 0
size (var _)  = 0
size (pr s u) = 1 + size s + size u
size (π₁ t)   = 1 + size t
size (π₂ t)   = 1 + size t
size (s $ u)  = size s + size u
size (Λ t)    = 1 + size t

size-shift : (t : Trm Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) → size (shift t Γ⊆Γ′) ≡ size t
size-shift * Γ⊆Γ′        = refl
size-shift (var _) Γ⊆Γ′  = refl
size-shift (pr s u) Γ⊆Γ′ = cong₂ (λ a b → 1 + a + b) (size-shift s Γ⊆Γ′) (size-shift u Γ⊆Γ′)
size-shift (π₁ t) Γ⊆Γ′   = cong suc (size-shift t Γ⊆Γ′)
size-shift (π₂ t) Γ⊆Γ′   = cong suc (size-shift t Γ⊆Γ′)
size-shift (s $ u) Γ⊆Γ′  = cong₂ _+_ (size-shift s Γ⊆Γ′) (size-shift u Γ⊆Γ′)
size-shift (Λ t) Γ⊆Γ′    = cong (1 +_) (size-shift t (refl ∷ Γ⊆Γ′))

-- substitution

private
  subs-∈-helper : ∀ Γ′ Γ″ w → w ≡ Γ″ ++ T ∷ Γ′ ++ Γ → (Trm w S → Trm w U) → Trm (Γ″ ++ T ∷ Γ′ ++ Γ) S → Trm (Γ″ ++ T ∷ Γ′ ++ Γ) U
  subs-∈-helper Γ′ Γ″ w refl rec s = rec s

subs-∈ : ∀ Γ′ Γ″ → U ∈ Γ′ ++ S ∷ Γ → Trm (Γ″ ++ Γ′ ++ Γ) S → Trm (Γ″ ++ Γ′ ++ Γ) U
subs-∈ [] Γ″ 0d s                    = s
subs-∈ [] Γ″ (1+ U∈) s               = var (++⁺ʳ Γ″ U∈)
subs-∈ (T ∷ Γ′) Γ″ 0d s              = var (++⁺ʳ Γ″ 0d)
subs-∈ {Γ = Γ} (T ∷ Γ′) Γ″ (1+ U∈) s = subs-∈-helper Γ′ Γ″ _ (++-assoc Γ″ (T ∷ []) (Γ′ ++ Γ)) (subs-∈ Γ′ (Γ″ ++ T ∷ []) U∈) s

subs : ∀ Γ′ → Trm (Γ′ ++ S ∷ Γ) U → Trm (Γ′ ++ Γ) S → Trm (Γ′ ++ Γ) U
subs _ * s                = *
subs {S} {Γ} Γ′ (var T) s = subs-∈ Γ′ [] T s
subs Γ′ (pr s u) s′       = pr (subs Γ′ s s′) (subs Γ′ u s′)
subs Γ′ (π₁ t) s          = π₁ (subs Γ′ t s)
subs Γ′ (π₂ t) s          = π₂ (subs Γ′ t s)
subs Γ′ (t $ u) s         = subs Γ′ t s $ subs Γ′ u s
subs {S} Γ′ (Λ {U} t) s   = Λ (subs (U ∷ Γ′) t (shift s (U ∷ʳ ⊆-refl)))

infix 5 _[_]

_[_] : ∀ {Γ S T} → Trm (S ∷ Γ) T → Trm Γ S → Trm Γ T
_[_] = subs []

-- PROPERTIES

shift-shift : ∀ (t : Trm Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) (Γ′⊆Γ″ : Γ′ ⊆ Γ″) →
  shift (shift t Γ⊆Γ′) Γ′⊆Γ″ ≡ shift t (⊆-trans Γ⊆Γ′ Γ′⊆Γ″)
shift-shift * Γ⊆Γ′ Γ′⊆Γ″                             = refl
shift-shift (var T∈Γ) Γ⊆Γ′ Γ′⊆Γ″                     = cong var (∈-⊆-trans T∈Γ Γ⊆Γ′ Γ′⊆Γ″)
shift-shift (pr s u) Γ⊆Γ′ Γ′⊆Γ″                      = cong₂ pr (shift-shift s Γ⊆Γ′ Γ′⊆Γ″) (shift-shift u Γ⊆Γ′ Γ′⊆Γ″)
shift-shift (π₁ t) Γ⊆Γ′ Γ′⊆Γ″                        = cong π₁ (shift-shift t Γ⊆Γ′ Γ′⊆Γ″)
shift-shift (π₂ t) Γ⊆Γ′ Γ′⊆Γ″                        = cong π₂ (shift-shift t Γ⊆Γ′ Γ′⊆Γ″)
shift-shift (s $ u) Γ⊆Γ′ Γ′⊆Γ″
  rewrite shift-shift s Γ⊆Γ′ Γ′⊆Γ″
        | shift-shift u Γ⊆Γ′ Γ′⊆Γ″                   = refl
shift-shift (Λ t) Γ⊆Γ′ Γ′⊆Γ″
  rewrite shift-shift t (refl ∷ Γ⊆Γ′) (refl ∷ Γ′⊆Γ″) = refl

shift-++ʳ-outer : ∀ (t : Trm Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) Γ″ →
  shift (shift t Γ⊆Γ′) (Γ″ ++ʳ ⊆-refl) ≡ shift t (Γ″ ++ʳ Γ⊆Γ′)
shift-++ʳ-outer t Γ⊆Γ′ Γ″
  rewrite shift-shift t Γ⊆Γ′ (Γ″ ++ʳ ⊆-refl)
        | sym (⊆-++ʳ′ Γ⊆Γ′ Γ″) = refl

shift-++ʳ-inner : ∀ (t : Trm Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) (Γ′⊆Γ″ : Γ′ ⊆ Γ″) Δ →
  shift (shift t (Δ ++ʳ Γ⊆Γ′)) (Δ ++ˡ Γ′⊆Γ″) ≡ shift t (Δ ++ʳ (⊆-trans Γ⊆Γ′ Γ′⊆Γ″))
shift-++ʳ-inner t Γ⊆Γ′ Γ′⊆Γ″ Δ
  rewrite shift-shift t (Δ ++ʳ Γ⊆Γ′) (Δ ++ˡ Γ′⊆Γ″)
        | ⊆-++ʳ-++ˡ Γ⊆Γ′ Γ′⊆Γ″ Δ = refl

shift-shift-swap : ∀ (t : Trm Γ T) S (Γ⊆Γ′ : Γ ⊆ Γ′) →
  shift (shift t (S ∷ʳ ⊆-refl)) (refl ∷ Γ⊆Γ′) ≡ shift (shift t Γ⊆Γ′) (S ∷ʳ ⊆-refl)
shift-shift-swap t S Γ⊆Γ′
  rewrite shift-shift t (S ∷ʳ ⊆-refl) (refl ∷ Γ⊆Γ′)
        | shift-shift t Γ⊆Γ′ (S ∷ʳ ⊆-refl)
        | ⊆-refl-trans Γ⊆Γ′
        | ⊆-trans-∷ʳ-refl S Γ⊆Γ′ = refl

shift-refl : ∀ (t : Trm Γ T) → shift t ⊆-refl ≡ t
shift-refl *         = refl
shift-refl (var T∈Γ) = cong var (∈-⊆-refl T∈Γ)
shift-refl (pr s u)  = cong₂ pr (shift-refl s) (shift-refl u)
shift-refl (π₁ t)    = cong π₁ (shift-refl t)
shift-refl (π₂ t)    = cong π₂ (shift-refl t)
shift-refl (t $ u)   = cong₂ _$_ (shift-refl t) (shift-refl u)
shift-refl (Λ t)     = cong Λ (shift-refl t)

shift-subs-∈ : ∀ Γ′ Δ (U∈ : U ∈ Γ′ ++ S ∷ Γ) (Γ⊆Γ″ : Γ ⊆ Γ″) (s : Trm (Δ ++ Γ′ ++ Γ) S) →
               shift (subs-∈ Γ′ Δ U∈ s) (Δ ++ˡ (Γ′ ++ˡ Γ⊆Γ″)) ≡ subs-∈ Γ′ Δ (∈-⊆ U∈ (Γ′ ++ˡ (refl ∷ Γ⊆Γ″))) (shift s (Δ ++ˡ (Γ′ ++ˡ Γ⊆Γ″)))
shift-subs-∈ [] Δ (here refl) Γ⊆Γ″ s       = refl
shift-subs-∈ [] Δ (1+ U∈) Γ⊆Γ″ s           = cong var (∈-⊆-++ Δ U∈ Γ⊆Γ″)
shift-subs-∈ (T ∷ Γ′) Δ (here refl) Γ⊆Γ″ s = cong var (∈-⊆-++ Δ (here refl) (refl ∷ (Γ′ ++ˡ Γ⊆Γ″)))
shift-subs-∈ {Γ = Γ} {Γ″ = Γ″} (T ∷ Γ′) Δ (1+ U∈) Γ⊆Γ″ s
  with subs-∈ Γ′ (Δ ++ T ∷ []) U∈ | subs-∈ Γ′ (Δ ++ T ∷ []) (∈-⊆ U∈ (Γ′ ++ˡ (refl ∷ Γ⊆Γ″)))
     | Δ ++ˡ (_∷_ {x = T} refl (Γ′ ++ˡ Γ⊆Γ″)) | (Δ ++ T ∷ []) ++ˡ (Γ′ ++ˡ Γ⊆Γ″)
     | ++ˡ-assoc Δ (T ∷ []) (Γ′ ++ˡ Γ⊆Γ″)
     | shift-subs-∈ {Γ″ = Γ″} Γ′ (Δ ++ T ∷ []) U∈ Γ⊆Γ″
...  | _ | _ | _ | _ | assoc | rec
     with (Δ ++ T ∷ []) ++ Γ′ ++ Γ | (Δ ++ T ∷ []) ++ Γ′ ++ Γ″ | ++-assoc Δ (T ∷ []) (Γ′ ++ Γ) | ++-assoc Δ (T ∷ []) (Γ′ ++ Γ″)
...     | _ | _ | refl | refl with assoc
...                              | refl    = rec s

shift-subs : ∀ Γ′ (t : Trm (Γ′ ++ S ∷ Γ) T) (s : Trm (Γ′ ++ Γ) S) (Γ⊆Γ″ : Γ ⊆ Γ″) →
             shift (subs Γ′ t s) (Γ′ ++ˡ Γ⊆Γ″) ≡ subs Γ′ (shift t (Γ′ ++ˡ (refl ∷ Γ⊆Γ″))) (shift s (Γ′ ++ˡ Γ⊆Γ″))
shift-subs Γ′ * s Γ⊆Γ″                             = refl
shift-subs {S} {Γ} Γ′ (var T∈Γ) s Γ⊆Γ″             = shift-subs-∈ Γ′ [] T∈Γ Γ⊆Γ″ s
shift-subs Γ′ (pr s u) s′ Γ⊆Γ″                     = cong₂ pr (shift-subs Γ′ s s′ Γ⊆Γ″) (shift-subs Γ′ u s′ Γ⊆Γ″)
shift-subs Γ′ (π₁ t) s Γ⊆Γ″                        = cong π₁ (shift-subs Γ′ t s Γ⊆Γ″)
shift-subs Γ′ (π₂ t) s Γ⊆Γ″                        = cong π₂ (shift-subs Γ′ t s Γ⊆Γ″)
shift-subs Γ′ (t $ u) s Γ⊆Γ″                       = cong₂ _$_ (shift-subs Γ′ t s Γ⊆Γ″) (shift-subs Γ′ u s Γ⊆Γ″)
shift-subs Γ′ (Λ {S} t) s Γ⊆Γ″ with shift-subs (S ∷ Γ′) t (shift s (S ∷ʳ ⊆-refl)) Γ⊆Γ″
... | rec
  rewrite sym (shift-shift-swap s S (Γ′ ++ˡ Γ⊆Γ″)) = cong Λ rec

shift-cancel-∈ : ∀ Γ′ Δ (T∈ : T ∈ Γ′ ++ Γ) (s : Trm (Δ ++ Γ′ ++ Γ) S) →
  subs-∈ Γ′ Δ (∈-⊆ T∈ (Γ′ ++ˡ (S ∷ʳ ⊆-refl))) s ≡ var (++⁺ʳ Δ T∈)
shift-cancel-∈ [] Δ (here refl) s                             = refl
shift-cancel-∈ [] Δ (1+ T∈) s                                 = cong (λ t → var (++⁺ʳ Δ (1+ t))) (∈-⊆-refl T∈)
shift-cancel-∈ (_ ∷ Γ′) Δ (here refl) s                       = refl
shift-cancel-∈ {Γ = Γ} {S = S} (U ∷ Γ′) Δ (1+ T∈) s
  with subs-∈ Γ′ (Δ ++ U ∷ []) (∈-⊆ T∈ (Γ′ ++ˡ (S ∷ʳ ⊆-refl)))
     | ++⁺ʳ (Δ ++ U ∷ []) T∈
     | ++⁺ʳ-assoc Δ (U ∷ []) T∈
     | shift-cancel-∈ {Γ = Γ} {S = S} Γ′ (Δ ++ U ∷ []) T∈
...  | _ | _ | eq | rec rewrite ++-assoc Δ (U ∷ []) (Γ′ ++ Γ) = trans (rec s) (cong var eq)

subs-cancel : ∀ Γ′ (t : Trm (Γ′ ++ Γ) T) (s : Trm (Γ′ ++ Γ) S) →
                subs Γ′ (shift t (Γ′ ++ˡ (S ∷ʳ ⊆-refl))) s ≡ t
subs-cancel Γ′ * s         = refl
subs-cancel Γ′ (var T∈Γ) s = shift-cancel-∈ Γ′ [] T∈Γ s
subs-cancel Γ′ (pr s u) s′ = cong₂ pr (subs-cancel Γ′ s s′) (subs-cancel Γ′ u s′)
subs-cancel Γ′ (π₁ t) s    = cong π₁ (subs-cancel Γ′ t s)
subs-cancel Γ′ (π₂ t) s    = cong π₂ (subs-cancel Γ′ t s)
subs-cancel Γ′ (t $ u) s   = cong₂ _$_ (subs-cancel Γ′ t s) (subs-cancel Γ′ u s)
subs-cancel Γ′ (Λ {U} t) s = cong Λ (subs-cancel (U ∷ Γ′) t (shift s (U ∷ʳ ⊆-refl)))

weaken-t : ∀ S → Trm Γ T → Trm (S ∷ Γ) T
weaken-t S t = shift t (S ∷ʳ ⊆-refl)

weakens-t : ∀ Δ S → Trm (Δ ++ Γ) T → Trm (Δ ++ S ∷ Γ) T
weakens-t Δ S t = shift t (Δ ++ˡ (S ∷ʳ ⊆-refl))

module Subst′ where

  map : (∀ {T} → Trm Γ T → Trm Γ′ T) → Subst Γ Δ → Subst Γ′ Δ
  map f []      = []
  map f (t ∷ σ) = f t ∷ map f σ

  map-≡ : (f g : ∀ {T} → Trm Γ T → Trm Γ′ T) (σ : Subst Γ Δ) → (∀ {S} (s : Trm Γ S) → f s ≡ g s) → map f σ ≡ map g σ
  map-≡ f g [] eq = refl
  map-≡ f g (t ∷ σ) eq = cong₂ _∷_ (eq t) (map-≡ f g σ eq)

  lookup′ : Subst Γ Δ → T ∈ Δ → Trm Γ T
  lookup′ (t ∷ σ) 0d       = t
  lookup′ (t ∷ σ) (1+ T∈Δ) = lookup′ σ T∈Δ

  lookup-map : (f : ∀ {T} → Trm Γ T → Trm Γ′ T) → (σ : Subst Γ Δ) → (T∈Δ : T ∈ Δ) → lookup′ (map f σ) T∈Δ ≡ f (lookup′ σ T∈Δ)
  lookup-map f (t ∷ σ) 0d       = refl
  lookup-map f (t ∷ σ) (1+ T∈Δ) = lookup-map f σ T∈Δ

  weaken : ∀ T → Subst Γ Δ → Subst (T ∷ Γ) Δ
  weaken T σ = map (weaken-t T) σ

  qweaken : ∀ T → Subst Γ Δ → Subst (T ∷ Γ) (T ∷ Δ)
  qweaken T σ = var 0d ∷ weaken T σ

  id : ∀ {Γ} → Subst Γ Γ
  id {[]}    = []
  id {T ∷ Γ} = qweaken T id

  id-lookup : (T∈Γ : T ∈ Γ) → lookup′ id T∈Γ ≡ var T∈Γ
  id-lookup 0d           = refl
  id-lookup (there {S} T∈Γ)
    rewrite lookup-map (weaken-t S) id T∈Γ
          | id-lookup T∈Γ
          | ∈-⊆-refl T∈Γ = refl

  weaken-lookup : ∀ T (σ : Subst Γ Δ) (S∈Δ : S ∈ Δ) → lookup′ (weaken T σ) S∈Δ ≡ weaken-t T (lookup′ σ S∈Δ)
  weaken-lookup T σ S∈Δ
    rewrite lookup-map (weaken-t T) σ S∈Δ = refl

  apply : Subst Γ Γ′ → Trm Γ′ T → Trm Γ T
  apply σ *          = *
  apply σ (var T∈Γ′) = lookup′ σ T∈Γ′
  apply σ (pr s u)   = pr (apply σ s) (apply σ u)
  apply σ (π₁ t)     = π₁ (apply σ t)
  apply σ (π₂ t)     = π₂ (apply σ t)
  apply σ (s $ u)    = (apply σ s) $ (apply σ u)
  apply σ (Λ t)      = Λ (apply (qweaken _ σ) t)

  id-apply : (t : Trm Γ T) → apply id t ≡ t
  id-apply *         = refl
  id-apply (var T∈Γ) = id-lookup T∈Γ
  id-apply (pr s u)  = cong₂ pr (id-apply s) (id-apply u)
  id-apply (π₁ t)    = cong π₁ (id-apply t)
  id-apply (π₂ t)    = cong π₂ (id-apply t)
  id-apply (s $ u)   = cong₂ _$_ (id-apply s) (id-apply u)
  id-apply (Λ t)     = cong Λ (id-apply t)

  ⊆⇒Subst : Γ ⊆ Δ → Subst Δ Γ
  ⊆⇒Subst []           = []
  ⊆⇒Subst (T ∷ʳ Γ⊆Δ)   = weaken T (⊆⇒Subst Γ⊆Δ)
  ⊆⇒Subst (refl ∷ Γ⊆Δ) = qweaken _ (⊆⇒Subst Γ⊆Δ)

  proj : Subst (T ∷ Γ) Γ
  proj = weaken _ id -- ⊆⇒Subst (_ ∷ʳ ⊆-refl)

  ⊆⇒Subst-refl : ∀ Γ → ⊆⇒Subst ⊆-refl ≡ id {Γ}
  ⊆⇒Subst-refl []          = refl
  ⊆⇒Subst-refl (T ∷ Γ)
    rewrite ⊆⇒Subst-refl Γ = refl

  ⊆⇒Subst-lookup : (Δ⊆Γ : Δ ⊆ Γ) (T∈Δ : T ∈ Δ) → var (∈-⊆ T∈Δ Δ⊆Γ) ≡ lookup′ (⊆⇒Subst Δ⊆Γ) T∈Δ
  ⊆⇒Subst-lookup (S ∷ʳ Δ⊆Γ) T∈Δ
    rewrite weaken-lookup S (⊆⇒Subst Δ⊆Γ) T∈Δ
          | sym (⊆⇒Subst-lookup Δ⊆Γ T∈Δ)
          | ∈-⊆-refl (∈-⊆ T∈Δ Δ⊆Γ) = refl
  ⊆⇒Subst-lookup (refl ∷ Δ⊆Γ) 0d   = refl
  ⊆⇒Subst-lookup (_∷_ {S} refl Δ⊆Γ) (1+ T∈Δ)
    rewrite weaken-lookup S (⊆⇒Subst Δ⊆Γ) T∈Δ
          | sym (⊆⇒Subst-lookup Δ⊆Γ T∈Δ)
          | ∈-⊆-refl (∈-⊆ T∈Δ Δ⊆Γ) = refl

  shift-apply : (t : Trm Δ T) (Δ⊆Γ : Δ ⊆ Γ) → shift t Δ⊆Γ ≡ apply (⊆⇒Subst Δ⊆Γ) t
  shift-apply * Δ⊆Γ         = refl
  shift-apply (var T∈Δ) Δ⊆Γ = ⊆⇒Subst-lookup Δ⊆Γ T∈Δ
  shift-apply (pr s u) Δ⊆Γ  = cong₂ pr (shift-apply s Δ⊆Γ) (shift-apply u Δ⊆Γ)
  shift-apply (π₁ t) Δ⊆Γ    = cong π₁ (shift-apply t Δ⊆Γ)
  shift-apply (π₂ t) Δ⊆Γ    = cong π₂ (shift-apply t Δ⊆Γ)
  shift-apply (s $ u) Δ⊆Γ   = cong₂ _$_ (shift-apply s Δ⊆Γ) (shift-apply u Δ⊆Γ)
  shift-apply (Λ t) Δ⊆Γ     = cong Λ (shift-apply t (refl ∷ Δ⊆Γ))

  weaken-Subst : ∀ Δ → Subst Γ′ Γ → Subst (Δ ++ Γ′) (Δ ++ Γ)
  weaken-Subst [] σ      = σ
  weaken-Subst (T ∷ Δ) σ = qweaken T (weaken-Subst Δ σ)

  weaken-Subst′ : ∀ Δ S → Subst Γ′ Γ → Subst (Δ ++ S ∷ Γ′) (Δ ++ S ∷ Γ)
  weaken-Subst′ [] S σ      = qweaken S σ
  weaken-Subst′ (T ∷ Δ) S σ = qweaken T (weaken-Subst′ Δ S σ)

  weaken-t-apply : ∀ S (t : Trm Γ T) → weaken-t S t ≡ apply proj t
  weaken-t-apply {Γ} S t
    rewrite shift-apply t (S ∷ʳ ⊆-refl)
          | ⊆⇒Subst-refl Γ = refl

  weakens-weaken : ∀ Δ U S (t : Trm (Δ ++ Γ) T) → weakens-t (U ∷ Δ) S (weaken-t U t) ≡ weaken-t U (weakens-t Δ S t)
  weakens-weaken {Γ} Δ U S t
    rewrite shift-shift t (U ∷ʳ ⊆-refl) (refl ∷ Δ ++ˡ S ∷ʳ ⊆-refl)
          | shift-shift t (Δ ++ˡ S ∷ʳ ⊆-refl) (U ∷ʳ ⊆-refl)
          | ⊆-refl-trans (Δ ++ˡ S ∷ʳ ⊆-refl {x = Γ})
          | ⊆-trans-refl (Δ ++ˡ S ∷ʳ ⊆-refl {x = Γ}) = refl

  weaken-apply-gen : ∀ Δ S (σ : Subst Γ′ Γ) (t : Trm (Δ ++ Γ) T) → apply (weaken-Subst′ Δ S σ) (weakens-t Δ S t) ≡ weakens-t Δ S (apply (weaken-Subst Δ σ) t)
  weaken-apply-gen Δ S σ *        = refl
  weaken-apply-gen Δ S σ (var T∈) = helper Δ S σ T∈
    where helper : ∀ Δ S (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) → lookup′ (weaken-Subst′ Δ S σ) (∈-⊆ T∈ (Δ ++ˡ S ∷ʳ ⊆-refl)) ≡ weakens-t Δ S (lookup′ (weaken-Subst Δ σ) T∈)
          helper [] S (t ∷ σ) 0d      = refl
          helper [] S (_ ∷ σ) (1+ T∈) = helper [] S σ T∈
          helper (U ∷ Δ) S σ 0d       = refl
          helper (U ∷ Δ) S σ (1+ T∈)
            rewrite lookup-map (weaken-t U) (weaken-Subst Δ σ) T∈
                  | weakens-weaken Δ U S (lookup′ (weaken-Subst Δ σ) T∈)
                  | lookup-map (weaken-t U) (weaken-Subst′ Δ S σ) (∈-⊆ T∈ (Δ ++ˡ S ∷ʳ ⊆-refl))
                  | helper Δ S σ T∈   = refl
  weaken-apply-gen Δ S σ (pr s u) = cong₂ pr (weaken-apply-gen Δ S σ s) (weaken-apply-gen Δ S σ u)
  weaken-apply-gen Δ S σ (π₁ t)   = cong π₁ (weaken-apply-gen Δ S σ t)
  weaken-apply-gen Δ S σ (π₂ t)   = cong π₂ (weaken-apply-gen Δ S σ t)
  weaken-apply-gen Δ S σ (s $ u)  = cong₂ _$_ (weaken-apply-gen Δ S σ s) (weaken-apply-gen Δ S σ u)
  weaken-apply-gen Δ S σ (Λ t)    = cong Λ (weaken-apply-gen (_ ∷ Δ) S σ t)

  weaken-apply : ∀ S (σ : Subst Γ Δ) (t : Trm Δ T) → apply (qweaken S σ) (weaken-t S t) ≡ weaken-t S (apply σ t)
  weaken-apply = weaken-apply-gen []

  compose : Subst Γ Γ′ → Subst Γ′ Γ″ → Subst Γ Γ″
  compose σ δ = map (apply σ) δ

  lookup-compose : (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) (T∈Γ″ : T ∈ Γ″) → lookup′ (compose σ δ) T∈Γ″ ≡ apply σ (lookup′ δ T∈Γ″)
  lookup-compose σ δ T∈ = lookup-map (apply σ) δ T∈

  weaken-compose : ∀ {Γ Γ′ Γ″} T (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) → weaken T (compose σ δ) ≡ compose (qweaken T σ) (weaken T δ)
  weaken-compose T σ []          = refl
  weaken-compose T σ (t ∷ δ)
    rewrite weaken-apply T σ t
          | weaken-compose T σ δ = refl

  compose-apply : (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) (t : Trm Γ″ T) → apply (compose σ δ) t ≡ apply σ (apply δ t)
  compose-apply σ δ *            = refl
  compose-apply σ δ (var T∈Γ″)   = lookup-compose σ δ T∈Γ″
  compose-apply σ δ (pr s u)     = cong₂ pr (compose-apply σ δ s) (compose-apply σ δ u)
  compose-apply σ δ (π₁ t)       = cong π₁ (compose-apply σ δ t)
  compose-apply σ δ (π₂ t)       = cong π₂ (compose-apply σ δ t)
  compose-apply σ δ (s $ u)      = cong₂ _$_ (compose-apply σ δ s) (compose-apply σ δ u)
  compose-apply σ δ (Λ {S} t)
    rewrite weaken-compose S σ δ = cong Λ (compose-apply (qweaken _ σ) (qweaken _ δ) t)

  extend : Trm Γ T → Subst Γ (T ∷ Γ)
  extend t = t ∷ id

  qweaken-apply-natural : ∀ (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (t : Trm (Δ ++ Γ) T) → apply (weaken-Subst Δ′ σ) (apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) t) ≡ apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ′)) (apply (weaken-Subst Δ σ) t)
  qweaken-apply-natural Δ⊆Δ′ σ *         = refl
  qweaken-apply-natural Δ⊆Δ′ σ (var T∈)  = helper′ Δ⊆Δ′ σ T∈
    where helper : ∀ {Γ Γ′ Δ Δ′ T} (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) →  apply (weaken-Subst Δ′ σ) (lookup′ (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈) ≡ shift (lookup′ (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)
          helper {Γ} [] σ T∈
            rewrite ⊆⇒Subst-refl Γ
                  | shift-refl (lookup′ σ T∈)
                  | id-lookup T∈                = refl
          helper {Γ} {Γ′} (_∷ʳ_ {Δ} {Δ′} S Δ⊆Δ′) σ T∈
            rewrite weaken-lookup S (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈
                  | weaken-apply S (weaken-Subst Δ′ σ) (lookup′ (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈)
                  | helper Δ⊆Δ′ σ T∈
                  | shift-shift (lookup′ (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′) (S ∷ʳ ⊆-refl)
                  | ⊆-trans-refl (Δ⊆Δ′ ++ʳ′ Γ′) = refl
          helper (refl ∷ Δ⊆Δ′) σ 0d             = refl
          helper {Γ} {Γ′} (_∷_ {S} {Δ} {_} {Δ′} refl Δ⊆Δ′) σ (1+ T∈)
            rewrite weaken-lookup S (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈
                  | weaken-apply S (weaken-Subst Δ′ σ) (lookup′ (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈)
                  | helper Δ⊆Δ′ σ T∈
                  | shift-shift (lookup′ (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)(S ∷ʳ ⊆-refl)
                  | ⊆-trans-refl (Δ⊆Δ′ ++ʳ′ Γ′)
                  | weaken-lookup S (weaken-Subst Δ σ) T∈
                  | shift-shift (lookup′ (weaken-Subst Δ σ) T∈) (S ∷ʳ ⊆-refl) (refl ∷ (Δ⊆Δ′ ++ʳ′ Γ′))
                  | ⊆-refl-trans (Δ⊆Δ′ ++ʳ′ Γ′) = refl
          helper′ : ∀ {Γ Γ′ Δ Δ′ T} (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) → apply (weaken-Subst Δ′ σ) (lookup′ (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈) ≡ apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ′)) (lookup′ (weaken-Subst Δ σ) T∈)
          helper′ {_} {Γ′} {Δ} Δ⊆Δ′ σ T∈
            rewrite sym (shift-apply (lookup′ (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)) = helper Δ⊆Δ′ σ T∈
  qweaken-apply-natural Δ⊆Δ′ σ (pr s u)  = cong₂ pr (qweaken-apply-natural Δ⊆Δ′ σ s) (qweaken-apply-natural Δ⊆Δ′ σ u)
  qweaken-apply-natural Δ⊆Δ′ σ (π₁ t)    = cong π₁ (qweaken-apply-natural Δ⊆Δ′ σ t)
  qweaken-apply-natural Δ⊆Δ′ σ (π₂ t)    = cong π₂ (qweaken-apply-natural Δ⊆Δ′ σ t)
  qweaken-apply-natural Δ⊆Δ′ σ (s $ u)   = cong₂ _$_ (qweaken-apply-natural Δ⊆Δ′ σ s) (qweaken-apply-natural Δ⊆Δ′ σ u)
  qweaken-apply-natural Δ⊆Δ′ σ (Λ {S} t) = cong Λ (qweaken-apply-natural (refl ∷ Δ⊆Δ′) σ t)

  id-compose : (σ : Subst Δ Γ) → compose id σ ≡ σ
  id-compose []      = refl
  id-compose (t ∷ σ) = cong₂ _∷_ (id-apply t) (id-compose σ)

  Subst-≡ : {σ δ : Subst Δ Γ} → (∀ {T} (T∈ : T ∈ Γ) → lookup′ σ T∈ ≡ lookup′ δ T∈) → σ ≡ δ
  Subst-≡ {_} {_} {[]} {[]} Pf        = refl
  Subst-≡ {_} {_} {t ∷ σ} {t′ ∷ δ} Pf = cong₂ _∷_ (Pf 0d) (Subst-≡ (λ T∈ → Pf (1+ T∈)))

  compose-id : (σ : Subst Δ Γ) → compose σ id ≡ σ
  compose-id σ = Subst-≡ (λ T∈ → trans (lookup-compose σ id T∈) (cong (apply σ) (id-lookup T∈)))

  extend-weaken-gen : ∀ Δ (s : Trm Γ′ S) (σ : Subst Γ′ Γ) (t : Trm (Δ ++ Γ) T) → apply (weaken-Subst Δ (s ∷ σ)) (shift t (Δ ++ˡ S ∷ʳ ⊆-refl)) ≡ apply (weaken-Subst Δ σ) t
  extend-weaken-gen Δ s σ *        = refl
  extend-weaken-gen Δ s σ (var T∈) = helper Δ s σ T∈
    where helper : ∀ Δ (s : Trm Γ′ S) (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) → lookup′ (weaken-Subst Δ (s ∷ σ)) (∈-⊆ T∈ (Δ ++ˡ S ∷ʳ ⊆-refl)) ≡ lookup′ (weaken-Subst Δ σ) T∈
          helper [] s σ T∈                                = cong (lookup′ σ) (∈-⊆-refl T∈)
          helper (U ∷ Δ) s σ 0d                           = refl
          helper (U ∷ Δ) s σ (1+ T∈)
            rewrite weaken-lookup U (weaken-Subst Δ (s ∷ σ)) (∈-⊆ T∈ (Δ ++ˡ _ ∷ʳ ⊆-refl))
                  | weaken-lookup U (weaken-Subst Δ σ) T∈ = cong (weaken-t U) (helper Δ s σ T∈)
  extend-weaken-gen Δ s σ (pr t u) = cong₂ pr (extend-weaken-gen Δ s σ t) (extend-weaken-gen Δ s σ u)
  extend-weaken-gen Δ s σ (π₁ t)   = cong π₁ (extend-weaken-gen Δ s σ t)
  extend-weaken-gen Δ s σ (π₂ t)   = cong π₂ (extend-weaken-gen Δ s σ t)
  extend-weaken-gen Δ s σ (t $ u)  = cong₂ _$_ (extend-weaken-gen Δ s σ t) (extend-weaken-gen Δ s σ u)
  extend-weaken-gen Δ s σ (Λ t)    = cong Λ (extend-weaken-gen (_ ∷ Δ) s σ t)

  extend-weaken : (t : Trm Δ T) (σ : Subst Δ Γ) → compose (extend t) (weaken T σ) ≡ σ
  extend-weaken t [] = refl
  extend-weaken t (t′ ∷ σ) = cong₂ _∷_ (trans (extend-weaken-gen [] t id t′) (id-apply t′)) (extend-weaken t σ)

  extend-qweaken : (t : Trm Δ T) (σ : Subst Δ Γ) → compose (extend t) (qweaken T σ) ≡ t ∷ σ
  extend-qweaken t σ = cong (t ∷_) (extend-weaken t σ)

  extend-qweaken-apply : (t : Trm Δ T) (σ : Subst Δ Γ) (s : Trm (T ∷ Γ) S) → apply (extend t) (apply (qweaken T σ) s) ≡ apply (t ∷ σ) s
  extend-qweaken-apply t σ s
    rewrite sym (compose-apply (extend t) (qweaken _ σ) s) = cong (λ δ → apply δ s) (extend-qweaken t σ)

infix 5 _⟦_⟧ _⟦_⟧!

_⟦_⟧ : ∀ {Γ Γ′ T} → Trm Γ′ T → Subst Γ Γ′ → Trm Γ T
t ⟦ σ ⟧ = Subst′.apply σ t

_⟦_⟧! : ∀ {Γ S T} → Trm (S ∷ Γ) T → Trm Γ S → Trm Γ T
t ⟦ t′ ⟧! = t ⟦ Subst′.extend t′ ⟧

module Forall′ where

  module _ {a} {P : ∀ {T} → Trm Γ T → Set a} where

    lookup′ : {σ : Subst Γ Δ} → Forall P σ → (T∈Δ : T ∈ Δ) → P (Subst′.lookup′ σ T∈Δ)
    lookup′ (Pt ∷ P*) 0d       = Pt
    lookup′ (Pt ∷ P*) (1+ T∈Δ) = lookup′ P* T∈Δ
