{-# OPTIONS --without-K --safe #-}

module STLC.Statics where

open import Lib

open import Data.Nat
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties


infixr 5 _⟶_
infixr 9 _X_

-- types
data Typ : Set where
  *   : Typ
  _X_ : Typ → Typ → Typ
  _⟶_ : Typ → Typ → Typ

Env : Set
Env = List Typ

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Env

-- legal terms
infixl 10 _$_
data Trm : Env → Typ → Set where
  *   : Trm Γ *
  var : T ∈ Γ → Trm Γ T
  pr  : Trm Γ (S ⟶ U ⟶ S X U)
  π₁  : Trm Γ (S X U ⟶ S)
  π₂  : Trm Γ (S X U ⟶ U)
  _$_ : Trm Γ (S ⟶ U) → Trm Γ S → Trm Γ U
  Λ   : Trm (S ∷ Γ) U → Trm Γ (S ⟶ U)

data Subst : Env → Env → Set where
  []  : Subst Γ []
  _∷_ : ∀ {Γ Γ′ T} → Trm Γ T → Subst Γ Γ′ → Subst Γ (T ∷ Γ′)

-- shifting of de Bruijn indices based on OPE
shift : Trm Γ T → Γ ⊆ Γ′ → Trm Γ′ T
shift * Γ⊆Γ′         = *
shift (var T∈Γ) Γ⊆Γ′ = var (∈-⊆ T∈Γ Γ⊆Γ′)
shift pr Γ⊆Γ′        = pr
shift π₁ Γ⊆Γ′        = π₁
shift π₂ Γ⊆Γ′        = π₂
shift (s $ u) Γ⊆Γ′   = shift s Γ⊆Γ′ $ shift u Γ⊆Γ′
shift (Λ t) Γ⊆Γ′     = Λ (shift t (refl ∷ Γ⊆Γ′))

size : ∀ {Γ T} → Trm Γ T → ℕ
size *       = 0
size (var _) = 0
size pr      = 0
size π₁      = 0
size π₂      = 0
size (s $ u) = size s + size u
size (Λ t)   = 1 + size t

size-shift : ∀ {Γ Γ′ T} (t : Trm Γ T) (Γ⊆Γ′ : Γ ⊆ Γ′) → size (shift t Γ⊆Γ′) ≡ size t
size-shift * Γ⊆Γ′       = refl
size-shift (var _) Γ⊆Γ′ = refl
size-shift pr Γ⊆Γ′      = refl
size-shift π₁ Γ⊆Γ′      = refl
size-shift π₂ Γ⊆Γ′      = refl
size-shift (s $ u) Γ⊆Γ′ = cong₂ _+_ (size-shift s Γ⊆Γ′) (size-shift u Γ⊆Γ′)
size-shift (Λ t) Γ⊆Γ′   = cong (1 +_) (size-shift t (refl ∷ Γ⊆Γ′))

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
subs _ pr s               = pr
subs _ π₁ s               = π₁
subs _ π₂ s               = π₂
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
shift-shift pr Γ⊆Γ′ Γ′⊆Γ″                            = refl
shift-shift π₁ Γ⊆Γ′ Γ′⊆Γ″                            = refl
shift-shift π₂ Γ⊆Γ′ Γ′⊆Γ″                            = refl
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
shift-refl pr        = refl
shift-refl π₁        = refl
shift-refl π₂        = refl
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
shift-subs Γ′ pr s Γ⊆Γ″                            = refl
shift-subs Γ′ π₁ s Γ⊆Γ″                            = refl
shift-subs Γ′ π₂ s Γ⊆Γ″                            = refl
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
subs-cancel Γ′ pr s        = refl
subs-cancel Γ′ π₁ s        = refl
subs-cancel Γ′ π₂ s        = refl
subs-cancel Γ′ (t $ u) s   = cong₂ _$_ (subs-cancel Γ′ t s) (subs-cancel Γ′ u s)
subs-cancel Γ′ (Λ {U} t) s = cong Λ (subs-cancel (U ∷ Γ′) t (shift s (U ∷ʳ ⊆-refl)))

weaken-t : ∀ {Γ T} S → Trm Γ T → Trm (S ∷ Γ) T
weaken-t S t = shift t (S ∷ʳ ⊆-refl)

weakens-t : ∀ {Γ T} Δ S → Trm (Δ ++ Γ) T → Trm (Δ ++ S ∷ Γ) T
weakens-t Δ S t = shift t (Δ ++ˡ (S ∷ʳ ⊆-refl))

module Subst′ where

  map : ∀ {Γ Γ′ Δ} → (∀ {T} → Trm Γ T → Trm Γ′ T) → Subst Γ Δ → Subst Γ′ Δ
  map f []      = []
  map f (t ∷ σ) = f t ∷ map f σ

  map-≡ : ∀ {Γ Γ′ Δ} (f g : ∀ {T} → Trm Γ T → Trm Γ′ T) (σ : Subst Γ Δ) → (∀ {S} (s : Trm Γ S) → f s ≡ g s) → map f σ ≡ map g σ
  map-≡ f g [] eq = refl
  map-≡ f g (t ∷ σ) eq = cong₂ _∷_ (eq t) (map-≡ f g σ eq)

  lookup : ∀ {Γ Δ T} → Subst Γ Δ → T ∈ Δ → Trm Γ T
  lookup (t ∷ σ) 0d       = t
  lookup (t ∷ σ) (1+ T∈Δ) = lookup σ T∈Δ

  lookup-map : ∀ {Γ Γ′ Δ T} → (f : ∀ {T} → Trm Γ T → Trm Γ′ T) → (σ : Subst Γ Δ) → (T∈Δ : T ∈ Δ) → lookup (map f σ) T∈Δ ≡ f (lookup σ T∈Δ)
  lookup-map f (t ∷ σ) 0d       = refl
  lookup-map f (t ∷ σ) (1+ T∈Δ) = lookup-map f σ T∈Δ

  weaken : ∀ {Γ Δ} T → Subst Γ Δ → Subst (T ∷ Γ) Δ
  weaken T σ = map (weaken-t T) σ

  qweaken : ∀ {Γ Δ} T → Subst Γ Δ → Subst (T ∷ Γ) (T ∷ Δ)
  qweaken T σ = var 0d ∷ weaken T σ

  id : ∀ {Γ} → Subst Γ Γ
  id {[]}    = []
  id {T ∷ Γ} = qweaken T id

  id-lookup : ∀ {Γ T} → (T∈Γ : T ∈ Γ) → lookup id T∈Γ ≡ var T∈Γ
  id-lookup 0d           = refl
  id-lookup (there {S} T∈Γ)
    rewrite lookup-map (weaken-t S) id T∈Γ
          | id-lookup T∈Γ
          | ∈-⊆-refl T∈Γ = refl

  weaken-lookup : ∀ {Γ Δ S} T (σ : Subst Γ Δ) (S∈Δ : S ∈ Δ) → lookup (weaken T σ) S∈Δ ≡ weaken-t T (lookup σ S∈Δ)
  weaken-lookup T σ S∈Δ
    rewrite lookup-map (weaken-t T) σ S∈Δ = refl

  apply : ∀ {Γ Γ′ T} → Subst Γ Γ′ → Trm Γ′ T → Trm Γ T
  apply σ *          = *
  apply σ (var T∈Γ′) = lookup σ T∈Γ′
  apply σ pr         = pr
  apply σ π₁         = π₁
  apply σ π₂         = π₂
  apply σ (s $ u)    = (apply σ s) $ (apply σ u)
  apply σ (Λ t)      = Λ (apply (qweaken _ σ) t)

  id-apply : ∀ {Γ T} (t : Trm Γ T) → apply id t ≡ t
  id-apply *         = refl
  id-apply (var T∈Γ) = id-lookup T∈Γ
  id-apply pr        = refl
  id-apply π₁        = refl
  id-apply π₂        = refl
  id-apply (s $ u)   = cong₂ _$_ (id-apply s) (id-apply u)
  id-apply (Λ t)     = cong Λ (id-apply t)

  ⊆⇒Subst : ∀ {Γ Δ} → Γ ⊆ Δ → Subst Δ Γ
  ⊆⇒Subst []           = []
  ⊆⇒Subst (T ∷ʳ Γ⊆Δ)   = weaken T (⊆⇒Subst Γ⊆Δ)
  ⊆⇒Subst (refl ∷ Γ⊆Δ) = qweaken _ (⊆⇒Subst Γ⊆Δ)

  proj : ∀ {Γ T} → Subst (T ∷ Γ) Γ
  proj = weaken _ id -- ⊆⇒Subst (_ ∷ʳ ⊆-refl)

  ⊆⇒Subst-refl : ∀ Γ → ⊆⇒Subst ⊆-refl ≡ id {Γ}
  ⊆⇒Subst-refl []          = refl
  ⊆⇒Subst-refl (T ∷ Γ)
    rewrite ⊆⇒Subst-refl Γ = refl

  ⊆⇒Subst-lookup : ∀ {Γ Δ T} (Δ⊆Γ : Δ ⊆ Γ) (T∈Δ : T ∈ Δ) → var (∈-⊆ T∈Δ Δ⊆Γ) ≡ lookup (⊆⇒Subst Δ⊆Γ) T∈Δ
  ⊆⇒Subst-lookup (S ∷ʳ Δ⊆Γ) T∈Δ
    rewrite weaken-lookup S (⊆⇒Subst Δ⊆Γ) T∈Δ
          | sym (⊆⇒Subst-lookup Δ⊆Γ T∈Δ)
          | ∈-⊆-refl (∈-⊆ T∈Δ Δ⊆Γ) = refl
  ⊆⇒Subst-lookup (refl ∷ Δ⊆Γ) 0d   = refl
  ⊆⇒Subst-lookup (_∷_ {S} refl Δ⊆Γ) (1+ T∈Δ)
    rewrite weaken-lookup S (⊆⇒Subst Δ⊆Γ) T∈Δ
          | sym (⊆⇒Subst-lookup Δ⊆Γ T∈Δ)
          | ∈-⊆-refl (∈-⊆ T∈Δ Δ⊆Γ) = refl

  shift-apply : ∀ {Γ Δ T} (t : Trm Δ T) (Δ⊆Γ : Δ ⊆ Γ) → shift t Δ⊆Γ ≡ apply (⊆⇒Subst Δ⊆Γ) t
  shift-apply * Δ⊆Γ         = refl
  shift-apply (var T∈Δ) Δ⊆Γ = ⊆⇒Subst-lookup Δ⊆Γ T∈Δ
  shift-apply pr Δ⊆Γ        = refl
  shift-apply π₁ Δ⊆Γ        = refl
  shift-apply π₂ Δ⊆Γ        = refl
  shift-apply (s $ u) Δ⊆Γ   = cong₂ _$_ (shift-apply s Δ⊆Γ) (shift-apply u Δ⊆Γ)
  shift-apply (Λ t) Δ⊆Γ     = cong Λ (shift-apply t (refl ∷ Δ⊆Γ))

  weaken-Subst : ∀ {Γ′ Γ} Δ → Subst Γ′ Γ → Subst (Δ ++ Γ′) (Δ ++ Γ)
  weaken-Subst [] σ      = σ
  weaken-Subst (T ∷ Δ) σ = qweaken T (weaken-Subst Δ σ)

  weaken-Subst′ : ∀ {Γ′ Γ} Δ S → Subst Γ′ Γ → Subst (Δ ++ S ∷ Γ′) (Δ ++ S ∷ Γ)
  weaken-Subst′ [] S σ      = qweaken S σ
  weaken-Subst′ (T ∷ Δ) S σ = qweaken T (weaken-Subst′ Δ S σ)

  weaken-t-apply : ∀ {Γ T} S (t : Trm Γ T) → weaken-t S t ≡ apply proj t
  weaken-t-apply {Γ} S t
    rewrite shift-apply t (S ∷ʳ ⊆-refl)
          | ⊆⇒Subst-refl Γ = refl

  weakens-weaken : ∀ {Γ T} Δ U S (t : Trm (Δ ++ Γ) T) → weakens-t (U ∷ Δ) S (weaken-t U t) ≡ weaken-t U (weakens-t Δ S t)
  weakens-weaken {Γ} Δ U S t
    rewrite shift-shift t (U ∷ʳ ⊆-refl) (refl ∷ Δ ++ˡ S ∷ʳ ⊆-refl)
          | shift-shift t (Δ ++ˡ S ∷ʳ ⊆-refl) (U ∷ʳ ⊆-refl)
          | ⊆-refl-trans (Δ ++ˡ S ∷ʳ ⊆-refl {x = Γ})
          | ⊆-trans-refl (Δ ++ˡ S ∷ʳ ⊆-refl {x = Γ}) = refl

  weaken-apply-gen : ∀ {Γ′ Γ T} Δ S (σ : Subst Γ′ Γ) (t : Trm (Δ ++ Γ) T) → apply (weaken-Subst′ Δ S σ) (weakens-t Δ S t) ≡ weakens-t Δ S (apply (weaken-Subst Δ σ) t)
  weaken-apply-gen Δ S σ *        = refl
  weaken-apply-gen Δ S σ (var T∈) = helper Δ S σ T∈
    where helper : ∀ {Γ′ Γ T} Δ S (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) → lookup (weaken-Subst′ Δ S σ) (∈-⊆ T∈ (Δ ++ˡ S ∷ʳ ⊆-refl)) ≡ weakens-t Δ S (lookup (weaken-Subst Δ σ) T∈)
          helper [] S (t ∷ σ) 0d      = refl
          helper [] S (_ ∷ σ) (1+ T∈) = helper [] S σ T∈
          helper (U ∷ Δ) S σ 0d       = refl
          helper (U ∷ Δ) S σ (1+ T∈)
            rewrite lookup-map (weaken-t U) (weaken-Subst Δ σ) T∈
                  | weakens-weaken Δ U S (lookup (weaken-Subst Δ σ) T∈)
                  | lookup-map (weaken-t U) (weaken-Subst′ Δ S σ) (∈-⊆ T∈ (Δ ++ˡ S ∷ʳ ⊆-refl))
                  | helper Δ S σ T∈   = refl
  weaken-apply-gen Δ S σ pr       = refl
  weaken-apply-gen Δ S σ π₁       = refl
  weaken-apply-gen Δ S σ π₂       = refl
  weaken-apply-gen Δ S σ (s $ u)  = cong₂ _$_ (weaken-apply-gen Δ S σ s) (weaken-apply-gen Δ S σ u)
  weaken-apply-gen Δ S σ (Λ t)    = cong Λ (weaken-apply-gen (_ ∷ Δ) S σ t)

  weaken-apply : ∀ {Γ Δ T} S (σ : Subst Γ Δ) (t : Trm Δ T) → apply (qweaken S σ) (weaken-t S t) ≡ weaken-t S (apply σ t)
  weaken-apply = weaken-apply-gen []

  compose : ∀ {Γ Γ′ Γ″} → Subst Γ Γ′ → Subst Γ′ Γ″ → Subst Γ Γ″
  compose σ δ = map (apply σ) δ

  lookup-compose : ∀ {Γ Γ′ Γ″ T} (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) (T∈Γ″ : T ∈ Γ″) → lookup (compose σ δ) T∈Γ″ ≡ apply σ (lookup δ T∈Γ″)
  lookup-compose σ δ T∈ = lookup-map (apply σ) δ T∈

  weaken-compose : ∀ {Γ Γ′ Γ″} T (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) → weaken T (compose σ δ) ≡ compose (qweaken T σ) (weaken T δ)
  weaken-compose T σ []          = refl
  weaken-compose T σ (t ∷ δ)
    rewrite weaken-apply T σ t
          | weaken-compose T σ δ = refl

  compose-apply : ∀ {Γ Γ′ Γ″ T} (σ : Subst Γ Γ′) (δ : Subst Γ′ Γ″) (t : Trm Γ″ T) → apply (compose σ δ) t ≡ apply σ (apply δ t)
  compose-apply σ δ *            = refl
  compose-apply σ δ (var T∈Γ″)   = lookup-compose σ δ T∈Γ″
  compose-apply σ δ pr           = refl
  compose-apply σ δ π₁           = refl
  compose-apply σ δ π₂           = refl
  compose-apply σ δ (s $ u)      = cong₂ _$_ (compose-apply σ δ s) (compose-apply σ δ u)
  compose-apply σ δ (Λ {S} t)
    rewrite weaken-compose S σ δ = cong Λ (compose-apply (qweaken _ σ) (qweaken _ δ) t)

  extend : ∀ {Γ T} → Trm Γ T → Subst Γ (T ∷ Γ)
  extend t = t ∷ id

  qweaken-apply-natural : ∀ {Γ Γ′ Δ Δ′ T} (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (t : Trm (Δ ++ Γ) T) → apply (weaken-Subst Δ′ σ) (apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) t) ≡ apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ′)) (apply (weaken-Subst Δ σ) t)
  qweaken-apply-natural Δ⊆Δ′ σ *         = refl
  qweaken-apply-natural Δ⊆Δ′ σ (var T∈)  = helper′ Δ⊆Δ′ σ T∈
    where helper : ∀ {Γ Γ′ Δ Δ′ T} (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) →  apply (weaken-Subst Δ′ σ) (lookup (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈) ≡ shift (lookup (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)
          helper {Γ} [] σ T∈
            rewrite ⊆⇒Subst-refl Γ
                  | shift-refl (lookup σ T∈)
                  | id-lookup T∈                = refl
          helper {Γ} {Γ′} (_∷ʳ_ {Δ} {Δ′} S Δ⊆Δ′) σ T∈
            rewrite weaken-lookup S (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈
                  | weaken-apply S (weaken-Subst Δ′ σ) (lookup (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈)
                  | helper Δ⊆Δ′ σ T∈
                  | shift-shift (lookup (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′) (S ∷ʳ ⊆-refl)
                  | ⊆-trans-refl (Δ⊆Δ′ ++ʳ′ Γ′) = refl
          helper (refl ∷ Δ⊆Δ′) σ 0d             = refl
          helper {Γ} {Γ′} (_∷_ {S} {Δ} {_} {Δ′} refl Δ⊆Δ′) σ (1+ T∈)
            rewrite weaken-lookup S (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈
                  | weaken-apply S (weaken-Subst Δ′ σ) (lookup (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈)
                  | helper Δ⊆Δ′ σ T∈
                  | shift-shift (lookup (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)(S ∷ʳ ⊆-refl)
                  | ⊆-trans-refl (Δ⊆Δ′ ++ʳ′ Γ′)
                  | weaken-lookup S (weaken-Subst Δ σ) T∈
                  | shift-shift (lookup (weaken-Subst Δ σ) T∈) (S ∷ʳ ⊆-refl) (refl ∷ (Δ⊆Δ′ ++ʳ′ Γ′))
                  | ⊆-refl-trans (Δ⊆Δ′ ++ʳ′ Γ′) = refl
          helper′ : ∀ {Γ Γ′ Δ Δ′ T} (Δ⊆Δ′ : Δ ⊆ Δ′) (σ : Subst Γ′ Γ) (T∈ : T ∈ Δ ++ Γ) → apply (weaken-Subst Δ′ σ) (lookup (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ)) T∈) ≡ apply (⊆⇒Subst (Δ⊆Δ′ ++ʳ′ Γ′)) (lookup (weaken-Subst Δ σ) T∈)
          helper′ {_} {Γ′} {Δ} Δ⊆Δ′ σ T∈
            rewrite sym (shift-apply (lookup (weaken-Subst Δ σ) T∈) (Δ⊆Δ′ ++ʳ′ Γ′)) = helper Δ⊆Δ′ σ T∈
  qweaken-apply-natural Δ⊆Δ′ σ pr        = refl
  qweaken-apply-natural Δ⊆Δ′ σ π₁        = refl
  qweaken-apply-natural Δ⊆Δ′ σ π₂        = refl
  qweaken-apply-natural Δ⊆Δ′ σ (s $ u)   = cong₂ _$_ (qweaken-apply-natural Δ⊆Δ′ σ s) (qweaken-apply-natural Δ⊆Δ′ σ u)
  qweaken-apply-natural Δ⊆Δ′ σ (Λ {S} t) = cong Λ (qweaken-apply-natural (refl ∷ Δ⊆Δ′) σ t)

infix 5 _⟦_⟧ _⟦_⟧!

_⟦_⟧ : ∀ {Γ Γ′ T} → Trm Γ′ T → Subst Γ Γ′ → Trm Γ T
t ⟦ σ ⟧ = Subst′.apply σ t

_⟦_⟧! : ∀ {Γ S T} → Trm (S ∷ Γ) T → Trm Γ S → Trm Γ T
t ⟦ t′ ⟧! = t ⟦ Subst′.extend t′ ⟧
