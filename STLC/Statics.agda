{-# OPTIONS --without-K --safe #-}

module STLC.Statics where

open import Lib

open import Data.Product

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

-- shifting of de Bruijn indices based on OPE
shift : Trm Γ T → Γ ⊆ Γ′ → Trm Γ′ T
shift * Γ⊆Γ′         = *
shift (var T∈Γ) Γ⊆Γ′ = var (∈-⊆ T∈Γ Γ⊆Γ′)
shift pr Γ⊆Γ′        = pr
shift π₁ Γ⊆Γ′        = π₁
shift π₂ Γ⊆Γ′        = π₂
shift (s $ u) Γ⊆Γ′   = shift s Γ⊆Γ′ $ shift u Γ⊆Γ′
shift (Λ t) Γ⊆Γ′     = Λ (shift t (refl ∷ Γ⊆Γ′))

-- substitution

private
  subs-∈-helper : ∀ Γ′ Γ″ w → w ≡ Γ″ ++ T ∷ Γ′ ++ Γ → (Trm w S → Trm w U) → Trm (Γ″ ++ T ∷ Γ′ ++ Γ) S → Trm (Γ″ ++ T ∷ Γ′ ++ Γ) U
  subs-∈-helper Γ′ Γ″ w refl rec s = rec s

subs-∈ : ∀ Γ′ Γ″ → U ∈ Γ′ ++ S ∷ Γ → Trm (Γ″ ++ Γ′ ++ Γ) S → Trm (Γ″ ++ Γ′ ++ Γ) U
subs-∈ [] Γ″ (here refl) s              = s
subs-∈ [] Γ″ (there U∈) s               = var (++⁺ʳ Γ″ U∈)
subs-∈ (T ∷ Γ′) Γ″ (here refl) s        = var (++⁺ʳ Γ″ (here refl))
subs-∈ {Γ = Γ} (T ∷ Γ′) Γ″ (there U∈) s = subs-∈-helper Γ′ Γ″ _ (++-assoc Γ″ (T ∷ []) (Γ′ ++ Γ)) (subs-∈ Γ′ (Γ″ ++ T ∷ []) U∈) s

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
shift-subs-∈ [] Δ (there U∈) Γ⊆Γ″ s        = cong var (∈-⊆-++ Δ U∈ Γ⊆Γ″)
shift-subs-∈ (T ∷ Γ′) Δ (here refl) Γ⊆Γ″ s = cong var (∈-⊆-++ Δ (here refl) (refl ∷ (Γ′ ++ˡ Γ⊆Γ″)))
shift-subs-∈ {Γ = Γ} {Γ″ = Γ″} (T ∷ Γ′) Δ (there U∈) Γ⊆Γ″ s
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
shift-cancel-∈ [] Δ (there T∈) s                              = cong (λ t → var (++⁺ʳ Δ (there t))) (∈-⊆-refl T∈)
shift-cancel-∈ (_ ∷ Γ′) Δ (here refl) s                       = refl
shift-cancel-∈ {Γ = Γ} {S = S} (U ∷ Γ′) Δ (there T∈) s
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
