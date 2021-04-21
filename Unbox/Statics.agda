{-# OPTIONS --without-K --safe #-}

module Unbox.Statics where

open import Lib

open import Level renaming (suc to succ)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties
open import Relation.Binary.Definitions

import Data.Nat.ExtraProperties as Nₚ
import Data.List.ExtraProperties as Lₚ
open import Data.List.Membership.Propositional.ExtraProperties

infixr 5 _⟶_

-- types
data Typ : Set where
  *   : Typ
  N   : Typ
  _⟶_ : Typ → Typ → Typ
  □   : Typ → Typ

Env : Set
Env = List Typ

Envs : Set
Envs = List Env

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Env
  Δ Δ′ Δ″ : Envs

infixl 10 _$_
data Exp : Set where
  v     : (x : ℕ) → Exp
  *     : Exp
  ze    : Exp
  su    : Exp → Exp
  Λ     : Exp → Exp
  _$_   : Exp → Exp → Exp
  box   : Exp → Exp
  unbox : ℕ → Exp → Exp

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp

-- modal weakening
-- If Δ′ ++ Δ ⊢ t ∶ T, then Δ′ ++ Δ″ ++ Δ ⊢ t ⇑[ |Δ″| ] |Δ′| ∶ T
infix 5 _⇑[_]_ _⇑_
_⇑[_]_ : Exp → ℕ → ℕ → Exp
v x ⇑[ n ] m   = v x
* ⇑[ n ] m     = *
ze ⇑[ n ] m    = ze
su t ⇑[ n ] m  = su (t ⇑[ n ] m)
Λ t ⇑[ n ] m   = Λ (t ⇑[ n ] m)
s $ u ⇑[ n ] m = (s ⇑[ n ] m) $ (u ⇑[ n ] m)
box t ⇑[ n ] m = box (t ⇑[ n ] 1 + m)
unbox x t ⇑[ n ] m with m ≤? x
... | yes p    = unbox (x + n) t
... | no ¬p    = unbox x (t ⇑[ n ] m ∸ x)

_⇑_ : Exp → ℕ → Exp
t ⇑ n = t ⇑[ n ] 1

-- weakening
-- shift n if index ≥ k in the m'th context
infixl 5 _↑[_/_]_ _↑[_]_ _↑
_↑[_/_]_ : Exp → ℕ → ℕ → ℕ → Exp
v x ↑[ n / k ] 0 with k ≤? x
... | yes p          = v (n + x)
... | no ¬p          = v x
v x ↑[ n / k ] suc m = v x
* ↑[ n / k ] m       = *
ze ↑[ n / k ] m      = ze
su t ↑[ n / k ] m    = su (t ↑[ n / k ] m)
Λ t ↑[ n / k ] 0     = Λ (t ↑[ n / 1 + k ] 0)
Λ t ↑[ n / k ] suc m = Λ (t ↑[ n / k ] suc m)
s $ u ↑[ n / k ] m   = (s ↑[ n / k ] m) $ (u ↑[ n / k ] m)
box t ↑[ n / k ] m   = box (t ↑[ n / k ] 1 + m)
unbox x t ↑[ n / k ] m with x ≤? m
... | yes p          = unbox x (t ↑[ n / k ] m ∸ x)
... | no ¬p          = unbox x t -- x > m

_↑[_]_ : Exp → ℕ → ℕ → Exp
t ↑[ n ] m = t ↑[ n / m ] 0

_↑ : Exp → Exp
t ↑ = t ↑[ 1 ] 0

-- substitution
infixl 5 _[_/_]_ _[_]
_[_/_]_ : Exp → Exp → ℕ → ℕ → Exp
v x [ s / n ] 0 with Nₚ.<-cmp x n
... | tri< x<n _ _  = v x
... | tri≈ _ x≡n _  = s ↑[ n ] 0
... | tri> _ _ n<x  = v (x ∸ 1)
v x [ s / n ] suc m = v x
* [ s / n ] m       = *
ze [ s / n ] m      = ze
su t [ s / n ] m    = su (t [ s / n ] m)
Λ t [ s / n ] 0     = Λ (t [ s / 1 + n ] 0)
Λ t [ s / n ] suc m = Λ (t [ s / n ] suc m)
t $ u [ s / n ] m   = (t [ s / n ] m) $ (u [ s / n ] m)
box t [ s / n ] m   = box (t [ s / n ] 1 + m)
unbox x t [ s / n ] m with x ≤? m
... | yes p         = unbox x (t [ s / n ] m ∸ x)
... | no ¬p         = unbox x t

_[_] : Exp → Exp → Exp
t [ s ] = t [ s / 0 ] 0

-- modal fusion
-- If Δ ++ Γ ∷ Γ′ ∷ Δ′ ⊢ t ∶ T, then Δ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ t ↓[ |Γ| ] |Δ| ∶ T
infixl 5 _↓[_]_ _↓
_↓[_]_ : Exp → ℕ → ℕ → Exp
v x ↓[ n ] m       = v x
* ↓[ n ] m         = *
ze ↓[ n ] m        = ze
su t ↓[ n ] m      = su (t ↓[ n ] m)
Λ t ↓[ n ] 0       = Λ (t ↓[ 1 + n ] 0)
Λ t ↓[ n ] suc m   = Λ (t ↓[ n ] suc m)
s $ t ↓[ n ] m     = (s ↓[ n ] m) $ (t ↓[ n ] m)
box t ↓[ n ] m     = box (t ↓[ n ] 1 + m)
unbox x t ↓[ n ] m with x Nₚ.≤?> m
... | tri< a ¬b ¬c = unbox x (t ↓[ n ] m ∸ x)
... | tri≈ ¬a b ¬c = unbox m (t ↑[ n ] 0)
... | tri> ¬a ¬b c = unbox (x ∸ 1) t

_↓ : Exp → Exp
t ↓ = t ↓[ 0 ] 0

infix 3 _⊢_∶_ _⊢_≈_∶_

data _⊢_∶_ : Envs → Exp → Typ → Set where
  vlookup : ∀ {x} →
            x ∶ T ∈ Γ →
            ---------------
            Γ ∷ Δ ⊢ v x ∶ T
  *-I     : Δ ⊢ * ∶ *
  ze-I    : Δ ⊢ ze ∶ N
  su-I    : Δ ⊢ t ∶ N →
            ------------
            Δ ⊢ su t ∶ N
  Λ-I     : (S ∷ Γ) ∷ Δ ⊢ t ∶ T →
            ---------------------
            Γ ∷ Δ ⊢ Λ t ∶ S ⟶ T
  Λ-E     : Δ ⊢ r ∶ S ⟶ T →
            Δ ⊢ s ∶ S →
            -------------------
            Δ ⊢ r $ s ∶ T
  □-I     : [] ∷ Δ ⊢ t ∶ T →
            ----------------
            Δ ⊢ box t ∶ □ T
  □-E     : ∀ {n} Δ →
            Δ′ ⊢ t ∶ □ T →
            L.length Δ ≡ n →
            ------------------------
            Δ ++ Δ′ ⊢ unbox n t ∶ T

data _⊢_≈_∶_ : Envs → Exp → Exp → Typ → Set where
  v-refl     : ∀ {x} →
               x ∶ T ∈ Γ →
               ----------------------
               Γ ∷ Δ ⊢ v x ≈ v x ∶ T
  *-η        : Δ ⊢ t ∶ * →
               --------------
               Δ ⊢ * ≈ t ∶ *
  ze-≈       : Δ ⊢ ze ≈ ze ∶ N
  su-cong    : Δ ⊢ s ≈ r ∶ N →
               -------------------
               Δ ⊢ su s ≈ su r ∶ N
  Λ-cong     : (S ∷ Γ) ∷ Δ  ⊢ t ≈ t′ ∶ T →
               ---------------------------
               Γ ∷ Δ ⊢ Λ t ≈ Λ t′ ∶ S ⟶ T
  $-cong     : Δ ⊢ t ≈ t′ ∶ S ⟶ T →
               Δ ⊢ s ≈ s′ ∶ S →
               -----------------------
               Δ ⊢ t $ s ≈ t′ $ s′ ∶ T
  box-cong   : [] ∷ Δ ⊢ t ≈ t′ ∶ T →
               ------------------------
               Δ ⊢ box t ≈ box t′ ∶ □ T
  unbox-cong : ∀ {n} Δ →
               Δ′ ⊢ t ≈ t′ ∶ □ T →
               L.length Δ ≡ n →
               ------------------------------------
               Δ ++ Δ′ ⊢ unbox n t ≈ unbox n t′ ∶ T
  ⟶-β        : (S ∷ Γ) ∷ Δ  ⊢ t ∶ T →
               Γ ∷ Δ  ⊢ s ∶ S →
               -------------------------------
               Γ ∷ Δ ⊢ (Λ t) $ s ≈ t [ s ] ∶ T
  ⟶-η        : Γ ∷ Δ ⊢ t ∶ S ⟶ T →
               -----------------------------------
               Γ ∷ Δ ⊢ t ≈ Λ ((t ↑) $ v 0) ∶ S ⟶ T
  □-β₀       : [] ∷ Γ ∷ Δ ⊢ t ∶ T →
               ----------------------------------
               Γ ∷ Δ ⊢ unbox 0 (box t) ≈ t ↓ ∶ T
  □-β        : ∀ {n} Δ′ Γ →
               [] ∷ Δ ⊢ t ∶ T →
               L.length Δ′ ≡ n →
               ---------------------------------------------------------
               Γ ∷ Δ′ ++ Δ ⊢ unbox (suc n) (box t) ≈ t ⇑ L.length Δ′ ∶ T
  □-η        : Δ ⊢ t ∶ □ T →
               -----------------------------
               Δ ⊢ t ≈ box (unbox 1 t) ∶ □ T
  ≈-sym      : Δ ⊢ t ≈ t′ ∶ T →
               ----------------
               Δ ⊢ t′ ≈ t ∶ T
  ≈-trans    : Δ ⊢ t ≈ t′ ∶ T →
               Δ ⊢ t′ ≈ t″ ∶ T →
               ----------------
               Δ ⊢ t ≈ t″ ∶ T

modal-weaken-gen : ∀ {Γs} Δ′ →
                   Γs ⊢ t ∶ T →
                   Γs ≡ Δ′ ++ Δ →
                   1 ≤ L.length Δ′ →
                   Δ′ ++ Δ″ ++ Δ ⊢ t ⇑[ L.length Δ″ ] L.length Δ′ ∶ T
modal-weaken-gen (_ ∷ Δ′) (vlookup T∈Γ) refl (s≤s ≤L)    = vlookup T∈Γ
modal-weaken-gen Δ′ *-I eq ≤L                            = *-I
modal-weaken-gen Δ′ ze-I eq ≤L                           = ze-I
modal-weaken-gen Δ′ (su-I t) eq ≤L                       = su-I (modal-weaken-gen Δ′ t eq ≤L)
modal-weaken-gen (_ ∷ Δ′) (Λ-I t∶T) refl (s≤s ≤L)        = Λ-I (modal-weaken-gen (_ ∷ Δ′) t∶T refl (s≤s ≤L))
modal-weaken-gen Δ′ (Λ-E s u) eq ≤L                      = Λ-E (modal-weaken-gen Δ′ s eq ≤L) (modal-weaken-gen Δ′ u eq ≤L)
modal-weaken-gen Δ′ (□-I t) refl ≤L                      = □-I (modal-weaken-gen ([] ∷ Δ′) t refl (s≤s z≤n))
modal-weaken-gen {unbox n s} {T} {Δ} {Δ₁} (Γ ∷ Δ′) (□-E {Δ″} {_} {_} {n = n} Δ‴ t eq′) eq (s≤s _)
  with L.length (Γ ∷ Δ′) ≤? n
...  | yes p with Lₚ.++-length-inv Δ‴ (Γ ∷ Δ′) eq (subst (λ n → _ ≤ n) (sym eq′) p)
...  | Δ⁗ , refl , refl                = subst (_⊢ unbox (n + L.length Δ₁) s  ∶ T) (sym env-eq) (□-E _ t l-eq)
  where open ≡-Reasoning
        env-eq : Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗ ++ Δ″ ≡ (Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗) ++ Δ″
        env-eq = begin
          Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗ ++ Δ″   ≡˘⟨ cong ((Γ ∷ Δ′) ++_) (++-assoc Δ₁ Δ⁗ Δ″) ⟩
          Γ ∷ Δ′ ++ (Δ₁ ++ Δ⁗) ++ Δ″ ≡˘⟨ ++-assoc (Γ ∷ Δ′) (Δ₁ ++ Δ⁗) Δ″ ⟩
          (Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗) ++ Δ″ ∎
        l-eq : L.length (Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗) ≡ n + L.length Δ₁
        l-eq = begin
          L.length (Γ ∷ Δ′ ++ Δ₁ ++ Δ⁗)                   ≡⟨ Lₚ.length-++ (Γ ∷ Δ′) ⟩
          L.length (Γ ∷ Δ′) + L.length (Δ₁ ++ Δ⁗)         ≡⟨ cong (L.length (Γ ∷ Δ′) +_) (Lₚ.length-++ Δ₁) ⟩
          L.length (Γ ∷ Δ′) + (L.length Δ₁ + L.length Δ⁗) ≡⟨ cong (L.length (Γ ∷ Δ′) +_) (Nₚ.+-comm (L.length Δ₁) _) ⟩
          L.length (Γ ∷ Δ′) + (L.length Δ⁗ + L.length Δ₁) ≡˘⟨ Nₚ.+-assoc (L.length (Γ ∷ Δ′)) _ _ ⟩
          L.length (Γ ∷ Δ′) + L.length Δ⁗ + L.length Δ₁   ≡˘⟨ cong (_+ L.length Δ₁) (length-++ (Γ ∷ Δ′)) ⟩
          L.length (Γ ∷ Δ′ ++ Δ⁗) + L.length Δ₁           ≡⟨ cong (_+ _) eq′ ⟩
          n + L.length Δ₁                                 ∎
modal-weaken-gen {unbox n s} {T} {Δ} {Δ₁} (Γ ∷ Δ′) (□-E {Δ″} {_} {_} {n = n} Δ‴ t eq′) eq (s≤s _)
     | no ¬p with Lₚ.<-length (Γ ∷ Δ′) (Nₚ.≰⇒> ¬p)
...  | Ψ , Ψ′ , eq″ , eq‴ , eq⁗ , 0<Ψ′ = subst₂ (λ Δ m → Δ ⊢ unbox n (s ⇑[ L.length Δ₁ ] m) ∶ T) (sym env-eq) (sym eq⁗) (□-E Ψ s⇑ (sym eq‴))
  where open ≡-Reasoning
        env-eq : Γ ∷ Δ′ ++ Δ₁ ++ Δ ≡ Ψ ++ Ψ′ ++ Δ₁ ++ Δ
        env-eq = begin
          Γ ∷ Δ′ ++ Δ₁ ++ Δ        ≡⟨ cong (_++ _) eq″ ⟩
          (Ψ L.++ Ψ′) L.++ Δ₁ ++ Δ ≡⟨ ++-assoc Ψ _ _ ⟩
          Ψ ++ (Ψ′ ++ Δ₁ ++ Δ)     ∎
        env-eq′ = trans eq (trans (cong (_++ Δ) eq″) (++-assoc Ψ _ _))
        Ψ-eq : Δ‴ ≡ Ψ
        Ψ-eq = Lₚ.length-≡ _ _ env-eq′ (trans eq′ eq‴)
        t∶□T : Ψ′ ++ Δ ⊢ s ∶ □ T
        t∶□T = subst (_⊢ s ∶ □ T) (++-cancelˡ Δ‴ (trans env-eq′ (cong (λ Ψ → Ψ ++ Ψ′ ++ Δ) (sym Ψ-eq)))) t
        s⇑ : Ψ′ L.++ Δ₁ L.++ Δ ⊢ s ⇑[ L.length Δ₁ ] L.length Ψ′ ∶ □ T
        s⇑ = modal-weaken-gen Ψ′ t∶□T refl 0<Ψ′

modal-weaken : ∀ Δ′ →
               Δ′ ++ Δ ⊢ t ∶ T →
               1 ≤ L.length Δ′ →
               Δ′ ++ Δ″ ++ Δ ⊢ t ⇑[ L.length Δ″ ] L.length Δ′ ∶ T
modal-weaken Δ′ t 1<Δ′ = modal-weaken-gen Δ′ t refl 1<Δ′


weaken-gen : ∀ {Γs} Δ′ Γ′ →
             Γs ⊢ t ∶ T →
             Γs ≡ Δ′ ++ (Γ′ ++ Γ) ∷ Δ →
             Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Δ ⊢ t ↑[ L.length Γ″ / L.length Γ′ ] L.length Δ′ ∶ T
weaken-gen {.(v _)} {T} {Γ} {Δ} {Γ″} [] Γ′ (vlookup {_} {_} {_} {x} T∈Γ) refl
  with L.length Γ′ ≤? x
...  | yes p                                                         = vlookup (length-≤-∈ Γ′ T∈Γ p)
weaken-gen {.(v _)} {T} {Γ} {Δ} {Γ″} [] Γ′ (vlookup {_} {_} {_} {x} T∈Γ) refl
     | no ¬p                                                         = vlookup (∈-++ (<-length-∈ Γ′ T∈Γ (Nₚ.≰⇒> ¬p)))
weaken-gen {.(v _)} {T} {Γ} {Δ} {Γ″} (_ ∷ Δ′) Γ′ (vlookup T∈Γ) refl  = vlookup T∈Γ
weaken-gen {.*} {.*} {Γ} {Δ} {Γ″} Δ′ Γ′ *-I eq                       = *-I
weaken-gen {.ze} {.N} {Γ} {Δ} {Γ″} Δ′ Γ′ ze-I eq                     = ze-I
weaken-gen {.(su _)} {.N} {Γ} {Δ} {Γ″} Δ′ Γ′ (su-I t∶T) eq           = su-I (weaken-gen Δ′ Γ′ t∶T eq)
weaken-gen {.(Λ _)} {S ⟶ _} {Γ} {Δ} {Γ″} [] Γ′ (Λ-I t∶T) refl        = Λ-I (weaken-gen [] (S ∷ Γ′) t∶T refl)
weaken-gen {.(Λ _)} {S ⟶ _} {Γ} {Δ} {Γ″} (Γ‴ ∷ Δ′) Γ′ (Λ-I t∶T) refl = Λ-I (weaken-gen ((S ∷ Γ‴) ∷ Δ′) Γ′ t∶T refl)
weaken-gen {.(_ $ _)} {T} {Γ} {Δ} {Γ″} Δ′ Γ′ (Λ-E s∶F t∶T) eq        = Λ-E (weaken-gen Δ′ Γ′ s∶F eq) (weaken-gen Δ′ Γ′ t∶T eq)
weaken-gen {.(box _)} {.(□ _)} {Γ} {Δ} {Γ″} Δ′ Γ′ (□-I t∶T) refl     = □-I (weaken-gen ([] ∷ Δ′) Γ′ t∶T refl)
weaken-gen {unbox n t} {T} {Γ} {Δ} {Γ″} Δ′ Γ′ (□-E {Δ₁} Δ₂ t∶T eq′) eq
  with n ≤? L.length Δ′
...  | yes p with Lₚ.≤-length Δ′ p
...  | Ψ , Ψ′ , refl , eq‴ , eq⁗                                     = subst₂ (λ Δ m → Δ ⊢ unbox n (t ↑[ L.length Γ″ / L.length Γ′ ] m) ∶ T)
                                                                              (sym (++-assoc Ψ _ _)) (sym eq⁗)
                                                                              (□-E Ψ (weaken-gen Ψ′ Γ′ t∶T (++-cancelˡ Ψ (trans (cong (λ Δ → Δ ++ Δ₁) (sym Ψ-eq)) env-eq)))
                                                                                   (sym eq‴))
  where env-eq : Δ₂ ++ Δ₁ ≡ Ψ ++ Ψ′ ++ (Γ′ ++ Γ) ∷ Δ
        env-eq = trans eq (++-assoc Ψ _ _)
        Ψ-eq : Δ₂ ≡ Ψ
        Ψ-eq   = Lₚ.length-≡ Δ₂ Ψ env-eq (trans eq′ eq‴)
weaken-gen {unbox n t} {T} {Γ} {Δ} {Γ″} Δ′ Γ′ (□-E {Δ₁} Δ₂ t∶T eq′) eq
     | no ¬p with Lₚ.++-length-inv Δ₂ (Δ′ ++ (Γ′ ++ Γ) ∷ [])
                                   (trans eq (sym (++-assoc Δ′ _ _)))
                                   (Nₚ.≤-trans (Nₚ.≤-trans (Nₚ.≤-reflexive (trans (length-++ Δ′) (Nₚ.+-comm (L.length Δ′) 1))) (Nₚ.≰⇒> ¬p))
                                               (Nₚ.≤-reflexive (sym eq′)))
...  | Ψ , refl , refl = subst (_⊢ unbox n t ∶ T) (sym env-eq) unboxt
  where open ≡-Reasoning
        env-eq : Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Ψ ++ Δ₁ ≡ (Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Ψ) ++ Δ₁
        env-eq = sym (++-assoc Δ′ _ _)
        unboxt : (Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Ψ) ++ Δ₁ ⊢ unbox n t ∶ T
        unboxt = □-E _ t∶T (begin
          L.length (Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Ψ)   ≡⟨ length-++ Δ′ ⟩
          L.length Δ′ + suc (L.length Ψ)         ≡˘⟨ length-++ Δ′ ⟩
          L.length (Δ′ ++ (Γ′ ++ Γ) ∷ Ψ)         ≡˘⟨ cong L.length (++-assoc Δ′ _ _) ⟩
          L.length ((Δ′ ++ (Γ′ ++ Γ) ∷ []) ++ Ψ) ≡⟨ eq′ ⟩
          n                                      ∎)

weaken : ∀ Δ′ Γ′ →
         Δ′ ++ (Γ′ ++ Γ) ∷ Δ ⊢ t ∶ T →
         Δ′ ++ (Γ′ ++ Γ″ ++ Γ) ∷ Δ ⊢ t ↑[ L.length Γ″ / L.length Γ′ ] L.length Δ′ ∶ T
weaken Δ′ Γ′ t∶T = weaken-gen Δ′ Γ′ t∶T refl

weaken-hd : ∀ Γ′ →
            Γ ∷ Δ ⊢ t ∶ T →
            (Γ′ ++ Γ) ∷ Δ ⊢ t ↑[ L.length Γ′ ] 0 ∶ T
weaken-hd Γ′ t∶T = weaken [] [] t∶T

weaken-[] : ∀ S →
            Γ ∷ Δ ⊢ t ∶ T →
            (S ∷ Γ) ∷ Δ ⊢ t ↑ ∶ T
weaken-[] S = weaken-hd (S ∷ [])

subst-gen : ∀ {Γs} Δ Γ′ →
            Γ ∷ Δ′ ⊢ s ∶ S →
            Γs ⊢ t ∶ T →
            Γs ≡ Δ ++ (Γ′ ++ S ∷ Γ) ∷ Δ′ →
            Δ ++ (Γ′ ++ Γ) ∷ Δ′ ⊢ t [ s / L.length Γ′ ] L.length Δ ∶ T
subst-gen {Γ} {Δ′} {r} {S} {v x} {T} [] Γ′ s∶S (vlookup T∈Γ) refl
  with Nₚ.<-cmp x (L.length Γ′)
... | tri< x<l _ _                                                         = vlookup (∈-++ (<-length-∈ Γ′ T∈Γ x<l))
... | tri> _ _ x>l                                                         = vlookup (length->-inv Γ′ T∈Γ x>l)
... | tri≈ _ refl _ with length-∈-inv Γ′ T∈Γ
... | refl                                                                 = weaken-hd Γ′ s∶S
subst-gen {Γ} {Δ′} {r} {S} {v x} {T} (_ ∷ Δ) Γ′ s∶S (vlookup T∈Γ) refl     = vlookup T∈Γ
subst-gen {Γ} {Δ′} {r} {S} {.*} {.*} Δ Γ′ s∶S *-I eq                       = *-I
subst-gen {Γ} {Δ′} {r} {S} {.ze} {.N} Δ Γ′ s∶S ze-I eq                     = ze-I
subst-gen {Γ} {Δ′} {r} {S} {.(su _)} {.N} Δ Γ′ s∶S (su-I t∶T) eq           = su-I (subst-gen Δ Γ′ s∶S t∶T eq)
subst-gen {Γ} {Δ′} {r} {S} {.(Λ _)} {U ⟶ _} [] Γ′ s∶S (Λ-I t∶T) refl       = Λ-I (subst-gen [] (U ∷ Γ′) s∶S t∶T refl)
subst-gen {Γ} {Δ′} {r} {S} {.(Λ _)} {U ⟶ _} (Γ″ ∷ Δ) Γ′ s∶S (Λ-I t∶T) refl = Λ-I (subst-gen ((U ∷ Γ″) ∷ Δ) Γ′ s∶S t∶T refl)
subst-gen {Γ} {Δ′} {r} {S} {.(_ $ _)} {T} Δ Γ′ s∶S (Λ-E r∶F t∶T) eq        = Λ-E (subst-gen Δ Γ′ s∶S r∶F eq) (subst-gen Δ Γ′ s∶S t∶T eq)
subst-gen {Γ} {Δ′} {r} {S} {.(box _)} {.(□ _)} Δ Γ′ s∶S (□-I t∶T) eq       = □-I (subst-gen ([] ∷ Δ) Γ′ s∶S t∶T (cong ([] ∷_) eq))
subst-gen {Γ} {Δ′} {r} {S} {unbox n t} {T} Δ Γ′ s∶S (□-E {Δ₁} Δ₂ t∶T eq′) eq
  with n ≤? L.length Δ
... | yes p with Lₚ.≤-length Δ p
... | Ψ , Ψ′ , refl , eq‴ , eq⁗                                            = subst₂ (λ Δ m → Δ ⊢ unbox n (t [ r / L.length Γ′ ] m) ∶ T)
                                                                                    env-eq (sym eq⁗)
                                                                                    (□-E Ψ (subst-gen Ψ′ Γ′ s∶S t∶T (++-cancelˡ Ψ env-eq′)) (sym eq‴))
  where env-eq : Ψ ++ Ψ′ ++ (Γ′ ++ Γ) ∷ Δ′ ≡ (Ψ ++ Ψ′) ++ (Γ′ ++ Γ) ∷ Δ′
        env-eq  = sym (++-assoc Ψ _ _)
        Ψ-eq : Δ₂ ≡ Ψ
        Ψ-eq    = Lₚ.length-≡ Δ₂ Ψ (trans eq (++-assoc Ψ _ _)) (trans eq′ eq‴)
        env-eq′ : Ψ L.++ Δ₁ ≡ Ψ L.++ Ψ′ L.++ (Γ′ L.++ S L.∷ Γ) L.∷ Δ′
        env-eq′ = trans (cong (_++ Δ₁) (sym Ψ-eq)) (trans eq (++-assoc Ψ _ _))
subst-gen {Γ} {Δ′} {r} {S} {unbox n t} {T} Δ Γ′ s∶S (□-E {Δ₁} Δ₂ t∶T eq′) eq
    | no ¬p with Lₚ.++-length-inv Δ₂ (Δ ++ (Γ′ ++ S ∷ Γ) ∷ []) (trans eq (sym (++-assoc Δ _ _)))
                 (Nₚ.≤-trans (Nₚ.≤-reflexive (trans (Lₚ.length-++ Δ) (Nₚ.+-comm (L.length Δ) 1)))
                 (Nₚ.≤-trans (Nₚ.≰⇒> ¬p)
                             (Nₚ.≤-reflexive (sym eq′))))
... | Ψ , refl , refl                                                      = subst (_⊢ unbox n t ∶ T) (sym env-eq) unboxt
  where open ≡-Reasoning
        env-eq : Δ ++ (Γ′ ++ Γ) ∷ Ψ ++ Δ₁ ≡ (Δ ++ (Γ′ ++ Γ) ∷ Ψ) ++ Δ₁
        env-eq = sym (++-assoc Δ _ _)
        unboxt : (Δ ++ (Γ′ ++ Γ) ∷ Ψ) ++ Δ₁ ⊢ unbox n t ∶ T
        unboxt = □-E _ t∶T (begin
          L.length (Δ ++ (Γ′ ++ Γ) L.∷ Ψ)           ≡⟨ length-++ Δ ⟩
          L.length Δ + suc (L.length Ψ)             ≡˘⟨ length-++ Δ ⟩
          L.length (Δ ++ (Γ′ L.++ S ∷ Γ) ∷ Ψ)       ≡˘⟨ cong L.length (++-assoc Δ _ _) ⟩
          L.length ((Δ ++ (Γ′ ++ S ∷ Γ) ∷ []) ++ Ψ) ≡⟨ eq′ ⟩
          n                                         ∎)

subst-ty : ∀ Δ Γ′ →
           Γ ∷ Δ′ ⊢ s ∶ S →
           Δ ++ (Γ′ ++ S ∷ Γ) ∷ Δ′ ⊢ t ∶ T →
           Δ ++ (Γ′ ++ Γ) ∷ Δ′ ⊢ t [ s / L.length Γ′ ] L.length Δ ∶ T
subst-ty Δ Γ′ s∶S t∶T = subst-gen Δ Γ′ s∶S t∶T refl

subst-hd : Γ ∷ Δ ⊢ s ∶ S →
           (S ∷ Γ) ∷ Δ ⊢ t ∶ T →
           Γ ∷ Δ ⊢ t [ s ] ∶ T
subst-hd = subst-ty [] []

fusion-gen : ∀ {Γs} Δ →
             Γs ⊢ t ∶ T →
             Γs ≡ Δ ++ Γ ∷ Γ′ ∷ Δ′ →
             Δ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ t ↓[ L.length Γ ] L.length Δ ∶ T
fusion-gen {.(v _)} {T} {Γ} {Γ′} {Δ′} [] (vlookup T∈Γ) refl       = vlookup (∈-++ T∈Γ)
fusion-gen {.(v _)} {T} {Γ} {Γ′} {Δ′} (Γ″ ∷ Δ) (vlookup T∈Γ) refl = vlookup T∈Γ
fusion-gen {.*} {.*} {Γ} {Γ′} {Δ′} Δ *-I eq                       = *-I
fusion-gen {.ze} {.N} {Γ} {Γ′} {Δ′} Δ ze-I eq                     = ze-I
fusion-gen {.(su _)} {.N} {Γ} {Γ′} {Δ′} Δ (su-I t∶T) eq           = su-I (fusion-gen Δ t∶T eq)
fusion-gen {.(Λ _)} {_ ⟶ _} {Γ} {Γ′} {Δ′} [] (Λ-I t∶T) refl       = Λ-I (fusion-gen [] t∶T refl)
fusion-gen {.(Λ _)} {S ⟶ _} {Γ} {Γ′} {Δ′} (Γ″ ∷ Δ) (Λ-I t∶T) refl = Λ-I (fusion-gen ((S ∷ Γ″) ∷ Δ) t∶T refl)
fusion-gen {.(_ $ _)} {T} {Γ} {Γ′} {Δ′} Δ (Λ-E r∶F t∶T) eq        = Λ-E (fusion-gen Δ r∶F eq) (fusion-gen Δ t∶T eq)
fusion-gen {.(box _)} {.(□ _)} {Γ} {Γ′} {Δ′} Δ (□-I t∶T) eq       = □-I (fusion-gen ([] ∷ Δ) t∶T (cong ([] ∷_) eq))
fusion-gen {unbox n t} {T} {Γ} {Γ′} {Δ′} Δ (□-E Δ₁ t∶T eq′) eq with n Nₚ.≤?> L.length Δ
... | tri< n≤l _ _ with Lₚ.≤-length Δ n≤l
... | Ψ , Ψ′ , refl , eq‴ , eq⁗ with Lₚ.length-≡ Δ₁ Ψ (trans eq (++-assoc Ψ _ _)) (trans eq′ eq‴)
... | refl with Lₚ.++-cancelˡ Ψ (trans eq (++-assoc Ψ _ _))
... | refl                                                        = subst₂ (λ Δ m → Δ ⊢ unbox n (t ↓[ L.length Γ ] m) ∶ T)
                                                                           (sym (++-assoc Ψ _ _)) (sym eq⁗) unboxt
  where unboxt : Ψ ++ Ψ′ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ unbox n (t ↓[ L.length Γ ] L.length Ψ′) ∶ T
        unboxt                                                    = □-E Ψ (fusion-gen Ψ′ t∶T refl) (sym eq‴)
fusion-gen {unbox n t} {T} {Γ} {Γ′} {Δ′} Δ (□-E Δ₁ t∶T eq′) eq
    | tri≈ _ n≡1l _ with Lₚ.length-∷-inv Δ₁ Δ eq (trans eq′ n≡1l)
... | refl                                                        = □-E Δ (weaken-hd Γ t∶T) refl
fusion-gen {unbox n t} {T} {Γ} {Γ′} {Δ′} Δ (□-E {Δ₂} Δ₁ t∶T eq′) eq
    | tri> _ _ 1l<n with Lₚ.∷-∷-inv Δ₁ Δ eq (Nₚ.≤-trans 1l<n (Nₚ.≤-reflexive (sym eq′)))
... | Ψ , refl , refl                                             = subst (_⊢ unbox (n ∸ 1) t ∶ T) (++-assoc Δ _ _) unboxt
  where open ≡-Reasoning
        l-eq : L.length (Δ ++ (Γ ++ Γ′) L.∷ Ψ) ≡ n ∸ 1
        l-eq = begin
          L.length (Δ ++ (Γ ++ Γ′) L.∷ Ψ)     ≡⟨ length-++ Δ ⟩
          L.length Δ + suc (L.length Ψ)       ≡˘⟨ Nₚ.+-∸-assoc (L.length Δ) (s≤s z≤n) ⟩
          (L.length Δ + (2 + L.length Ψ)) ∸ 1 ≡˘⟨ cong (_∸ 1) (length-++ Δ) ⟩
          L.length (Δ ++ Γ ∷ Γ′ ∷ Ψ) ∸ 1      ≡⟨ cong (_∸ 1) eq′ ⟩
          n ∸ 1                               ∎
        unboxt : (Δ ++ (Γ ++ Γ′) ∷ Ψ) ++ Δ₂ ⊢ unbox (n ∸ 1) t ∶ T
        unboxt = □-E _ t∶T l-eq

fusion : ∀ Δ →
         Δ ++ Γ ∷ Γ′ ∷ Δ′ ⊢ t ∶ T →
         Δ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ t ↓[ L.length Γ ] L.length Δ ∶ T
fusion Δ t∶T = fusion-gen Δ t∶T refl

fusion-[] : [] ∷ Γ ∷ Δ′ ⊢ t ∶ T →
            Γ ∷ Δ′ ⊢ t ↓ ∶ T
fusion-[] = fusion []

auto-weaken-gen : ∀ {Γs} Δ →
                  Γs ⊢ t ∶ T →
                  Γs ≡ Δ ++ Γ ∷ Δ′ →
                  Δ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ t ∶ T
auto-weaken-gen {.(v _)} {T} {Γ} {Δ′} {Γ′} [] (vlookup T∈Γ) refl       = vlookup (∈-++ T∈Γ)
auto-weaken-gen {.(v _)} {T} {Γ} {Δ′} {Γ′} (Γ″ ∷ Δ) (vlookup T∈Γ) refl = vlookup T∈Γ
auto-weaken-gen {.*} {.*} {Γ} {Δ′} {Γ′} Δ *-I eq                       = *-I
auto-weaken-gen {.ze} {.N} {Γ} {Δ′} {Γ′} Δ ze-I eq                     = ze-I
auto-weaken-gen {.(su _)} {.N} {Γ} {Δ′} {Γ′} Δ (su-I t∶T) eq           = su-I (auto-weaken-gen Δ t∶T eq)
auto-weaken-gen {.(Λ _)} {S ⟶ _} {Γ} {Δ′} {Γ′} [] (Λ-I t∶T) refl       = Λ-I (auto-weaken-gen [] t∶T refl)
auto-weaken-gen {.(Λ _)} {S ⟶ _} {Γ} {Δ′} {Γ′} (Γ″ ∷ Δ) (Λ-I t∶T) refl = Λ-I (auto-weaken-gen ((S ∷ Γ″) ∷ Δ) t∶T refl)
auto-weaken-gen {.(_ $ _)} {T} {Γ} {Δ′} {Γ′} Δ (Λ-E t∶T t∶T₁) eq       = Λ-E (auto-weaken-gen Δ t∶T eq) (auto-weaken-gen Δ t∶T₁ eq)
auto-weaken-gen {.(box _)} {.(□ _)} {Γ} {Δ′} {Γ′} Δ (□-I t∶T) eq       = □-I (auto-weaken-gen ([] ∷ Δ) t∶T (cong ([] ∷_) eq))
auto-weaken-gen {unbox n t} {T} {Γ} {Δ′} {Γ′} Δ (□-E {Δ₂} Δ₁ t∶T eq′) eq
  with n ≤? L.length Δ
...  | yes p with Lₚ.≤-length Δ p
...  | Ψ , Ψ′ , refl , eq‴ , eq⁗ with Lₚ.length-≡ Δ₁ Ψ (trans eq (++-assoc Ψ _ _)) (trans eq′ eq‴)
...  | refl with Lₚ.++-cancelˡ Ψ (trans eq (++-assoc Ψ _ _))
...  | refl                                                            = subst (_⊢ unbox n t ∶ T) (sym (++-assoc Ψ _ _)) unboxt
  where unboxt : Ψ ++ Ψ′ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ unbox n t ∶ T
        unboxt = □-E Ψ (auto-weaken-gen Ψ′ t∶T refl) eq′
auto-weaken-gen {unbox n t} {T} {Γ} {Δ′} {Γ′} Δ (□-E {Δ₂} Δ₁ t∶T eq′) eq
     | no ¬p with Lₚ.++-length-inv Δ₁ (Δ ++ Γ ∷ []) (trans eq (sym (++-assoc Δ _ _)))
                                   (Nₚ.≤-trans (Nₚ.≤-reflexive (trans (length-++ Δ) (Nₚ.+-comm (L.length Δ) 1)))
                                   (Nₚ.≤-trans (Nₚ.≰⇒> ¬p)
                                               (Nₚ.≤-reflexive (sym eq′))))
...  | Ψ , refl , refl                                                 = subst (_⊢ unbox n t ∶ T) (++-assoc Δ _ _) unboxt
  where open ≡-Reasoning
        l-eq :  L.length (Δ ++ (Γ ++ Γ′) ∷ Ψ) ≡ n
        l-eq = begin
          L.length (Δ ++ (Γ ++ Γ′) ∷ Ψ) ≡⟨ length-++ Δ ⟩
          L.length Δ + suc (L.length Ψ) ≡˘⟨ length-++ Δ ⟩
          L.length (Δ ++ Γ ∷ Ψ)         ≡˘⟨ cong L.length (++-assoc Δ _ _) ⟩
          L.length ((Δ ++ Γ ∷ []) ++ Ψ) ≡⟨ eq′ ⟩
          n                             ∎
        unboxt : (Δ ++ (Γ ++ Γ′) ∷ Ψ) ++ Δ₂ ⊢ unbox n t ∶ T
        unboxt = □-E _ t∶T l-eq

auto-weaken : ∀ Δ →
              Δ ++ Γ ∷ Δ′ ⊢ t ∶ T →
              Δ ++ (Γ ++ Γ′) ∷ Δ′ ⊢ t ∶ T
auto-weaken Δ t∶T = auto-weaken-gen Δ t∶T refl

≈-refl : Δ ⊢ t ∶ T →
         Δ ⊢ t ≈ t ∶ T
≈-refl (vlookup T∈Γ) = v-refl T∈Γ
≈-refl *-I           = *-η *-I
≈-refl ze-I          = ze-≈
≈-refl (su-I t)      = su-cong (≈-refl t)
≈-refl (Λ-I t)       = Λ-cong (≈-refl t)
≈-refl (Λ-E s u)     = $-cong (≈-refl s) (≈-refl u)
≈-refl (□-I t)       = box-cong (≈-refl t)
≈-refl (□-E Δ t eq)  = unbox-cong Δ (≈-refl t) eq

≈-inv : Δ ⊢ t ≈ t′ ∶ T →
        Δ ⊢ t ∶ T × Δ ⊢ t′ ∶ T
≈-inv (v-refl T∈Γ)            = vlookup T∈Γ , vlookup T∈Γ
≈-inv (*-η t′∶*)              = *-I , t′∶*
≈-inv ze-≈                    = ze-I , ze-I
≈-inv (su-cong t≈t′) with ≈-inv t≈t′
... | t∶N , t′∶N              = su-I t∶N , su-I t′∶N
≈-inv (Λ-cong t≈t′) with ≈-inv t≈t′
... | t∶T , t′∶T              = Λ-I t∶T , Λ-I t′∶T
≈-inv ($-cong t≈t′ s≈s′) with ≈-inv t≈t′ | ≈-inv s≈s′
... | t∶F , t′∶F | s∶S , s′∶S = Λ-E t∶F s∶S , Λ-E t′∶F s′∶S
≈-inv (box-cong t≈t′) with ≈-inv t≈t′
... | t∶T , t′∶T              = □-I t∶T , □-I t′∶T
≈-inv (unbox-cong Δ t≈t′ eq) with ≈-inv t≈t′
... | t∶T , t′∶T              = □-E Δ t∶T eq , □-E Δ t′∶T eq
≈-inv (⟶-β t s)               = Λ-E (Λ-I t) s , subst-hd s t
≈-inv (⟶-η t)                 = t , Λ-I (Λ-E (weaken-[] _ t) (vlookup here))
≈-inv (□-β₀ t)                = □-E [] (□-I t) refl , fusion-[] t
≈-inv (□-β Δ′ Γ t eq)         = □-E _ (□-I t) (cong suc eq) , modal-weaken (Γ ∷ []) (auto-weaken [] t) (s≤s z≤n)
≈-inv (□-η t)                 = t , □-I (□-E _ t refl)
≈-inv (≈-sym t≈t′) with ≈-inv t≈t′
... | t∶T , t′∶T              = t′∶T , t∶T
≈-inv (≈-trans t≈t′ t′≈t″) with ≈-inv t≈t′ | ≈-inv t′≈t″
... | t∶T , _ | _ , t″∶T      = t∶T , t″∶T
