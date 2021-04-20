{-# OPTIONS --without-K --safe #-}

module Unbox.Statics where

open import Lib

open import Level renaming (suc to succ)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties

import Data.Nat.Properties as Nₚ
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

-- If Δ′ ++ Δ ⊢ t ∶ T, then Δ′ ++ Δ″ ++ Δ ⊢ t ⇑[ |Δ″| ] |Δ′| ∶ T
infix 5 _⇑[_]_
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


-- shift n if index ≥ k in the m'th context
infixl 5 _↑[_/_]_ _↑[_]_
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

infix 3 _⊢_∶_

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

weaken-hd : Γ ∷ Δ ⊢ t ∶ T →
            (Γ′ ++ Γ) ∷ Δ ⊢ t ↑[ L.length Γ′ ] 0 ∶ T
weaken-hd t∶T = weaken [] [] t∶T
