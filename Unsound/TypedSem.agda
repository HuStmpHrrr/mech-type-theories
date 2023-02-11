{-# OPTIONS --without-K --safe #-}

module Unsound.TypedSem where

open import Lib
open import Unsound.Statics


mutual
  Env : Set
  Env = ℕ → D

  data D : Set where
    tru : D
    fls : D
    Λ   : (t : Exp) → (ρ : Env) → D
    ↑   : (T : Typ) → (e : Dn) → D

  data Dn : Set where
    l   : (x : ℕ) → Dn
    _$_ : Dn → (d : Df) → Dn

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ T x          = ↑ T (l x)
pattern [_]_$′_ T x y   = ↑ T (_$_ x y)

variable
  a a′ a″    : D
  b b′ b″    : D
  f f′ f″    : D
  e e′ e″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Env

infixl 8 _↦_
_↦_ : Env → D → Env
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x

drop : Env → Env
drop ρ n = ρ (suc n)

infix 4 _∙_↘_ thw_,_,_,_,_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ S T e a → ↑ (S ⟶ T) e ∙ a ↘ ↑ T (e $ ↓ S a)

  data thw_,_,_,_,_↘_ : D → Exp → Exp → Exp → Env → D → Set where
    tru∙ : ⟦ r ⟧ ρ ↘ a →
           --------------------------------
           thw tru , r , r′ , r″ , ρ ↘ a
    fls∙ : ⟦ r′ ⟧ ρ ↘ a →
           --------------------------------
           thw fls , r , r′ , r″ , ρ ↘ a
    ne∙  : ⟦ r″ ⟧ ρ ↘ a →
           --------------------------------
           thw ↑ Bo e , r , r′ , r″ , ρ ↘ a

  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦v⟧   : ∀ n →
            ⟦ v n ⟧ ρ ↘ ρ n
    ⟦tru⟧ : ⟦ tru ⟧ ρ ↘ tru
    ⟦fls⟧ : ⟦ fls ⟧ ρ ↘ fls
    ⟦thw⟧ : ⟦ t ⟧ ρ ↘ a →
            thw a , r , r′ , r″ , ρ ↘ b →
            -----------------------------
            ⟦ thw t r r′ r″ ⟧ ρ ↘ b
    ⟦Λ⟧   : ∀ t →
            ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧   : ⟦ r ⟧ ρ ↘ f →
            ⟦ s ⟧ ρ ↘ a →
            f ∙ a ↘ b →
            ------------------------
            ⟦ r $ s ⟧ ρ ↘ b
    ⟦[]⟧  : ⟦ σ ⟧s ρ ↘ ρ′ →
            ⟦ t ⟧ ρ′ ↘ a →
            ---------------------
            ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Subst → Env → Env → Set where
    ⟦↑⟧ : ⟦ ↑ ⟧s ρ ↘ drop ρ
    ⟦I⟧ : ⟦ I ⟧s ρ ↘ ρ
    ⟦∘⟧ : ⟦ τ ⟧s ρ ↘ ρ′ →
          ⟦ σ ⟧s ρ′ ↘ ρ″ →
          -----------------
          ⟦ σ ∘ τ ⟧s ρ ↘ ρ″
    ⟦,⟧ : ⟦ σ ⟧s ρ ↘ ρ′ →
          ⟦ t ⟧ ρ ↘ a →
          ---------------------
          ⟦ σ , t ⟧s ρ ↘ ρ′ ↦ a


mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′)             = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ S T e _) ($∙ .S .T .e _) = refl

  thw-det : thw a , r , r′ , r″ , ρ ↘ b → thw a , r , r′ , r″ , ρ ↘ b′ → b ≡ b′
  thw-det (tru∙ ↘b) (tru∙ ↘b′) = ⟦⟧-det ↘b ↘b′
  thw-det (fls∙ ↘b) (fls∙ ↘b′) = ⟦⟧-det ↘b ↘b′
  thw-det (ne∙ ↘b) (ne∙ ↘b′)   = ⟦⟧-det ↘b ↘b′

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n) = refl
  ⟦⟧-det ⟦tru⟧ ⟦tru⟧      = refl
  ⟦⟧-det ⟦fls⟧ ⟦fls⟧      = refl
  ⟦⟧-det (⟦thw⟧ ↘a ↘b) (⟦thw⟧ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘a ↘a′ = thw-det ↘b ↘b′
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t) = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′ = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b  = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦↑⟧ ⟦↑⟧           = refl
  ⟦⟧s-det ⟦I⟧ ⟦I⟧           = refl
  ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
          | ⟦⟧s-det ↘ρ″ ↘ρ⁗ = refl
  ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b    = refl


infix 4 Rf_-_↘_ Re_-_↘_

mutual

  data Rf_-_↘_ : ℕ → Df → Nf → Set where
    Rtru : ∀ n →
           Rf n - ↓ Bo tru ↘ tru
    Rfls : ∀ n →
           Rf n - ↓ Bo fls ↘ fls
    RΛ   : ∀ n →
           f ∙ l′ S n ↘ a →
           Rf (suc n) - ↓ T a ↘ w →
           ---------------------
           Rf n - ↓ (S ⟶ T) f ↘ Λ w
    Rne  : ∀ n →
           Re n - e ↘ u →
           ---------------------
           Rf n - ↓ Bo (↑ T e) ↘ ne u

  data Re_-_↘_ : ℕ → Dn → Ne → Set where
    Rl : ∀ n x →
         Re n - l x ↘ v (n ∸ x ∸ 1)
    R$ : ∀ n →
         Re n - e ↘ u →
         Rf n - d ↘ w →
         ---------------------
         Re n - e $ d ↘ u $ w

mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (Rtru _) (Rtru _)      = refl
  Rf-det (Rfls _) (Rfls _)      = refl
  Rf-det (RΛ _ ↘a ↘w) (RΛ _ ↘a′ ↘w′)
    rewrite ap-det ↘a ↘a′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - e ↘ u → Re n - e ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x) = refl
  Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)
    rewrite Re-det ↘u ↘u′
          | Rf-det ↘w ↘w′   = refl

record Nbe n ρ t T w : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↓⟦t⟧ : Rf n - ↓ T ⟦t⟧ ↘ w

InitialEnv : Ctx → Env
InitialEnv []      i       = tru
InitialEnv (T ∷ Γ) zero    = l′ T (L.length Γ)
InitialEnv (T ∷ Γ) (suc i) = InitialEnv Γ i
