{-# OPTIONS --without-K --safe #-}

module T.TypedSem where

open import Lib
open import T.Statics

open Extensional public

mutual
  Env : Set
  Env = ℕ → D

  data D : Set where
    ze : D
    su : D → D
    Λ  : (t : Exp) → (ρ : Env) → D
    ↑  : (T : Typ) → (e : Dn) → D

  data Dn : Set where
    l   : (x : ℕ) → Dn
    rec : (T : Typ) → (z s : Df) → Dn → Dn
    _$_ : Dn → (d : Df) → Dn

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ T x          = ↑ T (l x)
pattern rec′ T T′ z s w = ↑ T (rec T′ z s w)
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

infix 4 _∙_↘_ ⟦_⟧_↘_ rec_,_,_,_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ S T e a → ↑ (S ⟶ T) e ∙ a ↘ ↑ T (e $ ↓ S a)

  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦v⟧   : ∀ n →
            ⟦ v n ⟧ ρ ↘ ρ n
    ⟦ze⟧  : ⟦ ze ⟧ ρ ↘ ze
    ⟦su⟧  : ⟦ t ⟧ ρ ↘ a →
            -----------------
            ⟦ su t ⟧ ρ ↘ su a
    ⟦rec⟧ : ⟦ s ⟧ ρ ↘ a′ →
            ⟦ r ⟧ ρ ↘ a″ →
            ⟦ t ⟧ ρ ↘ a →
            rec T , a′ , a″ , a ↘ b →
            -----------------------
            ⟦ rec T s r t ⟧ ρ ↘ b
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

  data rec_,_,_,_↘_ : Typ → D → D → D → D → Set where
    rze : rec T , a′ , a″ , ze ↘ a′
    rsu : rec T , a′ , a″ , a ↘ b →
          a″ ∙ a ↘ f →
          f ∙ b ↘ b′ →
          ----------------------
          rec T , a′ , a″ , su a ↘ b′
    rec : rec T , a′ , a″ , ↑ S e ↘ ↑ T (rec T (↓ T a′) (↓ (N ⟶ T ⟶ T) a″) e)

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

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n)    = refl
  ⟦⟧-det ⟦ze⟧ ⟦ze⟧           = refl
  ⟦⟧-det (⟦su⟧ ↘a) (⟦su⟧ ↘b) = cong su (⟦⟧-det ↘a ↘b)
  ⟦⟧-det (⟦rec⟧ ↘a′ ↘a″ ↘a r↘) (⟦rec⟧ ↘b′ ↘b″ ↘b r↘′)
    rewrite ⟦⟧-det ↘a′ ↘b′
          | ⟦⟧-det ↘a″ ↘b″
          | ⟦⟧-det ↘a ↘b
          | rec-det r↘ r↘′   = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t)    = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′    = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b     = refl

  rec-det : rec T , f , f′ , f″ ↘ a → rec T , f , f′ , f″ ↘ b → a ≡ b
  rec-det rze rze         = refl
  rec-det (rsu ↘a ↘f ↘b) (rsu ↘a′ ↘f′ ↘b′)
    rewrite rec-det ↘a ↘a′
          | ap-det ↘f ↘f′
          | ap-det ↘b ↘b′ = refl
  rec-det rec rec         = refl

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
    Rze : ∀ n →
          Rf n - ↓ N ze ↘ ze
    Rsu : ∀ n →
          Rf n - ↓ N a ↘ w →
          --------------------
          Rf n - ↓ N (su a) ↘ su w
    RΛ  : ∀ n →
          f ∙ l′ S n ↘ a →
          Rf (suc n) - ↓ T a ↘ w →
          ---------------------
          Rf n - ↓ (S ⟶ T) f ↘ Λ w
    Rne : ∀ n →
          Re n - e ↘ u →
          ---------------------
          Rf n - ↓ N (↑ T e) ↘ ne u

  data Re_-_↘_ : ℕ → Dn → Ne → Set where
    Rl : ∀ n x →
         Re n - l x ↘ v (n ∸ x ∸ 1)
    Rr : ∀ n →
         Rf n - d′ ↘ w′ →
         Rf n - d″ ↘ w″ →
         Re n - e ↘ u →
         ----------------------------------
         Re n - rec T d′ d″ e ↘ rec T w′ w″ u
    R$ : ∀ n →
         Re n - e ↘ u →
         Rf n - d ↘ w →
         ---------------------
         Re n - e $ d ↘ u $ w

mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (Rze _) (Rze _)        = refl
  Rf-det (Rsu _ ↘w) (Rsu _ ↘w′) = cong su (Rf-det ↘w ↘w′)
  Rf-det (RΛ _ ↘a ↘w) (RΛ _ ↘a′ ↘w′)
    rewrite ap-det ↘a ↘a′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - e ↘ u → Re n - e ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x) = refl
  Re-det (Rr _ ↘w ↘w′ ↘u) (Rr _ ↘w″ ↘w‴ ↘u′)
    rewrite Rf-det ↘w ↘w″
          | Rf-det ↘w′ ↘w‴
          | Re-det ↘u ↘u′   = refl
  Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)
    rewrite Re-det ↘u ↘u′
          | Rf-det ↘w ↘w′   = refl

record Nbe n ρ t T w : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↓⟦t⟧ : Rf n - ↓ T ⟦t⟧ ↘ w

InitialEnv : Ctx → Env
InitialEnv []      i       = ze
InitialEnv (T ∷ Γ) zero    = l′ T (L.length Γ)
InitialEnv (T ∷ Γ) (suc i) = InitialEnv Γ i
