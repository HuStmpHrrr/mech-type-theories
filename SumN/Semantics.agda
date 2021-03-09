{-# OPTIONS --without-K --safe #-}

module SumN.Semantics where

open import Lib
open import SumN.Statics

mutual
  Ctx : Set
  Ctx = ℕ → D

  data D : Set where
    ze : D
    su : D → D
    p₁ : D → D
    p₂ : D → D
    pr : D → D → D
    i₁ : D → D
    i₂ : D → D
    Λ  : (t : Exp) → (ρ : Ctx) → D
    ↑  : (T : Typ) → (e : Dn) → D

  data Dn : Set where
    l   : (x : ℕ) → Dn
    _$_ : Dn → (d : Df) → Dn
    pm  : (T : Typ) → Dn → (e e′ : Df) → Dn

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
  ρ ρ′ ρ″    : Ctx

infixl 8 _↦_
_↦_ : Ctx → D → Ctx
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x

drop : Ctx → Ctx
drop ρ n = ρ (suc n)

infix 4 _∙_↘_ p₁_↘_ p₂_↘_ pm_,_,_,_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ S T e a → ↑ (S ⟶ T) e ∙ a ↘ ↑ T (e $ ↓ S a)

  data p₁_↘_ : D → D → Set where
    pr∙ : p₁ pr a b ↘ a
    p₁∙ : p₁ ↑ (S X T) e ↘ p₁ (↑ (S X T) e)

  data p₂_↘_ : D → D → Set where
    pr∙ : p₂ pr a b ↘ b
    p₂∙ : p₂ ↑ (S X T) e ↘ p₂ (↑ (S X T) e)

  data pm_,_,_,_↘_ : Typ → D → D → D → D → Set where
    i₁∙ : b ∙ a ↘ b″ →
          pm T , i₁ a , b , b′ ↘ b″
    i₂∙ : b′ ∙ a ↘ b″ →
          pm T , i₂ a , b , b′ ↘ b″
    pm∙ : pm T , ↑ (S ∪ U) e , b , b′ ↘ ↑ T (pm T e (↓ (S ⟶ T) b) (↓ (S ⟶ U) b′))

  data ⟦_⟧_↘_ : Exp → Ctx → D → Set where
    ⟦v⟧   : ∀ n →
            ⟦ v n ⟧ ρ ↘ ρ n
    ⟦ze⟧  : ⟦ ze ⟧ ρ ↘ ze
    ⟦su⟧  : ⟦ t ⟧ ρ ↘ a →
            -----------------
            ⟦ su t ⟧ ρ ↘ su a
    ⟦p₁⟧  : ⟦ t ⟧ ρ ↘ a →
            p₁ a ↘ b →
            --------------
            ⟦ p₁ t ⟧ ρ ↘ b
    ⟦p₂⟧  : ⟦ t ⟧ ρ ↘ a →
            p₂ a ↘ b →
            --------------
            ⟦ p₁ t ⟧ ρ ↘ b
    ⟦pr⟧  : ⟦ s ⟧ ρ ↘ a →
            ⟦ r ⟧ ρ ↘ b →
            ---------------------
            ⟦ pr s r ⟧ ρ ↘ pr a b
    ⟦i₁⟧  : ⟦ t ⟧ ρ ↘ a →
            -----------------
            ⟦ i₁ t ⟧ ρ ↘ i₁ a
    ⟦i₂⟧  : ⟦ t ⟧ ρ ↘ a →
            -----------------
            ⟦ i₂ t ⟧ ρ ↘ i₂ a
    ⟦pm⟧  : ⟦ t ⟧ ρ ↘ a →
            ⟦ s ⟧ ρ ↘ b →
            ⟦ r ⟧ ρ ↘ b′ →
            pm T , a , b , b′ ↘ b″ →
            ------------------------
            ⟦ pm T t s r ⟧ ρ ↘ b″
    ⟦Λ⟧   : ∀ t →
            ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧   : ⟦ r ⟧ ρ ↘ f →
            ⟦ s ⟧ ρ ↘ a →
            f ∙ a ↘ b →
            ---------------
            ⟦ r $ s ⟧ ρ ↘ b
    ⟦[]⟧  : ⟦ σ ⟧s ρ ↘ ρ′ →
            ⟦ t ⟧ ρ′ ↘ a →
            -----------------
            ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Subst → Ctx → Ctx → Set where
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


-- mutual
--   ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
--   ap-det (Λ∙ ↘b) (Λ∙ ↘b′)             = ⟦⟧-det ↘b ↘b′
--   ap-det ($∙ S T e _) ($∙ .S .T .e _) = refl

--   ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
--   ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n)    = refl
--   ⟦⟧-det ⟦ze⟧ ⟦ze⟧           = refl
--   ⟦⟧-det (⟦su⟧ ↘a) (⟦su⟧ ↘b) = cong su (⟦⟧-det ↘a ↘b)
--   ⟦⟧-det (⟦rec⟧ ↘a′ ↘a″ ↘a r↘) (⟦rec⟧ ↘b′ ↘b″ ↘b r↘′)
--     rewrite ⟦⟧-det ↘a′ ↘b′
--           | ⟦⟧-det ↘a″ ↘b″
--           | ⟦⟧-det ↘a ↘b
--           | rec-det r↘ r↘′   = refl
--   ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t)    = refl
--   ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
--     rewrite ⟦⟧-det ↘f ↘f′
--           | ⟦⟧-det ↘a ↘a′
--           | ap-det ↘b ↘b′    = refl
--   ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
--     rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
--           | ⟦⟧-det ↘a ↘b     = refl

--   rec-det : rec T , f , f′ , f″ ↘ a → rec T , f , f′ , f″ ↘ b → a ≡ b
--   rec-det rze rze         = refl
--   rec-det (rsu ↘a ↘f ↘b) (rsu ↘a′ ↘f′ ↘b′)
--     rewrite rec-det ↘a ↘a′
--           | ap-det ↘f ↘f′
--           | ap-det ↘b ↘b′ = refl
--   rec-det rec rec         = refl

--   ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
--   ⟦⟧s-det ⟦↑⟧ ⟦↑⟧           = refl
--   ⟦⟧s-det ⟦I⟧ ⟦I⟧           = refl
--   ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
--     rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
--           | ⟦⟧s-det ↘ρ″ ↘ρ⁗ = refl
--   ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
--     rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
--           | ⟦⟧-det ↘a ↘b    = refl

-- infix 4 Rf_-_↘_ Re_-_↘_

-- mutual

--   data Rf_-_↘_ : ℕ → Df → Nf → Set where
--     Rze : ∀ n →
--           Rf n - ↓ N ze ↘ ze
--     Rsu : ∀ n →
--           Rf n - ↓ N a ↘ w →
--           --------------------
--           Rf n - ↓ N (su a) ↘ su w
--     RΛ  : ∀ n →
--           f ∙ l′ S n ↘ a →
--           Rf (suc n) - ↓ T a ↘ w →
--           ---------------------
--           Rf n - ↓ (S ⟶ T) f ↘ Λ w
--     Rne : ∀ n →
--           Re n - e ↘ u →
--           ---------------------
--           Rf n - ↓ N (↑ N e) ↘ ne u

--   data Re_-_↘_ : ℕ → Dn → Ne → Set where
--     Rl : ∀ n x →
--          Re n - l x ↘ v (n ∸ x ∸ 1)
--     Rr : ∀ n →
--          Rf n - d′ ↘ w′ →
--          Rf n - d″ ↘ w″ →
--          Re n - e ↘ u →
--          ----------------------------------
--          Re n - rec T d′ d″ e ↘ rec T w′ w″ u
--     R$ : ∀ n →
--          Re n - e ↘ u →
--          Rf n - d ↘ w →
--          ---------------------
--          Re n - e $ d ↘ u $ w

-- mutual
--   Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
--   Rf-det (Rze _) (Rze _)        = refl
--   Rf-det (Rsu _ ↘w) (Rsu _ ↘w′) = cong su (Rf-det ↘w ↘w′)
--   Rf-det (RΛ _ ↘a ↘w) (RΛ _ ↘a′ ↘w′)
--     rewrite ap-det ↘a ↘a′       = cong Λ (Rf-det ↘w ↘w′)
--   Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

--   Re-det : ∀ {n} → Re n - e ↘ u → Re n - e ↘ u′ → u ≡ u′
--   Re-det (Rl _ x) (Rl _ .x) = refl
--   Re-det (Rr _ ↘w ↘w′ ↘u) (Rr _ ↘w″ ↘w‴ ↘u′)
--     rewrite Rf-det ↘w ↘w″
--           | Rf-det ↘w′ ↘w‴
--           | Re-det ↘u ↘u′   = refl
--   Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)
--     rewrite Re-det ↘u ↘u′
--           | Rf-det ↘w ↘w′   = refl

-- record Nbe n ρ t T w : Set where
--   field
--     ⟦t⟧  : D
--     ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
--     ↓⟦t⟧ : Rf n - ↓ T ⟦t⟧ ↘ w

-- InitialCtx : Env → Ctx
-- InitialCtx []      i       = ze
-- InitialCtx (T ∷ Γ) zero    = l′ T (List′.length Γ)
-- InitialCtx (T ∷ Γ) (suc i) = InitialCtx Γ i
