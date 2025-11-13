{-# OPTIONS --without-K --safe #-}

module STLCSubst.Semantics.Definitions where

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Lib

open import STLCSubst.Statics

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
    rec : (T : Typ) → (z : Df) → (s : Exp) → (ρ : Env) → Dn → Dn
    _$_ : Dn → (d : Df) → Dn

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infixl 10 [_]_$′_
pattern l′ T x          = ↑ T (l x)
pattern rec′ T T′ z s ρ w = ↑ T (rec T′ z s ρ w)
pattern [_]_$′_ T x y   = ↑ T (_$_ x y)

variable
  a a′ a″    : D
  b b′ b″    : D
  f f′ f″    : D
  e e′ e″    : Dn
  d d′ d″ d‴ : Df
  ρ ρ′ ρ″    : Env

env-ext : Env → D → Env
env-ext ρ d zero = d
env-ext ρ d (suc x) = ρ x

instance
  Env-Extends : Extends Env D
  Env-Extends = record { _↦_ = env-ext }

ext-cong : ρ ≗ ρ′ → a ≡ a′ → ρ ↦ a ≗ ρ′ ↦ a′
ext-cong eq eq′ zero    = eq′
ext-cong eq eq′ (suc x) = eq x

drop : Env → Env
drop ρ n = ρ (suc n)

infix 4 _∙_↘_ ⟦_⟧_↘_ rec_,_,_,_,_↘_ ⟦_⟧s_↘_

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
            ⟦ t ⟧ ρ ↘ a →
            rec T , a′ , r , ρ , a ↘ b →
            -----------------------
            ⟦ rec T s r t ⟧ ρ ↘ b
    ⟦Λ⟧   : ∀ t →
            ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧   : ⟦ r ⟧ ρ ↘ f →
            ⟦ s ⟧ ρ ↘ a →
            f ∙ a ↘ b →
            ------------------------
            ⟦ r $ s ⟧ ρ ↘ b

  data rec_,_,_,_,_↘_ : Typ → D → Exp → Env → D → D → Set where
    rze : rec T , a′ , r , ρ , ze ↘ a′
    rsu : rec T , a′ , r , ρ , a ↘ b →
          ⟦ r ⟧ ρ ↦ a ↦ b ↘ b′ →
          ----------------------
          rec T , a′ , r , ρ , su a ↘ b′
    rec : rec T , a′ , r , ρ , ↑ S e ↘ ↑ T (rec T (↓ T a′) r ρ e)

⟦_⟧s_↘_ : Subst → Env → Env → Set
⟦ σ ⟧s ρ ↘ ρ′ = ∀ x → ⟦ σ x ⟧ ρ ↘ ρ′ x

⟦⟧s-transp : (δ : Subst) → σ ≗ δ → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ δ ⟧s ρ ↘ ρ′
⟦⟧s-transp δ eq ↘ρ′ x
  with ↘ρ′ x
...  | ↘ρ′ rewrite eq x = ↘ρ′

⟦⟧s-transp-ret : ρ′ ≗ ρ″ → ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″
⟦⟧s-transp-ret {_} {ρ″} eq ↘ρ′ x
  with ρ″ x | eq x
...  | _ | refl = ↘ρ′ x

⟦⟧s-ext : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ t ⟧ ρ ↘ a → ⟦ σ ↦ t ⟧s ρ ↘ ρ′ ↦ a
⟦⟧s-ext ↘ρ′ ↘a zero    = ↘a
⟦⟧s-ext ↘ρ′ ↘a (suc x) = ↘ρ′ x

⟦_⟧w : Wk → Env → Env
⟦ ϕ ⟧w ρ n = ρ (ϕ n)

⟦⟧s-conv : (ϕ : Wk) → ⟦ conv ϕ ⟧s ρ ↘ ρ′ → ρ′ ≗ ⟦ ϕ ⟧w ρ
⟦⟧s-conv {ρ′ = ρ′} ϕ ↘ρ′ x
  with ρ′ x | ↘ρ′ x
... | _ | ⟦v⟧ n = refl

⟦⟧s-id : ⟦ id ⟧s ρ ↘ ρ′ → ρ ≗ ρ′
⟦⟧s-id {ρ} {ρ′} ↘ρ′ x
  with ρ′ x | ↘ρ′ x
...  | _ | ⟦v⟧ n = refl

⟦⟧w-comp : ∀ ψ ϕ ρ → ⟦ ψ ⟧w (⟦ ϕ ⟧w ρ) ≗ ⟦ ψ ∙ ϕ ⟧w ρ
⟦⟧w-comp ψ ϕ ρ x = refl

mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′)             = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ S T e _) ($∙ .S .T .e _) = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n)    = refl
  ⟦⟧-det ⟦ze⟧ ⟦ze⟧           = refl
  ⟦⟧-det (⟦su⟧ ↘a) (⟦su⟧ ↘b) = cong su (⟦⟧-det ↘a ↘b)
  ⟦⟧-det (⟦rec⟧ ↘a′ ↘a r↘) (⟦rec⟧ ↘b′ ↘b r↘′)
    rewrite ⟦⟧-det ↘a′ ↘b′
          | ⟦⟧-det ↘a ↘b
          | rec-det r↘ r↘′   = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t)    = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′    = refl

  rec-det : rec T , f , t , ρ , f″ ↘ a → rec T , f , t , ρ , f″ ↘ b → a ≡ b
  rec-det rze rze         = refl
  rec-det (rsu ↘a ↘b) (rsu ↘a′ ↘b′)
    rewrite rec-det ↘a ↘a′
          | ⟦⟧-det ↘b ↘b′ = refl
  rec-det rec rec         = refl

⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≗ ρ″
⟦⟧s-det ↘ρ′ ↘ρ″ x = ⟦⟧-det (↘ρ′ x) (↘ρ″ x)

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
         ⟦ s ⟧ ρ ↦ l′ N n ↦ l′ T (1 + n) ↘ a →
         Rf (2 + n) - ↓ T a ↘ w″ →
         Re n - e ↘ u →
         ----------------------------------
         Re n - rec T d′ s ρ e ↘ rec T w′ w″ u
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
  Re-det (Rr _ ↘w ↘a ↘w′ ↘u) (Rr _ ↘w″ ↘a′ ↘w‴ ↘u′)
    rewrite Rf-det ↘w ↘w″
          | ⟦⟧-det ↘a ↘a′
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
