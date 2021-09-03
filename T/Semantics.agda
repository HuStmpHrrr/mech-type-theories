{-# OPTIONS --without-K --safe #-}

module T.Semantics where

open import Lib
open import T.Statics

open Intentional public

mutual
  Env : Set
  Env = ℕ → D

  data D : Set where
    ze : D
    su : D → D
    Λ  : (t : Exp) → (ρ : Env) → D
    ne : Dn → D

  data Dn : Set where
    l   : (x : ℕ) → Dn
    rec : (z s : D) → Dn → Dn
    _$_ : Dn → (d : D) → Dn

infixl 10 _$′_
pattern l′ x = ne (l x)
pattern rec′ z s w = ne (rec z s w)
pattern _$′_ x y = ne (_$_ x y)

variable
  a b d f : D
  d′ d″ : D
  e e′ e″ : Dn
  ρ ρ′ ρ″ : Env

infixl 8 _↦_
_↦_ : Env → D → Env
(ρ ↦ d) zero    = d
(ρ ↦ d) (suc x) = ρ x

drop : Env → Env
drop ρ n = ρ (suc n)


infix 4 _∙_↘_ ⟦_⟧_↘_ rec_,_,_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ e d → ne e ∙ d ↘ e $′ d

  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦v⟧   : ∀ n →
            ⟦ v n ⟧ ρ ↘ ρ n
    ⟦ze⟧  : ⟦ ze ⟧ ρ ↘ ze
    ⟦su⟧  : ⟦ t ⟧ ρ ↘ d →
            -----------------
            ⟦ su t ⟧ ρ ↘ su d
    ⟦rec⟧ : ⟦ s ⟧ ρ ↘ d′ →
            ⟦ r ⟧ ρ ↘ d″ →
            ⟦ t ⟧ ρ ↘ d →
            rec d′ , d″ , d ↘ a →
            -----------------------
            ⟦ rec T s r t ⟧ ρ ↘ a
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

  data rec_,_,_↘_ : D → D → D → D → Set where
    rze : rec d′ , d″ , ze ↘ d′
    rsu : rec d′ , d″ , d ↘ a →
          d″ ∙ d ↘ f →
          f ∙ a ↘ b →
          ----------------------
          rec d′ , d″ , su d ↘ b
    rec : rec d′ , d″ , ne e ↘ rec′ d′ d″ e

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
  ap-det : f ∙ a ↘ b → f ∙ a ↘ d → b ≡ d
  ap-det (Λ∙ x) (Λ∙ y)      = ⟦⟧-det x y
  ap-det ($∙ e _) ($∙ .e _) = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n)     = refl
  ⟦⟧-det ⟦ze⟧ ⟦ze⟧            = refl
  ⟦⟧-det (⟦su⟧ it) (⟦su⟧ it′) = cong su (⟦⟧-det it it′)
  ⟦⟧-det (⟦rec⟧ is ir it r) (⟦rec⟧ is′ ir′ it′ r′)
    rewrite ⟦⟧-det is is′
          | ⟦⟧-det ir ir′
          | ⟦⟧-det it it′
          | rec-det r r′      = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t)     = refl
  ⟦⟧-det (⟦$⟧ ia ia′ ap) (⟦$⟧ ib ib′ ap′)
    rewrite ⟦⟧-det ia ib
          | ⟦⟧-det ia′ ib′
          | ap-det ap ap′     = refl
  ⟦⟧-det (⟦[]⟧ σ it) (⟦[]⟧ σ′ it′)
    rewrite ⟦⟧s-det σ σ′
          | ⟦⟧-det it it′     = refl

  rec-det : rec d , d′ , d″ ↘ a → rec d , d′ , d″ ↘ b → a ≡ b
  rec-det rze rze         = refl
  rec-det (rsu ir f fa) (rsu ir′ f′ fa′)
    rewrite rec-det ir ir′
          | ap-det f f′
          | ap-det fa fa′ = refl
  rec-det rec rec         = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦↑⟧ ⟦↑⟧          = refl
  ⟦⟧s-det ⟦I⟧ ⟦I⟧          = refl
  ⟦⟧s-det (⟦∘⟧ iσ iτ) (⟦∘⟧ iσ′ iτ′)
    rewrite ⟦⟧s-det iσ iσ′
          | ⟦⟧s-det iτ iτ′ = refl
  ⟦⟧s-det (⟦,⟧ iσ it) (⟦,⟧ iσ′ it′)
    rewrite ⟦⟧s-det iσ iσ′
          | ⟦⟧-det it it′  = refl

infix 4 Rf_-_↘_ Re_-_↘_

mutual

  data Rf_-_↘_ : ℕ → D → Nf → Set where
    Rze : ∀ n →
          Rf n - ze ↘ ze
    Rsu : ∀ n →
          Rf n - d ↘ w →
          --------------------
          Rf n - su d ↘ su w
    RΛ  : ∀ n →
          ⟦ t ⟧ ρ ↦ l′ n ↘ b →
          Rf suc n - b ↘ w →
          ---------------------
          Rf n - Λ t ρ ↘ Λ w
    Rne : ∀ n →
          Re n - e ↘ u →
          ---------------------
          Rf n - ne e ↘ ne u

  data Re_-_↘_ : ℕ → Dn → Ne → Set where
    Rl : ∀ n x →
         Re n - l x ↘ v (n ∸ x ∸ 1)
    Rr : ∀ n →
         Rf n - d′ ↘ w′ →
         Rf n - d″ ↘ w″ →
         Re n - e ↘ u →
         ----------------------------------
         Re n - rec d′ d″ e ↘ rec w′ w″ u
    R$ : ∀ n →
         Re n - e ↘ u →
         Rf n - d ↘ w →
         ---------------------
         Re n - e $ d ↘ u $ w

mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (Rze _) (Rze _)             = refl
  Rf-det (Rsu _ ↘w) (Rsu _ ↘w′)      = cong su (Rf-det ↘w ↘w′)
  Rf-det (RΛ _ ↘b ↘w) (RΛ _ ↘b′ ↘w′) = cong Λ (Rf-det ↘w (subst _ (⟦⟧-det ↘b′ ↘b) ↘w′))
  Rf-det (Rne _ ↘u) (Rne _ ↘u′)      = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - e ↘ u → Re n - e ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x)                 = refl
  Re-det (Rr _ ↘w ↘w′ ↘u) (Rr _ ↘v ↘v′ ↘u′) = cong₃ rec (Rf-det ↘w ↘v) (Rf-det ↘w′ ↘v′) (Re-det ↘u ↘u′)
  Re-det (R$ _ ↘u ↘w) (R$ _ ↘u′ ↘w′)        = cong₂ _$_ (Re-det ↘u ↘u′) (Rf-det ↘w ↘w′)

InitEnv : ℕ → Env
InitEnv n i = l′ (n ∸ i ∸ 1)

NormalForm : ℕ → Exp → Nf → Set
NormalForm n t w = ∃ λ d → ⟦ t ⟧ InitEnv n ↘ d × Rf n - d ↘ w
