{-# OPTIONS --without-K --safe #-}

module NonCumulative.Unascribed.Semantics.Evaluation where

open import Lib hiding (lookup)
open import NonCumulative.Unascribed.Semantics.Domain

infix 4 _∙_↘_ rec∙_,_,_,_,_↘_ unli∙_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ A c →
         ⟦ T ⟧ ρ ↦ a ↘ B →
         -----------------------------------
         ↑ (Π A T ρ) c ∙ a ↘ ↑ B (c $ ↓ A a)

  data rec∙_,_,_,_,_↘_ : Typ → D → Exp → Env → D → D → Set where
    ze↘  : rec∙ T , a , t , ρ , ze ↘ a
    su↘  : rec∙ T , a , t , ρ , b ↘ b′ →
           ⟦ t ⟧ ρ ↦ b ↦ b′ ↘ a′ →
           ---------------------------------
           rec∙ T , a , t , ρ , su b ↘ a′
    rec∙ : ⟦ T ⟧ ρ ↦ ↑ A′ c ↘ A →
           ------------------------------------------------
           rec∙ T , a , t , ρ , ↑ A′ c ↘ ↑ A (rec T a t ρ c)

  data unli∙_↘_ : D → D → Set where
    li↘   : ∀ {i} → unli∙ li i a ↘ a
    unli↘ : ∀ {i} → unli∙ ↑ (Li i A) c ↘ ↑ A (unli c)

  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦N⟧     : ⟦ N ⟧ ρ ↘ N
    ⟦Π⟧     : ⟦ S ⟧ ρ ↘ A →
              ----------------------
              ⟦ Π S T ⟧ ρ ↘ Π A T ρ
    ⟦Liftt⟧ : ∀ {i} →
              ⟦ T ⟧ ρ ↘ A →
              ---------------------------
              ⟦ Liftt i T ⟧ ρ ↘ Li i A
    ⟦Se⟧    : ∀ i →
              ⟦ Se i ⟧ ρ ↘ U i
    ⟦v⟧     : ∀ n →
              ⟦ v n ⟧ ρ ↘ lookup ρ n
    ⟦ze⟧    : ⟦ ze ⟧ ρ ↘ ze
    ⟦su⟧    : ⟦ t ⟧ ρ ↘ a →
              -----------------
              ⟦ su t ⟧ ρ ↘ su a
    ⟦rec⟧   : ⟦ s ⟧ ρ ↘ a →
              ⟦ t ⟧ ρ ↘ b →
              rec∙ T , a , r , ρ , b ↘ a′ →
              ------------------------
              ⟦ rec T s r t ⟧ ρ ↘ a′
    ⟦Λ⟧     : ∀ t →
              ⟦ Λ S t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧     : ⟦ r ⟧ ρ ↘ f →
              ⟦ s ⟧ ρ ↘ a →
              f ∙ a ↘ b →
              ---------------------
              ⟦ r $ s ⟧ ρ ↘ b
    ⟦liftt⟧ : ∀ {i} →
              ⟦ t ⟧ ρ ↘ a →
              --------------------------
              ⟦ liftt i t ⟧ ρ ↘ li i a
    ⟦unlift⟧ : ⟦ t ⟧ ρ ↘ a →
               unli∙ a ↘ b →
               --------------------------
               ⟦ unlift t ⟧ ρ ↘ b
    ⟦[]⟧    : ⟦ σ ⟧s ρ ↘ ρ′ →
              ⟦ t ⟧ ρ′ ↘ a →
              ---------------------
              ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Subst → Env → Env → Set where
    ⟦I⟧  : ⟦ I ⟧s ρ ↘ ρ
    ⟦wk⟧ : ⟦ wk ⟧s ρ ↘ drop ρ
    ⟦,⟧  : ⟦ σ ⟧s ρ ↘ ρ′ →
           ⟦ t ⟧ ρ ↘ a →
           ---------------------
           ⟦ σ , t ∶ T ⟧s ρ ↘ ρ′ ↦ a
    ⟦∘⟧  : ⟦ τ ⟧s ρ ↘ ρ′ →
           ⟦ σ ⟧s ρ′ ↘ ρ″ →
           -----------------
           ⟦ σ ∘ τ ⟧s ρ ↘ ρ″

-- Evaluation and associated operations are determinitstic.
mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′) = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ A c ↘B) ($∙ .A .c ↘B′)
    rewrite ⟦⟧-det ↘B ↘B′ = refl

  rec-det : rec∙ T , a , r , ρ , b ↘ a′ → rec∙ T , a , r , ρ , b ↘ b′ → a′ ≡ b′
  rec-det ze↘ ze↘          = refl
  rec-det (su↘ ↘a′ ↘a″) (su↘ ↘b′ ↘b″)
    rewrite rec-det ↘a′ ↘b′
          | ⟦⟧-det ↘a″ ↘b″ = refl
  rec-det (rec∙ ↘A) (rec∙ ↘A′)
    rewrite ⟦⟧-det ↘A ↘A′  = refl

  unli-det : unli∙ a ↘ b → unli∙ a ↘ b′ → b ≡ b′
  unli-det li↘ li↘             = refl
  unli-det unli↘ unli↘         = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det ⟦N⟧ ⟦N⟧               = refl
  ⟦⟧-det (⟦Π⟧ ↘a) (⟦Π⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦Se⟧ i) (⟦Se⟧ .i)    = refl
  ⟦⟧-det ⟦ze⟧ ⟦ze⟧             = refl
  ⟦⟧-det (⟦su⟧ ↘a) (⟦su⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦rec⟧ ↘a ↘b rec↘) (⟦rec⟧ ↘a′ ↘b′ rec↘′)
    rewrite ⟦⟧-det ↘a ↘a′
          | ⟦⟧-det ↘b ↘b′
          | rec-det rec↘ rec↘′ = refl
  ⟦⟧-det (⟦v⟧ n) (⟦v⟧ .n)      = refl
  ⟦⟧-det (⟦Λ⟧ t) (⟦Λ⟧ .t)      = refl
  ⟦⟧-det (⟦$⟧ ↘f ↘a ↘b) (⟦$⟧ ↘f′ ↘a′ ↘b′)
    rewrite ⟦⟧-det ↘f ↘f′
          | ⟦⟧-det ↘a ↘a′
          | ap-det ↘b ↘b′      = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦Liftt⟧ ↘a) (⟦Liftt⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦liftt⟧ ↘a) (⟦liftt⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦unlift⟧ ↘a ↘a′) (⟦unlift⟧ ↘b ↘b′)
    rewrite ⟦⟧-det ↘a ↘b
          | unli-det ↘a′ ↘b′   = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦I⟧ ⟦I⟧             = refl
  ⟦⟧s-det ⟦wk⟧ ⟦wk⟧           = refl
  ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b      = refl
  ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
          | ⟦⟧s-det ↘ρ″ ↘ρ⁗   = refl
