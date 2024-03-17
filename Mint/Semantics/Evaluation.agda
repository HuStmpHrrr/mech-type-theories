{-# OPTIONS --without-K --safe #-}

-- Definition of the evaluation operations
--
-- The evaluation operation evaluates the corresponding syntactic terms into a value
-- in the domain model. During the evaluation, β reduction is performed, so if the
-- evaluation terminates gracefully, the domain value must contain no β redex.
module Mint.Semantics.Evaluation where

open import Lib hiding (lookup)
open import Mint.Semantics.Domain

infix 4 _∙_↘_ unbox∙_,_↘_ rec∙_,_,_,_,_↘_ ⟦_⟧_↘_ ⟦_⟧s_↘_

mutual
  data _∙_↘_ : D → D → D → Set where
    Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
         ------------------
         Λ t ρ ∙ a ↘ b
    $∙ : ∀ A c →
         ⟦ T ⟧ ρ ↦ a ↘ B →
         -----------------------------------
         ↑ (Π A T ρ) c ∙ a ↘ ↑ B (c $ ↓ A a)

  data unbox∙_,_↘_ : ℕ → D → D → Set where
    box↘   : ∀ n →
             unbox∙ n , box a ↘ a [ ins vone n ]
    unbox∙ : ∀ n →
             unbox∙ n , ↑ (□ A) c ↘ ↑ (A [ ins vone n ]) (unbox n c)

  data rec∙_,_,_,_,_↘_ : Typ → D → Exp → Envs → D → D → Set where
    ze↘  : rec∙ T , a , t , ρ , ze ↘ a
    su↘  : rec∙ T , a , t , ρ , b ↘ b′ →
           ⟦ t ⟧ ρ ↦ b ↦ b′ ↘ a′ →
           ---------------------------------
           rec∙ T , a , t , ρ , su b ↘ a′
    rec∙ : ⟦ T ⟧ ρ ↦ ↑ N c ↘ A →
           ------------------------------------------------
           rec∙ T , a , t , ρ , ↑ N c ↘ ↑ A (rec T a t ρ c)

  data ⟦_⟧_↘_ : Exp → Envs → D → Set where
    ⟦N⟧     : ⟦ N ⟧ ρ ↘ N
    ⟦Π⟧     : ⟦ S ⟧ ρ ↘ A →
              ----------------------
              ⟦ Π S T ⟧ ρ ↘ Π A T ρ
    ⟦Se⟧    : ∀ i →
              ⟦ Se i ⟧ ρ ↘ U i
    ⟦□⟧     : ⟦ T ⟧ ext ρ 1 ↘ A →
              --------------------
              ⟦ □ T ⟧ ρ ↘ □ A
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
              ⟦ Λ t ⟧ ρ ↘ Λ t ρ
    ⟦$⟧     : ⟦ r ⟧ ρ ↘ f →
              ⟦ s ⟧ ρ ↘ a →
              f ∙ a ↘ b →
              ---------------------
              ⟦ r $ s ⟧ ρ ↘ b
    ⟦box⟧   : ⟦ t ⟧ ext ρ 1 ↘ a →
              ---------------------
              ⟦ box t ⟧ ρ ↘ box a
    ⟦unbox⟧ : ∀ n →
              ⟦ t ⟧ ρ ∥ n ↘ a →
              unbox∙ O ρ n , a ↘ b →
              ----------------------
              ⟦ unbox n t ⟧ ρ ↘ b
    ⟦[]⟧    : ⟦ σ ⟧s ρ ↘ ρ′ →
              ⟦ t ⟧ ρ′ ↘ a →
              ---------------------
              ⟦ t [ σ ] ⟧ ρ ↘ a

  data ⟦_⟧s_↘_ : Substs → Envs → Envs → Set where
    ⟦I⟧  : ⟦ I ⟧s ρ ↘ ρ
    ⟦wk⟧ : ⟦ wk ⟧s ρ ↘ drop ρ
    ⟦,⟧  : ⟦ σ ⟧s ρ ↘ ρ′ →
           ⟦ t ⟧ ρ ↘ a →
           ---------------------
           ⟦ σ , t ⟧s ρ ↘ ρ′ ↦ a
    ⟦；⟧ : ∀ {n} →
          ⟦ σ ⟧s ρ ∥ n ↘ ρ′ →
          -----------------------------
          ⟦ σ ； n ⟧s ρ ↘ ext ρ′ (O ρ n)
    ⟦∘⟧  : ⟦ τ ⟧s ρ ↘ ρ′ →
           ⟦ σ ⟧s ρ′ ↘ ρ″ →
           -----------------
           ⟦ σ ∘ τ ⟧s ρ ↘ ρ″

pattern ⟦q⟧ ↘σ = ⟦,⟧ (⟦∘⟧ ⟦wk⟧ ↘σ) (⟦v⟧ 0)
pattern ⟦[|ze]⟧ ↘T = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ⟦ze⟧) ↘T
pattern ⟦[[wk∘wk],su[v1]]⟧ ↘T = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ ⟦wk⟧) (⟦su⟧ (⟦v⟧ 1))) ↘T

-- Evaluation and associated operations are determinitstic.
mutual
  ap-det : f ∙ a ↘ b → f ∙ a ↘ b′ → b ≡ b′
  ap-det (Λ∙ ↘b) (Λ∙ ↘b′) = ⟦⟧-det ↘b ↘b′
  ap-det ($∙ A c ↘B) ($∙ .A .c ↘B′)
    rewrite ⟦⟧-det ↘B ↘B′ = refl

  unbox-det : ∀ {n} → unbox∙ n , a ↘ b → unbox∙ n , a ↘ b′ → b ≡ b′
  unbox-det (box↘ _) (box↘ _)     = refl
  unbox-det (unbox∙ _) (unbox∙ _) = refl

  rec-det : rec∙ T , a , r , ρ , b ↘ a′ → rec∙ T , a , r , ρ , b ↘ b′ → a′ ≡ b′
  rec-det ze↘ ze↘          = refl
  rec-det (su↘ ↘a′ ↘a″) (su↘ ↘b′ ↘b″)
    rewrite rec-det ↘a′ ↘b′
          | ⟦⟧-det ↘a″ ↘b″ = refl
  rec-det (rec∙ ↘A) (rec∙ ↘A′)
    rewrite ⟦⟧-det ↘A ↘A′  = refl

  ⟦⟧-det : ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  ⟦⟧-det ⟦N⟧ ⟦N⟧               = refl
  ⟦⟧-det (⟦Π⟧ ↘a) (⟦Π⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦Se⟧ i) (⟦Se⟧ .i)    = refl
  ⟦⟧-det (⟦□⟧ ↘a) (⟦□⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
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
  ⟦⟧-det (⟦box⟧ ↘a) (⟦box⟧ ↘b)
    rewrite ⟦⟧-det ↘a ↘b       = refl
  ⟦⟧-det (⟦unbox⟧ n ↘a ↘a′) (⟦unbox⟧ .n ↘b ↘b′)
    rewrite ⟦⟧-det ↘a ↘b
          | unbox-det ↘a′ ↘b′  = refl
  ⟦⟧-det (⟦[]⟧ ↘ρ′ ↘a) (⟦[]⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b       = refl

  ⟦⟧s-det : ⟦ σ ⟧s ρ ↘ ρ′ → ⟦ σ ⟧s ρ ↘ ρ″ → ρ′ ≡ ρ″
  ⟦⟧s-det ⟦I⟧ ⟦I⟧             = refl
  ⟦⟧s-det ⟦wk⟧ ⟦wk⟧           = refl
  ⟦⟧s-det (⟦,⟧ ↘ρ′ ↘a) (⟦,⟧ ↘ρ″ ↘b)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ″
          | ⟦⟧-det ↘a ↘b      = refl
  ⟦⟧s-det (⟦；⟧ ↘ρ′) (⟦；⟧ ↘ρ″)
      rewrite ⟦⟧s-det ↘ρ′ ↘ρ″ = refl
  ⟦⟧s-det (⟦∘⟧ ↘ρ′ ↘ρ″) (⟦∘⟧ ↘ρ‴ ↘ρ⁗)
    rewrite ⟦⟧s-det ↘ρ′ ↘ρ‴
          | ⟦⟧s-det ↘ρ″ ↘ρ⁗   = refl
