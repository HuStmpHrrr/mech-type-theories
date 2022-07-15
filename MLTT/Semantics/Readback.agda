{-# OPTIONS --without-K --safe #-}

-- Definition of readback functions
--
-- The readback functions read from the domain model back to the syntax as
-- normal/neutral forms. The readback function is tyle-intended value directed and
-- performs η expansion during the process. Combined with evaluation, after reading
-- back, we obtain β-η normal form.
--
-- All readback functions receive a natural number. This number is the length of the
-- context and is responsible for maintaining the correspondence between syntactic
-- variables and domain variables.
module MLTT.Semantics.Readback where

open import Lib
open import MLTT.Semantics.Domain
open import MLTT.Semantics.Evaluation


-- Readback functions
--
-- There are three readback functions:
-- Rf: readback from domain normal forms to syntactic normal forms, performing η expansion as well
-- Re: readback from domain neutral forms to syntactic neutral forms
-- Rty: readback from domain value that is intended to represent types to syntactic normal forms
infix 4 Rf_-_↘_ Re_-_↘_ Rty_-_↘_

mutual

  data Rf_-_↘_ : ℕ → Df → Nf → Set where
    RU  : ∀ {i} n →
          Rty n - A ↘ W →
          ---------------------
          Rf n - ↓ (U i) A ↘ W
    Rze : ∀ n →
          Rf n - ↓ N ze ↘ ze
    Rsu : ∀ n →
          Rf n - ↓ N a ↘ w →
          ---------------------------
          Rf n - ↓ N (su a) ↘ (su w)
    RΛ  : ∀ n →
          a ∙ l′ A n ↘ b →
          ⟦ T ⟧ ρ ↦ l′ A n ↘ B →
          Rf 1 + n - ↓ B b ↘ w →
          ------------------------------
          Rf n - ↓ (Π A T ρ) a ↘ Λ w
    RN  : ∀ n →
          Re n - c ↘ u →
          --------------------------
          Rf n - ↓ N (↑ N c) ↘ ne u
    Rne : ∀ n →
          Re n - c′ ↘ u →
          ----------------------------------
          Rf n - ↓ (↑ A c) (↑ A′ c′) ↘ ne u

  data Re_-_↘_ : ℕ → Dn → Ne → Set where
    Rl : ∀ n x →
         Re n - l x ↘ v (n ∸ x ∸ 1)
    R$ : ∀ n →
         Re n - c ↘ u →
         Rf n - d ↘ w →
         ---------------------
         Re n - c $ d ↘ u $ w
    Rr : ∀ n →
         -- compute normal form of the motive
         ⟦ T ⟧ ρ ↦ l′ N n ↘ A →
         Rty 1 + n - A ↘ W →
         -- compute normal form of the base case
         ⟦ T ⟧ ρ ↦ ze ↘ A′ →
         Rf n - ↓ A′ a ↘ w →
         -- compute normal form of the step case
         ⟦ t ⟧ ρ ↦ l′ N n ↦ l′ A (suc n) ↘ b →
         ⟦ T ⟧ ρ ↦ su (l′ N n) ↘ A″ →
         Rf 2 + n - ↓ A″ b ↘ w′ →
         -- compute neutral form of the number
         Re n - c ↘ u →
         Re n - rec T a t ρ c ↘ rec W w w′ u

  data Rty_-_↘_ : ℕ → D → Nf → Set where
    RU  : ∀ {i} n →
          Rty n - U i ↘ Se i
    RN  : ∀ n →
          Rty n - N ↘ N
    RΠ  : ∀ n →
          Rty n - A ↘ W →
          ⟦ T ⟧ ρ ↦ l′ A n ↘ B →
          Rty 1 + n - B ↘ W′ →
          ------------------------------
          Rty n - Π A T ρ ↘ Π W W′
    Rne : ∀ n →
          Re n - c ↘ V →
          ---------------------
          Rty n - ↑ A c ↘ ne V

-- All readback functions are deterministic.
mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (RU _ ↘W) (RU _ ↘W′)   = Rty-det ↘W ↘W′
  Rf-det (Rze _) (Rze _)        = refl
  Rf-det (Rsu _ ↘w) (Rsu _ ↘w′) = cong su (Rf-det ↘w ↘w′)
  Rf-det (RΛ _ ↘a ↘A ↘w) (RΛ _ ↘a′ ↘A′ ↘w′)
    rewrite ap-det ↘a ↘a′
          | ⟦⟧-det ↘A ↘A′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (RN _ ↘u) (RN _ ↘u′)   = cong ne (Re-det ↘u ↘u′)
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {n} → Re n - c ↘ u → Re n - c ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x)          = refl
  Re-det (R$ _ ↘c ↘w) (R$ _ ↘c′ ↘w′) = cong₂ _$_ (Re-det ↘c ↘c′) (Rf-det ↘w ↘w′)
  Re-det (Rr _ ↘A ↘W ↘Az ↘w ↘b ↘As ↘w′ ↘c) (Rr _ ↘A′ ↘W′ ↘Az′ ↘w″ ↘b′ ↘As′ ↘w‴ ↘c′)
    rewrite ⟦⟧-det ↘A ↘A′
          | Rty-det ↘W ↘W′
          | ⟦⟧-det ↘Az ↘Az′
          | Rf-det ↘w ↘w″
          | ⟦⟧-det ↘b ↘b′
          | ⟦⟧-det ↘As ↘As′
          | Rf-det ↘w′ ↘w‴
          | Re-det ↘c ↘c′            = refl

  Rty-det : ∀ {n} → Rty n - A ↘ W → Rty n - A ↘ W′ → W ≡ W′
  Rty-det (RU _) (RU _)          = refl
  Rty-det (RN _) (RN _)          = refl
  Rty-det (RΠ _ ↘W ↘B ↘W′) (RΠ _ ↘W″ ↘B′ ↘W‴)
    rewrite Rty-det ↘W ↘W″
          | ⟦⟧-det ↘B ↘B′
          | Rty-det ↘W′ ↘W‴      = refl
  Rty-det (Rne _ ↘V) (Rne _ ↘V′) = cong ne (Re-det ↘V ↘V′)

-- Normalization by evaluation where an evaluation environment is passed externally
record NbEEnvs n ρ t T w : Set where
  field
    ⟦t⟧  : D
    ⟦T⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦T⟧ : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↓⟦t⟧ : Rf n - ↓ ⟦T⟧ ⟦t⟧ ↘ w

-- Compute an initial global evaluation environment using a context stack
data InitEnvs : Ctx → Env → Set where
  base : InitEnvs [] emp
  s-∷  : InitEnvs Γ ρ →
         ⟦ T ⟧ ρ ↘ A →
         ------------------------------------------
         InitEnvs (T ∷ Γ) (ρ ↦ l′ A (len Γ))

-- Normalization by evaluation
--
-- We will show that if Γ ⊢ t ∶ T, then there must be a normal form w such that NbE Γ t T w
record NbE Γ t T w : Set where
  field
    envs : Env
    init : InitEnvs Γ envs
    nbe  : NbEEnvs (len Γ) envs t T w

-- Above definitions are all deterministic
InitEnvs-det : InitEnvs Γ ρ → InitEnvs Γ ρ′ → ρ ≡ ρ′
InitEnvs-det base base                     = refl
InitEnvs-det (s-∷ {Ψ} ↘ρ ↘A) (s-∷ ↘ρ′ ↘A′)
  rewrite InitEnvs-det ↘ρ ↘ρ′ = cong (λ A → _ ↦ l′ A (len Ψ)) (⟦⟧-det ↘A ↘A′)

NbE-det : NbE Γ t T w →
          NbE Γ t T w′ →
          w ≡ w′
NbE-det nbe nbe′
  with nbe | nbe′
... | record { envs = _ ; init = ↘ρ ; nbe = record { ⟦t⟧ = _ ; ⟦T⟧ = _ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } }
    | record { envs = _ ; init = ↘ρ′ ; nbe = record { ⟦t⟧ = _ ; ⟦T⟧ = _ ; ↘⟦t⟧ = ↘⟦t⟧′ ; ↘⟦T⟧ = ↘⟦T⟧′ ; ↓⟦t⟧ = ↓⟦t⟧′ } }
    rewrite InitEnvs-det ↘ρ ↘ρ′
          | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′
          | ⟦⟧-det ↘⟦t⟧ ↘⟦t⟧′ = Rf-det ↓⟦t⟧ ↓⟦t⟧′
