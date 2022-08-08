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
module NonCumulative.Semantics.Readback where

open import Lib
open import NonCumulative.Semantics.Domain
open import NonCumulative.Semantics.Evaluation


-- Readback functions
--
-- There are three readback functions:
-- Rf: readback from domain normal forms to syntactic normal forms, performing η expansion as well
-- Re: readback from domain neutral forms to syntactic neutral forms
-- Rty: readback from domain value that is intended to represent types to syntactic normal forms
infix 4 Rf_-_↘_ Re_-_↘_ Rty_-_at_↘_

mutual

  data Rf_-_↘_ : ℕ → Df → Nf → Set where
    RU  : ∀ {i j} n →
          Rty n - A at i ↘ W →
          j ≡ suc i →
          ---------------------
          Rf n - ↓ j (U i) A ↘ W
    Rze : ∀ n →
          Rf n - ↓ 0 N ze ↘ ze
    Rsu : ∀ n →
          Rf n - ↓ 0 N a ↘ w →
          ---------------------------
          Rf n - ↓ 0 N (su a) ↘ (su w)
    RΛ  : ∀ {i j k} n →
          Rty n - A at i ↘ W →
          a ∙ l′ i A n ↘ b →
          ⟦ T ⟧ ρ ↦ l′ i A n ↘ B →
          Rf 1 + n - ↓ j B b ↘ w →
          k ≡ max i j →
          ------------------------------
          Rf n - ↓ k (Π i A (T ↙ j) ρ) a ↘ Λ (W ↙ i) w
    Rli : ∀ {i j k} n →
          unli∙ a ↘ b →
          Rf n - ↓ j A b ↘ w →
          k ≡ i + j →
          ---------------------------
          Rf n - ↓ k (Li i j A) a ↘ liftt i w
    RN  : ∀ n →
          Re n - c ↘ u →
          --------------------------
          Rf n - ↓ 0 N (↑ 0 N c) ↘ ne u
    Rne : ∀ {i j k} n →
          Re n - c ↘ u →
          k ≡ suc j →
          i ≡ j →
          ----------------------------------
          Rf n - ↓ i (↑ k A C) (↑ j A′ c) ↘ ne u

  data Re_-_↘_ : ℕ → Dn → Ne → Set where
    Rl : ∀ n x →
         Re n - l x ↘ v (n ∸ x ∸ 1)
    R$ : ∀ n →
         Re n - c ↘ u →
         Rf n - d ↘ w →
         ---------------------
         Re n - c $ d ↘ u $ w
    Rr : ∀ {i} n →
         -- compute normal form of the motive
         ⟦ T ⟧ ρ ↦ l′ 0 N n ↘ A →
         Rty 1 + n - A at i ↘ W →
         -- compute normal form of the base case
         ⟦ T ⟧ ρ ↦ ze ↘ A′ →
         Rf n - ↓ i A′ a ↘ w →
         -- compute normal form of the step case
         ⟦ t ⟧ ρ ↦ l′ 0 N n ↦ l′ i A (suc n) ↘ b →
         ⟦ T ⟧ ρ ↦ su (l′ 0 N n) ↘ A″ →
         Rf 2 + n - ↓ i A″ b ↘ w′ →
         -- compute neutral form of the number
         Re n - c ↘ u →
         ----------------------------
         Re n - rec (T ↙ i) a t ρ c ↘ rec (W ↙ i) w w′ u
    Runli : ∀ n →
            Re n - c ↘ u →
            -----------------------
            Re n - unli c ↘ unlift u

  data Rty_-_at_↘_ : ℕ → D → ℕ → Nf → Set where
    RU  : ∀ {i j} n →
          j ≡ suc i →
          Rty n - U i at j ↘ Se i
    RN  : ∀ n →
          Rty n - N at 0 ↘ N
    RΠ  : ∀ {i j k} n →
          Rty n - A at i ↘ W →
          ⟦ T ⟧ ρ ↦ l′ i A n ↘ B →
          Rty 1 + n - B at j ↘ W′ →
          k ≡ max i j →
          ------------------------------
          Rty n - Π i A (T ↙ j) ρ at k ↘ Π (W ↙ i) (W′ ↙ j)
    RL  : ∀ {i j k} n →
          Rty n - A at j ↘ W →
          k ≡ i + j →
          ------------------------------
          Rty n - Li i j A at k ↘ Liftt i (W ↙ j)
    Rne : ∀ {i j} n →
          Re n - c ↘ V →
          i ≡ suc j →
          ---------------------
          Rty n - ↑ i A c at j ↘ ne V

pattern RU′ n ↘W = RU n ↘W refl
pattern Rne′ n ↘u = Rne n ↘u refl refl

-- All readback functions are deterministic.
mutual
  Rf-det : ∀ {n} → Rf n - d ↘ w → Rf n - d ↘ w′ → w ≡ w′
  Rf-det (RU _ ↘W _) (RU _ ↘W′ _)       = Rty-det ↘W ↘W′
  Rf-det (Rze _) (Rze _)                = refl
  Rf-det (Rsu _ ↘w) (Rsu _ ↘w′)         = cong su (Rf-det ↘w ↘w′)
  Rf-det (RΛ _ ↘W ↘a ↘A ↘w _) (RΛ _ ↘W′ ↘a′ ↘A′ ↘w′ _)
    rewrite ap-det ↘a ↘a′
          | ⟦⟧-det ↘A ↘A′               = cong₂ Λ (cong (_↙ _) (Rty-det ↘W ↘W′)) (Rf-det ↘w ↘w′)
  Rf-det (RN _ ↘u) (RN _ ↘u′)           = cong ne (Re-det ↘u ↘u′)
  Rf-det (Rne _ ↘u _ _) (Rne _ ↘u′ _ _) = cong ne (Re-det ↘u ↘u′)
  Rf-det (Rli _ ↘a ↘w _) (Rli _ ↘b ↘w′ _)
    rewrite unli-det ↘a ↘b              = cong (liftt _) (Rf-det ↘w ↘w′)

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
  Re-det (Runli _ ↘u) (Runli _ ↘u′)  = cong unlift (Re-det ↘u ↘u′)

  Rty-det : ∀ {n i} → Rty n - A at i ↘ W → Rty n - A at i ↘ W′ → W ≡ W′
  Rty-det (RU _ _) (RU _ _)          = refl
  Rty-det (RN _) (RN _)              = refl
  Rty-det (RΠ _ ↘W ↘B ↘W′ _) (RΠ _ ↘W″ ↘B′ ↘W‴ _)
    rewrite Rty-det ↘W ↘W″
          | ⟦⟧-det ↘B ↘B′
          | Rty-det ↘W′ ↘W‴          = refl
  Rty-det (Rne _ ↘V _) (Rne _ ↘V′ _) = cong ne (Re-det ↘V ↘V′)
  Rty-det (RL _ ↘W _) (RL _ ↘W′ _)   = cong (λ W → Liftt _ (W ↙ _)) (Rty-det ↘W ↘W′)

-- Normalization by evaluation where an evaluation environment is passed externally
record NbEEnvs n ρ t i T w : Set where
  field
    ⟦t⟧  : D
    ⟦T⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦T⟧ : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↓⟦t⟧ : Rf n - ↓ i ⟦T⟧ ⟦t⟧ ↘ w

-- Compute an initial global evaluation environment using a context stack
data InitEnvs : Ctx → Env → Set where
  base : InitEnvs [] emp
  s-∷  : ∀ {i} →
         InitEnvs Γ ρ →
         ⟦ T ⟧ ρ ↘ A →
         ------------------------------------------
         InitEnvs ((T ↙ i) ∷ Γ) (ρ ↦ l′ i A (len Γ))

-- Normalization by evaluation
--
-- We will show that if Γ ⊢ t ∶ T, then there must be a normal form w such that NbE Γ t T w
record NbE Γ t i T w : Set where
  field
    envs : Env
    init : InitEnvs Γ envs
    nbe  : NbEEnvs (len Γ) envs t i T w

-- Above definitions are all deterministic
InitEnvs-det : InitEnvs Γ ρ → InitEnvs Γ ρ′ → ρ ≡ ρ′
InitEnvs-det base base                     = refl
InitEnvs-det (s-∷ {Ψ} ↘ρ ↘A) (s-∷ ↘ρ′ ↘A′)
  rewrite InitEnvs-det ↘ρ ↘ρ′ = cong (λ A → _ ↦ l′ _ A (len Ψ)) (⟦⟧-det ↘A ↘A′)

NbE-det : ∀ {i} →
          NbE Γ t i T w →
          NbE Γ t i T w′ →
          w ≡ w′
NbE-det nbe nbe′
  with nbe | nbe′
... | record { envs = _ ; init = ↘ρ ; nbe = record { ⟦t⟧ = _ ; ⟦T⟧ = _ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } }
    | record { envs = _ ; init = ↘ρ′ ; nbe = record { ⟦t⟧ = _ ; ⟦T⟧ = _ ; ↘⟦t⟧ = ↘⟦t⟧′ ; ↘⟦T⟧ = ↘⟦T⟧′ ; ↓⟦t⟧ = ↓⟦t⟧′ } }
    rewrite InitEnvs-det ↘ρ ↘ρ′
          | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′
          | ⟦⟧-det ↘⟦t⟧ ↘⟦t⟧′ = Rf-det ↓⟦t⟧ ↓⟦t⟧′
