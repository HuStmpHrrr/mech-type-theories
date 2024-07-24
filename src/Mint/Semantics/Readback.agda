{-# OPTIONS --without-K --safe #-}

-- Definition of readback functions
--
-- The readback functions read from the domain model back to the syntax as
-- normal/neutral forms. The readback function is tyle-intended value directed and
-- performs η expansion during the process. Combined with evaluation, after reading
-- back, we obtain β-η normal form.
--
-- All readback functions receive a nonempty list of natural numbers. This list
-- contains the length of each context in a context stack and is responsible for
-- maintaining the correspondence between syntactic variables and domain
-- variables. The correspondence is at context level and can be seen in the Rl
-- constructor.
module Mint.Semantics.Readback where

open import Lib
open import Mint.Semantics.Domain
open import Mint.Semantics.Evaluation


instance
  ℕsHasTr : HasTr (List⁺ ℕ)
  ℕsHasTr = record { _∥_ = λ ns n → drop+ n ns }

-- Increment the topmost length, corresponding to entering a closure
inc : List⁺ ℕ → List⁺ ℕ
inc (n ∷ ns) = (suc n ∷ ns)

-- Readback functions
--
-- There are three readback functions:
-- Rf: readback from domain normal forms to syntactic normal forms, performing η expansion as well
-- Re: readback from domain neutral forms to syntactic neutral forms
-- Rty: readback from domain value that is intended to represent types to syntactic normal forms
infix 4 Rf_-_↘_ Re_-_↘_ Rty_-_↘_

mutual

  data Rf_-_↘_ : List⁺ ℕ → Df → Nf → Set where
    RU  : ∀ {i} ns →
          Rty ns - A ↘ W →
          ---------------------
          Rf ns - ↓ (U i) A ↘ W
    Rze : ∀ ns →
          Rf ns - ↓ N ze ↘ ze
    Rsu : ∀ ns →
          Rf ns - ↓ N a ↘ w →
          ---------------------------
          Rf ns - ↓ N (su a) ↘ (su w)
    RΛ  : ∀ ns →
          a ∙ l′ A (head ns) ↘ b →
          ⟦ T ⟧ ρ ↦ l′ A (head ns) ↘ B →
          Rf inc ns - ↓ B b ↘ w →
          ------------------------------
          Rf ns - ↓ (Π A T ρ) a ↘ Λ w
    R□  : ∀ ns →
          unbox∙ 1 , a ↘ b →
          Rf 0 ∷⁺ ns - ↓ A b ↘ w →
          -------------------------
          Rf ns - ↓ (□ A) a ↘ box w
    RN  : ∀ ns →
          Re ns - c ↘ u →
          --------------------------
          Rf ns - ↓ N (↑ N c) ↘ ne u
    Rne : ∀ ns →
          Re ns - c′ ↘ u →
          ----------------------------------
          Rf ns - ↓ (↑ A c) (↑ A′ c′) ↘ ne u

  data Re_-_↘_ : List⁺ ℕ → Dn → Ne → Set where
    Rl : ∀ ns x →
         Re ns - l x ↘ v (head ns ∸ x ∸ 1)
    R$ : ∀ ns →
         Re ns - c ↘ u →
         Rf ns - d ↘ w →
         ---------------------
         Re ns - c $ d ↘ u $ w
    Ru : ∀ ns k →
         Re ns ∥ k - c ↘ u →
         -------------------------
         Re ns - unbox k c ↘ unbox k u
    Rr : ∀ ns →
         -- compute normal form of the motive
         ⟦ T ⟧ ρ ↦ l′ N (head ns) ↘ A →
         Rty inc ns - A ↘ W →
         -- compute normal form of the base case
         ⟦ T ⟧ ρ ↦ ze ↘ A′ →
         Rf ns - ↓ A′ a ↘ w →
         -- compute normal form of the step case
         ⟦ t ⟧ ρ ↦ l′ N (head ns) ↦ l′ A (suc (head ns)) ↘ b →
         ⟦ T ⟧ ρ ↦ su (l′ N (head ns)) ↘ A″ →
         Rf inc (inc ns) - ↓ A″ b ↘ w′ →
         -- compute neutral form of the number
         Re ns - c ↘ u →
         Re ns - rec T a t ρ c ↘ rec W w w′ u

  data Rty_-_↘_ : List⁺ ℕ → D → Nf → Set where
    RU  : ∀ {i} ns →
          Rty ns - U i ↘ Se i
    RN  : ∀ ns →
          Rty ns - N ↘ N
    R□  : ∀ ns →
          Rty 0 ∷⁺ ns - A ↘ W →
          ---------------------
          Rty ns - □ A ↘ □ W
    RΠ  : ∀ ns →
          Rty ns - A ↘ W →
          ⟦ T ⟧ ρ ↦ l′ A (head ns) ↘ B →
          Rty inc ns - B ↘ W′ →
          ------------------------------
          Rty ns - Π A T ρ ↘ Π W W′
    Rne : ∀ ns →
          Re ns - c ↘ V →
          ---------------------
          Rty ns - ↑ A c ↘ ne V

-- All readback functions are deterministic.
mutual
  Rf-det : ∀ {ns} → Rf ns - d ↘ w → Rf ns - d ↘ w′ → w ≡ w′
  Rf-det (RU _ ↘W) (RU _ ↘W′)   = Rty-det ↘W ↘W′
  Rf-det (Rze _) (Rze _)        = refl
  Rf-det (Rsu _ ↘w) (Rsu _ ↘w′) = cong su (Rf-det ↘w ↘w′)
  Rf-det (RΛ _ ↘a ↘A ↘w) (RΛ _ ↘a′ ↘A′ ↘w′)
    rewrite ap-det ↘a ↘a′
          | ⟦⟧-det ↘A ↘A′       = cong Λ (Rf-det ↘w ↘w′)
  Rf-det (R□ _ ↘a ↘w) (R□ _ ↘a′ ↘w′)
    rewrite unbox-det ↘a ↘a′    = cong box (Rf-det ↘w ↘w′)
  Rf-det (RN _ ↘u) (RN _ ↘u′)   = cong ne (Re-det ↘u ↘u′)
  Rf-det (Rne _ ↘u) (Rne _ ↘u′) = cong ne (Re-det ↘u ↘u′)

  Re-det : ∀ {ns} → Re ns - c ↘ u → Re ns - c ↘ u′ → u ≡ u′
  Re-det (Rl _ x) (Rl _ .x)          = refl
  Re-det (R$ _ ↘c ↘w) (R$ _ ↘c′ ↘w′) = cong₂ _$_ (Re-det ↘c ↘c′) (Rf-det ↘w ↘w′)
  Re-det (Ru _ k ↘c) (Ru _ .k ↘c′)   = cong (unbox k) (Re-det ↘c ↘c′)
  Re-det (Rr _ ↘A ↘W ↘Az ↘w ↘b ↘As ↘w′ ↘c) (Rr _ ↘A′ ↘W′ ↘Az′ ↘w″ ↘b′ ↘As′ ↘w‴ ↘c′)
    rewrite ⟦⟧-det ↘A ↘A′
          | Rty-det ↘W ↘W′
          | ⟦⟧-det ↘Az ↘Az′
          | Rf-det ↘w ↘w″
          | ⟦⟧-det ↘b ↘b′
          | ⟦⟧-det ↘As ↘As′
          | Rf-det ↘w′ ↘w‴
          | Re-det ↘c ↘c′            = refl

  Rty-det : ∀ {ns} → Rty ns - A ↘ W → Rty ns - A ↘ W′ → W ≡ W′
  Rty-det (RU _) (RU _)          = refl
  Rty-det (RN _) (RN _)          = refl
  Rty-det (R□ _ ↘W) (R□ _ ↘W′)   = cong □ (Rty-det ↘W ↘W′)
  Rty-det (RΠ _ ↘W ↘B ↘W′) (RΠ _ ↘W″ ↘B′ ↘W‴)
    rewrite Rty-det ↘W ↘W″
          | ⟦⟧-det ↘B ↘B′
          | Rty-det ↘W′ ↘W‴      = refl
  Rty-det (Rne _ ↘V) (Rne _ ↘V′) = cong ne (Re-det ↘V ↘V′)

-- Normalization by evaluation where an evaluation environment is passed externally
record NbEEnvs ns ρ t T w : Set where
  field
    ⟦t⟧  : D
    ⟦T⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦T⟧ : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↓⟦t⟧ : Rf ns - ↓ ⟦T⟧ ⟦t⟧ ↘ w

-- Compute an initial global evaluation environment using a context stack
data InitEnvs : Ctxs → Envs → Set where
  base : InitEnvs ([] ∷ []) empty
  s-κ  : InitEnvs Γ ρ →
         ----------------------------
         InitEnvs ([] ∷⁺ Γ) (ext ρ 1)
  s-∺  : InitEnvs (Ψ ∷ Ψs) ρ →
         ⟦ T ⟧ ρ ↘ A →
         ------------------------------------------
         InitEnvs ((T ∷ Ψ) ∷ Ψs) (ρ ↦ l′ A (len Ψ))

-- Normalization by evaluation
--
-- We will show that if Γ ⊢ t ∶ T, then there must be a normal form w such that NbE Γ t T w
record NbE Γ t T w : Set where
  field
    envs : Envs
    init : InitEnvs Γ envs
    nbe  : NbEEnvs (map len Γ) envs t T w

-- Above definitions are all deterministic
InitEnvs-det : InitEnvs Γ ρ → InitEnvs Γ ρ′ → ρ ≡ ρ′
InitEnvs-det base base                     = refl
InitEnvs-det (s-κ ↘ρ) (s-κ ↘ρ′)            = cong (λ ρ → ext ρ 1) (InitEnvs-det ↘ρ ↘ρ′)
InitEnvs-det (s-∺ {Ψ} ↘ρ ↘A) (s-∺ ↘ρ′ ↘A′)
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
