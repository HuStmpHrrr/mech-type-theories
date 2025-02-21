{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Unascribed.Properties.NbE.Totality (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib hiding (lookup)
open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Ascribed.Semantics.Domain as A
open import NonCumulative.Ascribed.Semantics.Evaluation as A
open import NonCumulative.Ascribed.Semantics.Readback as A
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Semantics.Domain as U
open import NonCumulative.Unascribed.Semantics.Evaluation as U
open import NonCumulative.Unascribed.Semantics.Readback as U
open import NonCumulative.Unascribed.Statics.Transfer as U
open import NonCumulative.Unascribed.Semantics.Transfer as U


↦-⌊⌋-comm : ∀ ρ a → 
            (λ n → ⌊ (ρ A.↦ a) n ⌋ᵈ) ≡ ((λ n → ⌊ ρ n ⌋ᵈ) U.↦ ⌊ a ⌋ᵈ )
↦-⌊⌋-comm ρ a = fext helper
  where
    helper : ∀ n → _ ≡ _ 
    helper ℕ.zero = refl
    helper (ℕ.suc n) = refl

mutual
  ⟦⟧-⌊⌋-total : A.⟦ A.t ⟧ A.ρ ↘ A.a → 
                (U.⟦ ⌊ A.t ⌋ ⟧ (λ n → ⌊ A.ρ n ⌋ᵈ) ↘ ⌊ A.a ⌋ᵈ)
  ⟦⟧-⌊⌋-total ⟦N⟧ = ⟦N⟧
  ⟦⟧-⌊⌋-total (⟦Π⟧ ⟦t⟧) = ⟦Π⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦Liftt⟧ ⟦t⟧) = ⟦Liftt⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦Se⟧ i) = ⟦Se⟧ i
  ⟦⟧-⌊⌋-total (⟦v⟧ n) = ⟦v⟧ n
  ⟦⟧-⌊⌋-total ⟦ze⟧ = ⟦ze⟧
  ⟦⟧-⌊⌋-total (⟦su⟧ ⟦t⟧) = ⟦su⟧ ( ⟦⟧-⌊⌋-total ⟦t⟧ )
  ⟦⟧-⌊⌋-total (⟦rec⟧ ⟦r⟧ ⟦t⟧ rec∙a) = ⟦rec⟧ (⟦⟧-⌊⌋-total ⟦r⟧) (⟦⟧-⌊⌋-total ⟦t⟧) (rec∙-⌊⌋-total rec∙a)
  ⟦⟧-⌊⌋-total (⟦Λ⟧ t) = ⟦Λ⟧ ⌊ t ⌋
  ⟦⟧-⌊⌋-total (⟦$⟧ ⟦r⟧ ⟦s⟧ f∙a) = ⟦$⟧ (⟦⟧-⌊⌋-total ⟦r⟧) (⟦⟧-⌊⌋-total ⟦s⟧) (∙-⌊⌋-total f∙a)
  ⟦⟧-⌊⌋-total (⟦liftt⟧ ⟦t⟧) = ⟦liftt⟧ (⟦⟧-⌊⌋-total ⟦t⟧)
  ⟦⟧-⌊⌋-total (⟦unlift⟧ ⟦t⟧ unli∙a) = ⟦unlift⟧ (⟦⟧-⌊⌋-total ⟦t⟧) (unli∙-⌊⌋-total unli∙a)
  ⟦⟧-⌊⌋-total (⟦[]⟧ ⟦σ⟧ ⟦t⟧) = ⟦[]⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧-⌊⌋-total ⟦t⟧)

  ⟦⟧ˢ-⌊⌋-total : A.⟦ A.σ ⟧s A.ρ ↘ A.ρ′ → 
                 U.⟦ ⌊ A.σ ⌋ˢ ⟧s (λ n → ⌊ A.ρ n ⌋ᵈ) ↘ (λ n → ⌊ A.ρ′ n ⌋ᵈ)
  ⟦⟧ˢ-⌊⌋-total ⟦I⟧ = ⟦I⟧ 
  ⟦⟧ˢ-⌊⌋-total ⟦wk⟧ = ⟦wk⟧
  ⟦⟧ˢ-⌊⌋-total (⟦,⟧ {ρ′ = ρ′} {a = a} ⟦σ⟧ ⟦t⟧) 
    rewrite ↦-⌊⌋-comm ρ′ a
    = ⟦,⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧-⌊⌋-total ⟦t⟧) 
  ⟦⟧ˢ-⌊⌋-total (⟦∘⟧ ⟦σ⟧ ⟦τ⟧) = ⟦∘⟧ (⟦⟧ˢ-⌊⌋-total ⟦σ⟧) (⟦⟧ˢ-⌊⌋-total ⟦τ⟧)  

  ∙-⌊⌋-total : A.f A.∙ A.a ↘ A.b → 
               ⌊ A.f ⌋ᵈ U.∙ ⌊ A.a ⌋ᵈ ↘ ⌊ A.b ⌋ᵈ
  ∙-⌊⌋-total (Λ∙ {ρ = ρ} {a = a} ⟦t⟧)
    with ⟦t⟧′ ← ⟦⟧-⌊⌋-total ⟦t⟧
    rewrite (↦-⌊⌋-comm ρ a)
    = Λ∙ ⟦t⟧′ 
  ∙-⌊⌋-total ($∙ {ρ = ρ} {a = a} A c ⟦T⟧) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ a)
    = $∙ _ _ ⟦T⟧′

  unli∙-⌊⌋-total : A.unli∙ A.a ↘ A.b → 
                   U.unli∙ ⌊ A.a ⌋ᵈ ↘ ⌊ A.b ⌋ᵈ
  unli∙-⌊⌋-total li↘ = li↘ 
  unli∙-⌊⌋-total unli↘ = unli↘

  rec∙-⌊⌋-total : ∀ {i} →  
                  A.rec∙ (A.T ↙ i) , A.a , A.r , A.ρ , A.b ↘ A.a′ → 
                  U.rec∙ ⌊ A.T ⌋ , ⌊ A.a ⌋ᵈ , ⌊ A.r ⌋ , (λ n → ⌊ A.ρ n ⌋ᵈ) , ⌊ A.b ⌋ᵈ ↘ ⌊ A.a′ ⌋ᵈ
  rec∙-⌊⌋-total ze↘ = ze↘ 
  rec∙-⌊⌋-total (su↘ {ρ = ρ} {b = b} {b′ = b′} {a′ = a′} rec∙b ⟦r⟧) 
    with ⟦r⟧′ ← ⟦⟧-⌊⌋-total ⟦r⟧
    rewrite (↦-⌊⌋-comm (ρ A.↦ b) b′)
    rewrite (↦-⌊⌋-comm ρ b)
    = su↘ (rec∙-⌊⌋-total rec∙b) ⟦r⟧′
  rec∙-⌊⌋-total (rec∙ {ρ = ρ} {A′ = A′} {c = c} {j = j} ⟦T⟧) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ j A′ c))
    = rec∙ ⟦T⟧′

mutual 
  Rf-⌊⌋-total : ∀ {n} →
                A.Rf n - A.d ↘ A.w → 
                U.Rf n - ⌊ A.d ⌋ᵈᶠ ↘ ⌊ A.w ⌋ⁿᶠ
  Rf-⌊⌋-total (RU′ _ ↘W) = RU _ (Rty-⌊⌋-total ↘W) 
  Rf-⌊⌋-total (Rze _) = Rze _
  Rf-⌊⌋-total (Rsu _ ↘w) = Rsu _ (Rf-⌊⌋-total ↘w)
  Rf-⌊⌋-total (RΛ {A = A} {ρ = ρ} {i = i} n ↘W ↘b ⟦T⟧ Rf-d) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ i A (l n)))
    = RΛ _ (Rty-⌊⌋-total ↘W) (∙-⌊⌋-total ↘b) ⟦T⟧′ (Rf-⌊⌋-total Rf-d)
  Rf-⌊⌋-total (Rli _ x Rf-d) = Rli _ (unli∙-⌊⌋-total x) (Rf-⌊⌋-total Rf-d) 
  Rf-⌊⌋-total (RN _ ↘u) = RN _ (Rne-⌊⌋-total ↘u)
  Rf-⌊⌋-total (Rne′ _ ↘u) = Rne _ (Rne-⌊⌋-total ↘u)

  Rne-⌊⌋-total : ∀ {n} →
                 A.Re n - A.c ↘ A.u → 
                 U.Re n - ⌊ A.c ⌋ᵈⁿ ↘ ⌊ A.u ⌋ⁿᵉ
  Rne-⌊⌋-total (Rl _ x) = Rl _ x 
  Rne-⌊⌋-total (R$ _ ↘u ↘w) = R$ _ (Rne-⌊⌋-total ↘u) (Rf-⌊⌋-total ↘w)
  Rne-⌊⌋-total (Rr {ρ = ρ} {A = A} {i = i} n ⟦T⟧ ↘W ⟦T⟧₁ ↘w ⟦t⟧ ⟦T⟧₂ ↘w₁ ↘u) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    with ⟦T⟧₁′ ← ⟦⟧-⌊⌋-total ⟦T⟧₁
    with ⟦T⟧₂′ ← ⟦⟧-⌊⌋-total ⟦T⟧₂
    with ⟦t⟧′ ← ⟦⟧-⌊⌋-total ⟦t⟧
    rewrite (↦-⌊⌋-comm ρ ze) 
    rewrite (↦-⌊⌋-comm ρ (su (↑ 0 N (l n)))) 
    rewrite (↦-⌊⌋-comm (ρ A.↦ ↑ 0 N (l n)) (↑ i A (l (1 + n)))) 
    rewrite (↦-⌊⌋-comm ρ (↑ 0 N (l n))) 
    = Rr _ ⟦T⟧′ (Rty-⌊⌋-total ↘W) ⟦T⟧₁′ (Rf-⌊⌋-total ↘w) ⟦t⟧′ ⟦T⟧₂′ (Rf-⌊⌋-total ↘w₁) (Rne-⌊⌋-total ↘u)
  Rne-⌊⌋-total (Runli _ ↘u) = Runli _ (Rne-⌊⌋-total ↘u)

  Rty-⌊⌋-total : ∀ {n i} →
                 A.Rty n - A.a at i ↘ A.W → 
                 U.Rty n - ⌊ A.a ⌋ᵈ  ↘ ⌊ A.W ⌋ⁿᶠ
  Rty-⌊⌋-total (RU _) = RU _ 
  Rty-⌊⌋-total (RN _) = RN _
  Rty-⌊⌋-total (RΠ  {A = A} {ρ = ρ} {i = j} n ↘V ⟦T⟧ ↘W) 
    with ⟦T⟧′ ← ⟦⟧-⌊⌋-total ⟦T⟧
    rewrite (↦-⌊⌋-comm ρ (↑ j A (l n)))
    = RΠ _ (Rty-⌊⌋-total ↘V) ⟦T⟧′ (Rty-⌊⌋-total ↘W)
  Rty-⌊⌋-total (RL _ ↘W) = RL _ (Rty-⌊⌋-total ↘W)
  Rty-⌊⌋-total (Rne′ _ ↘U) = Rne _ (Rne-⌊⌋-total ↘U)

[⌊_⌋]-len-≡ : ∀ {Γ : A.Ctx} →
              (len [⌊ Γ ⌋]) ≡ (len Γ)
[⌊_⌋]-len-≡ {[]} = refl
[⌊_⌋]-len-≡ {_ ∷ Γ} 
  rewrite [⌊_⌋]-len-≡ {Γ = Γ}
  = refl

[⌊⌋]-InitEnvs : ∀ Γ ρ →
                A.InitEnvs Γ ρ →
                U.InitEnvs [⌊ Γ ⌋] (λ n → ⌊ ρ n ⌋ᵈ)
[⌊⌋]-InitEnvs .L.[] .A.emp base = base
[⌊⌋]-InitEnvs .((_ ↙ _) L.∷ _) .(_ A.↦ ↑ _ _ _) (s-∷ {Γ = Γ} {ρ = ρ} {A = A} {i = i} initEnv ⟦T⟧) 
  rewrite (sym ([⌊_⌋]-len-≡ {Γ = Γ}))
  rewrite (↦-⌊⌋-comm ρ (↑ i A (l (len [⌊ Γ ⌋]))))
  = s-∷ ([⌊⌋]-InitEnvs _ _ initEnv) (⟦⟧-⌊⌋-total ⟦T⟧)

NbE-⌊⌋-total : ∀ {i} →
                A.NbE A.Γ A.t i A.T A.w →
                U.NbE ([⌊ A.Γ ⌋]) (⌊ A.t ⌋) (⌊ A.T ⌋) (⌊ A.w ⌋ⁿᶠ)
NbE-⌊⌋-total {Γ = Γ} {w = w}
  record { envs = envs 
         ; init = init 
         ; nbe = record { ⟦t⟧ = ⟦t⟧ ; ⟦T⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↓⟦t⟧ = ↓⟦t⟧ } } = 
  record { envs = λ n → ⌊ envs n ⌋ᵈ ; init = [⌊⌋]-InitEnvs _ _ init 
         ; nbe = record { ⟦t⟧ = _ ; ⟦T⟧ = _ ; ↘⟦t⟧ = ⟦⟧-⌊⌋-total ↘⟦t⟧ ; ↘⟦T⟧ = ⟦⟧-⌊⌋-total ↘⟦T⟧ ; ↓⟦t⟧ = helper} }
  where 
    helper : U.Rf L.length [⌊ Γ ⌋] - ↓ ⌊ ⟦T⟧ ⌋ᵈ ⌊ ⟦t⟧ ⌋ᵈ ↘ ⌊ w ⌋ⁿᶠ
    helper 
      with ↘w ← Rf-⌊⌋-total ↓⟦t⟧
      rewrite [⌊_⌋]-len-≡ {Γ = Γ}
      = ↘w

