{-# OPTIONS --without-K --safe #-}

module NonCumulative.Unascribed.Statics.Transfer where

open import Lib

open import NonCumulative.Ascribed.Statics.Syntax as A
open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Ascribed.Semantics.Domain as A
open import NonCumulative.Unascribed.Statics.Syntax as U
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Semantics.Domain as U


infix 4 _↝s_ _[↝]_ _↝_ 

mutual  
  data _↝_ : A.Exp → U.Exp → Set where
    ↝N : N ↝ N
    ↝Π : ∀ {i j} →
          A.S ↝ U.S′ →
          A.T ↝ U.T′ →
          ----------------
          Π (A.S ↙ i) (A.T ↙ j) ↝ Π U.S′ U.T′
    ↝Liftt : ∀ {i n} →
             A.T ↝ U.T′ →
             ----------------
             Liftt n (A.T ↙ i) ↝ Liftt n U.T′
    ↝Se : ∀ {i} →
            A.Se i ↝ U.Se i
    ↝v : ∀ {x} →
          A.v x ↝ U.v x
    ↝ze : ze ↝ ze
    ↝su : ∀ {t t′} →
          t ↝ t′ →
          su t ↝ su t′
    ↝rec :  ∀ {i} →
            A.T ↝ U.T′ →
            A.s ↝ U.s′ →
            A.r ↝ U.r′ →
            A.t ↝ U.t′ →
            rec (A.T ↙ i) A.s A.r A.t ↝ rec U.T′ U.s′ U.r′ U.t′ 
    ↝Λ :  ∀ {i} →
          A.S ↝ U.S′ →
          A.t ↝ U.t′ →
          Λ (A.S ↙ i) A.t ↝ Λ U.S′ U.t′
    ↝$ :  A.t ↝ U.t′ →
          A.s ↝ U.s′ →
          A.t $ A.s ↝ U.t′ $ U.s′
    ↝liftt : ∀ {n} →
             A.t ↝ U.t′ →
             liftt n A.t ↝ liftt n U.t′
    ↝unlift : A.t ↝ U.t′ →
              unlift A.t ↝ unlift U.t′
    ↝sub :  A.t ↝ U.t′ →
            A.σ ↝s U.σ′ →
            sub A.t A.σ ↝ sub U.t′ U.σ′
      
  data _↝s_ : A.Subst → U.Subst → Set where
    ↝I : I ↝s I
    ↝wk : wk ↝s wk
    ↝∘ :  A.σ ↝s U.σ′ →
          A.τ ↝s U.τ′ →
          (A.σ ∘ A.τ) ↝s (U.σ′ ∘ U.τ′)
    ↝, : ∀ {i} →
           A.σ ↝s U.σ′ →
           A.t ↝ U.t′ →
           A.T ↝ U.T′ →
           (A.σ , A.t ∶ A.T ↙ i) ↝s (U.σ′ , U.t′ ∶ U.T′)

data _[↝]_ : A.Ctx → U.Ctx → Set where
  ↝[] : [] [↝] []
  ↝∷  : ∀ {i} → 
        A.Γ [↝] U.Γ′ →
        A.T ↝ U.T′ →
        --------------
        (A.T ↙ i) ∷ A.Γ [↝] U.T′ ∷ U.Γ′

mutual
    ⌊_⌋ : A.Exp → U.Exp
    ⌊ N ⌋ = N
    ⌊ Π (S ↙ _) (T ↙ _) ⌋ = Π ⌊ S ⌋ ⌊ T ⌋
    ⌊ Liftt i (T ↙ j) ⌋ = Liftt i ⌊ T ⌋
    ⌊ Se i ⌋ = Se i
    ⌊ v x ⌋ = v x
    ⌊ ze ⌋ = ze
    ⌊ su t ⌋ = su ⌊ t ⌋
    ⌊ rec (T ↙ i) r s t ⌋ = rec ⌊ T ⌋ ⌊ r ⌋ ⌊ s ⌋ ⌊ t ⌋
    ⌊ Λ (S ↙ _) t ⌋ = Λ ⌊ S ⌋ ⌊ t ⌋
    ⌊ r $ s ⌋ = ⌊ r ⌋ $ ⌊ s ⌋
    ⌊ liftt i t ⌋ = liftt i ⌊ t ⌋
    ⌊ unlift t ⌋ = unlift ⌊ t ⌋
    ⌊ sub t σ ⌋ = sub ⌊ t ⌋ ⌊ σ ⌋ˢ

    ⌊_⌋ˢ : A.Subst → U.Subst
    ⌊ I ⌋ˢ = I
    ⌊ wk ⌋ˢ = wk
    ⌊ σ ∘ τ ⌋ˢ = ⌊ σ ⌋ˢ ∘ ⌊ τ ⌋ˢ
    ⌊ σ , s ∶ T ↙ _ ⌋ˢ = ⌊ σ ⌋ˢ , ⌊ s ⌋ ∶ ⌊ T ⌋

mutual 
    ⌊_⌋ⁿᶠ : A.Nf → U.Nf
    ⌊ ne u ⌋ⁿᶠ = ne ⌊ u ⌋ⁿᵉ 
    ⌊ N ⌋ⁿᶠ = N
    ⌊ Π (V ↙ _) (W ↙ _) ⌋ⁿᶠ = Π ⌊ V ⌋ⁿᶠ ⌊ W ⌋ⁿᶠ 
    ⌊ Liftt i (T ↙ j) ⌋ⁿᶠ = Liftt i ⌊ T ⌋ⁿᶠ 
    ⌊ Se i ⌋ⁿᶠ = Se i
    ⌊ ze ⌋ⁿᶠ = ze
    ⌊ su w ⌋ⁿᶠ = su ⌊ w ⌋ⁿᶠ 
    ⌊ Λ (W ↙ i) w ⌋ⁿᶠ = Λ ⌊ W ⌋ⁿᶠ ⌊ w ⌋ⁿᶠ 
    ⌊ liftt i w ⌋ⁿᶠ = liftt i ⌊ w ⌋ⁿᶠ
    
    ⌊_⌋ⁿᵉ : A.Ne → U.Ne
    ⌊ v x ⌋ⁿᵉ = v x
    ⌊ rec (W ↙ _) z s u ⌋ⁿᵉ = rec ⌊ W ⌋ⁿᶠ ⌊ z ⌋ⁿᶠ ⌊ s ⌋ⁿᶠ ⌊ u ⌋ⁿᵉ 
    ⌊ u $ w ⌋ⁿᵉ = ⌊ u ⌋ⁿᵉ $ ⌊ w ⌋ⁿᶠ
    ⌊ unlift u ⌋ⁿᵉ = unlift ⌊ u ⌋ⁿᵉ

[⌊_⌋] : A.Ctx → U.Ctx
[⌊_⌋] [] = []
[⌊_⌋] ((T ↙ i) ∷ Γ) = ⌊ T ⌋ ∷ ([⌊_⌋] Γ)

mutual
  ⌊⌋⇒↝ : A.t ↝ ⌊ A.t ⌋
  ⌊⌋⇒↝ {N} = ↝N 
  ⌊⌋⇒↝ {Π S T} = ↝Π ⌊⌋⇒↝ ⌊⌋⇒↝
  ⌊⌋⇒↝ {Liftt _ T} = ↝Liftt ⌊⌋⇒↝
  ⌊⌋⇒↝ {Se i} = ↝Se
  ⌊⌋⇒↝ {v x} = ↝v
  ⌊⌋⇒↝ {ze} = ↝ze
  ⌊⌋⇒↝ {su t} = ↝su ⌊⌋⇒↝
  ⌊⌋⇒↝ {rec T r s t} = ↝rec ⌊⌋⇒↝ ⌊⌋⇒↝ ⌊⌋⇒↝ ⌊⌋⇒↝
  ⌊⌋⇒↝ {Λ S t} = ↝Λ ⌊⌋⇒↝ ⌊⌋⇒↝
  ⌊⌋⇒↝ {r $ s} = ↝$ ⌊⌋⇒↝ ⌊⌋⇒↝
  ⌊⌋⇒↝ {liftt i t} = ↝liftt ⌊⌋⇒↝
  ⌊⌋⇒↝ {unlift t} = ↝unlift ⌊⌋⇒↝
  ⌊⌋⇒↝ {sub t σ} = ↝sub ⌊⌋⇒↝ ⌊⌋s⇒↝s

  ⌊⌋s⇒↝s : A.σ ↝s ⌊ A.σ ⌋ˢ
  ⌊⌋s⇒↝s {I} = ↝I 
  ⌊⌋s⇒↝s {wk} = ↝wk 
  ⌊⌋s⇒↝s {σ ∘ τ} = ↝∘ ⌊⌋s⇒↝s ⌊⌋s⇒↝s
  ⌊⌋s⇒↝s {σ , t ∶ T} = ↝, ⌊⌋s⇒↝s ⌊⌋⇒↝ ⌊⌋⇒↝

mutual
  ↝⇒⌊⌋ : A.t ↝ U.t′ →
         U.t′ ≡ ⌊ A.t ⌋
  ↝⇒⌊⌋ ↝N = refl 
  ↝⇒⌊⌋ (↝Π S↝ T↝) = cong₂ Π (↝⇒⌊⌋ S↝) (↝⇒⌊⌋ T↝)
  ↝⇒⌊⌋ (↝Liftt T↝) = cong (Liftt _) (↝⇒⌊⌋ T↝)
  ↝⇒⌊⌋ ↝Se = refl
  ↝⇒⌊⌋ ↝v = refl
  ↝⇒⌊⌋ ↝ze = refl
  ↝⇒⌊⌋ (↝su t↝) = cong su (↝⇒⌊⌋ t↝)
  ↝⇒⌊⌋ (↝rec T↝ r↝ s↝ t↝) 
    rewrite ↝⇒⌊⌋ T↝
          | ↝⇒⌊⌋ r↝
          | ↝⇒⌊⌋ s↝
          | ↝⇒⌊⌋ t↝
    = refl
  ↝⇒⌊⌋ (↝Λ S↝ t↝) = cong₂ Λ (↝⇒⌊⌋ S↝) (↝⇒⌊⌋ t↝)
  ↝⇒⌊⌋ (↝$ r↝ s↝) = cong₂ _$_ (↝⇒⌊⌋ r↝) (↝⇒⌊⌋ s↝)
  ↝⇒⌊⌋ (↝liftt t↝) = cong (liftt _) (↝⇒⌊⌋ t↝)
  ↝⇒⌊⌋ (↝unlift t↝) = cong unlift (↝⇒⌊⌋ t↝)
  ↝⇒⌊⌋ (↝sub t↝ ⊢σ) = cong₂ sub (↝⇒⌊⌋ t↝) (↝s⇒⌊⌋s ⊢σ)

  ↝s⇒⌊⌋s : A.σ ↝s U.σ′ →
           U.σ′ ≡ ⌊ A.σ ⌋ˢ
  ↝s⇒⌊⌋s ↝I = refl 
  ↝s⇒⌊⌋s ↝wk = refl
  ↝s⇒⌊⌋s (↝∘ ↝σ ↝τ) = cong₂ _∘_ (↝s⇒⌊⌋s ↝σ) (↝s⇒⌊⌋s ↝τ)
  ↝s⇒⌊⌋s (↝, ↝σ ↝t ↝T) 
    rewrite ↝s⇒⌊⌋s ↝σ 
          | ↝⇒⌊⌋ ↝t
          | ↝⇒⌊⌋ ↝T
    = refl

[⌊⌋]⇒↝[] : A.Γ [↝] [⌊ A.Γ ⌋]
[⌊⌋]⇒↝[] {[]} = ↝[] 
[⌊⌋]⇒↝[] {_ ∷ _} = ↝∷ [⌊⌋]⇒↝[] ⌊⌋⇒↝

↝[]⇒[⌊⌋] : A.Γ [↝] U.Γ′ →
           U.Γ′ ≡ [⌊ A.Γ ⌋]
↝[]⇒[⌊⌋] ↝[] = refl 
↝[]⇒[⌊⌋] (↝∷ Γ↝ T↝) 
  rewrite ↝[]⇒[⌊⌋] Γ↝
        | ↝⇒⌊⌋ T↝ 
  = refl

mutual 
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm : ∀ w →
                    U.Nf⇒Exp (⌊ w ⌋ⁿᶠ) ≡ ⌊ A.Nf⇒Exp w ⌋
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (ne u) = ⌊⌋ⁿᵉ-Ne⇒Exp-comm u
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm N = refl
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (Π (W ↙ i) (V ↙ j)) = cong₂ Π (⌊⌋ⁿᶠ-Nf⇒Exp-comm W) (⌊⌋ⁿᶠ-Nf⇒Exp-comm V)
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (Liftt i (W ↙ j)) = cong (Liftt i) (⌊⌋ⁿᶠ-Nf⇒Exp-comm W)
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (Se i) = refl
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm ze = refl
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (su w) = cong su (⌊⌋ⁿᶠ-Nf⇒Exp-comm w)
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (Λ (W ↙ i) w) = cong₂ Λ (⌊⌋ⁿᶠ-Nf⇒Exp-comm W) (⌊⌋ⁿᶠ-Nf⇒Exp-comm w)
  ⌊⌋ⁿᶠ-Nf⇒Exp-comm (liftt i w) = cong (liftt i) (⌊⌋ⁿᶠ-Nf⇒Exp-comm w)

  ⌊⌋ⁿᵉ-Ne⇒Exp-comm : ∀ u →
                    U.Ne⇒Exp (⌊ u ⌋ⁿᵉ) ≡ ⌊ A.Ne⇒Exp u ⌋
  ⌊⌋ⁿᵉ-Ne⇒Exp-comm (v x) = refl
  ⌊⌋ⁿᵉ-Ne⇒Exp-comm (rec (W ↙ i) w w′ u) 
    rewrite ⌊⌋ⁿᶠ-Nf⇒Exp-comm W
          | ⌊⌋ⁿᶠ-Nf⇒Exp-comm w
          | ⌊⌋ⁿᶠ-Nf⇒Exp-comm w′
          | ⌊⌋ⁿᵉ-Ne⇒Exp-comm u
    = refl
  ⌊⌋ⁿᵉ-Ne⇒Exp-comm (u $ w) = cong₂ _$_ (⌊⌋ⁿᵉ-Ne⇒Exp-comm u) (⌊⌋ⁿᶠ-Nf⇒Exp-comm w)
  ⌊⌋ⁿᵉ-Ne⇒Exp-comm (unlift u) = cong unlift (⌊⌋ⁿᵉ-Ne⇒Exp-comm u)