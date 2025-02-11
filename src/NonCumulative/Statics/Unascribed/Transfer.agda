{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Unascribed.Transfer where

open import Lib

open import NonCumulative.Statics.Unascribed.Full as U
open import NonCumulative.Statics.Ascribed.Full as A renaming (Ctx to lCtx)

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