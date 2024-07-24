{-# OPTIONS --without-K --safe #-}

-- Restricted weakening
--
-- A restrcited weakening describes the only possible changes in context stacks during
-- EVALUATION, hence restricted. That is, during evaluation, there are only three
-- possible changes in context stacks:
--
-- 1. It stays unchanged. Consider the β reduction of function:
--
--    Γ ⊢ (Λ t) $ s ≈ t [| s ] ∶ T
--
--    In this case, both terms (Λ t) and s live in Γ and thus the context stack
--    remains the same.
--
-- 2. It gets one extra variable on the topmost context. This happens due to
-- congruence of function. Due to congruence, when a function body evaluates, the
-- context stack has one extra variable.
--
-- 3. It gets one more context. For a similar reason, this happens when evaluation
-- happens under a box due to congruence.
module Mint.Soundness.Restricted where

open import Lib

open import Data.List.Properties as Lₚ

open import Mint.Statics
open import Mint.Statics.Properties

infix 4 _⊢r_∶_

data _⊢r_∶_ : Ctxs → Substs → Ctxs → Set where
  r-I : Γ ⊢s σ ≈ I ∶ Δ →
        ----------------
        Γ ⊢r σ ∶ Δ
  r-p : Γ ⊢r τ ∶ T ∺ Δ →
        Γ ⊢s σ ≈ p τ ∶ Δ →
        -------------------
        Γ ⊢r σ ∶ Δ
  r-； : ∀ {n} Ψs →
        Γ ⊢r τ ∶ Δ →
        Ψs ++⁺ Γ ⊢s σ ≈ τ ； n ∶ [] ∷⁺ Δ →
        len Ψs ≡ n →
        -----------------------------------
        Ψs ++⁺ Γ ⊢r σ ∶ [] ∷⁺ Δ


-- A restricted weakening is a well-formed substitution.
⊢r⇒⊢s : Γ ⊢r σ ∶ Δ → Γ ⊢s σ ∶ Δ
⊢r⇒⊢s (r-I ⊢σ)        = proj₁ (proj₂ (presup-s-≈ ⊢σ))
⊢r⇒⊢s (r-p _ ⊢σ)      = proj₁ (proj₂ (presup-s-≈ ⊢σ))
⊢r⇒⊢s (r-； _ _ ⊢σ _) = proj₁ (proj₂ (presup-s-≈ ⊢σ))

-- If a substitution is restricted, then its equivalent substitution is also restricted.
s≈-resp-⊢r : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢r σ′ ∶ Δ → Γ ⊢r σ ∶ Δ
s≈-resp-⊢r σ≈σ′ (r-I σ′≈)           = r-I (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-p ⊢δ σ′≈)        = r-p ⊢δ (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-； Γs ⊢δ σ′≈ eq) = r-； Γs ⊢δ (s-≈-trans σ≈σ′ σ′≈) eq

-- Trunction of a restrcited weakening remains restricted.
⊢r-∥ : ∀ n →
       Γ ⊢r σ ∶ Γ′ →
       n < len Γ′ →
       -------------------------
       ∃₂ λ Ψs′ Δ′ → ∃₂ λ Ψs Δ →
            Γ′ ≡ Ψs′ ++⁺ Δ′
          × Γ ≡ Ψs ++⁺ Δ
          × len Ψs′ ≡ n
          × len Ψs ≡ O σ n
          × Δ ⊢r σ ∥ n ∶ Δ′
⊢r-∥ {Γ} {σ} {Γ′} n (r-I σ≈I) n<
  with chop Γ′ n<
...  | Ψs , Γ″ , refl , refl
     with ∥-resp-≈′ Ψs σ≈I
...     | Ψs′ , Γ‴ , eq , eql , σ∥≈
        rewrite I-∥ (len Ψs)          = Ψs , Γ″ , Ψs′ , Γ‴ , refl , eq , refl
                                      , eql , r-I σ∥≈
⊢r-∥ zero (r-p ⊢τ σ≈p) n<             = [] , _ , [] , _ , refl , refl , refl , refl , r-p ⊢τ σ≈p
⊢r-∥ {Γ} {σ} (suc n) (r-p ⊢τ σ≈p) n<
  with ⊢r-∥ (suc n) ⊢τ n<
...  | (_ ∷ Ψ) ∷ Ψs′ , Δ′ , Ψs , Δ
     , refl , eq′ , refl , eql′ , ⊢τ∥
     with ∥-resp-≈′ (Ψ ∷ Ψs′) σ≈p
...     | Ψs″ , Δ″ , eq″ , eql″ , σ≈∥ = Ψ ∷ Ψs′ , Δ′ , Ψs , Δ
                                      , refl , eq′ , refl , trans eql′ (sym eqL)
                                      , helper (++⁺-cancelˡ′ Ψs Ψs″ (trans (sym eq′) eq″) (sym (trans eql″ (trans eqL (sym eql′)))))
  where eqL         = O-resp-≈ (suc n) σ≈p
        helper : Δ ≡ Δ″ → Δ ⊢r σ ∥ suc (len Ψs′) ∶ Δ′
        helper refl = s≈-resp-⊢r σ≈∥ (s≈-resp-⊢r (I-∘ (⊢r⇒⊢s ⊢τ∥)) ⊢τ∥)
⊢r-∥ zero (r-； Ψs ⊢τ σ≈； eq) n<     = [] , _ , [] , _ , refl , refl , refl , refl , r-； Ψs ⊢τ σ≈； eq
⊢r-∥ {_} {σ} (suc n) (r-； Ψs ⊢τ σ≈； refl) (s≤s n<)
  with ⊢r-∥ n ⊢τ n<
...  | Ψs′ , Δ′ , Ψs₁ , Δ
     , refl , refl , refl , eql′ , ⊢τ∥
     with ∥-resp-≈′ ([] ∷ Ψs′) σ≈；
...     | Ψs″ , Δ″ , eq″ , eql″ , σ≈∥ = [] ∷ Ψs′ , Δ′ , Ψs ++ Ψs₁ , Δ
                                      , refl , sym (++-++⁺ Ψs)
                                      , refl , trans (length-++ Ψs) (trans (cong (len Ψs +_) eql′) (sym eqL))
                                      , helper (++⁺-cancelˡ′ (Ψs ++ Ψs₁) Ψs″
                                                            (trans (++-++⁺ Ψs) eq″)
                                                            (sym (trans eql″
                                                                 (trans eqL
                                                                 (trans (cong (_ +_) (sym eql′))
                                                                        (sym (length-++ Ψs)))))))
  where eqL = O-resp-≈ (suc n) σ≈；
        helper : Δ ≡ Δ″ → Δ ⊢r σ ∥ suc (len Ψs′) ∶ Δ′
        helper refl = s≈-resp-⊢r σ≈∥ ⊢τ∥

⊢r-∥′ : ∀ Ψs →
        Γ ⊢r σ ∶ Ψs ++⁺ Γ′ →
        ----------------------------
        ∃₂ λ Ψs′ Δ′ →
             Γ ≡ Ψs′ ++⁺ Δ′
           × len Ψs′ ≡ O σ (len Ψs)
           × Δ′ ⊢r σ ∥ len Ψs ∶ Γ′
⊢r-∥′ Ψs ⊢σ
  with ⊢r-∥ (len Ψs) ⊢σ (length-<-++⁺ Ψs)
...  | Ψs′ , Δ′ , Ψs₁ , Δ
     , eq , eq′ , eql , eql′ , ⊢τ∥
     rewrite ++⁺-cancelˡ′ Ψs Ψs′ eq (sym eql) = Ψs₁ , Δ , eq′ , eql′ , ⊢τ∥

⊢r-∥″ : ∀ Ψs Ψs′ →
        Ψs ++⁺ Γ ⊢r σ ∶ Ψs′ ++⁺ Δ →
        len Ψs ≡ O σ (len Ψs′) →
        ----------------------------
        Γ ⊢r σ ∥ len Ψs′ ∶ Δ
⊢r-∥″ Ψs Ψs′ ⊢σ eql
  with ⊢r-∥′ Ψs′ ⊢σ
...  | Ψs₁ , Γ₁ , eq , eql′ , ⊢σ∥
     rewrite ++⁺-cancelˡ′ Ψs Ψs₁ eq (trans eql (sym eql′)) = ⊢σ∥

-- Restricted weakenings respects context stack equivalence.
⊢r-resp-⊢≈ˡ : Γ ⊢r σ ∶ Δ →
             ⊢ Γ ≈ Γ′ →
             --------------
             Γ′ ⊢r σ ∶ Δ
⊢r-resp-⊢≈ˡ (r-I σ≈I) Γ≈Γ′          = r-I (ctxeq-s-≈ Γ≈Γ′ σ≈I)
⊢r-resp-⊢≈ˡ (r-p ⊢τ ≈pτ) Γ≈Γ′       = r-p (⊢r-resp-⊢≈ˡ ⊢τ Γ≈Γ′) (ctxeq-s-≈ Γ≈Γ′ ≈pτ)
⊢r-resp-⊢≈ˡ (r-； Ψs ⊢τ ≈τ；n refl) ΨsΓ≈Γ′
  with ≈⇒∥⇒∥ Ψs ΨsΓ≈Γ′
...  | Ψs′ , Δ′ , refl , eql , Γ≈Δ′ = r-； Ψs′ (⊢r-resp-⊢≈ˡ ⊢τ Γ≈Δ′) (ctxeq-s-≈ ΨsΓ≈Γ′ ≈τ；n) (sym eql)

⊢r-resp-⊢≈ʳ : Γ ⊢r σ ∶ Δ →
             ⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢r σ ∶ Δ′
⊢r-resp-⊢≈ʳ (r-I σ≈) Δ≈Δ′                       = r-I (s-≈-conv σ≈ Δ≈Δ′)
⊢r-resp-⊢≈ʳ (r-p ⊢τ ≈pτ) Δ≈Δ′
  with presup-s (⊢r⇒⊢s ⊢τ)
... | _ , ⊢∺ ⊢Δ ⊢T                              = r-p (⊢r-resp-⊢≈ʳ ⊢τ (∺-cong Δ≈Δ′ (≈-refl ⊢T))) (s-≈-conv ≈pτ Δ≈Δ′)
⊢r-resp-⊢≈ʳ (r-； Ψs ⊢τ ≈τ；n eq) (κ-cong Δ≈Δ′) = r-； Ψs (⊢r-resp-⊢≈ʳ ⊢τ Δ≈Δ′) (s-≈-conv ≈τ；n (κ-cong Δ≈Δ′)) eq

----------------------------------------
-- Restricted weakenings form a category.

-- Restricted weakenings are closed under composition.
⊢r-∘ : Γ′ ⊢r σ′ ∶ Γ″ →
       Γ ⊢r σ ∶ Γ′ →
       -----------------
       Γ ⊢r σ′ ∘ σ ∶ Γ″
⊢r-∘ (r-I σ′≈I) ⊢σ
  with presup-s-≈ σ′≈I
...  | _ , _ , ⊢I , ⊢Γ″            = ⊢r-resp-⊢≈ʳ (s≈-resp-⊢r (s-≈-trans (∘-cong (s-≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈I) (s-≈-conv (I-∘ (⊢r⇒⊢s ⊢σ)) Γ′≈Γ″))
                                                             (⊢r-resp-⊢≈ʳ ⊢σ Γ′≈Γ″))
                                                 (⊢≈-refl ⊢Γ″)
  where Γ′≈Γ″ = ⊢I-inv ⊢I
⊢r-∘ (r-p ⊢τ ≈pτ) ⊢σ               = r-p (⊢r-∘ ⊢τ ⊢σ)
                                         (s-≈-trans (∘-cong (s-≈-refl (⊢r⇒⊢s ⊢σ)) ≈pτ)
                                                    (∘-assoc (s-wk (proj₂ (presup-s (⊢r⇒⊢s ⊢τ)))) (⊢r⇒⊢s ⊢τ) (⊢r⇒⊢s ⊢σ)))
⊢r-∘ (r-； Ψs ⊢τ ≈τ；n refl) ⊢σ
  with ⊢r-∥′ Ψs ⊢σ
...  | Ψs′ , Γ″ , refl , eql , ⊢σ∥ = r-； Ψs′ (⊢r-∘ ⊢τ ⊢σ∥)
                                         (s-≈-trans (∘-cong (s-≈-refl (⊢r⇒⊢s ⊢σ)) ≈τ；n)
                                                    (subst (λ n → Ψs′ ++⁺ Γ″ ⊢s _ ≈ _ ； n ∶ _)
                                                           (sym eql) (；-∘ Ψs (⊢r⇒⊢s ⊢τ) (⊢r⇒⊢s ⊢σ) refl)))
                                         refl

-- Identity is restricted.
⊢rI : ⊢ Γ → Γ ⊢r I ∶ Γ
⊢rI ⊢Γ = r-I (I-≈ ⊢Γ)

⊢rwk : ⊢ T ∺ Γ → T ∺ Γ ⊢r wk ∶ Γ
⊢rwk ⊢TΓ = r-p (⊢rI ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ)))
