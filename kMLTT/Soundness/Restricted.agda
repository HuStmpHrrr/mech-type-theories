{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.Restricted where

open import Lib

open import Data.List.Properties as Lₚ

open import kMLTT.Statics

infix 4 _⊢r_∶_

data _⊢r_∶_ : Ctxs → Substs → Ctxs → Set where
  r-I : Γ ⊢s σ ≈ I ∶ Γ →
        ----------------
        Γ ⊢r σ ∶ Γ
  -- TODO: r-wk
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


⊢r⇒⊢s : Γ ⊢r σ ∶ Δ → Γ ⊢s σ ∶ Δ
⊢r⇒⊢s (r-I ⊢σ)        = proj₁ (proj₂ (presup-s-≈ ⊢σ))
⊢r⇒⊢s (r-p _ ⊢σ)      = proj₁ (proj₂ (presup-s-≈ ⊢σ))
⊢r⇒⊢s (r-； _ _ ⊢σ _) = proj₁ (proj₂ (presup-s-≈ ⊢σ))

s≈-resp-⊢r : Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢r σ′ ∶ Δ → Γ ⊢r σ ∶ Δ
s≈-resp-⊢r σ≈σ′ (r-I σ′≈)           = r-I (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-p ⊢δ σ′≈)        = r-p ⊢δ (s-≈-trans σ≈σ′ σ′≈)
s≈-resp-⊢r σ≈σ′ (r-； Γs ⊢δ σ′≈ eq) = r-； Γs ⊢δ (s-≈-trans σ≈σ′ σ′≈) eq

⊢r-∥ : ∀ n →
       Γ ⊢r σ ∶ Γ′ →
       n < len Γ′ →
       -------------------------
       ∃₂ λ Ψs′ Δ′ → ∃₂ λ Ψs Δ →
            Γ′ ≡ Ψs′ ++⁺ Δ′
          × Γ ≡ Ψs ++⁺ Δ
          × len Ψs′ ≡ n
          × len Ψs ≡ L σ n
          × Δ ⊢r σ ∥ n ∶ Δ′
⊢r-∥ {Γ} {σ} n (r-I σ≈I) n<
  with chop Γ n<
...  | Ψs , Γ′ , refl , refl
     with ∥-resp-≈′ Ψs σ≈I
...     | Ψs′ , Γ″ , eq , eql , σ∥≈
        rewrite I-∥ (len Ψs)          = Ψs , Γ′ , Ψs , Γ′ , refl , refl , refl
                                      , sym (trans (L-resp-≈ n σ≈I) (L-I _)) , helper (++⁺ˡ-cancel Ψs Ψs′ eq (sym (trans eql (trans (L-resp-≈ n σ≈I) (L-I (len Ψs))))))
  where helper : Γ′ ≡ Γ″ →  Γ′ ⊢r σ ∥ n ∶ Γ′
        helper refl = r-I σ∥≈
⊢r-∥ zero (r-p ⊢τ σ≈p) n<             = [] , _ , [] , _ , refl , refl , refl , refl , r-p ⊢τ σ≈p
⊢r-∥ {Γ} {σ} (suc n) (r-p ⊢τ σ≈p) n<
  with ⊢r-∥ (suc n) ⊢τ n<
...  | (_ ∷ Ψ) ∷ Ψs′ , Δ′ , Ψs , Δ
     , refl , eq′ , refl , eql′ , ⊢τ∥
     with ∥-resp-≈′ (Ψ ∷ Ψs′) σ≈p
...     | Ψs″ , Δ″ , eq″ , eql″ , σ≈∥ = Ψ ∷ Ψs′ , Δ′ , Ψs , Δ
                                      , refl , eq′ , refl , trans eql′ (sym eqL)
                                      , helper (++⁺ˡ-cancel Ψs Ψs″ (trans (sym eq′) eq″) (sym (trans eql″ (trans eqL (sym eql′)))))
  where eqL         = L-resp-≈ (suc n) σ≈p
        helper : Δ ≡ Δ″ → Δ ⊢r σ ∥ suc (len Ψs′) ∶ Δ′
        helper refl = s≈-resp-⊢r σ≈∥ (s≈-resp-⊢r (s-≈-refl (⊢r⇒⊢s {!⊢τ∥!})) {!!})
⊢r-∥ zero (r-； Ψs ⊢τ σ≈； eq) n<     = [] , _ , [] , _ , refl , refl , refl , refl , r-； Ψs ⊢τ σ≈； eq
⊢r-∥ {_} {σ} (suc n) (r-； Ψs ⊢τ σ≈； refl) (s≤s n<)
  with ⊢r-∥ n ⊢τ n<
...  | Ψs′ , Δ′ , Ψs₁ , Δ
     , refl , refl , refl , eql′ , ⊢τ∥
     with ∥-resp-≈′ ([] ∷ Ψs′) σ≈；
...     | Ψs″ , Δ″ , eq″ , eql″ , σ≈∥ = [] ∷ Ψs′ , Δ′ , Ψs ++ Ψs₁ , Δ
                                      , refl , sym (++-++⁺ Ψs)
                                      , refl , trans (length-++ Ψs) (trans (cong (len Ψs +_) eql′) (sym eqL))
                                      , helper (++⁺ˡ-cancel (Ψs ++ Ψs₁) Ψs″
                                                            (trans (++-++⁺ Ψs) eq″)
                                                            (sym (trans eql″
                                                                 (trans eqL
                                                                 (trans (cong (_ +_) (sym eql′))
                                                                        (sym (length-++ Ψs)))))))
  where eqL = L-resp-≈ (suc n) σ≈；
        helper : Δ ≡ Δ″ → Δ ⊢r σ ∥ suc (len Ψs′) ∶ Δ′
        helper refl = s≈-resp-⊢r σ≈∥ ⊢τ∥

⊢r-∥′ : ∀ Ψs →
        Γ ⊢r σ ∶ Ψs ++⁺ Γ′ →
        ----------------------------
        ∃₂ λ Ψs′ Δ′ →
             Γ ≡ Ψs′ ++⁺ Δ′
           × len Ψs′ ≡ L σ (len Ψs)
           × Δ′ ⊢r σ ∥ len Ψs ∶ Γ′
⊢r-∥′ Ψs ⊢σ
  with ⊢r-∥ (len Ψs) ⊢σ (length-<-++⁺ Ψs)
...  | Ψs′ , Δ′ , Ψs₁ , Δ
     , eq , eq′ , eql , eql′ , ⊢τ∥
     rewrite ++⁺ˡ-cancel Ψs Ψs′ eq (sym eql) = Ψs₁ , Δ , eq′ , eql′ , ⊢τ∥

⊢r-∘ : Γ′ ⊢r σ′ ∶ Γ″ → Γ ⊢r σ ∶ Γ′ → Γ ⊢r σ′ ∘ σ ∶ Γ″
⊢r-∘ (r-I σ′≈I) ⊢σ                = s≈-resp-⊢r (s-≈-trans (∘-cong (s-≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈I) (I-∘ (⊢r⇒⊢s ⊢σ))) ⊢σ
⊢r-∘ (r-p ⊢τ σ′≈p) ⊢σ             = r-p (⊢r-∘ ⊢τ ⊢σ) {!σ′≈p!}
⊢r-∘ (r-； Ψs ⊢τ σ′≈； refl) ⊢σ
  with ⊢r-∥′ Ψs ⊢σ
...  | Ψs₁ , Γ″ , refl , eql , ⊢σ∥ = r-； Ψs₁ (⊢r-∘ ⊢τ ⊢σ∥)
                                        (s-≈-trans (∘-cong (s-≈-refl (⊢r⇒⊢s ⊢σ)) σ′≈；)
                                                   (subst (λ n → Ψs₁ ++⁺ Γ″ ⊢s _ ≈ _ ； n ∶ _)
                                                          (sym eql)
                                                          (；-∘ Ψs (⊢r⇒⊢s ⊢τ) (⊢r⇒⊢s ⊢σ) refl)))
                                        refl
