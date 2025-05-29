{-# OPTIONS --without-K --safe #-}

module NonCumulative.Unascribed.Properties.Equivalence.Completeness where

open import Lib

open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Statics.Transfer

A⇒U-vlookup : ∀ {x i} →
  x ∶[ i ] A.T ∈! A.Γ →
  x ∶ ⌊ A.T ⌋ ∈! [⌊ A.Γ ⌋]
A⇒U-vlookup here = here
A⇒U-vlookup (there x∈Γ) = there (A⇒U-vlookup x∈Γ)

mutual
  A⇒U-⊢′ : A.⊢ A.Γ →
          -------
          U.⊢ [⌊ A.Γ ⌋]
  A⇒U-⊢′ ⊢[] = ⊢[]
  A⇒U-⊢′ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (A⇒U-⊢′ ⊢Γ) (A⇒U-tm′ ⊢T)

  A⇒U-⊢≈′ : A.⊢ A.Γ ≈ A.Δ →
           -------
           U.⊢ [⌊ A.Γ ⌋] ≈ [⌊ A.Δ ⌋]
  A⇒U-⊢≈′ []-≈ = []-≈
  A⇒U-⊢≈′ (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈′T′) = ∷-cong (A⇒U-⊢≈′ Γ≈Δ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢T′) (A⇒U-≈′ T≈T′) (A⇒U-≈′ T≈′T′)

  A⇒U-tm′ : ∀ {i} →
           A.Γ A.⊢ A.t ∶[ i ] A.T →
          -------------
           [⌊ A.Γ ⌋] U.⊢ ⌊ A.t ⌋ ∶ ⌊ A.T ⌋
  A⇒U-tm′ (N-wf ⊢Γ) = N-wf (A⇒U-⊢′ ⊢Γ)
  A⇒U-tm′ (Se-wf i ⊢Γ) = Se-wf _ (A⇒U-⊢′ ⊢Γ)
  A⇒U-tm′ (Liftt-wf n ⊢t) = Liftt-wf _ (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (Π-wf ⊢S ⊢T k≡maxij) = Π-wf (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) k≡maxij
  A⇒U-tm′ (vlookup ⊢Γ x∈Γ) = vlookup (A⇒U-⊢′ ⊢Γ) (A⇒U-vlookup x∈Γ)
  A⇒U-tm′ (ze-I ⊢Γ) = ze-I (A⇒U-⊢′ ⊢Γ)
  A⇒U-tm′ (su-I ⊢t) = su-I (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (N-E ⊢T ⊢s ⊢r ⊢t) = N-E (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢s) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (Λ-I ⊢S ⊢t k≡maxij) = Λ-I (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (Λ-E ⊢S ⊢T ⊢r ⊢s k≡maxij) = Λ-E (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢s)
  A⇒U-tm′ (L-I n ⊢t) = L-I _ (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (L-E n ⊢T ⊢t) = L-E _ (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-tm′ (t[σ] ⊢t ⊢σ) = t[σ] (A⇒U-tm′ ⊢t) (A⇒U-s′ ⊢σ)
  A⇒U-tm′ (conv ⊢t S≈T) = conv (A⇒U-tm′ ⊢t) (A⇒U-≈′ S≈T)

  A⇒U-s′ : A.Γ A.⊢s A.σ ∶ A.Δ →
          -------------
          [⌊ A.Γ ⌋] U.⊢s ⌊ A.σ ⌋ˢ ∶ [⌊ A.Δ ⌋]
  A⇒U-s′ (s-I ⊢Γ) = s-I (A⇒U-⊢′ ⊢Γ)
  A⇒U-s′ (s-wk ⊢T∷Δ) = s-wk (A⇒U-⊢′ ⊢T∷Δ)
  A⇒U-s′ (s-∘ ⊢σ ⊢τ) = s-∘ (A⇒U-s′ ⊢σ) (A⇒U-s′ ⊢τ)
  A⇒U-s′ (s-, ⊢σ ⊢T ⊢t) = s-, (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-s′ (s-conv ⊢σ Γ≈Δ) = s-conv (A⇒U-s′ ⊢σ) (A⇒U-⊢≈′ Γ≈Δ)

  A⇒U-≈′ : ∀ {i} →
          A.Γ A.⊢ A.t ≈ A.s ∶[ i ] A.T →
        -------------
          [⌊ A.Γ ⌋] U.⊢ ⌊ A.t ⌋ ≈ ⌊ A.s ⌋ ∶ ⌊ A.T ⌋
  A⇒U-≈′ (N-[] ⊢σ) = N-[] (A⇒U-s′ ⊢σ)
  A⇒U-≈′ (Se-[] i ⊢σ) = Se-[] _ (A⇒U-s′ ⊢σ)
  A⇒U-≈′ (Liftt-[] n ⊢σ ⊢T) = Liftt-[] _ (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢T)
  A⇒U-≈′ (Π-[] ⊢σ ⊢S ⊢T k≡maxij) = Π-[] (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) k≡maxij
  A⇒U-≈′ (Π-cong ⊢S S≈S′ T≈T′ k≡maxij) = Π-cong (A⇒U-tm′ ⊢S) (A⇒U-≈′ S≈S′) (A⇒U-≈′ T≈T′) k≡maxij
  A⇒U-≈′ (Liftt-cong n t≈s) = Liftt-cong _ (A⇒U-≈′ t≈s)
  A⇒U-≈′ (v-≈ ⊢Γ x∈Γ) = v-≈ (A⇒U-⊢′ ⊢Γ) (A⇒U-vlookup x∈Γ)
  A⇒U-≈′ (ze-≈ ⊢Γ) = ze-≈ (A⇒U-⊢′ ⊢Γ)
  A⇒U-≈′ (su-cong t≈s) = su-cong (A⇒U-≈′ t≈s)
  A⇒U-≈′ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′) = rec-cong (A⇒U-tm′ ⊢T) (A⇒U-≈′ T≈T′) (A⇒U-≈′ s≈s′) (A⇒U-≈′ r≈r′) (A⇒U-≈′ t≈t′)
  A⇒U-≈′ (Λ-cong ⊢S r≈r′ s≈s′ _) = Λ-cong (A⇒U-tm′ ⊢S) (A⇒U-≈′ r≈r′) (A⇒U-≈′ s≈s′)
  A⇒U-≈′ ($-cong ⊢S ⊢T r≈r s≈s′ _) = $-cong (A⇒U-tm′  ⊢S) (A⇒U-tm′ ⊢T) (A⇒U-≈′ r≈r) (A⇒U-≈′ s≈s′)
  A⇒U-≈′ (liftt-cong n t≈s) = liftt-cong _ (A⇒U-≈′ t≈s)
  A⇒U-≈′ (unlift-cong n ⊢T t≈s) = unlift-cong _ (A⇒U-tm′ ⊢T) (A⇒U-≈′ t≈s)
  A⇒U-≈′ ([]-cong t≈s σ≈τ) = []-cong (A⇒U-≈′ t≈s) (A⇒U-s≈′ σ≈τ)
  A⇒U-≈′ (ze-[] ⊢σ) = ze-[] (A⇒U-s′ ⊢σ)
  A⇒U-≈′ (su-[] ⊢σ ⊢t) = su-[] (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t) = rec-[] (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢s) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (Λ-[] ⊢σ ⊢S ⊢t k≡maxij) = Λ-[] (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ ($-[] ⊢S ⊢T ⊢σ ⊢r ⊢s _) = $-[] (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢s)
  A⇒U-≈′ (liftt-[] n ⊢σ ⊢T ⊢t) = liftt-[] _ (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (unlift-[] n ⊢T ⊢σ ⊢t) = unlift-[] _ (A⇒U-tm′ ⊢T) (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (rec-β-ze ⊢T ⊢s ⊢r) = rec-β-ze (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢s) (A⇒U-tm′ ⊢r)
  A⇒U-≈′ (rec-β-su ⊢T ⊢s ⊢r ⊢t) = rec-β-su (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢s) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (Λ-β ⊢S ⊢T ⊢r ⊢s) = Λ-β (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢r) (A⇒U-tm′ ⊢s)
  A⇒U-≈′ (Λ-η ⊢S ⊢T ⊢t i≡maxjk) = Λ-η (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ (L-β n ⊢s) = L-β _ (A⇒U-tm′ ⊢s)
  A⇒U-≈′ (L-η n ⊢T ⊢t) =  L-η _ (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ ([I] ⊢s) = [I] (A⇒U-tm′ ⊢s)
  A⇒U-≈′ ([wk] ⊢Γ ⊢S x∈Γ) = [wk] (A⇒U-⊢′ ⊢Γ) (A⇒U-tm′ ⊢S) (A⇒U-vlookup x∈Γ)
  A⇒U-≈′ ([∘] ⊢τ ⊢σ ⊢t) = [∘] (A⇒U-s′ ⊢τ) (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢t)
  A⇒U-≈′ ([,]-v-ze ⊢σ ⊢S ⊢s) = [,]-v-ze (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢s)
  A⇒U-≈′ ([,]-v-su ⊢σ ⊢S ⊢s x∈Γ) = [,]-v-su (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢S) (A⇒U-tm′ ⊢s) (A⇒U-vlookup x∈Γ)
  A⇒U-≈′ (≈-conv r≈s s≈t) = ≈-conv (A⇒U-≈′ r≈s) (A⇒U-≈′ s≈t)
  A⇒U-≈′ (≈-sym t≈s) = ≈-sym (A⇒U-≈′ t≈s)
  A⇒U-≈′ (≈-trans t≈s s≈r) = ≈-trans (A⇒U-≈′ t≈s) (A⇒U-≈′ s≈r)

  A⇒U-s≈′ : A.Γ A.⊢s A.σ ≈ A.τ ∶ A.Δ →
          -------------
           [⌊ A.Γ ⌋] U.⊢s ⌊ A.σ ⌋ˢ ≈ ⌊ A.τ ⌋ˢ ∶ [⌊ A.Δ ⌋]
  A⇒U-s≈′ (I-≈ ⊢Γ) = I-≈ (A⇒U-⊢′ ⊢Γ)
  A⇒U-s≈′ (wk-≈ ⊢T∷Δ) = wk-≈ (A⇒U-⊢′ ⊢T∷Δ)
  A⇒U-s≈′ (∘-cong τ≈τ′ σ≈σ′) = ∘-cong (A⇒U-s≈′ τ≈τ′) (A⇒U-s≈′ σ≈σ′)
  A⇒U-s≈′ (,-cong σ≈τ ⊢T T≈T′ t≈t′) = ,-cong (A⇒U-s≈′ σ≈τ) (A⇒U-tm′ ⊢T) (A⇒U-≈′ T≈T′) (A⇒U-≈′ t≈t′)
  A⇒U-s≈′ (I-∘ ⊢τ) = I-∘ (A⇒U-s′ ⊢τ)
  A⇒U-s≈′ (∘-I ⊢τ) = ∘-I (A⇒U-s′ ⊢τ)
  A⇒U-s≈′ (∘-assoc ⊢σ ⊢σ′ ⊢σ″) = ∘-assoc (A⇒U-s′ ⊢σ) (A⇒U-s′ ⊢σ′) (A⇒U-s′ ⊢σ″)
  A⇒U-s≈′ (,-∘ ⊢σ ⊢T ⊢t ⊢τ) = ,-∘ (A⇒U-s′ ⊢σ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t) (A⇒U-s′ ⊢τ)
  A⇒U-s≈′ (p-, ⊢τ ⊢T ⊢t) = p-, (A⇒U-s′ ⊢τ) (A⇒U-tm′ ⊢T) (A⇒U-tm′ ⊢t)
  A⇒U-s≈′ (,-ext ⊢σ) = ,-ext (A⇒U-s′ ⊢σ)
  A⇒U-s≈′ (s-≈-sym σ≈τ) = s-≈-sym (A⇒U-s≈′ σ≈τ)
  A⇒U-s≈′ (s-≈-trans σ≈τ τ≈τ′) = s-≈-trans (A⇒U-s≈′ σ≈τ) (A⇒U-s≈′ τ≈τ′)
  A⇒U-s≈′ (s-≈-conv σ≈τ Γ≈Δ) = s-≈-conv (A⇒U-s≈′ σ≈τ) (A⇒U-⊢≈′ Γ≈Δ)

mutual
  A⇒U-⊢ : A.⊢ A.Γ →
          A.Γ [↝] U.Γ′ →
          -------
          U.⊢ U.Γ′
  A⇒U-⊢ ⊢Γ Γ[↝]Γ′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ = A⇒U-⊢′ ⊢Γ

  A⇒U-⊢≈ : A.⊢ A.Γ ≈ A.Δ →
           A.Γ [↝] U.Γ′ →
           A.Δ [↝] U.Δ′ →
           -------
           U.⊢ U.Γ′ ≈ U.Δ′
  A⇒U-⊢≈ Γ≈Δ Γ[↝]Γ′ Δ[↝]Δ′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ 
          | ↝[]⇒[⌊⌋] Δ[↝]Δ′ = A⇒U-⊢≈′ Γ≈Δ

  A⇒U-tm : ∀ {i} →
           A.Γ A.⊢ A.t ∶[ i ] A.T →
           A.Γ [↝] U.Γ′ →
           A.t ↝ U.t′ →
           A.T ↝ U.T′ →
          -------------
           U.Γ′ U.⊢ U.t′ ∶ U.T′
  A⇒U-tm ⊢t Γ[↝]Γ′ t↝t′ T↝T′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ 
          | ↝⇒⌊⌋ t↝t′
          | ↝⇒⌊⌋ T↝T′ = A⇒U-tm′ ⊢t

  A⇒U-s : A.Γ A.⊢s A.σ ∶ A.Δ →
          A.Γ [↝] U.Γ′ →
          A.σ ↝s U.σ′ →
          A.Δ [↝] U.Δ′ →
          -------------
          U.Γ′ U.⊢s U.σ′ ∶ U.Δ′
  A⇒U-s ⊢σ Γ[↝]Γ′ σ↝σ′ Δ[↝]Δ′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ 
          | ↝s⇒⌊⌋s σ↝σ′
          | ↝[]⇒[⌊⌋] Δ[↝]Δ′ = A⇒U-s′ ⊢σ

  A⇒U-≈ : ∀ {i} →
          A.Γ A.⊢ A.t ≈ A.s ∶[ i ] A.T →
          A.Γ [↝] U.Γ′ →
          A.t ↝ U.t′ →
          A.s ↝ U.s′ →
          A.T ↝ U.T′ →
        -------------
          U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′
  A⇒U-≈ t≈s Γ[↝]Γ′ t↝t′ s↝s′ T↝T′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ 
          | ↝⇒⌊⌋ t↝t′
          | ↝⇒⌊⌋ s↝s′
          | ↝⇒⌊⌋ T↝T′ = A⇒U-≈′ t≈s

  A⇒U-s≈ : A.Γ A.⊢s A.σ ≈ A.τ ∶ A.Δ →
           A.Γ [↝] U.Γ′ →
           A.Δ [↝] U.Δ′ →
           A.σ ↝s U.σ′ →
           A.τ ↝s U.τ′ →
          -------------
           U.Γ′ U.⊢s U.σ′ ≈ U.τ′ ∶ U.Δ′
  A⇒U-s≈ σ≈τ Γ[↝]Γ′ Δ[↝]Δ′ σ↝σ′ τ↝τ′ 
    rewrite ↝[]⇒[⌊⌋] Γ[↝]Γ′ 
          | ↝s⇒⌊⌋s σ↝σ′
          | ↝s⇒⌊⌋s τ↝τ′
          | ↝[]⇒[⌊⌋] Δ[↝]Δ′ = A⇒U-s≈′ σ≈τ
