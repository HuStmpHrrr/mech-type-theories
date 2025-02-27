{-# OPTIONS --without-K --safe #-}

module NonCumulative.Unascribed.Properties.Equivalence.Completeness where

open import Lib

open import NonCumulative.Ascribed.Statics.Full as A
open import NonCumulative.Unascribed.Statics.Full as U
open import NonCumulative.Unascribed.Statics.Transfer

-- ↝ relation is functonal (deterministic and total)
mutual
  ↝-det : ∀ {t₁′ t₂′} →
          A.t ↝ t₁′ →
          A.t ↝ t₂′ →
          -------------
          t₁′ ≡ t₂′
  ↝-det {N} ↝N ↝N = refl
  ↝-det {Π .(_ ↙ _) .(_ ↙ _)} (↝Π S↝S₁′ T↝T₁′) (↝Π S↝S₂′ T↝T₂′) = cong₂ Π (↝-det S↝S₁′ S↝S₂′) (↝-det T↝T₁′ T↝T₂′)
  ↝-det {Liftt n .(_ ↙ _)} (↝Liftt T↝T₁′) (↝Liftt T↝T₂′) = cong₂ Liftt refl (↝-det T↝T₁′ T↝T₂′)
  ↝-det {Se i} ↝Se ↝Se = refl
  ↝-det {v x} ↝v ↝v = refl
  ↝-det {ze} ↝ze ↝ze = refl
  ↝-det {su t} (↝su t↝₁t′) (↝su t↝₂t′) = cong su (↝-det t↝₁t′ t↝₂t′)
  ↝-det {rec .(_ ↙ _) t t₁ t₂} (↝rec T↝T₁′ r↝r₁′ s↝s₁′ t↝₁t′) (↝rec T↝T₂′ r↝r₂′ s↝s₂′ t↝₂t′)
    with ↝-det T↝T₂′ T↝T₁′
       | ↝-det r↝r₂′ r↝r₁′
       | ↝-det s↝s₂′ s↝s₁′
       | ↝-det t↝₂t′ t↝₁t′
  ... | refl | refl | refl | refl = refl
  ↝-det {Λ .(_ ↙ _) t} (↝Λ S↝₁S′ t↝₁t′) (↝Λ S↝₂S′ t↝₂t′) = cong₂ Λ (↝-det S↝₁S′ S↝₂S′) (↝-det t↝₁t′ t↝₂t′)
  ↝-det {t $ s} (↝$ t↝₁t′ s↝s₁′) (↝$ t↝₂t′ s↝s₂′) = cong₂ _$_ (↝-det t↝₁t′ t↝₂t′) (↝-det s↝s₁′ s↝s₂′)
  ↝-det {liftt x t} (↝liftt t↝₁t′) (↝liftt t↝₂t′) = cong₂ liftt refl (↝-det t↝₁t′ t↝₂t′)
  ↝-det {unlift t} (↝unlift t↝₁t′) (↝unlift t↝₂t′) = cong unlift (↝-det t↝₁t′ t↝₂t′)
  ↝-det {sub t σ} (↝sub t↝₁t′ σ↝₁σ′) (↝sub t↝₂t′ σ↝₂σ′) = cong₂ sub (↝-det t↝₁t′ t↝₂t′) (↝s-det σ↝₁σ′ σ↝₂σ′)

  ↝s-det : ∀ {σ₁′ σ₂′} →
            _↝s_ A.σ σ₁′ →
            _↝s_ A.σ σ₂′ →
            -------------
            σ₁′ ≡ σ₂′
  ↝s-det {I} ↝I ↝I = refl
  ↝s-det {wk} ↝wk ↝wk = refl
  ↝s-det {σ ∘ τ} (↝∘ σ↝₁σ′ τ↝τ₁′) (↝∘ σ↝₂σ′ τ↝τ₂′) = cong₂ _∘_ (↝s-det σ↝₁σ′ σ↝₂σ′) (↝s-det τ↝τ₁′ τ↝τ₂′)
  ↝s-det {σ , t ∶ T} (↝, σ↝₁σ′ t↝₁t′ T↝₁T′) (↝, σ↝₂σ′ t↝₂t′ T↝₂T′) = cong₃ _,_∶_ (↝s-det σ↝₁σ′ σ↝₂σ′) (↝-det t↝₁t′ t↝₂t′) (↝-det T↝₁T′ T↝₂T′)

[↝]-det : ∀ {Γ₁′ Γ₂′} →
          A.Γ [↝] Γ₁′ →
          A.Γ [↝] Γ₂′ →
          -------------
          Γ₁′ ≡ Γ₂′
[↝]-det {[]} ↝[] ↝[] = refl
[↝]-det {.(_ ↙ _) ∷ Γ} (↝∷ Γ↝Γ₁′ T↝T₁′) (↝∷ Γ↝Γ₂ T↝T₂′) = cong₂ _∷_ (↝-det T↝T₁′ T↝T₂′) ([↝]-det Γ↝Γ₁′ Γ↝Γ₂)

mutual
  ↝-total : ∀ t →
            ∃ λ t′ → t ↝ t′
  ↝-total N = _ , ↝N
  ↝-total (Π (S ↙ i) (T ↙ j))
    with ↝-total S
       | ↝-total T
  ...  | _ , S↝S′ | _ , T↝T′ = _ , (↝Π S↝S′ T↝T′)
  ↝-total (Liftt n (T ↙ i))
    with ↝-total T
  ... | _ , T↝T′ = _ , (↝Liftt T↝T′)
  ↝-total (Se i) = _ , ↝Se
  ↝-total (v x) = _ , ↝v
  ↝-total ze = _ , ↝ze
  ↝-total (su t)
    with ↝-total t
  ... | _ , t↝t′ = _ , ↝su t↝t′
  ↝-total (rec (T ↙ i) s r t)
    with ↝-total T
       | ↝-total s
       | ↝-total r
       | ↝-total t
  ...  | _ , T↝T′ | _ , s↝s′
       | _ , r↝r′ | _ , t↝t′ = _ , ↝rec T↝T′ s↝s′ r↝r′ t↝t′
  ↝-total (Λ (S ↙ i) t)
    with ↝-total S
       | ↝-total t
  ... | _ , S↝S′ | _ , t↝t′ = _ , ↝Λ S↝S′ t↝t′
  ↝-total (r $ s)
    with ↝-total r
       | ↝-total s
  ...  | _ , r↝r′ | _ , s↝s′ = _ , ↝$ r↝r′ s↝s′
  ↝-total (liftt n t)
    with ↝-total t
  ... | _ , t↝t′ = _ , ↝liftt t↝t′
  ↝-total (unlift t)
    with ↝-total t
  ... | _ , t↝t′ = _ , (↝unlift t↝t′)
  ↝-total (sub t σ)
    with ↝-total t
       | ↝s-total σ
  ...  | _ , t↝t′ | _ , σ↝σ′ = _ , ↝sub t↝t′ σ↝σ′

  ↝s-total : ∀ σ →
              ∃ λ σ′ → σ ↝s σ′
  ↝s-total I = _ , ↝I
  ↝s-total wk = _ , ↝wk
  ↝s-total (σ ∘ τ)
    with ↝s-total σ
       | ↝s-total τ
  ...  | _ , σ↝σ′ | _ , τ↝τ′ = _ , ↝∘ σ↝σ′ τ↝τ′
  ↝s-total (σ , t ∶ T ↙ i)
    with ↝s-total σ
       | ↝-total t
       | ↝-total T
  ...  | _ , σ↝σ′ | _ , t↝t′ | _ , T↝T′ = _ , ↝, σ↝σ′ t↝t′ T↝T′

[↝]-total : ∀ Γ →
            ∃ λ Γ′ → Γ [↝] Γ′
[↝]-total [] = _ , ↝[]
[↝]-total ((T ↙ i) ∷ Γ)
  with ↝-total T
     | [↝]-total Γ
...  | T′ , T↝T′
     | Γ′ , Γ↝Γ′ = _ , ↝∷ Γ↝Γ′ T↝T′

A⇒U-vlookup : ∀ {x i} →
  x ∶[ i ] A.T ∈! A.Γ →
  A.Γ [↝] U.Γ′ →
  A.T ↝ U.T′ →
  x ∶ U.T′ ∈! U.Γ′
A⇒U-vlookup here (↝∷ Γ↝Γ′ T↝T′) (↝sub T↝′T′ ↝wk) with ↝-det T↝T′ T↝′T′
... | refl = here
A⇒U-vlookup (there x∈Γ′) (↝∷ Γ↝Γ′ _) (↝sub T↝T′ ↝wk) = there (A⇒U-vlookup x∈Γ′ Γ↝Γ′ T↝T′)

mutual
  A⇒U-⊢ : A.⊢ A.Γ →
          A.Γ [↝] U.Γ′ →
          -------
          U.⊢ U.Γ′
  A⇒U-⊢ ⊢[] ↝[] = ⊢[]
  A⇒U-⊢ (⊢∷ ⊢Γ ⊢T) (↝∷ Γ↝Γ′ T↝T′) = ⊢∷ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se)

  A⇒U-⊢≈ : A.⊢ A.Γ ≈ A.Δ →
           A.Γ [↝] U.Γ′ →
           A.Δ [↝] U.Δ′ →
           -------
           U.⊢ U.Γ′ ≈ U.Δ′
  A⇒U-⊢≈ []-≈ ↝[] ↝[] = []-≈
  A⇒U-⊢≈ (∷-cong {T = T} {T′ = S} Γ≈Δ ⊢T ⊢S T≈S T≈′S) (↝∷ Γ↝Γ′ T↝T′) (↝∷ {Γ′ = Δ′} {T′ = S′} Δ↝Δ′ S↝S′) =
    ∷-cong (A⇒U-⊢≈ Γ≈Δ Γ↝Γ′ Δ↝Δ′) (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se) (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se)
           (A⇒U-≈ T≈S Γ↝Γ′ T↝T′ S↝S′ ↝Se) (A⇒U-≈ T≈′S Δ↝Δ′ T↝T′ S↝S′ ↝Se)

  A⇒U-tm : ∀ {i} →
           A.Γ A.⊢ A.t ∶[ i ] A.T →
           A.Γ [↝] U.Γ′ →
           A.t ↝ U.t′ →
           A.T ↝ U.T′ →
          -------------
           U.Γ′ U.⊢ U.t′ ∶ U.T′
  A⇒U-tm (N-wf ⊢Γ) Γ↝Γ′ ↝N ↝Se = N-wf (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (Se-wf i ⊢Γ) Γ↝Γ′ ↝Se ↝Se = Se-wf _ (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (Liftt-wf n ⊢T) Γ↝Γ′ (↝Liftt T↝T′) ↝Se = Liftt-wf _ (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se)
  A⇒U-tm (Π-wf ⊢S ⊢T k≡maxij) Γ↝Γ′ (↝Π S↝S′ T↝T′) ↝Se = Π-wf (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se) k≡maxij
  A⇒U-tm (vlookup ⊢Γ x∈Γ) Γ↝Γ′ ↝v T↝T′ = vlookup (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-vlookup x∈Γ Γ↝Γ′ T↝T′)
  A⇒U-tm (ze-I ⊢Γ) Γ↝Γ′ ↝ze ↝N = ze-I (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-tm (su-I ⊢t) Γ↝Γ′ (↝su t↝t′) ↝N = su-I (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ ↝N)
  A⇒U-tm (N-E ⊢T ⊢s ⊢r ⊢t) Γ↝Γ′ (↝rec T↝T′ s↝s′ r↝r′ t↝t′) (↝sub T↝′T′ (↝, ↝I t↝₁t′ ↝N))
    with ↝-det t↝₁t′  t↝t′
       | ↝-det T↝′T′ T↝T′
  ... | refl | refl = N-E (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ ↝N) T↝T′ ↝Se)
                          (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub T↝T′ (↝, ↝I ↝ze ↝N)))
                          (A⇒U-tm ⊢r (↝∷ (↝∷ Γ↝Γ′ ↝N) T↝T′) r↝r′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N)))
                          (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ ↝N)
  A⇒U-tm (Λ-I {i = j} {j = k} ⊢S ⊢t i≡maxjk) Γ↝Γ′ (↝Λ S↝S′ t↝t′) (↝Π S↝₁S′ T↝T′)
    with ↝-det S↝S′ S↝₁S′
  ... | refl = Λ-I (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)  (A⇒U-tm ⊢t (↝∷ Γ↝Γ′ S↝S′) t↝t′ T↝T′)
  A⇒U-tm (Λ-E {S = S} ⊢S ⊢T ⊢r ⊢s k≡maxij) Γ↝Γ′ (↝$ r↝r′ s↝s′) (↝sub T↝T′ (↝, ↝I s↝₁s′ S↝S′)) with ↝-det s↝₁s′  s↝s′
  ... | refl
    = Λ-E (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se)  (A⇒U-tm ⊢r Γ↝Γ′ r↝r′ (↝Π S↝S′ T↝T′))  (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ S↝S′)
  A⇒U-tm (L-I n ⊢t) Γ↝Γ′ (↝liftt t↝t′) (↝Liftt T↝T′) = L-I _ (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ T↝T′)
  A⇒U-tm (L-E n ⊢T ⊢t) Γ↝Γ′ (↝unlift t↝t′) T↝T′ = L-E _ (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se) (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝Liftt T↝T′))
  A⇒U-tm (t[σ] {Δ = Δ} ⊢t ⊢σ) Γ↝Γ′ (↝sub t↝t′ σ↝σ′) (↝sub {t′ = T′} T↝T′ σ↝₁σ′)
    with ↝s-det σ↝₁σ′ σ↝σ′
       | [↝]-total Δ
  ... | refl
      | Δ′ , Δ↝Δ′ = t[σ] (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ T↝T′) (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
  A⇒U-tm (conv {S = S} ⊢t S≈T) Γ↝Γ′ t↝t′ T↝T′ with ↝-total S
  ... | S′ , S↝S′ = conv (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ S↝S′) (A⇒U-≈ S≈T Γ↝Γ′ S↝S′ T↝T′ ↝Se)

  A⇒U-s : A.Γ A.⊢s A.σ ∶ A.Δ →
          A.Γ [↝] U.Γ′ →
          A.σ ↝s U.σ′ →
          A.Δ [↝] U.Δ′ →
          -------------
          U.Γ′ U.⊢s U.σ′ ∶ U.Δ′
  A⇒U-s (s-I ⊢Γ) Γ↝Γ′ ↝I Δ↝Δ′ with [↝]-det Δ↝Δ′ Γ↝Γ′
  ... | refl = s-I (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-s (s-wk (⊢∷ ⊢Γ ⊢t)) (↝∷ Γ↝Γ′ T↝T′) ↝wk Δ↝Δ′ with [↝]-det Δ↝Δ′ Γ↝Γ′
  ... | refl = s-wk (⊢∷ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢t Γ↝Γ′ T↝T′ ↝Se))
  A⇒U-s (s-∘ {Γ′ = Σ} ⊢σ ⊢τ) Γ↝Γ′ (↝∘ σ↝σ′ τ↝τ′) Δ↝Δ′ with [↝]-total Σ
  ... | Σ′ , Σ↝Σ′ = s-∘ (A⇒U-s ⊢σ Γ↝Γ′ τ↝τ′ Σ↝Σ′) (A⇒U-s ⊢τ Σ↝Σ′ σ↝σ′ Δ↝Δ′)
  A⇒U-s (s-, ⊢σ ⊢T ⊢t) Γ↝Γ′ (↝, σ↝σ′ t↝t′ T↝T′) (↝∷ Δ↝Δ′ T↝T₁′) 
    with refl ← ↝-det T↝T′ T↝T₁′
    = s-, (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′  Δ↝Δ′) (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se) (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝sub T↝T′ σ↝σ′))
  A⇒U-s (s-conv {Δ = Δ} {Δ′ = Σ} ⊢σ Δ≈Σ) Γ↝Γ′ σ↝σ′ Σ↝Σ′ with [↝]-total Δ
  ... | Δ′ , Δ↝Δ′ = s-conv (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) (A⇒U-⊢≈ Δ≈Σ Δ↝Δ′ Σ↝Σ′)

  A⇒U-≈ : ∀ {i} →
          A.Γ A.⊢ A.t ≈ A.s ∶[ i ] A.T →
          A.Γ [↝] U.Γ′ →
          A.t ↝ U.t′ →
          A.s ↝ U.s′ →
          A.T ↝ U.T′ →
        -------------
          U.Γ′ U.⊢ U.t′ ≈ U.s′ ∶ U.T′
  A⇒U-≈ (N-[] {Δ = Δ} ⊢σ) Γ↝Γ′ (↝sub ↝N σ↝σ′) ↝N ↝Se with [↝]-total Δ
  ... | Δ′ , Δ↝Δ′ = N-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
  A⇒U-≈ (Se-[] {Δ = Δ} i ⊢σ) Γ↝Γ′ (↝sub ↝Se σ↝σ′) ↝Se ↝Se with [↝]-total Δ
  ... | Δ′ , Δ↝Δ′ = Se-[] _ (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
  A⇒U-≈ (Liftt-[] {Δ = Δ} n ⊢σ ⊢T) Γ↝Γ′ (↝sub (↝Liftt T↝T′) σ↝σ′) (↝Liftt (↝sub T↝′T′ σ↝₁σ′ )) ↝Se
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝-det T↝T′ T↝′T′
       | [↝]-total Δ
  ... | refl | refl
      | Δ′ , Δ↝Δ′ = Liftt-[] _ (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se)
  A⇒U-≈ {s′ = ._} (Π-[] {Δ = Δ} ⊢σ ⊢S ⊢T k≡maxij) Γ↝Γ′ (↝sub (↝Π S↝S′ T↝T′) σ↝σ′) (↝Π (↝sub S↝′S′ σ↝₁σ′ ) (↝sub T↝′T′ (↝, (↝∘ σ↝₂σ′  ↝wk) ↝v S↝″S′))) ↝Se
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝-det T↝T′ T↝′T′
       | ↝-det S↝S′ S↝′S′
       | ↝-det S↝S′ S↝″S′
       | [↝]-total Δ
  ... | refl | refl | refl | refl | Δ′ , Δ↝Δ′
    with ↝s-det σ↝σ′ σ↝₂σ′
  ... | refl = Π-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
                    (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se)
                    (A⇒U-tm ⊢T (↝∷ Δ↝Δ′ S↝S′) T↝T′ ↝Se) k≡maxij
  A⇒U-≈ (Π-cong ⊢S S≈S₂ T≈T₂ k≡maxij) Γ↝Γ′ (↝Π S↝S′ T↝T′) (↝Π S₂↝S₂′ T₂↝T₂′) ↝Se = Π-cong
                                                                                    (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)
                                                                                    (A⇒U-≈ S≈S₂ Γ↝Γ′ S↝S′ S₂↝S₂′ ↝Se)
                                                                                    (A⇒U-≈ T≈T₂ (↝∷ Γ↝Γ′ S↝S′) T↝T′ T₂↝T₂′ ↝Se) k≡maxij
  A⇒U-≈ (Liftt-cong n T≈S) Γ↝Γ′ (↝Liftt T↝T′) (↝Liftt S↝S′) ↝Se = Liftt-cong _ (A⇒U-≈ T≈S Γ↝Γ′ T↝T′ S↝S′ ↝Se)
  A⇒U-≈ (v-≈ ⊢Γ x∈Γ) Γ↝Γ′ ↝v ↝v T↝T′ = v-≈ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-vlookup x∈Γ Γ↝Γ′ T↝T′)
  A⇒U-≈ (ze-≈ ⊢Γ) Γ↝Γ′ ↝ze ↝ze ↝N = ze-≈ (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-≈ (su-cong t≈s) Γ↝Γ′ (↝su t↝t′) (↝su s↝s′) ↝N = su-cong (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ ↝N)
  A⇒U-≈ (rec-cong ⊢T T≈T₂ s≈s₂ r≈r₂ t≈t₂) Γ↝Γ′ (↝rec T↝T′ s↝s′ r↝r′ t↝t′) (↝rec T₂↝T₂′ s₂↝s₂′ r₂↝r₂′ t₂↝t₂′) (↝sub T↝′T′ (↝, ↝I t↝₁t′ ↝N))
   with ↝-det T↝T′ T↝′T′
      | ↝-det t↝t′ t↝₁t′
  ... | refl | refl = rec-cong (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ ↝N) T↝T′ ↝Se)
                               (A⇒U-≈ T≈T₂ (↝∷ Γ↝Γ′ ↝N) T↝T′ T₂↝T₂′ ↝Se)
                               (A⇒U-≈ s≈s₂ Γ↝Γ′ s↝s′ s₂↝s₂′ (↝sub T↝T′ (↝, ↝I ↝ze ↝N)))
                               (A⇒U-≈ r≈r₂ (↝∷ (↝∷ Γ↝Γ′ ↝N) T↝T′) r↝r′ r₂↝r₂′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N)))
                               (A⇒U-≈ t≈t₂ Γ↝Γ′ t↝t′ t₂↝t₂′ ↝N)
  A⇒U-≈ (Λ-cong ⊢S S≈T t≈s _) Γ↝Γ′ (↝Λ S↝S′ t↝t′) (↝Λ S₁↝S₁′ s↝s′) (↝Π S↝₁S′ T↝T′)
    with ↝-det S↝S′ S↝₁S′
  ...  | refl = Λ-cong (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-≈ S≈T Γ↝Γ′ S↝S′ S₁↝S₁′ ↝Se) (A⇒U-≈ t≈s (↝∷ Γ↝Γ′ S↝S′) t↝t′ s↝s′ T↝T′)
  A⇒U-≈ ($-cong {S = S} ⊢S ⊢T r≈r₂ s≈s₂ k≡maxij) Γ↝Γ′ (↝$ r↝r′ s↝s′) (↝$ r₂↝r₂′ s₂↝s₂′) (↝sub T↝T′ (↝, ↝I s↝₁s′ S↝S′))
    with ↝-det s↝s′ s↝₁s′
  ...  | refl
    = $-cong (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)
                     (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se)
                     (A⇒U-≈ r≈r₂ Γ↝Γ′ r↝r′ r₂↝r₂′ (↝Π S↝S′ T↝T′))
                     (A⇒U-≈ s≈s₂ Γ↝Γ′ s↝s′ s₂↝s₂′ S↝S′)
  A⇒U-≈ (liftt-cong n t≈s) Γ↝Γ′ (↝liftt t↝t′) (↝liftt s↝s′) (↝Liftt T↝T′) = liftt-cong _ (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ T↝T′)
  A⇒U-≈ (unlift-cong n ⊢T t≈s) Γ↝Γ′ (↝unlift t↝t′) (↝unlift s↝s′) T↝T′ = unlift-cong _
                                                                                     (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se)
                                                                                     (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ (↝Liftt T↝T′))
  A⇒U-≈ ([]-cong {Δ = Δ} t≈s σ≈τ) Γ↝Γ′ (↝sub t↝t′ σ↝σ′) (↝sub s↝s′ τ↝τ′) (↝sub T↝T′ σ↝₁σ′ )
    with ↝s-det σ↝σ′ σ↝₁σ′
       | [↝]-total Δ
  ...  | refl
       | Δ′ , Δ↝Δ′ = []-cong (A⇒U-≈ t≈s Δ↝Δ′ t↝t′ s↝s′ T↝T′) (A⇒U-s≈ σ≈τ Γ↝Γ′ Δ↝Δ′ σ↝σ′ τ↝τ′)
  A⇒U-≈ (ze-[] {Δ = Δ} ⊢σ) Γ↝Γ′ (↝sub ↝ze σ↝σ′) ↝ze ↝N with [↝]-total Δ
  ... | Δ′ , Δ↝Δ′ =  ze-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
  A⇒U-≈ (su-[] {Δ = Δ} ⊢σ ⊢t) Γ↝Γ′ (↝sub (↝su t↝t′) σ↝σ′) (↝su (↝sub t↝₁t′  σ↝₁σ′ )) ↝N
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝-det t↝t′ t↝₁t′
       | [↝]-total Δ
  ...  | refl | refl | Δ′ , Δ↝Δ′ 
    = su-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ ↝N)
  A⇒U-≈ (rec-[] {Δ = Δ} ⊢σ ⊢T ⊢s ⊢r ⊢t) Γ↝Γ′ (↝sub (↝rec T↝T′ s↝s′ r↝r′ t↝t′) σ↝σ′) 
                                             (↝rec (↝sub T↝T₁′ (↝, (↝∘ σ↝₁σ′ ↝wk) ↝v ↝N)) (↝sub s↝s₁′ σ↝₂σ′) (↝sub r↝r₁′ (↝, (↝∘ (↝, (↝∘ σ↝σ₃′ ↝wk) ↝v ↝N) ↝wk) ↝v T↝T₂′)) (↝sub t↝₁t′ σ↝σ₄′)) 
                                             (↝sub T↝T₃′ (↝, σ↝σ₅′ (↝sub t↝₂t′ σ↝σ₆′) ↝N))
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝s-det σ↝σ′ σ↝σ₃′
       | ↝s-det σ↝σ′ σ↝σ₄′
       | ↝s-det σ↝σ′ σ↝σ₅′
       | ↝s-det σ↝σ′ σ↝σ₆′
       | ↝-det T↝T′ T↝T₁′
       | ↝-det T↝T′ T↝T₂′
       | ↝-det T↝T′ T↝T₃′
       | ↝-det r↝r′ r↝r₁′
       | ↝-det s↝s′ s↝s₁′
       | ↝-det t↝t′ t↝₁t′
       | ↝-det t↝t′ t↝₂t′
       | [↝]-total Δ
  ...  | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl | Δ′ , Δ↝Δ′ 
    = rec-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) (A⇒U-tm ⊢T (↝∷ Δ↝Δ′ ↝N) T↝T′ ↝Se) (A⇒U-tm ⊢s Δ↝Δ′ s↝s′ (↝sub T↝T′ (↝, ↝I ↝ze ↝N))) (A⇒U-tm ⊢r (↝∷ (↝∷ Δ↝Δ′ ↝N) T↝T′) r↝r′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N))) (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ ↝N)
  A⇒U-≈ (Λ-[] {Δ = Δ} ⊢σ ⊢S ⊢t _) Γ↝Γ′ (↝sub (↝Λ S↝S′ t↝t′) σ↝σ′) (↝Λ (↝sub S↝₁S′ σ↝₁σ′) (↝sub t↝₁t′  (↝, (↝∘ σ↝₂σ′ ↝wk) ↝v S↝₃S′))) (↝sub (↝Π S↝₂S′ T↝T′) σ↝₃σ′ )
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝s-det σ↝σ′ σ↝₃σ′
       | ↝-det S↝S′ S↝₁S′
       | ↝-det S↝S′ S↝₂S′
       | ↝-det S↝S′ S↝₃S′
       | ↝-det t↝t′ t↝₁t′
       | [↝]-total Δ
  ...  | refl | refl | refl | refl | refl | refl | refl
       | Δ′ , Δ↝Δ′ 
    = Λ-[] (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′) (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se) (A⇒U-tm ⊢t (↝∷ Δ↝Δ′ S↝S′) t↝t′ T↝T′)
  A⇒U-≈ ($-[] {Δ = Δ} {S = S} ⊢S ⊢T ⊢σ ⊢r ⊢s i≡maxjk) Γ↝Γ′ (↝sub (↝$ r↝r′ s↝s′) σ↝σ′) (↝$ (↝sub r↝r₁′ σ↝₁σ′) (↝sub s↝s₁′ σ↝₂σ′)) (↝sub T↝T′ (↝, σ↝σ₃′ (↝sub s↝s₂′ σ↝σ₄′) S↝S′))
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝s-det σ↝σ′ σ↝σ₃′
       | ↝s-det σ↝σ′ σ↝σ₄′
       | ↝-det r↝r′ r↝r₁′
       | ↝-det s↝s′ s↝s₁′
       | ↝-det s↝s′ s↝s₂′
       | [↝]-total Δ
  ...  | refl | refl | refl | refl | refl | refl | refl | Δ′ , Δ↝Δ′ 
    = $-[] (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se)
           (A⇒U-tm ⊢T (↝∷ Δ↝Δ′ S↝S′) T↝T′ ↝Se)
           (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
           (A⇒U-tm ⊢r Δ↝Δ′ r↝r′ (↝Π S↝S′ T↝T′))
           (A⇒U-tm ⊢s Δ↝Δ′ s↝s′ S↝S′)
  A⇒U-≈ (liftt-[] {Δ = Δ} n ⊢σ ⊢T ⊢t) Γ↝Γ′ (↝sub (↝liftt t↝t′) σ↝σ′) (↝liftt (↝sub t↝₁t′ σ↝₁σ′)) (↝sub (↝Liftt T↝T′) σ↝₂σ′)
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝-det t↝t′ t↝₁t′
       | [↝]-total Δ
  ...  | refl | refl | refl | Δ′ , Δ↝Δ′ 
    = liftt-[] _ (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
                 (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se)
                 (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ T↝T′)
  A⇒U-≈ (unlift-[] {Δ = Δ} n ⊢T ⊢σ ⊢t) Γ↝Γ′ (↝sub (↝unlift t↝t′) σ↝σ′) (↝unlift (↝sub t↝₁t′ σ↝₁σ′)) (↝sub T↝T′ σ↝₂σ′)
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝-det t↝t′ t↝₁t′
       | [↝]-total Δ
  ...  | refl | refl | refl | Δ′ , Δ↝Δ′ 
    = unlift-[] _ (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se)
                  (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
                  (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ (↝Liftt T↝T′))
  A⇒U-≈ (rec-β-ze ⊢T ⊢s ⊢r) Γ↝Γ′ (↝rec T↝T′ s↝s′ r↝r′ ↝ze) s↝s₁′ (↝sub T↝T₁′ (↝, ↝I ↝ze ↝N))
    with ↝-det s↝s′ s↝s₁′
       | ↝-det T↝T′ T↝T₁′
  ... | refl | refl 
    = rec-β-ze (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ ↝N) T↝T′ ↝Se)
               (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub T↝T′ (↝, ↝I ↝ze ↝N)))
               (A⇒U-tm ⊢r (↝∷ (↝∷ Γ↝Γ′ ↝N) T↝T′) r↝r′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N)))
  A⇒U-≈ (rec-β-su ⊢T ⊢s ⊢r ⊢t) Γ↝Γ′ (↝rec T↝T′ s↝s′ r↝r′ (↝su t↝t′)) 
                                    (↝sub r↝r₁′ (↝, (↝, ↝I t↝₁t′ ↝N) (↝rec T↝T₁′ s↝s₁′ r↝r₂′ t↝₂t′) T↝T₃′)) 
                                    (↝sub T↝T₂′ (↝, ↝I (↝su t↝t₃′) ↝N))
    with ↝-det s↝s′ s↝s₁′
       | ↝-det r↝r′ r↝r₁′
       | ↝-det r↝r′ r↝r₂′
       | ↝-det t↝t′ t↝₁t′
       | ↝-det t↝t′ t↝₂t′
       | ↝-det t↝t′ t↝t₃′
       | ↝-det T↝T′ T↝T₁′
       | ↝-det T↝T′ T↝T₂′
       | ↝-det T↝T′ T↝T₃′
  ...  | refl | refl | refl | refl | refl | refl | refl | refl | refl = rec-β-su (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ ↝N) T↝T′ ↝Se)
                                                                         (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub T↝T′ (↝, ↝I ↝ze ↝N)))
                                                                         (A⇒U-tm ⊢r (↝∷ (↝∷ Γ↝Γ′ ↝N) T↝T′) r↝r′ (↝sub T↝T′ (↝, (↝∘ ↝wk ↝wk) (↝su ↝v) ↝N)))
                                                                         (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ ↝N)
  A⇒U-≈ (Λ-β {S = S} ⊢S ⊢T ⊢t ⊢s) Γ↝Γ′ (↝$ (↝Λ S↝S′ t↝t′) s↝s′) (↝sub t↝₁t′  (↝, ↝I s↝₁s′ S↝S₁′)) (↝sub T↝T′ (↝, ↝I s↝₂s′  S↝S₂′))
    with ↝-det t↝t′ t↝₁t′
       | ↝-det s↝s′ s↝₁s′
       | ↝-det s↝s′ s↝₂s′
       | ↝-det S↝S′ S↝S₁′
       | ↝-det S↝S′ S↝S₂′
  ...  | refl | refl | refl | refl | refl = Λ-β (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)
                         (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se)
                         (A⇒U-tm ⊢t (↝∷ Γ↝Γ′ S↝S′) t↝t′ T↝T′)
                         (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ S↝S′)
  A⇒U-≈ (Λ-η ⊢S ⊢T ⊢t _) Γ↝Γ′ t↝t′ (↝Λ S↝S′ (↝$ (↝sub t↝₁t′  ↝wk) ↝v)) (↝Π S↝₁S′ T↝T′)
    with ↝-det t↝t′ t↝₁t′
       | ↝-det S↝S′ S↝₁S′
  ...  | refl | refl = Λ-η (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se)
                    (A⇒U-tm ⊢T (↝∷ Γ↝Γ′ S↝S′) T↝T′ ↝Se)
                    (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝Π S↝S′ T↝T′))
  A⇒U-≈ {Γ′ = Γ′} (L-β n ⊢s) Γ↝Γ′ (↝unlift (↝liftt t↝t′)) s↝s′ T↝T′ with ↝-det s↝s′ t↝t′
  ... | refl  = L-β _ (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ T↝T′)
  A⇒U-≈ (L-η n ⊢T ⊢t) Γ↝Γ′ t↝t′ (↝liftt (↝unlift t↝₁t′ )) (↝Liftt T↝T′) with ↝-det t↝t′ t↝₁t′
  ... | refl = L-η _ (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se)
                     (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝Liftt T↝T′))
  A⇒U-≈ ([I] ⊢s) Γ↝Γ′ (↝sub s↝s′ ↝I) s↝₁s′  T↝T′ with ↝-det s↝s′ s↝₁s′
  ... | refl = [I] (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ T↝T′)
  A⇒U-≈ ([wk] ⊢Γ ⊢S x∈Γ) (↝∷ Γ↝Γ′ S↝S′) (↝sub ↝v ↝wk) ↝v (↝sub T↝T′ ↝wk) = [wk] (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢S Γ↝Γ′ S↝S′ ↝Se) (A⇒U-vlookup x∈Γ Γ↝Γ′ T↝T′)
  A⇒U-≈ ([∘] {Γ′ = Σ} {Γ″ = Δ} ⊢τ ⊢σ ⊢t) Γ↝Γ′ (↝sub t↝t′ (↝∘ σ↝σ′ τ↝τ′)) (↝sub (↝sub t↝₁t′  σ↝₁σ′ ) τ↝′τ′) (↝sub T↝T′ (↝∘ σ↝₂σ′  τ↝″τ′))
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝s-det τ↝τ′ τ↝′τ′
       | ↝s-det τ↝τ′ τ↝″τ′
       | ↝-det t↝t′ t↝₁t′
       | [↝]-total Σ
       | [↝]-total Δ
  ... | refl | refl | refl | refl | refl 
      | Σ′ , Σ↝Σ′
      | Δ′ , Δ↝Δ′  = [∘] (A⇒U-s ⊢τ Γ↝Γ′ τ↝τ′ Σ↝Σ′)
                         (A⇒U-s ⊢σ Σ↝Σ′ σ↝σ′ Δ↝Δ′)
                         (A⇒U-tm ⊢t Δ↝Δ′ t↝t′ T↝T′)
  A⇒U-≈ ([,]-v-ze {Δ = Δ} ⊢σ ⊢S ⊢s) Γ↝Γ′ (↝sub ↝v (↝, σ↝σ′ s↝s′ S↝S′)) s↝₁s′  (↝sub S↝S₁′ σ↝₁σ′ )
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝-det s↝s′ s↝₁s′
       | ↝-det S↝S′ S↝S₁′
       | [↝]-total Δ
  ...  | refl | refl | refl
       | Δ′ , Δ↝Δ′ = [,]-v-ze (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
                              (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se)
                              (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub S↝S′ σ↝σ′))
  A⇒U-≈ ([,]-v-su {Δ = Δ} {S = S} ⊢σ ⊢S ⊢s x∈Γ) Γ↝Γ′ (↝sub ↝v (↝, σ↝σ′ s↝s′ S↝S′)) (↝sub ↝v σ↝₁σ′ ) (↝sub T↝T′ σ↝₂σ′ )
   with ↝s-det σ↝σ′ σ↝₁σ′
      | ↝s-det σ↝σ′ σ↝₂σ′
  ... | refl | refl
   with [↝]-total Δ
  ... | Δ′ , Δ↝Δ′ = [,]-v-su (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ Δ↝Δ′)
                             (A⇒U-tm ⊢S Δ↝Δ′ S↝S′ ↝Se)
                             (A⇒U-tm ⊢s Γ↝Γ′ s↝s′ (↝sub S↝S′ σ↝σ′))
                             (A⇒U-vlookup x∈Γ Δ↝Δ′ T↝T′)
  A⇒U-≈ (≈-conv {S = S} t≈s S≈T) Γ↝Γ′ t↝t′ s↝s′ T↝T′ with ↝-total S
  ... | S′ , S↝S′ = ≈-conv (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ S↝S′)  (A⇒U-≈ S≈T Γ↝Γ′ S↝S′ T↝T′ ↝Se)
  A⇒U-≈ (≈-sym t≈s) Γ↝Γ′ t↝t′ s↝s′ T↝T′ = ≈-sym (A⇒U-≈ t≈s Γ↝Γ′ s↝s′ t↝t′ T↝T′)
  A⇒U-≈ (≈-trans {t′ = r} r≈s t≈r) Γ↝Γ′ t↝t′ s↝s′ T↝T′ with ↝-total r
  ... | r′ , r↝r′ = ≈-trans (A⇒U-≈ r≈s Γ↝Γ′ t↝t′ r↝r′ T↝T′) (A⇒U-≈ t≈r Γ↝Γ′ r↝r′ s↝s′ T↝T′)

  A⇒U-s≈ : A.Γ A.⊢s A.σ ≈ A.τ ∶ A.Δ →
           A.Γ [↝] U.Γ′ →
           A.Δ [↝] U.Δ′ →
           A.σ ↝s U.σ′ →
           A.τ ↝s U.τ′ →
          -------------
           U.Γ′ U.⊢s U.σ′ ≈ U.τ′ ∶ U.Δ′
  A⇒U-s≈ (I-≈ ⊢Γ) Γ↝Γ′ Δ↝Δ′ ↝I ↝I
    with [↝]-det  Γ↝Γ′ Δ↝Δ′
  ... | refl = I-≈ (A⇒U-⊢ ⊢Γ Γ↝Γ′)
  A⇒U-s≈ (wk-≈ (⊢∷ ⊢Γ ⊢T)) (↝∷ Γ↝Γ′ T↝T′) Δ↝Δ′ ↝wk ↝wk
    with [↝]-det Γ↝Γ′ Δ↝Δ′
  ... | refl = wk-≈ (⊢∷ (A⇒U-⊢ ⊢Γ Γ↝Γ′) (A⇒U-tm ⊢T Γ↝Γ′ T↝T′ ↝Se))
  A⇒U-s≈ (∘-cong {τ′ = γ} {Γ′ = Σ} {σ′ = φ} σ≈φ τ≈γ) Γ↝Γ′ Δ↝Δ′ (↝∘ σ↝σ′ τ↝τ′) (↝∘ φ↝φ′ γ↝γ′)
    with [↝]-total Σ
  ... | Σ′ , Σ↝Σ′ = ∘-cong (A⇒U-s≈ σ≈φ Γ↝Γ′ Σ↝Σ′ τ↝τ′ γ↝γ′)
                           (A⇒U-s≈ τ≈γ Σ↝Σ′ Δ↝Δ′ σ↝σ′ φ↝φ′)
  A⇒U-s≈ (,-cong {σ′ = τ} {T′ = S} {t′ = s} σ≈τ ⊢T T≈S t≈s) Γ↝Γ′ (↝∷ Δ↝Δ′ T↝T′) (↝, σ↝σ′ t↝t′ T↝T₁′) (↝, τ↝τ′ s↝s′ S↝S₁′)
    with refl ← ↝-det T↝T′ T↝T₁′
   = ,-cong (A⇒U-s≈ σ≈τ Γ↝Γ′ Δ↝Δ′ σ↝σ′ τ↝τ′) (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se) (A⇒U-≈ T≈S Δ↝Δ′ T↝T′ S↝S₁′ ↝Se) (A⇒U-≈ t≈s Γ↝Γ′ t↝t′ s↝s′ (↝sub T↝T′ σ↝σ′))
  A⇒U-s≈ (I-∘ ⊢τ) Γ↝Γ′ Δ↝Δ′ (↝∘ ↝I τ↝τ′) τ↝τ₁′ with ↝s-det τ↝τ′ τ↝τ₁′
  ... | refl = I-∘ (A⇒U-s ⊢τ Γ↝Γ′ τ↝τ′ Δ↝Δ′)
  A⇒U-s≈ (∘-I ⊢τ) Γ↝Γ′ Δ↝Δ′ (↝∘ τ↝τ′ ↝I) τ↝τ₁′ with ↝s-det τ↝τ′ τ↝τ₁′
  ... | refl = ∘-I (A⇒U-s ⊢τ Γ↝Γ′ τ↝τ′ Δ↝Δ′)
  A⇒U-s≈ (∘-assoc {Γ′ = Σ} {Γ″ = Ψ} {σ′ = τ} {σ″ = φ} ⊢σ ⊢τ ⊢φ) Γ↝Γ′ Δ↝Δ′ (↝∘ (↝∘ σ↝σ′ τ↝τ′) φ↝φ′) (↝∘ σ↝₁σ′ (↝∘ τ↝₁τ′ φ↝₁φ′))
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det τ↝τ′ τ↝₁τ′
       | ↝s-det φ↝φ′ φ↝₁φ′
       | [↝]-total Σ
       | [↝]-total Ψ
  ...  | refl | refl | refl | Σ′ , Σ↝Σ′ | Ψ′ , Ψ↝Ψ′ = ∘-assoc (A⇒U-s ⊢σ Σ↝Σ′ σ↝σ′ Δ↝Δ′)
                                                              (A⇒U-s ⊢τ Ψ↝Ψ′ τ↝τ′ Σ↝Σ′)
                                                              (A⇒U-s ⊢φ Γ↝Γ′ φ↝φ′ Ψ↝Ψ′)
  A⇒U-s≈ (,-∘ {Γ′ = Σ} {Γ″ = Δ} ⊢σ ⊢T ⊢t ⊢τ) Γ↝Γ′ (↝∷ Δ↝Δ′ T↝T′) (↝∘ (↝, σ↝σ′ t↝t′ T↝T₁′) τ↝τ′) (↝, (↝∘ σ↝₁σ′ τ↝₁τ′) (↝sub t↝₁t′ τ↝₂τ′) T↝T₂′)
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det τ↝τ′ τ↝₁τ′
       | ↝s-det τ↝τ′ τ↝₂τ′
       | ↝-det t↝t′ t↝₁t′
       | ↝-det T↝T′ T↝T₁′
       | ↝-det T↝T′ T↝T₂′
       | [↝]-total Σ
  ...  | refl | refl | refl | refl | refl | refl
       | Σ′ , Σ↝Σ′ = ,-∘ (A⇒U-s ⊢σ Σ↝Σ′ σ↝σ′ Δ↝Δ′)
                                                     (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se)
                                                     (A⇒U-tm ⊢t Σ↝Σ′ t↝t′ (↝sub T↝T′ σ↝σ′))
                                                     (A⇒U-s ⊢τ Γ↝Γ′ τ↝τ′ Σ↝Σ′)
  A⇒U-s≈ (p-, {T = T} ⊢τ ⊢T ⊢t) Γ↝Γ′ Δ↝Δ′ (↝∘ ↝wk (↝, τ↝τ′ t↝t′ T↝T′)) τ↝₁τ′
    with ↝s-det τ↝τ′ τ↝₁τ′
  ...  | refl  = p-, (A⇒U-s ⊢τ Γ↝Γ′ τ↝τ′ Δ↝Δ′)
                                (A⇒U-tm ⊢T Δ↝Δ′ T↝T′ ↝Se)
                                (A⇒U-tm ⊢t Γ↝Γ′ t↝t′ (↝sub T↝T′ τ↝τ′))
  A⇒U-s≈ (,-ext ⊢σ) Γ↝Γ′ (↝∷ Δ↝Δ′ T↝T′) σ↝σ′ (↝, (↝∘ ↝wk σ↝₁σ′) (↝sub ↝v σ↝₂σ′) T↝T₁′)
    with ↝s-det σ↝σ′ σ↝₁σ′
       | ↝s-det σ↝σ′ σ↝₂σ′
       | ↝-det T↝T′ T↝T₁′
  ... | refl | refl | refl = ,-ext (A⇒U-s ⊢σ Γ↝Γ′ σ↝σ′ (↝∷ Δ↝Δ′ T↝T′))
  A⇒U-s≈ (s-≈-sym σ≈τ) Γ↝Γ′ Δ↝Δ′ σ↝σ′ τ↝τ′ = s-≈-sym (A⇒U-s≈ σ≈τ Γ↝Γ′ Δ↝Δ′ τ↝τ′ σ↝σ′)
  A⇒U-s≈ (s-≈-trans {σ′ = φ} σ≈φ φ≈τ) Γ↝Γ′ Δ↝Δ′ σ↝σ′ τ↝τ′
    with ↝s-total φ
  ... | φ′ , φ↝φ′ = s-≈-trans (A⇒U-s≈ σ≈φ Γ↝Γ′ Δ↝Δ′ σ↝σ′ φ↝φ′) (A⇒U-s≈ φ≈τ Γ↝Γ′ Δ↝Δ′ φ↝φ′ τ↝τ′)
  A⇒U-s≈ (s-≈-conv {Δ = Σ} σ≈τ Σ≈Δ) Γ↝Γ′ Δ↝Δ′ σ↝σ′ τ↝τ′
    with [↝]-total Σ
  ... | Σ′ , Σ↝Σ′ = s-≈-conv (A⇒U-s≈ σ≈τ Γ↝Γ′ Σ↝Σ′ σ↝σ′ τ↝τ′)
                             (A⇒U-⊢≈ Σ≈Δ Σ↝Σ′ Δ↝Δ′) 