{-# OPTIONS --without-K --safe #-}

module Idem.StaticProps where

open import Lib
open import Idem.Statics

open import Data.List.Properties as Lₚ

mutual
  ≈-refl : Δ ﹔ Γ ⊢ t ∶ T → Δ ﹔ Γ ⊢ t ≈ t ∶ T
  ≈-refl (vlookup T∈Γ) = v-≈ T∈Γ
  ≈-refl (⟶-I ⊢t)      = Λ-cong (≈-refl ⊢t)
  ≈-refl (⟶-E ⊢t ⊢s)   = $-cong (≈-refl ⊢t) (≈-refl ⊢s)
  ≈-refl (□-I ⊢t)      = box-cong (≈-refl ⊢t)
  ≈-refl (□-E ⊢t)      = unbox-cong (≈-refl ⊢t)
  ≈-refl (t[σ] ⊢t ⊢σ)  = []-cong (≈-refl ⊢t) (s≈-refl ⊢σ)

  s≈-refl : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢s σ ≈ σ ∶ Δ′ ﹔ Γ′
  s≈-refl (S-I Δ″)         = I-≈ Δ″
  s≈-refl (S-p ⊢σ)         = p-cong (s≈-refl ⊢σ)
  s≈-refl (S-, ⊢σ ⊢t)      = ,-cong (s≈-refl ⊢σ) (≈-refl ⊢t)
  s≈-refl (S-hat Γ₁ ⊢σ eq) = hat-cong Γ₁ (s≈-refl ⊢σ) eq
  s≈-refl (S-∘ ⊢σ ⊢δ)      = ∘-cong (s≈-refl ⊢σ) (s≈-refl ⊢δ)

⊢q∘I, : Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢ t ∶ T → Δ ﹔ Γ ⊢s q σ ∘ (I , t) ≈ σ , t ∶ Δ′ ﹔ T ∷ Γ′
⊢q∘I, ⊢σ ⊢t = s-≈-trans (,-∘ (S-∘ (S-p S-I′) ⊢σ) (vlookup here) (S-, S-I′ ⊢t))
                        (,-cong (s-≈-trans (∘-assoc (S-, S-I′ ⊢t) (S-p S-I′) ⊢σ)
                                (s-≈-trans (∘-cong (s-≈-trans (p-∘ S-I′ (S-, S-I′ ⊢t))
                                                   (s-≈-trans (p-cong (I-∘ (S-, S-I′ ⊢t)))
                                                              (p-, S-I′ ⊢t)))
                                                   (s≈-refl ⊢σ))
                                           (∘-I ⊢σ)))
                                (v-ze S-I′ ⊢t))

til-idem : ∀ σ → til (til σ) ≡ til σ
til-idem I       = refl
til-idem (p σ)   = cong p (til-idem σ)
til-idem (σ , t) = cong (_, t) (til-idem σ)
til-idem (hat σ) = til-idem σ
til-idem (σ ∘ δ) = cong₂ _∘_ (til-idem σ) (til-idem δ)


mutual
  presup : Δ ﹔ Γ ⊢ t ≈ t′ ∶ T → Δ ﹔ Γ ⊢ t ∶ T × Δ ﹔ Γ ⊢ t′ ∶ T
  presup (v-≈ T∈Γ)              = vlookup T∈Γ , vlookup T∈Γ
  presup (Λ-cong t≈t′)
    with presup t≈t′
  ...  | ⊢t , ⊢t′               = ⟶-I ⊢t , ⟶-I ⊢t′
  presup ($-cong t≈t′ s≈s′)
    with presup t≈t′ | presup s≈s′
  ...  | ⊢t , ⊢t′    | ⊢s , ⊢s′ = ⟶-E ⊢t ⊢s , ⟶-E ⊢t′ ⊢s′
  presup (box-cong t≈t′)
    with presup t≈t′
  ...  | ⊢t , ⊢t′               = □-I ⊢t , □-I ⊢t′
  presup (unbox-cong t≈t′)
    with presup t≈t′
  ...  | ⊢t , ⊢t′               = □-E ⊢t , □-E ⊢t′
  presup ([]-cong t≈t′ σ≈σ′)
    with presup t≈t′ | presup-s σ≈σ′
  ...  | ⊢t , ⊢t′    | ⊢σ , ⊢σ′ = t[σ] ⊢t ⊢σ , t[σ] ⊢t′ ⊢σ′
  presup (Λ-[] ⊢σ ⊢t)           = t[σ] (⟶-I ⊢t) ⊢σ , ⟶-I (t[σ] ⊢t (⊢q ⊢σ _))
  presup ($-[] ⊢σ ⊢t ⊢s)        = t[σ] (⟶-E ⊢t ⊢s) ⊢σ , (⟶-E (t[σ] ⊢t ⊢σ) (t[σ] ⊢s ⊢σ))
  presup (box-[] ⊢σ ⊢t)         = t[σ] (□-I ⊢t) ⊢σ , □-I (t[σ] ⊢t (S-hat [] ⊢σ refl))
  presup (unbox-[] ⊢σ ⊢t)       = t[σ] (□-E ⊢t) ⊢σ , □-E (t[σ] ⊢t (⊢s-til ⊢σ))
  presup (⟶-β ⊢t ⊢s)            = ⟶-E (⟶-I ⊢t) ⊢s , t[σ] ⊢t (S-, S-I′ ⊢s)
  presup (□-β {Γ} ⊢t)           = □-E (□-I (subst (_﹔ _ ⊢ _ ∶ _) (sym (++-identityʳ _)) ⊢t)) , ⊢-mweaken Γ ⊢t
  presup (⟶-η ⊢t)               = ⊢t , ⟶-I (⟶-E (t[σ] ⊢t (S-p S-I′)) (vlookup here))
  presup (□-η ⊢t)               = ⊢t , □-I (□-E (⊢-mweaken′ ⊢t))
  presup ([I] ⊢t)               = t[σ] ⊢t S-I′ , ⊢t
  presup ([∘] ⊢σ ⊢σ′ ⊢t)        = t[σ] ⊢t (S-∘ ⊢σ ⊢σ′) , t[σ] (t[σ] ⊢t ⊢σ′) ⊢σ
  presup (v-ze ⊢σ ⊢t)           = t[σ] (vlookup here) (S-, ⊢σ ⊢t) , ⊢t
  presup (v-su ⊢σ ⊢t T∈Γ)       = t[σ] (vlookup (there T∈Γ)) (S-, ⊢σ ⊢t) , t[σ] (vlookup T∈Γ) ⊢σ
  presup ([p] ⊢σ T∈Γ)           = t[σ] (vlookup T∈Γ) (S-p ⊢σ) , t[σ] (vlookup (there T∈Γ)) ⊢σ
  presup (≈-sym t′≈t)
    with presup t′≈t
  ...  | ⊢t′ , ⊢t               = ⊢t , ⊢t′
  presup (≈-trans t≈t″ t″≈t′)
    with presup t≈t″ | presup t″≈t′
  ...  | ⊢t , _      | _ , ⊢t′  = ⊢t , ⊢t′

  presup-s : Δ ﹔ Γ ⊢s σ ≈ σ′ ∶ Δ′ ﹔ Γ′ → Δ ﹔ Γ ⊢s σ ∶ Δ′ ﹔ Γ′ × Δ ﹔ Γ ⊢s σ′ ∶ Δ′ ﹔ Γ′
  presup-s (I-≈ Δ″)                 = S-I Δ″ , S-I Δ″
  presup-s (p-cong σ≈σ′)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = S-p ⊢σ , S-p ⊢σ′
  presup-s (,-cong σ≈σ′ t≈t′)
    with presup-s σ≈σ′ | presup t≈t′
  ...  | ⊢σ , ⊢σ′      | ⊢t , ⊢t′   = S-, ⊢σ ⊢t , S-, ⊢σ′ ⊢t′
  presup-s (hat-cong _ σ≈σ′ eq)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = S-hat _ ⊢σ eq , S-hat _ ⊢σ′ eq
  presup-s (∘-cong σ≈σ′ δ≈δ′)
    with presup-s σ≈σ′ | presup-s δ≈δ′
  ...  | ⊢σ , ⊢σ′      | ⊢δ , ⊢δ′   = S-∘ ⊢σ ⊢δ , S-∘ ⊢σ′ ⊢δ′
  presup-s (∘-I ⊢σ)                 = S-∘ S-I′ ⊢σ , ⊢σ
  presup-s (I-∘ ⊢σ)                 = S-∘ ⊢σ S-I′ , ⊢σ
  presup-s (∘-assoc ⊢σ ⊢σ′ ⊢σ″)     = S-∘ ⊢σ (S-∘ ⊢σ′ ⊢σ″) , S-∘ (S-∘ ⊢σ ⊢σ′) ⊢σ″
  presup-s (,-∘ ⊢σ ⊢t ⊢δ)           = S-∘ ⊢δ (S-, ⊢σ ⊢t) , S-, (S-∘ ⊢δ ⊢σ) (t[σ] ⊢t ⊢δ)
  presup-s (p-∘ ⊢σ ⊢δ)              = S-∘ ⊢δ (S-p ⊢σ) , S-p (S-∘ ⊢δ ⊢σ)
  presup-s (p-, ⊢σ ⊢t)              = S-p (S-, ⊢σ ⊢t) , ⊢σ
  presup-s (,-ext ⊢σ)               = ⊢σ , S-, (S-p ⊢σ) (t[σ] (vlookup here) ⊢σ)
  presup-s (hat-ext {_} {_} {_} {Δ′} {Γ′} Γ₁ ⊢σ eq)
    with S-hat Γ₁ (⊢s-til ⊢σ) (trans (++-identityʳ _) eq)
  ...  | ⊢htσ
    rewrite ++-identityʳ (Γ′ ++ Δ′) = ⊢htσ , S-hat Γ₁ ⊢σ eq
  presup-s (s-≈-sym σ≈σ′)
    with presup-s σ≈σ′
  ...  | ⊢σ , ⊢σ′                   = ⊢σ′ , ⊢σ
  presup-s (s-≈-trans σ≈σ′ σ′≈σ″)
    with presup-s σ≈σ′ | presup-s σ′≈σ″
  ...  | ⊢σ , _ | _ , ⊢σ″           = ⊢σ , ⊢σ″

mutual
  [til] : Δ′ ﹔ Γ′ ⊢s σ ∶ Δ ﹔ Γ → Δ ﹔ Γ ⊢ t ∶ T → [] ﹔ Γ′ ++ Δ′ ⊢ t [ til σ ] ≈ t [ σ ] ∶ T
  [til] (S-I Δ′) (vlookup T∈Γ)            = ≈-refl (t[σ] (vlookup (∈-++ʳ (∈-++ʳ T∈Γ))) S-I′)
  [til] (S-p ⊢σ) (vlookup T∈Γ)            = ≈-trans ([p] (⊢s-til ⊢σ) (∈-++ʳ T∈Γ))
                                            (≈-trans ([til] ⊢σ (vlookup (there T∈Γ)))
                                                     (≈-sym ([p] (⊢s-mweaken′ ⊢σ) T∈Γ)))
  [til] (S-, ⊢σ ⊢t) (vlookup here)        = ≈-trans (v-ze (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t))
                                                    (≈-sym (v-ze (⊢s-mweaken′ ⊢σ) (⊢-mweaken′ ⊢t)))
  [til] (S-, ⊢σ ⊢t) (vlookup (there T∈Γ)) = ≈-trans (v-su (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t) (∈-++ʳ T∈Γ))
                                            (≈-trans ([til] ⊢σ (vlookup T∈Γ))
                                                     (≈-sym (v-su (⊢s-mweaken′ ⊢σ) (⊢-mweaken′ ⊢t) T∈Γ)))
  [til] (S-∘ ⊢σ ⊢δ) (vlookup T∈Γ)         = ≈-trans ([∘] (⊢s-til ⊢σ) (⊢s-til ⊢δ) (vlookup (∈-++ʳ T∈Γ)))
                                            (≈-trans ([]-cong ([til] ⊢δ (vlookup T∈Γ)) (s≈-refl (⊢s-til ⊢σ)))
                                            (≈-trans ([til] ⊢σ (t[σ] (vlookup T∈Γ) ⊢δ))
                                                     (≈-sym ([∘] (⊢s-mweaken′ ⊢σ) ⊢δ (vlookup T∈Γ)))))
  [til] ⊢σ (⟶-I ⊢t)                       = ≈-trans (Λ-[] (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t))
                                            (≈-trans (Λ-cong ([til] (⊢q ⊢σ _) ⊢t))
                                            {!!})
  [til] ⊢σ (⟶-E ⊢t ⊢s)                    = ≈-trans ($-[] (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t) (⊢-mweaken′ ⊢s))
                                            (≈-trans ($-cong ([til] ⊢σ ⊢t) ([til] ⊢σ ⊢s))
                                                     (≈-sym ($-[] (⊢s-mweaken′ ⊢σ) ⊢t ⊢s)))
  [til] ⊢σ (□-I ⊢t)                       = ≈-trans (box-[] (⊢s-til ⊢σ) (subst (_﹔ _ ⊢ _ ∶ _) (sym (++-identityʳ _)) ⊢t))
                                            (≈-trans (box-cong ([]-cong (≈-refl ⊢t) (hat-ext [] ⊢σ (sym (++-identityʳ _)))))
                                                     (≈-sym (box-[] (⊢s-mweaken′ ⊢σ) ⊢t)))
  [til] ⊢σ (□-E ⊢t)                       = {!!}
  [til] ⊢σ (t[σ] ⊢t ⊢δ)                   = ≈-trans (≈-sym ([∘] (⊢s-til ⊢σ) (⊢s-mweaken′ ⊢δ) ⊢t))
                                            (≈-trans ([]-cong (≈-refl ⊢t) (til∘ ⊢σ ⊢δ))
                                                     ([∘] (⊢s-mweaken′ ⊢σ) ⊢δ ⊢t))

  til∘ : Δ′ ﹔ Γ′ ⊢s σ ∶ Δ ﹔ Γ → Δ ﹔ Γ ⊢s δ ∶ Δ″ ﹔ Γ″ → [] ﹔ Γ′ ++ Δ′ ⊢s δ ∘ til σ ≈ δ ∘ σ ∶ Δ″ ﹔ Γ″
  til∘ ⊢σ (S-I Δ′)        = {!⊢s-til ⊢σ!}
  til∘ ⊢σ (S-p ⊢δ)        = {!!}
  til∘ ⊢σ (S-, ⊢δ ⊢t)     = s-≈-trans (,-∘ ⊢δ ⊢t {!⊢s-til ⊢σ!})
                            {!!}
  til∘ ⊢σ (S-hat _ ⊢δ eq) = {!!}
  til∘ ⊢σ (S-∘ ⊢δ ⊢δ′)    = {!!}

-- til-resp-≈ : Δ ﹔ Γ ⊢s σ ≈ σ′ ∶ Δ′ ﹔ Γ′ → [] ﹔ Γ ++ Δ ⊢s til σ ≈ til σ′ ∶ [] ﹔ Γ′ ++ Δ′
-- til-resp-≈ {Δ} {_} {_} {_} {_} {Γ′} (I-≈ Δ′)
--   rewrite ++-assoc Γ′ Δ′ Δ        = I-≈′
-- til-resp-≈ (p-cong σ≈σ′)          = p-cong (til-resp-≈ σ≈σ′)
-- til-resp-≈ (,-cong σ≈σ′ t≈t′)     = ,-cong (til-resp-≈ σ≈σ′) (≈-mweaken′ t≈t′)
-- til-resp-≈ (hat-cong _ σ≈σ′ eq)
--   rewrite sym eq                  = til-resp-≈ σ≈σ′
-- til-resp-≈ (∘-cong σ≈σ′ σ′≈σ″)    = ∘-cong (til-resp-≈ σ≈σ′) (til-resp-≈ σ′≈σ″)
-- til-resp-≈ (∘-I ⊢σ)               = ∘-I (⊢s-til ⊢σ)
-- til-resp-≈ (I-∘ ⊢σ)               = I-∘ (⊢s-til ⊢σ)
-- til-resp-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)   = ∘-assoc (⊢s-til ⊢σ) (⊢s-til ⊢σ′) (⊢s-til ⊢σ″)
-- til-resp-≈ (,-∘ ⊢σ ⊢t ⊢δ)         = s-≈-trans (,-∘ (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t) (⊢s-til ⊢δ))
--                                               (,-cong (s≈-refl (S-∘ (⊢s-til ⊢δ) (⊢s-til ⊢σ))) {!!})
-- til-resp-≈ (p-∘ ⊢σ ⊢δ)            = p-∘ (⊢s-til ⊢σ) (⊢s-til ⊢δ)
-- til-resp-≈ (p-, ⊢σ ⊢t)            = p-, (⊢s-til ⊢σ) (⊢-mweaken′ ⊢t)
-- til-resp-≈ (,-ext ⊢σ)             = s-≈-trans (,-ext (⊢s-til ⊢σ))
--                                               (,-cong (s≈-refl (S-p (⊢s-til ⊢σ))) {!!})
-- til-resp-≈ (hat-ext {_} {_} {σ} _ ⊢σ eq)
--   rewrite til-idem σ | sym eq     = s≈-refl (⊢s-til ⊢σ)
-- til-resp-≈ (s-≈-sym σ≈σ′)         = s-≈-sym (til-resp-≈ σ≈σ′)
-- til-resp-≈ (s-≈-trans σ≈σ′ σ′≈σ″) = s-≈-trans (til-resp-≈ σ≈σ′) (til-resp-≈ σ′≈σ″)
