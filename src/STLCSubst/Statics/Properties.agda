{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Properties where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality hiding ([_])

import Relation.Binary.Reasoning.Setoid as SR

open import Lib
open import STLCSubst.Statics.Definitions public

record AlgLemmas {i} (A : Set i)
   : Set (lsuc i) where

  infix 4 _≈_

  field
    {{has-id}}     : HasIdentity A
    {{composable}} : Composable A

    _≈_      : Rel A 0ℓ
    ≈-equiv  : IsEquivalence _≈_
    left-id  : ∀ a → id ∙ a ≈ a
    right-id : ∀ a → a ∙ id ≈ a
    assoc    : ∀ a b c → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)


  open IsEquivalence ≈-equiv public

open AlgLemmas {{...}} hiding (refl; trans) public

subst-qid≈id : q v ≗ id
subst-qid≈id zero    = refl
subst-qid≈id (suc _) = refl

subst-q-cong : σ ≗ τ → q σ ≗ q τ
subst-q-cong eq zero = refl
subst-q-cong eq (suc x) = cong (λ z → z [ wk 0 ]) (eq x)

subst-qqid≈id : q (q v) ≗ id
subst-qqid≈id = ≗.trans (subst-q-cong subst-qid≈id) subst-qid≈id
  where module ≗ = IsEquivalence (Setoid.isEquivalence (ℕ →-setoid Exp))

q-alt : Subst → Subst
q-alt σ = σ [ wk 0 ] ↦ v 0

conv-equiv-gen : (n : ℕ) (t : Exp) (ϕ : Wk) → t [ repeat q n (conv ϕ) ] ≡ t [ repeat q n ϕ ]
conv-equiv-gen n (v x) ϕ       = lem n x
  where lem : ∀ n x → repeat subst-q n (conv ϕ) x ≡ v (repeat wk-q n ϕ x)
        lem zero x        = refl
        lem (suc n) zero  = refl
        lem (suc n) (suc x)
          rewrite lem n x = refl
conv-equiv-gen n ze ϕ          = refl
conv-equiv-gen n (su t) ϕ      = cong su (conv-equiv-gen n t ϕ)
conv-equiv-gen n (rec T u s t) ϕ
  rewrite conv-equiv-gen n u ϕ
        | conv-equiv-gen (2 + n) s ϕ
        | conv-equiv-gen n t ϕ = refl
conv-equiv-gen n (Λ t) ϕ       = cong Λ (conv-equiv-gen (1 + n) t ϕ)
conv-equiv-gen n (t $ s) ϕ     = cong₂ _$_ (conv-equiv-gen n t ϕ) (conv-equiv-gen n s ϕ)

conv-equiv : (t : Exp) (ϕ : Wk) → t [ conv ϕ ] ≡ t [ ϕ ]
conv-equiv = conv-equiv-gen 0

subst-q-equiv : (σ : Subst) → q σ ≗ q-alt σ
subst-q-equiv σ zero    = refl
subst-q-equiv σ (suc x) = refl

wk-drop-ext : (σ : Subst) (t : Exp) → conv (wk 0) ∙ (σ ↦ t) ≗ σ
wk-drop-ext _ _ _ = refl

wk-q-wk0 : (n : ℕ) (t : Exp) → t [ repeat q n (wk 0) ] [ wk 0 ] ≡ t [ wk 0 ] [ repeat q n (wk 0) ]
wk-q-wk0 zero t = refl
wk-q-wk0 (suc n) t = {!wk-q-wk0 n t!}

wk-comp-q-equiv-gen : (n : ℕ) (t : Exp) (σ : Subst) → t [ repeat q n (wk 0) ] [ repeat q n (q σ) ] ≡ t [ repeat q n σ ] [ repeat q n (wk 0) ]
wk-comp-q-equiv-gen n (v x) σ       = lem n x
  where lem : ∀ n x → repeat q n (q σ) (repeat q n (wk 0) x) ≡ (repeat q n σ x) [ repeat q n (wk 0) ]
        lem zero x        = refl
        lem (suc n) zero  = refl
        lem (suc n) (suc x)
          rewrite lem n x = {!!}
wk-comp-q-equiv-gen n ze σ          = refl
wk-comp-q-equiv-gen n (su t) σ      = cong su (wk-comp-q-equiv-gen n t σ)
wk-comp-q-equiv-gen n (rec T u s t) σ
  rewrite wk-comp-q-equiv-gen n u σ
        | wk-comp-q-equiv-gen (2 + n) s σ
        | wk-comp-q-equiv-gen n t σ = refl
wk-comp-q-equiv-gen n (Λ t) σ       = cong Λ (wk-comp-q-equiv-gen (1 + n) t σ)
wk-comp-q-equiv-gen n (t $ s) σ     = cong₂ _$_ (wk-comp-q-equiv-gen n t σ) (wk-comp-q-equiv-gen n s σ)


subst-q-∙-dist : (σ σ′ : Subst) → q σ ∙ q σ′ ≗ q (σ ∙ σ′)
subst-q-∙-dist σ σ′ zero = refl
subst-q-∙-dist σ σ′ (suc x) = begin
  σ x [ wk 0 ] [ q σ′ ] ≡⟨ wk-comp-q-equiv-gen 0 (σ x) σ′ ⟩
  σ x [ σ′ ] [ wk 0 ] ∎
  where open ≡-Reasoning

subst-qq-∙-dist : (σ σ′ : Subst) → q (q σ) ∙ q (q σ′) ≗ q (q (σ ∙ σ′))
subst-qq-∙-dist σ σ′ = begin
  q (q σ) ∙ q (q σ′) ≈⟨ subst-q-∙-dist (q σ) (q σ′) ⟩
  q (q σ ∙ q σ′)     ≈⟨ subst-q-cong (subst-q-∙-dist σ σ′) ⟩
  q (q (σ ∙ σ′))     ∎
  where open SR (ℕ →-setoid Exp)


subst-transp : (t : Exp) → σ ≗ τ → t [ σ ] ≡ t [ τ ]
subst-transp (v x) eq       = eq x
subst-transp ze eq          = refl
subst-transp (su t) eq      = cong su (subst-transp t eq)
subst-transp (rec T u s t) eq
  rewrite subst-transp u eq
        | subst-transp s (subst-q-cong (subst-q-cong eq))
        | subst-transp t eq = refl
subst-transp (Λ t) eq       = cong Λ (subst-transp t (subst-q-cong eq))
subst-transp (t $ s) eq     = cong₂ _$_ (subst-transp t eq) (subst-transp s eq)

subst-app-id : (t : Exp) → t [ v ] ≡ t
subst-app-id (v _)       = refl
subst-app-id ze          = refl
subst-app-id (su t)      = cong su (subst-app-id t)
subst-app-id (rec T u s t)
  rewrite subst-app-id u
        | trans (subst-transp s subst-qqid≈id) (subst-app-id s)
        | subst-app-id t = refl
subst-app-id (Λ t)       = cong Λ (trans (subst-transp t subst-qid≈id) (subst-app-id t))
subst-app-id (t $ s)     = cong₂ _$_ (subst-app-id t) (subst-app-id s)

subst-app-comb : (t : Exp) (σ σ′ : Subst) → t [ σ ] [ σ′ ] ≡ t [ σ ∙ σ′ ]
subst-app-comb (v x) σ σ′       = refl
subst-app-comb ze σ σ′          = refl
subst-app-comb (su t) σ σ′      = cong su (subst-app-comb t σ σ′)
subst-app-comb (rec T u s t) σ σ′
  rewrite subst-app-comb u σ σ′
        | trans (subst-app-comb s (q (q σ)) (q (q σ′))) (subst-transp s (subst-qq-∙-dist σ σ′))
        | subst-app-comb t σ σ′ = refl
subst-app-comb (Λ t) σ σ′       = cong Λ (trans (subst-app-comb t (q σ) (q σ′)) (subst-transp t (subst-q-∙-dist σ σ′)))
subst-app-comb (t $ s) σ σ′     = cong₂ _$_ (subst-app-comb t σ σ′) (subst-app-comb s σ σ′)

subst-comp-assoc : ∀ (σ σ′ σ″ : Subst) x → ((σ ∙ σ′) ∙ σ″) x ≡ (σ ∙ (σ′ ∙ σ″)) x
subst-comp-assoc σ σ′ σ″ x = subst-app-comb (σ x) σ′ σ″

instance
  Wk-AlgLemmas : AlgLemmas Wk
  Wk-AlgLemmas = record
    { _≈_      = _≗_
    ; ≈-equiv  = Setoid.isEquivalence wk-setoid
    ; left-id  = λ _ _ → refl
    ; right-id = λ _ _ → refl
    ; assoc    = λ _ _ _ _ → refl
    }
    where wk-setoid = ℕ →-setoid ℕ

  Subst-AlgLemmas : AlgLemmas Subst
  Subst-AlgLemmas = record
    { _≈_         = _≗_
    ; ≈-equiv     = Setoid.isEquivalence (ℕ →-setoid Exp)
    ; left-id     = λ _ _ → refl
    ; right-id    = λ σ x → subst-app-id (σ x)
    ; assoc       = subst-comp-assoc
    }
