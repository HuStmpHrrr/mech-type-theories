{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Properties.Ops where

open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality using (_≗_) public

import Data.Nat.Properties as ℕₚ
import Relation.Binary.Reasoning.Setoid as SR

open import Lib
open import STLCSubst.Statics.Definitions

record AlgLemmas {i} (A : Set i)
   : Set (lsuc i) where

  infix 4 _≈_

  field
    {{has-id}}     : HasIdentity A
    {{composable}} : Composable A
    {{head-wk}}    : HeadWeaken A

    _≈_      : Rel A 0ℓ
    ≈-equiv  : IsEquivalence _≈_
    left-id  : ∀ a → id ∙ a ≈ a
    right-id : ∀ a → a ∙ id ≈ a
    assoc    : ∀ a b c → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ∙-cong   : ∀ a b c d → a ≈ b → c ≈ d → a ∙ c ≈ b ∙ d

    q-id     : q id ≈ id
    q-cong   : ∀ {a b} → a ≈ b → q a ≈ q b
    q-∙-dist : ∀ a b → q a ∙ q b ≈ q (a ∙ b)

  ≈-setoid : Setoid _ _
  ≈-setoid = record { Carrier = _ ; _≈_ = _≈_ ; isEquivalence = ≈-equiv }

  module ≈ = Setoid ≈-setoid
  module ≈-Reasoning = SR ≈-setoid

  repeat-q-∙-dist : ∀ n a b → repeat q n a ∙ repeat q n b ≈ repeat q n (a ∙ b)
  repeat-q-∙-dist zero a b    = ≈.refl
  repeat-q-∙-dist (suc n) a b = ≈.trans (q-∙-dist (repeat q n a) (repeat q n b)) (q-cong (repeat-q-∙-dist n a b))

  repeat-q-id : ∀ n → repeat q n id ≈ id
  repeat-q-id zero    = ≈.refl
  repeat-q-id (suc n) = ≈.trans (q-cong (repeat-q-id n)) q-id

open AlgLemmas {{...}} hiding (_≈_; has-id; composable; head-wk) public

---------------------------------------
-- properties of weakenings

module ≗ {a b} {A : Set a} {B : Set b} = Setoid (A →-setoid B)

wk-q-cong : ϕ ≗ ψ → q ϕ ≗ q ψ
wk-q-cong eq zero    = refl
wk-q-cong eq (suc x) = cong suc (eq x)

wk-transp : (t : Exp) → ϕ ≗ ψ → t [ ϕ ] ≡ t [ ψ ]
wk-transp (v x) eq         = cong v (eq x)
wk-transp ze eq            = refl
wk-transp (su t) eq        = cong su (wk-transp t eq)
wk-transp (rec T u s t) eq
  rewrite wk-transp u eq
        | wk-transp s (wk-q-cong (wk-q-cong eq))
        | wk-transp t eq = refl
wk-transp (Λ t) eq         = cong Λ (wk-transp t (wk-q-cong eq))
wk-transp (t $ s) eq       = cong₂ _$_ (wk-transp t eq) (wk-transp s eq)

wk-q-∙-dist : (ϕ ψ : Wk) → q ϕ ∙ q ψ ≗ q (ϕ ∙ ψ)
wk-q-∙-dist ϕ ψ zero    = refl
wk-q-∙-dist ϕ ψ (suc x) = refl

wk-qq-∙-dist : (ϕ ψ : Wk) → q (q ϕ) ∙ q (q ψ) ≗ q (q (ϕ ∙ ψ))
wk-qq-∙-dist ϕ ψ = ≗.trans (wk-q-∙-dist (q ϕ) (q ψ)) (wk-q-cong (wk-q-∙-dist ϕ ψ))

wk-app-comb : (t : Exp) (ϕ ψ : Wk) → t [ ϕ ] [ ψ ] ≡ t [ ϕ ∙ ψ ]
wk-app-comb (v x) ϕ ψ       = refl
wk-app-comb ze ϕ ψ          = refl
wk-app-comb (su t) ϕ ψ      = cong su (wk-app-comb t ϕ ψ)
wk-app-comb (rec T u s t) ϕ ψ
  rewrite wk-app-comb u ϕ ψ
        | trans (wk-app-comb s (q (q ϕ)) (q (q ψ))) (wk-transp s (wk-qq-∙-dist ϕ ψ))
        | wk-app-comb t ϕ ψ = refl
wk-app-comb (Λ t) ϕ ψ       = cong Λ (trans (wk-app-comb t (q ϕ) (q ψ)) (wk-transp t (wk-q-∙-dist ϕ ψ)))
wk-app-comb (t $ s) ϕ ψ     = cong₂ _$_ (wk-app-comb t ϕ ψ) (wk-app-comb s ϕ ψ)

wk-comp-q : (n : ℕ) (t : Exp) (ϕ : Wk) → t [ repeat q n ⇑ ] [ repeat q n (q ϕ) ] ≡ t [ repeat q n ϕ ] [ repeat q n ⇑ ]
wk-comp-q n (v x) ϕ       = cong v (lem n x)
  where lem : ∀ n x → repeat q n (q ϕ) (repeat q n ⇑ x) ≡ repeat q n ⇑ (repeat q n ϕ x)
        lem zero x        = refl
        lem (suc n) zero  = refl
        lem (suc n) (suc x)
          rewrite lem n x = refl
wk-comp-q n ze ϕ          = refl
wk-comp-q n (su t) ϕ      = cong su (wk-comp-q n t ϕ)
wk-comp-q n (rec T u s t) ϕ
  rewrite wk-comp-q n u ϕ
        | wk-comp-q (2 + n) s ϕ
        | wk-comp-q n t ϕ = refl
wk-comp-q n (Λ t) ϕ       = cong Λ (wk-comp-q (1 + n) t ϕ)
wk-comp-q n (t $ s) ϕ     = cong₂ _$_ (wk-comp-q n t ϕ) (wk-comp-q n s ϕ)

wk-suc : ∀ n x → wk (suc n) (suc x) ≡ suc (wk n x)
wk-suc n x
  with n ≤? x | suc n ≤? suc x
... | yes p | yes p′       = refl
... | yes p | no ¬p′       = ⊥-elim (¬p′ (s≤s p))
... | no ¬p | yes (s≤s p′) = ⊥-elim (¬p p′)
... | no ¬p | no ¬p′       = refl

wk-repeat-q-eq : ∀ n → repeat q n ⇑ ≗ wk n
wk-repeat-q-eq zero x       = refl
wk-repeat-q-eq (suc n) zero = refl
wk-repeat-q-eq (suc n) (suc x)
  rewrite wk-repeat-q-eq n x
        | wk-suc n x        = refl

wk-repeat-q-gen : ∀ n m → repeat q n (wk m) ≗ wk (n + m)
wk-repeat-q-gen zero m x             = refl
wk-repeat-q-gen (suc n) zero x
  rewrite ℕₚ.+-identityʳ n           = wk-repeat-q-eq (suc n) x
wk-repeat-q-gen (suc n) (suc m) zero = refl
wk-repeat-q-gen (suc n) (suc m) (suc x)
  rewrite wk-repeat-q-gen n (suc m) x
        | wk-suc (n + suc m) x       = refl

wk-q-wk0 : (n : ℕ) (t : Exp) → t [ repeat q n ⇑ ] [ ⇑ ] ≡ t [ ⇑ ] [ repeat q (1 + n) ⇑ ]
wk-q-wk0 n t = begin
  t [ repeat q n ⇑ ] [ ⇑ ]       ≡⟨ cong (_[ ⇑ ]) (wk-transp t (wk-repeat-q-eq n)) ⟩
  t [ wk n ] [ ⇑ ]                    ≡⟨ wk-app-comb t (wk n) ⇑ ⟩
  t [ wk n ∙ ⇑ ]                      ≡⟨ wk-transp t lem ⟩
  t [ ⇑ ∙ wk (1 + n) ]                ≡⟨ sym (wk-app-comb t ⇑ (wk (1 + n))) ⟩
  t [ ⇑ ] [ wk (1 + n) ]              ≡⟨ sym (wk-transp (t [ ⇑ ]) (wk-repeat-q-eq (1 + n))) ⟩
  t [ ⇑ ] [ repeat q (1 + n) ⇑ ] ∎
  where open ≡-Reasoning
        lem : wk-compose (wk n) ⇑ ≗ wk-compose ⇑ (wk (suc n))
        lem x
          rewrite wk-suc n x = refl

wk-comp-q-equiv-gen : (n : ℕ) (t : Exp) (σ : Subst) → t [ repeat q n ⇑ ] [ repeat q n (q σ) ] ≡ t [ repeat q n σ ] [ repeat q n ⇑ ]
wk-comp-q-equiv-gen n (v x) σ       = lem n x
  where lem : ∀ n x → repeat q n (q σ) (repeat q n ⇑ x) ≡ (repeat q n σ x) [ repeat q n ⇑ ]
        lem zero x        = refl
        lem (suc n) zero  = refl
        lem (suc n) (suc x)
          rewrite lem n x = wk-q-wk0 n (repeat q n σ x)
wk-comp-q-equiv-gen n ze σ          = refl
wk-comp-q-equiv-gen n (su t) σ      = cong su (wk-comp-q-equiv-gen n t σ)
wk-comp-q-equiv-gen n (rec T u s t) σ
  rewrite wk-comp-q-equiv-gen n u σ
        | wk-comp-q-equiv-gen (2 + n) s σ
        | wk-comp-q-equiv-gen n t σ = refl
wk-comp-q-equiv-gen n (Λ t) σ       = cong Λ (wk-comp-q-equiv-gen (1 + n) t σ)
wk-comp-q-equiv-gen n (t $ s) σ     = cong₂ _$_ (wk-comp-q-equiv-gen n t σ) (wk-comp-q-equiv-gen n s σ)

wk-qid≈id : wk-q id ≗ id
wk-qid≈id zero    = refl
wk-qid≈id (suc x) = refl

wk-qqid≈id : wk-q (q id) ≗ id
wk-qqid≈id = ≗.trans (wk-q-cong wk-qid≈id) wk-qid≈id

wk-app-id : (t : Exp) → wk-app t id ≡ t
wk-app-id (v x)       = refl
wk-app-id ze          = refl
wk-app-id (su t)      = cong su (wk-app-id t)
wk-app-id (rec T u s t)
  rewrite wk-app-id u
        | trans (wk-transp s wk-qqid≈id) (wk-app-id s)
        | wk-app-id t = refl
wk-app-id (Λ t)       = cong Λ (trans (wk-transp t wk-qid≈id) (wk-app-id t))
wk-app-id (t $ s)     = cong₂ _$_ (wk-app-id t) (wk-app-id s)

wk-∙-cong : (ϕ ϕ′ ψ ψ′ : Wk) → ϕ ≗ ϕ′ → ψ ≗ ψ′ → ϕ ∙ ψ ≗ ϕ′ ∙ ψ′
wk-∙-cong ϕ ϕ′ ψ ψ′ eq eq′ x
  rewrite eq x = eq′ _

---------------------------------------
-- properties of substitutions

subst-qid≈id : q v ≗ id
subst-qid≈id zero    = refl
subst-qid≈id (suc _) = refl

subst-q-cong : σ ≗ τ → q σ ≗ q τ
subst-q-cong eq zero = refl
subst-q-cong eq (suc x) = cong (λ z → z [ ⇑ ]) (eq x)

subst-qqid≈id : q (q v) ≗ id
subst-qqid≈id = ≗.trans (subst-q-cong subst-qid≈id) subst-qid≈id

q-alt : Subst → Subst
q-alt σ = σ [ ⇑ ] ↦ v 0

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

wk-drop-ext : (σ : Subst) (t : Exp) → conv ⇑ ∙ (σ ↦ t) ≗ σ
wk-drop-ext _ _ _ = refl


subst-q-∙-dist : (σ σ′ : Subst) → q σ ∙ q σ′ ≗ q (σ ∙ σ′)
subst-q-∙-dist σ σ′ zero = refl
subst-q-∙-dist σ σ′ (suc x) = begin
  σ x [ ⇑ ] [ q σ′ ] ≡⟨ wk-comp-q-equiv-gen 0 (σ x) σ′ ⟩
  σ x [ σ′ ] [ ⇑ ] ∎
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

subst-comp-assoc : ∀ (σ σ′ σ″ : Subst) → (σ ∙ σ′) ∙ σ″ ≗ σ ∙ (σ′ ∙ σ″)
subst-comp-assoc σ σ′ σ″ x = subst-app-comb (σ x) σ′ σ″

subst-∙-cong : (σ σ′ τ τ′ : Subst) → σ ≗ σ′ → τ ≗ τ′ → σ ∙ τ ≗ σ′ ∙ τ′
subst-∙-cong σ σ′ τ τ′ eq eq′ x
  rewrite eq x = subst-transp (σ′ x) eq′

subst-ext-η : ∀ σ → σ ≗ conv ⇑ ∙ σ ↦ (v 0 [ σ ])
subst-ext-η σ zero    = refl
subst-ext-η σ (suc x) = refl

---------------------------------------
-- instances

instance
  Wk-AlgLemmas : AlgLemmas Wk
  Wk-AlgLemmas = record
    { _≈_      = _≗_
    ; ≈-equiv  = Setoid.isEquivalence (ℕ →-setoid ℕ)
    ; left-id  = λ _ _ → refl
    ; right-id = λ _ _ → refl
    ; assoc    = λ _ _ _ _ → refl
    ; ∙-cong   = wk-∙-cong
    ; q-id     = wk-qid≈id
    ; q-cong   = wk-q-cong
    ; q-∙-dist = wk-q-∙-dist
    }

  Subst-AlgLemmas : AlgLemmas Subst
  Subst-AlgLemmas = record
    { _≈_         = _≗_
    ; ≈-equiv     = Setoid.isEquivalence (ℕ →-setoid Exp)
    ; left-id     = λ _ _ → refl
    ; right-id    = λ σ x → subst-app-id (σ x)
    ; assoc       = subst-comp-assoc
    ; ∙-cong      = subst-∙-cong
    ; q-id        = subst-qid≈id
    ; q-cong      = subst-q-cong
    ; q-∙-dist    = subst-q-∙-dist
    }

---------------------------------------
-- more properties

conv-q : ∀ ϕ → conv (q ϕ) ≗ q (conv ϕ)
conv-q _ zero    = refl
conv-q _ (suc _) = refl

conv-∙ : ∀ ϕ ψ → conv (ϕ ∙ ψ) ≗ conv ϕ ∙ conv ψ
conv-∙ _ _ _ = refl

ext-lookup-v0 : (σ : Subst) (t : Exp) → v 0 [ σ ↦ t ] ≡ t
ext-lookup-v0 _ _ = refl

ext-lookup-v1 : (σ : Subst) (t : Exp) (n : ℕ) → v (suc n) [ σ ↦ t ] ≡ v n [ σ ]
ext-lookup-v1 _ _ _ = refl

ext-comp : (σ δ : Subst) (t : Exp) → σ ↦ t ∙ δ ≗ σ ∙ δ ↦ (t [ δ ])
ext-comp σ δ t zero    = refl
ext-comp σ δ t (suc x) = refl

subst-wk-id : (σ : Subst) → σ [ id ] ≗ σ
subst-wk-id σ x = wk-app-id (σ x)

wk-app-cong : (ϕ : Wk) → σ ≗ τ → σ [ ϕ ] ≗ τ [ ϕ ]
wk-app-cong ϕ eq x
  rewrite eq x = refl

ext-wk : (σ : Subst) (t : Exp) (ϕ : Wk) → (σ ↦ t) [ ϕ ] ≗ σ [ ϕ ] ↦ (t [ ϕ ])
ext-wk σ t ϕ zero    = refl
ext-wk σ t ϕ (suc x) = refl

conv-equiv-subst : (σ : Subst) (ϕ : Wk) → σ ∙ conv ϕ ≗ σ [ ϕ ]
conv-equiv-subst σ ϕ x = conv-equiv (σ x) ϕ

wk-app-subst : (t : Exp) (σ : Subst) (ϕ : Wk) → t [ σ ] [ ϕ ] ≡ t [ σ [ ϕ ] ]
wk-app-subst t σ ϕ = trans (sym (conv-equiv (subst-app t σ) ϕ)) (trans (subst-app-comb t σ (conv ϕ)) (subst-transp t (conv-equiv-subst σ ϕ)))
