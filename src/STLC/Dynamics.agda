{-# OPTIONS --without-K --safe #-}

module STLC.Dynamics where

open import Lib
open import STLC.Statics

open import Data.Unit using (tt; ⊤)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_) renaming (gmap to *map)

data Value : Trm Γ T → Set where
  *  : Value (* {Γ})
  pr : ∀ {s : Trm Γ S} {u : Trm Γ U} → Value s → Value u → Value (pr s u)
  Λ  : (t : Trm (S ∷ Γ) T) → Value (Λ t)

infix 3 _↦_ _↦*_

data _↦_ : Trm Γ T → Trm Γ T → Set where
  π₁-pr    : ∀ {s : Trm Γ S} {u : Trm Γ U} (vs : Value s) (vu : Value u) → π₁ (pr s u) ↦ s
  π₂-pr    : ∀ {s : Trm Γ S} {u : Trm Γ U} (vs : Value s) (vu : Value u) → π₂ (pr s u) ↦ u
  Λ-$      : (t : Trm (S ∷ Γ) T) {s : Trm Γ S} (vs : Value s) → (Λ t) $ s ↦ t ⟦ s ⟧!

  π₁-cong  : ∀ {t t′ : Trm Γ (S X U)} → t ↦ t′ → π₁ t ↦ π₁ t′
  π₂-cong  : ∀ {t t′ : Trm Γ (S X U)} → t ↦ t′ → π₂ t ↦ π₂ t′
  pr-cong₁ : ∀ {s s′ : Trm Γ S} (u : Trm Γ U) → s ↦ s′ → pr s u ↦ pr s′ u
  pr-cong₂ : ∀ {s : Trm Γ S} {u u′ : Trm Γ U} (vs : Value s) → u ↦ u′ → pr s u ↦ pr s u′
  $-cong₁  : ∀ {t t′ : Trm Γ (S ⟶ U)} (s : Trm Γ S) → t ↦ t′ → t $ s ↦ t′ $ s
  $-cong₂  : ∀ {t : Trm Γ (S ⟶ U)} {s s′ : Trm Γ S} (vt : Value t) → s ↦ s′ → t $ s ↦ t $ s′

_↦*_ : Trm Γ T → Trm Γ T → Set
_↦*_ = Star _↦_

↦-¬Value : ∀ {t t′ : Trm Γ T} → t ↦ t′ → ¬ Value t
↦-¬Value (pr-cong₁ u r) (pr vs vu) = ↦-¬Value r vs
↦-¬Value (pr-cong₂ vs r) (pr _ vu) = ↦-¬Value r vu

↦-determ : ∀ {t t′ t″ : Trm Γ T} → t ↦ t′ → t ↦ t″ → t′ ≡ t″
↦-determ (π₁-pr vs vu) (π₁-pr vs′ vu′)     = refl
↦-determ (π₁-pr vs vu) (π₁-cong r′)        = ⊥-elim (↦-¬Value r′ (pr vs vu))
↦-determ (π₂-pr vs vu) (π₂-pr vs′ vu′)     = refl
↦-determ (π₂-pr vs vu) (π₂-cong r′)        = ⊥-elim (↦-¬Value r′ (pr vs vu))
↦-determ (Λ-$ t vs) (Λ-$ .t vs₁)           = refl
↦-determ (Λ-$ t vs) ($-cong₂ vt r′)        = ⊥-elim (↦-¬Value r′ vs)
↦-determ (π₁-cong r) (π₁-pr vs vu)         = ⊥-elim (↦-¬Value r (pr vs vu))
↦-determ (π₁-cong r) (π₁-cong r′)          = cong π₁ (↦-determ r r′)
↦-determ (π₂-cong r) (π₂-pr vs vu)         = ⊥-elim (↦-¬Value r (pr vs vu))
↦-determ (π₂-cong r) (π₂-cong r′)          = cong π₂ (↦-determ r r′)
↦-determ (pr-cong₁ u r) (pr-cong₁ .u r′)   = cong (λ z → pr z u) (↦-determ r r′)
↦-determ (pr-cong₁ u r) (pr-cong₂ vs r′)   = ⊥-elim (↦-¬Value r vs)
↦-determ (pr-cong₂ vs r) (pr-cong₁ _ r′)   = ⊥-elim (↦-¬Value r′ vs)
↦-determ (pr-cong₂ vs r) (pr-cong₂ vs₁ r′) = cong (pr _) (↦-determ r r′)
↦-determ ($-cong₁ s r) ($-cong₁ .s r′)     = cong (λ z → z $ s) (↦-determ r r′)
↦-determ ($-cong₁ s r) ($-cong₂ vt r′)     = ⊥-elim (↦-¬Value r vt)
↦-determ ($-cong₂ vt r) (Λ-$ t vs)         = ⊥-elim (↦-¬Value r vs)
↦-determ ($-cong₂ vt r) ($-cong₁ _ r′)     = ⊥-elim (↦-¬Value r′ vt)
↦-determ ($-cong₂ vt r) ($-cong₂ vt′ r′)   = cong (_ $_) (↦-determ r r′)

module ↦* where

  map : ∀ {t t′ : Trm Γ T} (f : Trm Γ T → Trm Γ S) → (∀ {t t′ : Trm Γ T} → t ↦ t′ → f t ↦* f t′) → t ↦* t′ → f t ↦* f t′
  map f pf ε        = ε
  map f pf (r ◅ r*) = pf r ◅◅ map f pf r*

Halts : Trm Γ T → Set
Halts t = ∃ (λ t′ → t ↦* t′ × Value t′)

Value⇒Halts : {t : Trm Γ T} → Value t → Halts t
Value⇒Halts {t = t} v = t , ε , v

↦-resp-Halts₁ : ∀ {t t′ : Trm Γ T} → t ↦ t′ → Halts t → Halts t′
↦-resp-Halts₁ (π₁-pr vs vu) _                                 = _ , ε , vs
↦-resp-Halts₁ (π₂-pr vs vu) _                                 = _ , ε , vu
↦-resp-Halts₁ (Λ-$ t vs) (t″ , Λ-$ .t _ ◅ r′ , vt″)           = t″ , r′ , vt″
↦-resp-Halts₁ (Λ-$ t vs) (t″ , $-cong₂ vt st ◅ r′ , vt″)      = ⊥-elim (↦-¬Value st vs)
↦-resp-Halts₁ (π₁-cong r) (t″ , π₁-pr vs vu ◅ r′ , vt″)       = ⊥-elim (↦-¬Value r (pr vs vu))
↦-resp-Halts₁ (π₁-cong r) (t″ , π₁-cong st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″
↦-resp-Halts₁ (π₂-cong r) (t″ , π₂-pr vs vu ◅ r′ , vt″)       = ⊥-elim (↦-¬Value r (pr vs vu))
↦-resp-Halts₁ (π₂-cong r) (t″ , π₂-cong st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″
↦-resp-Halts₁ (pr-cong₁ u r) (.(pr _ u) , ε , pr vs vu)       = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ (pr-cong₁ u r) (t″ , pr-cong₁ .u st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″
↦-resp-Halts₁ (pr-cong₁ u r) (t″ , pr-cong₂ vs st ◅ r′ , vt″) = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ (pr-cong₂ vs r) (.(pr _ _) , ε , pr _ vu)       = ⊥-elim (↦-¬Value r vu)
↦-resp-Halts₁ (pr-cong₂ vs r) (t″ , pr-cong₁ _ st ◅ r′ , vt″) = ⊥-elim (↦-¬Value st vs)
↦-resp-Halts₁ (pr-cong₂ vs r) (t″ , pr-cong₂ _ st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″
↦-resp-Halts₁ ($-cong₁ s r) (t″ , $-cong₁ .s st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″
↦-resp-Halts₁ ($-cong₁ s r) (t″ , $-cong₂ vt st ◅ r′ , vt″)   = ⊥-elim (↦-¬Value r vt)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , Λ-$ t vs ◅ r′ , vt″)       = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , $-cong₁ _ st ◅ r′ , vt″)   = ⊥-elim (↦-¬Value st vt)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , $-cong₂ _ st ◅ r′ , vt″)
  rewrite ↦-determ r st                                       = t″ , r′ , vt″

↦-resp-Halts₂ : ∀ {t t′ : Trm Γ T} → t ↦ t′ → Halts t′ → Halts t
↦-resp-Halts₂ r (t″ , r′ , vt″) = t″ , r ◅ r′ , vt″

Λ-$-subst : (t : Trm (S ∷ Γ) T) (σ : Subst Δ Γ) {s : Trm Δ S} → Value s → (Λ t ⟦ σ ⟧) $ s ↦ t ⟦ s ∷ σ ⟧
Λ-$-subst t σ vs = subst (λ t′ → (Λ t ⟦ σ ⟧) $ _ ↦ t′) (Subst′.extend-qweaken-apply _ σ t) (Λ-$ (t ⟦ Subst′.qweaken _ σ ⟧) vs)

module Direct where
  R : Trm [] T → Set
  R′ : Trm [] T → Set

  R t = Halts t × R′ t

  R′ {*} t     = ⊤
  R′ {S X U} t = R (π₁ t) × R (π₂ t)
  R′ {S ⟶ U} t = ∀ {s : Trm [] S} → R s → R (t $ s)

  R⇒Halts : {t : Trm [] T} → R t → Halts t
  R⇒Halts (h , _) = h

  ↦-resp-R₁ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R t → R t′
  ↦-resp-R′₁ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R′ t → R′ t′

  ↦-resp-R₁ r (ht , R′t) = ↦-resp-Halts₁ r ht , ↦-resp-R′₁ r R′t

  ↦-resp-R′₁ {*} r R′t           = tt
  ↦-resp-R′₁ {S X U} r (Rs , Ru) = ↦-resp-R₁ (π₁-cong r) Rs , ↦-resp-R₁ (π₂-cong r) Ru
  ↦-resp-R′₁ {S ⟶ U} r R′t Rs    = ↦-resp-R₁ ($-cong₁ _ r) (R′t Rs)

  ↦*-resp-R₁ : ∀ {t t′ : Trm [] T} → t ↦* t′ → R t → R t′
  ↦*-resp-R₁ ε Rt        = Rt
  ↦*-resp-R₁ (r ◅ r*) Rt = ↦*-resp-R₁ r* (↦-resp-R₁ r Rt)

  ↦-resp-R₂ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R t′ → R t
  ↦-resp-R′₂ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R′ t′ → R′ t

  ↦-resp-R₂ r (Ht′ , R′t′) = ↦-resp-Halts₂ r Ht′ , ↦-resp-R′₂ r R′t′

  ↦-resp-R′₂ {*} r Rt′             = tt
  ↦-resp-R′₂ {S X U} r (Rs′ , Ru′) = ↦-resp-R₂ (π₁-cong r) Rs′ , ↦-resp-R₂ (π₂-cong r) Ru′
  ↦-resp-R′₂ {S ⟶ U} r Rt′ Rs′     = ↦-resp-R₂ ($-cong₁ _ r) (Rt′ Rs′)

  ↦*-resp-R₂ : ∀ {t t′ : Trm [] T} → t ↦* t′ → R t′ → R t
  ↦*-resp-R₂ ε Rt′        = Rt′
  ↦*-resp-R₂ (r ◅ r*) Rt′ = ↦-resp-R₂ r (↦*-resp-R₂ r* Rt′)

  R-pr : {s : Trm [] S} {u : Trm [] U} → R s → R u → R (pr s u)
  R-pr {_} {_} {s} {u} Rs@((s′ , rs′ , vs′) , R′s) Ru@((u′ , ru′ , vu′) , R′u)
    = (pr s′ u′ , rs,u , pr vs′ vu′)
    , ↦*-resp-R₂ (↦*.map π₁ (λ r → π₁-cong r ◅ ε) rs,u ◅◅ π₁-pr vs′ vu′ ◅ ε) (↦*-resp-R₁ rs′ Rs)
    , ↦*-resp-R₂ (↦*.map π₂ (λ r → π₂-cong r ◅ ε) rs,u ◅◅ π₂-pr vs′ vu′ ◅ ε) (↦*-resp-R₁ ru′ Ru)
    where rs,u : pr s u ↦* pr s′ u′
          rs,u = ↦*.map (λ s → pr s u) (λ r → pr-cong₁ _ r ◅ ε) rs′ ◅◅ ↦*.map (pr s′) (λ r → pr-cong₂ vs′ r ◅ ε) ru′

  R-π₁ : {t : Trm [] (S X U)} → R t → R (π₁ t)
  R-π₁ (_ , Rs , _) = Rs

  R-π₂ : {t : Trm [] (S X U)} → R t → R (π₂ t)
  R-π₂ (_ , _ , Ru) = Ru

  R-$ : {t : Trm [] (S ⟶ U)} {s : Trm [] S} → R t → R s → R (t $ s)
  R-$ (_ , R′t) Rs = R′t Rs

  R-subst : {σ : Subst [] Γ} → Forall R σ → (t : Trm Γ T) → R (t ⟦ σ ⟧)
  R-subst R* *                 = (* , ε , *) , tt
  R-subst R* (var T∈)          = Forall′.lookup′ R* T∈
  R-subst R* (pr s u)          = R-pr (R-subst R* s) (R-subst R* u)
  R-subst R* (π₁ t)            = R-π₁ (R-subst R* t)
  R-subst R* (π₂ t)            = R-π₂ (R-subst R* t)
  R-subst R* (s $ u)           = R-$ (R-subst R* s) (R-subst R* u)
  R-subst {_} {_} {σ} R* (Λ {S} t) = (Λ t′ , ε , Λ t′) , helper
    where t′ : Trm (S ∷ []) _
          t′ = t ⟦ Subst′.qweaken S σ ⟧
          helper : {s : Trm [] S} → R s → R ((Λ t ⟦ σ ⟧) $ s)
          helper Rs@((s′ , rs , vs′) , R′s) =
            let Rs′ = R-subst (↦*-resp-R₁ rs Rs ∷ R*) t
            in ↦*-resp-R₂ (↦*.map (_ $_) (λ r → $-cong₂ (Λ t′) r ◅ ε) rs ◅◅ Λ-$-subst t σ vs′ ◅ ε) Rs′

  Rt : (t : Trm [] T) → R t
  Rt t with R-subst [] t
  ... | Rt′ rewrite Subst′.id-apply t = Rt′

  normalize : (t : Trm [] T) → Halts t
  normalize t = let Ht , _ = Rt t in Ht


module Another where

  mutual
    R : Trm [] T → Set
    R {T} t = ∃ λ t′ → t ↦* t′ × Σ (Value t′) λ v → RV t′ v

    RV : (t : Trm [] T) (v : Value t) → Set
    RV {*} .* *                    = ⊤
    RV {S X T} .(pr _ _) (pr v v′) = RV _ v × RV _ v′
    RV {S ⟶ T} t v                 = ∀ {s : Trm [] S} {v : Value s} → RV s v → R (t $ s)

  R⇒Halts : {t : Trm [] T} → R t → Halts t
  R⇒Halts (t′ , ↦t′ , v , _) = t′ , ↦t′ , v

  RV⇒R : {t : Trm [] T} {v : Value t} → RV t v → R t
  RV⇒R Rv = -, ε , -, Rv

  R-subst : {σ : Subst [] Γ} → Forall (λ t → Σ (Value t) (RV t)) σ → (t : Trm Γ T) → R (t ⟦ σ ⟧)
  R-subst R* *                              = * , ε , * , tt
  R-subst R* (var T∈)                       = RV⇒R (proj₂ (Forall′.lookup′ R* T∈))
  R-subst R* (pr s u)
    with R-subst R* s | R-subst R* u
  ...  | s′ , ↦*s′ , v  , Rv
       | u′ , ↦*u′ , v′ , Rv′               = pr s′ u′ , *map (λ s → pr s (u ⟦ _ ⟧)) (pr-cong₁ (u ⟦ _ ⟧)) ↦*s′ ◅◅ *map (pr s′) (pr-cong₂ v) ↦*u′ , pr v v′ , Rv , Rv′
  R-subst R* (π₁ t)
    with R-subst R* t
  ... | pr t _ , ↦*t′ , pr v v′ , Rv , Rv′  = t , *map π₁ π₁-cong ↦*t′ ◅◅ π₁-pr v v′ ◅ ε  , v , Rv
  R-subst R* (π₂ t)
    with R-subst R* t
  ... | pr _ t′ , ↦*t′ , pr v v′ , Rv , Rv′ = t′ , *map π₂ π₂-cong ↦*t′ ◅◅ π₂-pr v v′ ◅ ε  , v′ , Rv′
  R-subst R* (s $ u)
    with R-subst R* s | R-subst R* u
  ...  | s′ , ↦*s′ , v , Rv
       | Ru@(u′ , ↦*u′ , v′ , Rv′)
       with Rv Rv′
  ...     | su , ↦*su , v′ , Rv′            = su , *map (_$ (u ⟦ _ ⟧)) ($-cong₁ (u ⟦ _ ⟧)) ↦*s′ ◅◅ *map (_ $_) ($-cong₂ v) ↦*u′ ◅◅ ↦*su , v′ , Rv′
  R-subst {_} {S ⟶ T} {σ} R* (Λ t)          = Λ t′ , ε , Λ t′ , helper
    where t′ : Trm (S ∷ []) _
          t′ = t ⟦ Subst′.qweaken S σ ⟧
          helper : {s : Trm [] S} {v : Value s} → RV s v → R (Λ t′ $ s)
          helper {s} {v} Rv
            with R-subst ((v , Rv) ∷ R*) t
          ...  | ts , ↦*ts , v″ , Rv″ = ts , (Λ-$-subst t σ v ◅ ε) ◅◅ ↦*ts , v″ , Rv″

  Rt : (t : Trm [] T) → R t
  Rt t with R-subst [] t
  ... | Rt′ rewrite Subst′.id-apply t = Rt′

  normalize : (t : Trm [] T) → Halts t
  normalize t = R⇒Halts (Rt t)
