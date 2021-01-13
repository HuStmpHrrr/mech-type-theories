{-# OPTIONS --without-K --safe #-}

module Sum.Dynamics where

open import Lib
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sum.Statics

open import Data.Unit using (tt; ⊤)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)

data Value : Trm Γ T → Set where
  *  : Value (* {Γ})
  pr : ∀ {s : Trm Γ S} {u : Trm Γ U} → Value s → Value u → Value (pr s u)
  i₁ : ∀ {s : Trm Γ S} → Value s → ∀ U → Value (i₁ s U)
  i₂ : ∀ S → ∀ {u : Trm Γ U} → Value u → Value (i₂ S u)
  Λ  : (t : Trm (S ∷ Γ) T) → Value (Λ t)

infix 3 _↦_ _↦*_

data _↦_ : Trm Γ T → Trm Γ T → Set where
  π₁-pr    : ∀ {s : Trm Γ S} {u : Trm Γ U} (vs : Value s) (vu : Value u) → π₁ (pr s u) ↦ s
  π₂-pr    : ∀ {s : Trm Γ S} {u : Trm Γ U} (vs : Value s) (vu : Value u) → π₂ (pr s u) ↦ u
  Λ-$      : (t : Trm (S ∷ Γ) T) {s : Trm Γ S} (vs : Value s) → (Λ t) $ s ↦ t ⟦ s ⟧!
  pm-i₁    : ∀ {s : Trm Γ S} U (c₁ : Trm (S ∷ Γ) T) c₂ (vs : Value s) → pm (i₁ s U) c₁ c₂ ↦ c₁ ⟦ s ⟧!
  pm-i₂    : ∀ S {u : Trm Γ U} (c₁ : Trm (S ∷ Γ) T) c₂ (vu : Value u) → pm (i₂ S u) c₁ c₂ ↦ c₂ ⟦ u ⟧!

  π₁-cong  : ∀ {t t′ : Trm Γ (S X U)} → t ↦ t′ → π₁ t ↦ π₁ t′
  π₂-cong  : ∀ {t t′ : Trm Γ (S X U)} → t ↦ t′ → π₂ t ↦ π₂ t′
  pr-cong₁ : ∀ {s s′ : Trm Γ S} (u : Trm Γ U) → s ↦ s′ → pr s u ↦ pr s′ u
  pr-cong₂ : ∀ {s : Trm Γ S} {u u′ : Trm Γ U} (vs : Value s) → u ↦ u′ → pr s u ↦ pr s u′
  i₁-cong  : ∀ {s s′ : Trm Γ S} → s ↦ s′ → ∀ U → i₁ s U ↦ i₁ s′ U
  i₂-cong  : ∀ {u u′ : Trm Γ U} → ∀ S → u ↦ u′ → i₂ S u ↦ i₂ S u′
  pm-cong  : ∀ {t t′ : Trm Γ (S ∪ U)} (c₁ : Trm (S ∷ Γ) T) c₂ → t ↦ t′ → pm t c₁ c₂ ↦ pm t′ c₁ c₂
  $-cong₁  : ∀ {t t′ : Trm Γ (S ⟶ U)} (s : Trm Γ S) → t ↦ t′ → t $ s ↦ t′ $ s
  $-cong₂  : ∀ {t : Trm Γ (S ⟶ U)} {s s′ : Trm Γ S} (vt : Value t) → s ↦ s′ → t $ s ↦ t $ s′

_↦*_ : Trm Γ T → Trm Γ T → Set
_↦*_ = Star _↦_

↦-¬Value : ∀ {t t′ : Trm Γ T} → t ↦ t′ → ¬ Value t
↦-¬Value (pr-cong₁ u r) (pr vs vu)   = ↦-¬Value r vs
↦-¬Value (pr-cong₂ vs r) (pr vs′ vu) = ↦-¬Value r vu
↦-¬Value (i₁-cong r U) (i₁ vs .U)    = ↦-¬Value r vs
↦-¬Value (i₂-cong S r) (i₂ .S vu)    = ↦-¬Value r vu

↦-determ : ∀ {t t′ t″ : Trm Γ T} → t ↦ t′ → t ↦ t″ → t′ ≡ t″
↦-determ (π₁-pr vs vu) (π₁-pr vs′ vu′)             = refl
↦-determ (π₁-pr vs vu) (π₁-cong r′)                = ⊥-elim (↦-¬Value r′ (pr vs vu))
↦-determ (π₂-pr vs vu) (π₂-pr vs′ vu′)             = refl
↦-determ (π₂-pr vs vu) (π₂-cong r′)                = ⊥-elim (↦-¬Value r′ (pr vs vu))
↦-determ (Λ-$ t vs) (Λ-$ .t vs₁)                   = refl
↦-determ (Λ-$ t vs) ($-cong₂ vt r′)                = ⊥-elim (↦-¬Value r′ vs)
↦-determ (π₁-cong r) (π₁-pr vs vu)                 = ⊥-elim (↦-¬Value r (pr vs vu))
↦-determ (π₁-cong r) (π₁-cong r′)                  = cong π₁ (↦-determ r r′)
↦-determ (π₂-cong r) (π₂-pr vs vu)                 = ⊥-elim (↦-¬Value r (pr vs vu))
↦-determ (π₂-cong r) (π₂-cong r′)                  = cong π₂ (↦-determ r r′)
↦-determ (pr-cong₁ u r) (pr-cong₁ .u r′)           = cong (λ z → pr z u) (↦-determ r r′)
↦-determ (pr-cong₁ u r) (pr-cong₂ vs r′)           = ⊥-elim (↦-¬Value r vs)
↦-determ (pr-cong₂ vs r) (pr-cong₁ _ r′)           = ⊥-elim (↦-¬Value r′ vs)
↦-determ (pr-cong₂ vs r) (pr-cong₂ vs₁ r′)         = cong (pr _) (↦-determ r r′)
↦-determ ($-cong₁ s r) ($-cong₁ .s r′)             = cong (λ z → z $ s) (↦-determ r r′)
↦-determ ($-cong₁ s r) ($-cong₂ vt r′)             = ⊥-elim (↦-¬Value r vt)
↦-determ ($-cong₂ vt r) (Λ-$ t vs)                 = ⊥-elim (↦-¬Value r vs)
↦-determ ($-cong₂ vt r) ($-cong₁ _ r′)             = ⊥-elim (↦-¬Value r′ vt)
↦-determ ($-cong₂ vt r) ($-cong₂ vt′ r′)           = cong (_ $_) (↦-determ r r′)
↦-determ (pm-i₁ U c₁ c₂ vs) (pm-i₁ .U .c₁ .c₂ vs′) = refl
↦-determ (pm-i₁ U c₁ c₂ vs) (pm-cong .c₁ .c₂ r′)   = ⊥-elim (↦-¬Value r′ (i₁ vs U))
↦-determ (pm-i₂ S c₁ c₂ vu) (pm-i₂ .S .c₁ .c₂ vu′) = refl
↦-determ (pm-i₂ S c₁ c₂ vu) (pm-cong .c₁ .c₂ r′)   = ⊥-elim (↦-¬Value r′ (i₂ S vu))
↦-determ (i₁-cong r U) (i₁-cong r′ .U)             = cong (λ s → i₁ s U) (↦-determ r r′)
↦-determ (i₂-cong S r) (i₂-cong .S r′)             = cong (i₂ S) (↦-determ r r′)
↦-determ (pm-cong c₁ c₂ r) (pm-i₁ _ .c₁ .c₂ vs)    = ⊥-elim (↦-¬Value r (i₁ vs _))
↦-determ (pm-cong c₁ c₂ r) (pm-i₂ _ .c₁ .c₂ vu)    = ⊥-elim (↦-¬Value r (i₂ _ vu))
↦-determ (pm-cong c₁ c₂ r) (pm-cong .c₁ .c₂ r′)    = cong (λ t → pm t c₁ c₂) (↦-determ r r′)

module ↦* where

  map : ∀ {t t′ : Trm Γ T} (f : Trm Γ T → Trm Γ S) → (∀ {t t′ : Trm Γ T} → t ↦ t′ → f t ↦* f t′) → t ↦* t′ → f t ↦* f t′
  map f pf ε        = ε
  map f pf (r ◅ r*) = pf r ◅◅ map f pf r*

  map′ : ∀ {t t′ : Trm Γ T} (f : Trm Γ T → Trm Γ S) → (∀ {t t′ : Trm Γ T} → t ↦ t′ → f t ↦ f t′) → t ↦* t′ → f t ↦* f t′
  map′ f pf = map f (λ r → pf r ◅ ε)

Halts : Trm Γ T → Set
Halts t = ∃ (λ t′ → t ↦* t′ × Value t′)

Value⇒Halts : {t : Trm Γ T} → Value t → Halts t
Value⇒Halts {t = t} v = t , ε , v

data Rec : Typ → Set where
  *   : Rec *
  _X_ : ∀ {S U} → Rec S → Rec U → Rec (S X U)
  _⟶_ : ∀ {S U} → Rec S → Rec U → Rec (S ⟶ U)
  _∪_[_] : ∀ {S U T} → Rec S → Rec U → Rec T → Rec (S ∪ U)

R  : Trm [] T → Set
R′ : Trm [] T → Set

R t = Halts t × R′ t

R′ {*} t     = ⊤
R′ {S X U} t = R (π₁ t) × R (π₂ t)
R′ {S ∪ U} t = (∃ λ t′ → t ↦* i₁ t′ U × R t′) ⊎ ∃ λ t′ → t ↦* i₂ S t′ × R t′
R′ {S ⟶ U} t = ∀ {s : Trm [] S} → R s → R (t $ s)

↦-resp-Halts₁ : ∀ {t t′ : Trm Γ T} → t ↦ t′ → Halts t → Halts t′
↦-resp-Halts₁ (π₁-pr vs vu) _                                        = _ , ε , vs
↦-resp-Halts₁ (π₂-pr vs vu) _                                        = _ , ε , vu
↦-resp-Halts₁ (Λ-$ t vs) (t″ , Λ-$ .t _ ◅ r′ , vt″)                  = t″ , r′ , vt″
↦-resp-Halts₁ (Λ-$ t vs) (t″ , $-cong₂ vt st ◅ r′ , vt″)             = ⊥-elim (↦-¬Value st vs)
↦-resp-Halts₁ (π₁-cong r) (t″ , π₁-pr vs vu ◅ r′ , vt″)              = ⊥-elim (↦-¬Value r (pr vs vu))
↦-resp-Halts₁ (π₁-cong r) (t″ , π₁-cong st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ (π₂-cong r) (t″ , π₂-pr vs vu ◅ r′ , vt″)              = ⊥-elim (↦-¬Value r (pr vs vu))
↦-resp-Halts₁ (π₂-cong r) (t″ , π₂-cong st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ (pr-cong₁ u r) (.(pr _ u) , ε , pr vs vu)              = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ (pr-cong₁ u r) (t″ , pr-cong₁ .u st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ (pr-cong₁ u r) (t″ , pr-cong₂ vs st ◅ r′ , vt″)        = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ (pr-cong₂ vs r) (.(pr _ _) , ε , pr _ vu)              = ⊥-elim (↦-¬Value r vu)
↦-resp-Halts₁ (pr-cong₂ vs r) (t″ , pr-cong₁ _ st ◅ r′ , vt″)        = ⊥-elim (↦-¬Value st vs)
↦-resp-Halts₁ (pr-cong₂ vs r) (t″ , pr-cong₂ _ st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ ($-cong₁ s r) (t″ , $-cong₁ .s st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ ($-cong₁ s r) (t″ , $-cong₂ vt st ◅ r′ , vt″)          = ⊥-elim (↦-¬Value r vt)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , Λ-$ t vs ◅ r′ , vt″)              = ⊥-elim (↦-¬Value r vs)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , $-cong₁ _ st ◅ r′ , vt″)          = ⊥-elim (↦-¬Value st vt)
↦-resp-Halts₁ ($-cong₂ vt r) (t″ , $-cong₂ _ st ◅ r′ , vt″)
  rewrite ↦-determ r st                                              = t″ , r′ , vt″
↦-resp-Halts₁ (pm-i₁ U c₁ c₂ vs) (t , pm-i₁ .U .c₁ .c₂ vs′ ◅ r , vt) = t , r , vt
↦-resp-Halts₁ (pm-i₁ U c₁ c₂ vs) (t , pm-cong .c₁ .c₂ st ◅ r′ , vt)  = ⊥-elim (↦-¬Value st (i₁ vs U))
↦-resp-Halts₁ (pm-i₂ S c₁ c₂ vu) (t , pm-i₂ .S .c₁ .c₂ vu′ ◅ r , vt) = t , r , vt
↦-resp-Halts₁ (pm-i₂ S c₁ c₂ vu) (t , pm-cong .c₁ .c₂ st ◅ r , vt)   = ⊥-elim (↦-¬Value st (i₂ S vu))
↦-resp-Halts₁ (i₁-cong r U) (.(i₁ _ U) , ε , vt)                     = ⊥-elim (↦-¬Value (i₁-cong r U) vt)
↦-resp-Halts₁ (i₁-cong r U) (t , i₁-cong st .U ◅ r′ , vt)
  rewrite ↦-determ r st                                              = t , r′ , vt
↦-resp-Halts₁ (i₂-cong S r) (.(i₂ S _) , ε , vt)                     = ⊥-elim (↦-¬Value (i₂-cong S r) vt)
↦-resp-Halts₁ (i₂-cong S r) (t , i₂-cong .S st ◅ r′ , vt)
  rewrite ↦-determ r st                                              = t , r′ , vt
↦-resp-Halts₁ (pm-cong c₁ c₂ r) (t , pm-i₁ _ .c₁ .c₂ vs ◅ r′ , vt)   = ⊥-elim (↦-¬Value r (i₁ vs _))
↦-resp-Halts₁ (pm-cong c₁ c₂ r) (t , pm-i₂ _ .c₁ .c₂ vu ◅ r′ , vt)   = ⊥-elim (↦-¬Value r (i₂ _ vu))
↦-resp-Halts₁ (pm-cong c₁ c₂ r) (t , pm-cong .c₁ .c₂ st ◅ r′ , vt)
  rewrite ↦-determ r st                                              = t , r′ , vt

↦-resp-Halts₂ : ∀ {t t′ : Trm Γ T} → t ↦ t′ → Halts t′ → Halts t
↦-resp-Halts₂ r (t″ , r′ , vt″) = t″ , r ◅ r′ , vt″

↦-resp-R₁ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R t → R t′
↦-resp-R′₁ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R′ t → R′ t′

↦-resp-R₁ r (ht , R′t) = ↦-resp-Halts₁ r ht , ↦-resp-R′₁ r R′t

↦-resp-R′₁ {*} r R′t                                                     = tt
↦-resp-R′₁ {S X U} r (Rs , Ru)                                           = ↦-resp-R₁ (π₁-cong r) Rs , ↦-resp-R₁ (π₂-cong r) Ru
↦-resp-R′₁ {S ∪ U} (i₁-cong {_} {_} {_} {s′} r .U) (inj₁ (t′ , ε , Rt′)) = inj₁ (s′ , ε , ↦-resp-R₁ r Rt′)
↦-resp-R′₁ {S ∪ U} r (inj₁ (t′ , r′ ◅ r* , Rt′))
  rewrite ↦-determ r r′                                                  = inj₁ (t′ , r* , Rt′)
↦-resp-R′₁ {S ∪ U} (i₂-cong {_} {_} {_} {u′} .S r) (inj₂ (t′ , ε , Rt′)) = inj₂ (u′ , ε , ↦-resp-R₁ r Rt′)
↦-resp-R′₁ {S ∪ U} r (inj₂ (t′ , r′ ◅ r* , Rt′))
  rewrite ↦-determ r r′                                                  = inj₂ (t′ , r* , Rt′)
↦-resp-R′₁ {S ⟶ U} r R′t Rs                                              = ↦-resp-R₁ ($-cong₁ _ r) (R′t Rs)

↦-resp-R₂ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R t′ → R t
↦-resp-R′₂ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R′ t′ → R′ t

↦-resp-R₂ r (Ht′ , R′t′) = ↦-resp-Halts₂ r Ht′ , ↦-resp-R′₂ r R′t′

↦-resp-R′₂ {*} r Rt′                        = tt
↦-resp-R′₂ {S X U} r (Rs′ , Ru′)            = ↦-resp-R₂ (π₁-cong r) Rs′ , ↦-resp-R₂ (π₂-cong r) Ru′
↦-resp-R′₂ {S ∪ U} r (inj₁ (t′ , r* , Rt′)) = inj₁ (t′ , r ◅ r* , Rt′)
↦-resp-R′₂ {S ∪ U} r (inj₂ (t′ , r* , Rt′)) = inj₂ (t′ , r ◅ r* , Rt′)
↦-resp-R′₂ {S ⟶ U} r Rt′ Rs′                = ↦-resp-R₂ ($-cong₁ _ r) (Rt′ Rs′)

↦*-resp-R₁ : ∀ {t t′ : Trm [] T} → t ↦* t′ → R t → R t′
↦*-resp-R₁ ε Rt        = Rt
↦*-resp-R₁ (r ◅ r*) Rt = ↦*-resp-R₁ r* (↦-resp-R₁ r Rt)

↦*-resp-R₂ : ∀ {t t′ : Trm [] T} → t ↦* t′ → R t′ → R t
↦*-resp-R₂ ε Rt′        = Rt′
↦*-resp-R₂ (r ◅ r*) Rt′ = ↦-resp-R₂ r (↦*-resp-R₂ r* Rt′)

R-pr : {s : Trm [] S} {u : Trm [] U} → R s → R u → R (pr s u)
R-pr {_} {_} {s} {u} Rs@((s′ , rs′ , vs′) , R′s) Ru@((u′ , ru′ , vu′) , R′u)
  = (pr s′ u′ , rs,u , pr vs′ vu′)
  , ↦*-resp-R₂ (↦*.map′ π₁ π₁-cong rs,u ◅◅ π₁-pr vs′ vu′ ◅ ε) (↦*-resp-R₁ rs′ Rs)
  , ↦*-resp-R₂ (↦*.map′ π₂ π₂-cong rs,u ◅◅ π₂-pr vs′ vu′ ◅ ε) (↦*-resp-R₁ ru′ Ru)
  where rs,u : pr s u ↦* pr s′ u′
        rs,u = ↦*.map′ (λ s → pr s u) (λ r → pr-cong₁ _ r) rs′ ◅◅ ↦*.map′ (pr s′) (pr-cong₂ vs′) ru′

R-π₁ : {t : Trm [] (S X U)} → R t → R (π₁ t)
R-π₁ (_ , Rs , _) = Rs

R-π₂ : {t : Trm [] (S X U)} → R t → R (π₂ t)
R-π₂ (_ , _ , Ru) = Ru

R-i₁ : {s : Trm [] S} → R s → ∀ U → R (i₁ s U)
R-i₁ Rs@((s′ , r* , vs′) , _) U = (i₁ s′ U , ↦*.map′ (λ s → i₁ s U) (λ r → i₁-cong r U) r* , i₁ vs′ U) , inj₁ (_ , ε , Rs)

R-i₂ : ∀ S {u : Trm [] U} → R u → R (i₂ S u)
R-i₂ S Ru@((u′ , r* , vu′) , _) = (i₂ S u′ , (↦*.map′ (i₂ S) (i₂-cong S) r*) , i₂ S vu′) , inj₂ (_ , ε , Ru)

R-$ : {t : Trm [] (S ⟶ U)} {s : Trm [] S} → R t → R s → R (t $ s)
R-$ (_ , R′t) Rs = R′t Rs

Λ-$-subst : (t : Trm (S ∷ Γ) T) (σ : Subst Δ Γ) {s : Trm Δ S} → Value s → (Λ t ⟦ σ ⟧) $ s ↦ t ⟦ s ∷ σ ⟧
Λ-$-subst t σ vs = subst (λ t′ → (Λ t ⟦ σ ⟧) $ _ ↦ t′) (Subst′.extend-qweaken-apply _ σ t) (Λ-$ (t ⟦ Subst′.qweaken _ σ ⟧) vs)

pm-i₁-subst : ∀ {t : Trm Δ S} (σ : Subst Δ Γ) (c₁ : Trm (S ∷ Γ) T) c₂ → Value t → pm (i₁ t U) (c₁ ⟦ Subst′.qweaken S σ ⟧) (c₂ ⟦ Subst′.qweaken U σ ⟧) ↦ c₁ ⟦ t ∷ σ ⟧
pm-i₁-subst σ c₁ c₂ vt = subst (λ t′ → pm _ _ _ ↦ t′) (Subst′.extend-qweaken-apply _ σ c₁) (pm-i₁ _ (c₁ ⟦ Subst′.qweaken _ σ ⟧) (c₂ ⟦ Subst′.qweaken _ σ ⟧) vt)

pm-i₂-subst : ∀ {t : Trm Δ U} (σ : Subst Δ Γ) (c₁ : Trm (S ∷ Γ) T) c₂ → Value t → pm (i₂ S t) (c₁ ⟦ Subst′.qweaken S σ ⟧) (c₂ ⟦ Subst′.qweaken U σ ⟧) ↦ c₂ ⟦ t ∷ σ ⟧
pm-i₂-subst σ c₁ c₂ vt = subst (λ t′ → pm _ _ _ ↦ t′) (Subst′.extend-qweaken-apply _ σ c₂) (pm-i₂ _ (c₁ ⟦ Subst′.qweaken _ σ ⟧) (c₂ ⟦ Subst′.qweaken _ σ ⟧) vt)

R-subst : {σ : Subst [] Γ} → Forall R σ → (t : Trm Γ T) → R (t ⟦ σ ⟧)
R-subst R* *                                         = (* , ε , *) , tt
R-subst R* (var T∈)                                  = Forall′.lookup R* T∈
R-subst R* (pr s u)                                  = R-pr (R-subst R* s) (R-subst R* u)
R-subst R* (π₁ t)                                    = R-π₁ (R-subst R* t)
R-subst R* (π₂ t)                                    = R-π₂ (R-subst R* t)
R-subst R* (i₁ t U)                                  = R-i₁ (R-subst R* t) U
R-subst R* (i₂ S t)                                  = R-i₂ S (R-subst R* t)
R-subst {_} {_} {σ} R* (pm t c₁ c₂) with R-subst R* t
... | Ht , inj₁ (s , r* , Rs@((s′ , r*′ , vs′) , _)) = ↦*-resp-R₂ (↦*.map′ (λ t → pm t _ _) (pm-cong _ _) (r* ◅◅ ↦*.map′ (λ s → i₁ s _) (λ r → i₁-cong r _) r*′)
                                                                   ◅◅ pm-i₁-subst σ c₁ c₂ vs′ ◅ ε)
                                                                  (R-subst (↦*-resp-R₁ r*′ Rs ∷ R*) c₁)
... | Ht , inj₂ (u , r* , Ru@((u′ , r*′ , vu′) , _)) = ↦*-resp-R₂ (↦*.map′ (λ t → pm t _ _) (pm-cong _ _) (r* ◅◅ ↦*.map′ (i₂ _) (i₂-cong _) r*′)
                                                                  ◅◅ pm-i₂-subst σ c₁ c₂ vu′ ◅ ε)
                                                                  (R-subst (↦*-resp-R₁ r*′ Ru ∷ R*) c₂)
R-subst R* (s $ u)                                   = R-$ (R-subst R* s) (R-subst R* u)
R-subst {_} {_} {σ} R* (Λ {S} t)                     = (Λ t′ , ε , Λ t′) , helper
  where t′ : Trm (S ∷ []) _
        t′                                = t ⟦ Subst′.qweaken S σ ⟧
        helper : {s : Trm [] S} → R s → R ((Λ t ⟦ σ ⟧) $ s)
        helper Rs@((s′ , rs , vs′) , R′s) =
          let Rs′                         = R-subst (↦*-resp-R₁ rs Rs ∷ R*) t
          in ↦*-resp-R₂ (↦*.map (_ $_) (λ r → $-cong₂ (Λ t′) r ◅ ε) rs ◅◅ Λ-$-subst t σ vs′ ◅ ε) Rs′

Rt : (t : Trm [] T) → R t
Rt t with R-subst [] t
... | Rt′ rewrite Subst′.id-apply t = Rt′

normalize : (t : Trm [] T) → Halts t
normalize t = let Ht , _ = Rt t in Ht
