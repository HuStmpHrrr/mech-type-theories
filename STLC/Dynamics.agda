{-# OPTIONS --without-K --safe #-}

module STLC.Dynamics where

open import Lib
open import STLC.Statics

open import Data.Unit using (tt; ⊤)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

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

Halts : Trm Γ T → Set
Halts t = ∃ (λ t′ → t ↦* t′ × Value t′)

Value⇒Halts : {t : Trm Γ T} → Value t → Halts t
Value⇒Halts {t = t} v = t , ε , v

R : Trm [] T → Set
R′ : Trm [] T → Set

R t = Halts t × R′ t

R′ {*} t     = ⊤
R′ {S X U} t = R (π₁ t) × R (π₂ t)
R′ {S ⟶ U} t = ∀ {s : Trm [] S} → R s → R (t $ s)

R⇒Halts : {t : Trm [] T} → R t → Halts t
R⇒Halts (h , _) = h

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

↦-resp-R : ∀ {t t′ : Trm [] T} → t ↦ t′ → R t → R t′
↦-resp-R′ : ∀ {t t′ : Trm [] T} → t ↦ t′ → R′ t → R′ t′

↦-resp-R r (ht , R′t) = ↦-resp-Halts₁ r ht , ↦-resp-R′ r R′t

↦-resp-R′ {*} r R′t                         = tt
↦-resp-R′ {S X U} r ((Hs , R′s) , Hu , R′u) = (↦-resp-Halts₁ (π₁-cong r) Hs , ↦-resp-R′ (π₁-cong r) R′s)
                                            , ↦-resp-Halts₁ (π₂-cong r) Hu , ↦-resp-R′ (π₂-cong r) R′u
↦-resp-R′ {S ⟶ U} r R′t Rs@(Hs , R′s) with R′t Rs
... | Hts , R′ts                            = ↦-resp-Halts₁ ($-cong₁ _ r) Hts , ↦-resp-R′ ($-cong₁ _ r) R′ts

↦*-resp-R : ∀ {t t′ : Trm [] T} → t ↦* t′ → R t → R t′
↦*-resp-R ε Rt        = Rt
↦*-resp-R (r ◅ r*) Rt = ↦*-resp-R r* (↦-resp-R r Rt)
