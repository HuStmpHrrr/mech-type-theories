{-# OPTIONS --without-K --safe #-}

module Layered.Presheaf where

open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All.Properties

open import Layered.Typ

open All′ using (lookup) public


record Monotone {C : Set} (A : C → Set) (R : C → C → Set) : Set where
  infixl 8 _[_]
  field
    _[_] : ∀ {c c′} → A c′ → R c c′ → A c

open Monotone {{...}} public

data Layer : Set where
  zer one : Layer

variable
  i : Layer


pred? : Layer → Typ → Set
pred? zer = core?
pred? one = type?

preds? : Layer → Ctx → Set
preds? zer = cores?
preds? one = types?

infixl 10 _$_
data Exp : Layer → Ctx → Ctx → Typ → Set where
  v0     : cores? Ψ → cores? Γ → T ∈ Γ → Exp zer Ψ Γ T
  v1     : cores? Ψ → types? Γ → T ∈ Γ → Exp one Ψ Γ T
  u0     : cores? Ψ → cores? Γ → T ∈ Ψ → Exp zer Ψ Γ T
  u1     : cores? Ψ → types? Γ → T ∈ Ψ → Exp one Ψ Γ T
  zero0  : cores? Ψ → cores? Γ → Exp zer Ψ Γ N
  zero1  : cores? Ψ → types? Γ → Exp one Ψ Γ N
  succ   : Exp i Ψ Γ N → Exp i Ψ Γ N
  Λ      : Exp i Ψ (S ∷ Γ) T → Exp i Ψ Γ (S ⟶ T)
  _$_    : Exp i Ψ Γ (S ⟶ T) → Exp i Ψ Γ S → Exp i Ψ Γ T
  box    : types? Γ → Exp zer Ψ [] T → Exp one Ψ Γ (□ T)
  letbox : Exp one Ψ Γ (□ S) → Exp one (S ∷ Ψ) Γ T → Exp one Ψ Γ T


layer-lift : Exp zer Ψ Γ T → Exp one Ψ Γ T
layer-lift (v0 Ψwf Γwf T∈Γ) = v1 Ψwf (cores-types Γwf) T∈Γ
layer-lift (u0 Ψwf Γwf T∈Ψ) = u1 Ψwf (cores-types Γwf) T∈Ψ
layer-lift (zero0 Ψwf Γwf)  = zero1 Ψwf (cores-types Γwf)
layer-lift (succ t)         = layer-lift t
layer-lift (Λ t)            = Λ (layer-lift t)
layer-lift (t $ s)          = layer-lift t $ layer-lift s

lwk!-gen : Exp i Ψ Δ T → preds? i Γ → Exp i Ψ (Δ ++ Γ) T
lwk!-gen (v0 Ψwf Δwf T∈Δ) Γwf = v0 Ψwf (++⁺ Δwf Γwf) (++⁺ˡ T∈Δ)
lwk!-gen (v1 Ψwf Δwf T∈Δ) Γwf = v1 Ψwf (++⁺ Δwf Γwf) (++⁺ˡ T∈Δ)
lwk!-gen (u0 Ψwf Δwf T∈Ψ) Γwf = u0 Ψwf (++⁺ Δwf Γwf) T∈Ψ
lwk!-gen (u1 Ψwf Δwf T∈Ψ) Γwf = u1 Ψwf (++⁺ Δwf Γwf) T∈Ψ
lwk!-gen (zero0 Ψwf Δwf) Γwf  = zero0 Ψwf (++⁺ Δwf Γwf)
lwk!-gen (zero1 Ψwf Δwf) Γwf  = zero1 Ψwf (++⁺ Δwf Γwf)
lwk!-gen (succ t) Γwf         = lwk!-gen t Γwf
lwk!-gen (Λ t) Γwf            = Λ (lwk!-gen t Γwf)
lwk!-gen (t $ s) Γwf          = lwk!-gen t Γwf $ lwk!-gen s Γwf
lwk!-gen (box Δwf t) Γwf      = box (++⁺ Δwf Γwf) t
lwk!-gen (letbox s t) Γwf     = letbox (lwk!-gen s Γwf) (lwk!-gen t Γwf)

lwk! : Exp i Ψ [] T → preds? i Γ → Exp i Ψ Γ T
lwk! = lwk!-gen

validity-pred : Layer → Ctx → Typ → Set
validity-pred zer Γ T = cores? Γ × core? T
validity-pred one Γ T = types? Γ × type? T

validity : ∀ i → Exp i Ψ Γ T → cores? Ψ × validity-pred i Γ T
validity .zer (v0 Ψwf Γwf T∈Γ) = Ψwf , Γwf , lookup Γwf T∈Γ
validity .one (v1 Ψwf Γwf T∈Γ) = Ψwf , Γwf , lookup Γwf T∈Γ
validity .zer (u0 Ψwf Γwf T∈Ψ) = Ψwf , Γwf , lookup Ψwf T∈Ψ
validity .one (u1 Ψwf Γwf T∈Ψ) = Ψwf , Γwf , core-type (lookup Ψwf T∈Ψ)
validity .zer (zero0 Ψwf Γwf)  = Ψwf , Γwf , N
validity .one (zero1 Ψwf Γwf)  = Ψwf , Γwf , N
validity i (succ t)            = validity i t
validity zer (Λ t)
  with validity _ t
... | Ψwf , S ∷ Γwf , T        = Ψwf , Γwf , S ⟶ T
validity one (Λ t)
  with validity _ t
... | Ψwf , S ∷ Γwf , T        = Ψwf , Γwf , S ⟶ T
validity zer (t $ s)
  with validity _ t
... | Ψwf , Γwf , S ⟶ T        = Ψwf , Γwf , T
validity one (t $ s)
  with validity _ t
... | Ψwf , Γwf , S ⟶ T        = Ψwf , Γwf , T
validity .one (box Γwf t)
  with validity _ t
... | Ψwf , _ , T              = Ψwf , Γwf , □ T
validity .one (letbox s t)
  with validity _ t
... | _ ∷ Ψwf , Γwf , T        = Ψwf , Γwf , T


data GWk : Ctx → Ctx → Set where
  ε  : GWk [] []
  p  : core? T →
       GWk Ψ Φ →
       ----------------
       GWk (T ∷ Ψ) Φ
  q  : core? T →
       GWk Ψ Φ →
       --------------------
       GWk (T ∷ Ψ) (T ∷ Φ)


variable
  γ γ′ γ″ : GWk Ψ Φ

gwk-validity : GWk Ψ Φ → cores? Ψ × cores? Φ
gwk-validity ε   = [] , []
gwk-validity (p T γ)
  with gwk-validity γ
...  | Ψwf , Φwf = T ∷ Ψwf , Φwf
gwk-validity (q T γ)
  with gwk-validity γ
...  | Ψwf , Φwf = T ∷ Ψwf , T ∷ Φwf


idwk : cores? Ψ → GWk Ψ Ψ
idwk [] = ε
idwk (T ∷ Ψ) = q T (idwk Ψ)


infixl 3 _∘w_
_∘w_ : GWk Ψ′ Ψ → GWk Ψ″ Ψ′ → GWk Ψ″ Ψ
ε ∘w γ′          = γ′
p T γ ∘w q T′ γ′ = p T′ (γ ∘w γ′)
q T γ ∘w q T′ γ′ = q T′ (γ ∘w γ′)
γ ∘w p T′ γ′     = p T′ (γ ∘w γ′)

gwk-∈ : T ∈ Ψ → GWk Φ Ψ → T ∈ Φ
gwk-∈ T∈Ψ (p _ γ)      = 1+ (gwk-∈ T∈Ψ γ)
gwk-∈ 0d (q _ γ)       = 0d
gwk-∈ (1+ T∈Ψ) (q _ γ) = 1+ (gwk-∈ T∈Ψ γ)

instance
  ∈-gwk-mono : Monotone (λ Ψ → T ∈ Ψ) GWk
  ∈-gwk-mono = record { _[_] = gwk-∈ }


gwk : Exp i Ψ Γ T → GWk Φ Ψ → Exp i Φ Γ T
gwk (v0 Ψwf Γwf T∈Γ) γ = v0 (proj₁ (gwk-validity γ)) Γwf T∈Γ
gwk (v1 Ψwf Γwf T∈Γ) γ = v1 (proj₁ (gwk-validity γ)) Γwf T∈Γ
gwk (u0 Ψwf Γwf T∈Ψ) γ = u0 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
gwk (u1 Ψwf Γwf T∈Ψ) γ = u1 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
gwk (zero0 Ψwf Γwf) γ  = zero0 (proj₁ (gwk-validity γ)) Γwf
gwk (zero1 Ψwf Γwf) γ  = zero1 (proj₁ (gwk-validity γ)) Γwf
gwk (succ t) γ         = gwk t γ
gwk (Λ t) γ            = Λ (gwk t γ)
gwk (t $ s) γ          = gwk t γ $ gwk s γ
gwk (box Γwf t) γ      = box Γwf (gwk t γ)
gwk (letbox s t) γ
  with validity _ s
...  | _ , _ , □ S     = letbox (gwk s γ) (gwk t (q S γ))

instance
  gwk-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GWk
  gwk-mono = record { _[_] = gwk }

data GSubst : Ctx → Ctx → Set where
  [] : cores? Ψ → GSubst Ψ []
  _∷_ : Exp zer Ψ [] T → GSubst Ψ Φ → GSubst Ψ (T ∷ Φ)

variable
  σ σ′ σ″ : GSubst Φ Ψ

gsubst-validity : GSubst Ψ Φ → cores? Ψ × cores? Φ
gsubst-validity ([] Ψwf)     = Ψwf , []
gsubst-validity (t ∷ σ)
  with gsubst-validity σ | validity _ t
...  | Ψwf , Φwf | _ , _ , T = Ψwf , T ∷ Φwf

gsubst-lookup : GSubst Ψ Φ → T ∈ Φ → Exp zer Ψ [] T
gsubst-lookup (t ∷ σ) 0d       = t
gsubst-lookup (t ∷ σ) (1+ T∈Φ) = gsubst-lookup σ T∈Φ

gsubst-wk : GSubst Ψ Φ → GWk Ψ′ Ψ → GSubst Ψ′ Φ
gsubst-wk ([] _) γ  = [] (proj₁ (gwk-validity γ))
gsubst-wk (t ∷ σ) γ = t [ γ ] ∷ gsubst-wk σ γ

instance
  gsubst-wk-mono : Monotone (λ Ψ → GSubst Ψ Φ) GWk
  gsubst-wk-mono = record { _[_] = gsubst-wk }


gsubst : Exp i Ψ Γ T → GSubst Φ Ψ → Exp i Φ Γ T
gsubst (v0 Ψwf Γwf T∈Γ) σ = v0 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
gsubst (v1 Ψwf Γwf T∈Γ) σ = v1 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
gsubst (u0 Ψwf Γwf T∈Ψ) σ = lwk! (gsubst-lookup σ T∈Ψ) Γwf
gsubst (u1 Ψwf Γwf T∈Ψ) σ = lwk! (layer-lift (gsubst-lookup σ T∈Ψ)) Γwf
gsubst (zero0 Ψwf Γwf) σ  = zero0 (proj₁ (gsubst-validity σ)) Γwf
gsubst (zero1 Ψwf Γwf) σ  = zero1 (proj₁ (gsubst-validity σ)) Γwf
gsubst (succ t) σ         = gsubst t σ
gsubst (Λ t) σ            = Λ (gsubst t σ)
gsubst (t $ s) σ          = gsubst t σ $ gsubst s σ
gsubst (box Γwf t) σ      = box Γwf (gsubst t σ)
gsubst (letbox s t) σ
  with validity _ s
...  | _ , _ , □ S        = letbox (gsubst s σ) (gsubst t (u0 (S ∷ Φwf) All′.[] 0d ∷ σ [ p S (idwk Φwf) ]))
  where Φwf = proj₁ (gsubst-validity σ)


instance
  gsubst-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GSubst
  gsubst-mono = record { _[_] = gsubst }
