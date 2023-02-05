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
preds? i = All (pred? i)

-- Definitions of expressions, normal forms and neutral forms
-------------------------------------------------------------

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


mutual

  data Nf : Ctx → Ctx → Typ → Set where
    zero1 : cores? Ψ → types? Γ → Nf Ψ Γ N
    succ  : Nf Ψ Γ N → Nf Ψ Γ N
    Λ     : Nf Ψ (S ∷ Γ) T → Nf Ψ Γ (S ⟶ T)
    box   : types? Γ → Exp zer Ψ [] T → Nf Ψ Γ (□ T)
    ne    : Ne Ψ Γ T → Nf Ψ Γ T

  data Ne : Ctx → Ctx → Typ → Set where
    v1     : cores? Ψ → types? Γ → T ∈ Γ → Ne Ψ Γ T
    u1     : cores? Ψ → types? Γ → T ∈ Ψ → Ne Ψ Γ T
    _$_    : Ne Ψ Γ (S ⟶ T) → Nf Ψ Γ S → Ne Ψ Γ T
    letbox : Ne Ψ Γ (□ S) → Nf (S ∷ Ψ) Γ T → Ne Ψ Γ T


variable
  t t′ t″ : Exp i Ψ Γ T
  s s′ s″ : Exp i Ψ Γ T
  w w′ w″ : Nf Ψ Γ T
  v v′ v″ : Ne Ψ Γ T

-- Terms from layer 0 can be lifted to layer 1

layer-lift : Exp zer Ψ Γ T → Exp one Ψ Γ T
layer-lift (v0 Ψwf Γwf T∈Γ) = v1 Ψwf (cores-types Γwf) T∈Γ
layer-lift (u0 Ψwf Γwf T∈Ψ) = u1 Ψwf (cores-types Γwf) T∈Ψ
layer-lift (zero0 Ψwf Γwf)  = zero1 Ψwf (cores-types Γwf)
layer-lift (succ t)         = succ (layer-lift t)
layer-lift (Λ t)            = Λ (layer-lift t)
layer-lift (t $ s)          = layer-lift t $ layer-lift s


lwk!-gen : Exp i Ψ Δ T → preds? i Γ → Exp i Ψ (Δ ++ Γ) T
lwk!-gen (v0 Ψwf Δwf T∈Δ) Γwf = v0 Ψwf (++⁺ Δwf Γwf) (++⁺ˡ T∈Δ)
lwk!-gen (v1 Ψwf Δwf T∈Δ) Γwf = v1 Ψwf (++⁺ Δwf Γwf) (++⁺ˡ T∈Δ)
lwk!-gen (u0 Ψwf Δwf T∈Ψ) Γwf = u0 Ψwf (++⁺ Δwf Γwf) T∈Ψ
lwk!-gen (u1 Ψwf Δwf T∈Ψ) Γwf = u1 Ψwf (++⁺ Δwf Γwf) T∈Ψ
lwk!-gen (zero0 Ψwf Δwf) Γwf  = zero0 Ψwf (++⁺ Δwf Γwf)
lwk!-gen (zero1 Ψwf Δwf) Γwf  = zero1 Ψwf (++⁺ Δwf Γwf)
lwk!-gen (succ t) Γwf         = succ (lwk!-gen t Γwf)
lwk!-gen (Λ t) Γwf            = Λ (lwk!-gen t Γwf)
lwk!-gen (t $ s) Γwf          = lwk!-gen t Γwf $ lwk!-gen s Γwf
lwk!-gen (box Δwf t) Γwf      = box (++⁺ Δwf Γwf) t
lwk!-gen (letbox s t) Γwf     = letbox (lwk!-gen s Γwf) (lwk!-gen t Γwf)

lwk! : Exp i Ψ [] T → preds? i Γ → Exp i Ψ Γ T
lwk! = lwk!-gen

-- Syntactic validity
--
-- A well-typed term (nf, ne, resp.) must have valid contexts and type.

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

mutual
  nf-validity : Nf Ψ Γ T → cores? Ψ × types? Γ × type? T
  nf-validity (zero1 Ψwf Γwf) = Ψwf , Γwf , N
  nf-validity (succ w)        = nf-validity w
  nf-validity (Λ w)
    with nf-validity w
  ...  | Ψwf , S ∷ Γwf , T    = Ψwf , Γwf , S ⟶ T
  nf-validity (box Γwf t)
    with validity _ t
  ...  | Ψwf , _ , T          = Ψwf , Γwf , □ T
  nf-validity (ne v)          = ne-validity v

  ne-validity : Ne Ψ Γ T → cores? Ψ × types? Γ × type? T
  ne-validity (v1 Ψwf Γwf T∈Γ) = Ψwf , Γwf , lookup Γwf T∈Γ
  ne-validity (u1 Ψwf Γwf T∈Ψ) = Ψwf , Γwf , core-type (lookup Ψwf T∈Ψ)
  ne-validity (v $ w)
    with ne-validity v
  ...  | Ψwf , Γwf , _ ⟶ T     = Ψwf , Γwf , T
  ne-validity (letbox v w)
    with nf-validity w
  ... | _ ∷ Ψwf , Γwf , T      = Ψwf , Γwf , T


-- Definition of weakenings
--
-- In simple types, we can coerce weakenings for global and local contexts.
----------------------------------------------

data Wk : Layer → Ctx → Ctx → Set where
  ε  : Wk i [] []
  p  : pred? i T →
       Wk i Ψ Φ →
       ----------------
       Wk i (T ∷ Ψ) Φ
  q  : pred? i T →
       Wk i Ψ Φ →
       --------------------
       Wk i (T ∷ Ψ) (T ∷ Φ)

GWk = Wk zer

LWk = Wk one

variable
  γ γ′ γ″ : GWk Ψ Φ
  τ τ′ τ″ : LWk Γ Δ

-- Validity for weakenings
--------------------------

wk-validity : Wk i Ψ Φ → preds? i Ψ × preds? i Φ
wk-validity ε   = [] , []
wk-validity (p T γ)
  with wk-validity γ
...  | Ψwf , Φwf = T ∷ Ψwf , Φwf
wk-validity (q T γ)
  with wk-validity γ
...  | Ψwf , Φwf = T ∷ Ψwf , T ∷ Φwf


gwk-validity : GWk Ψ Φ → cores? Ψ × cores? Φ
gwk-validity = wk-validity

lwk-validity : LWk Γ Δ → types? Γ × types? Δ
lwk-validity = wk-validity

-- Identity and composition of weakenings
-----------------------------------------

idwk : preds? i Ψ → Wk i Ψ Ψ
idwk []      = ε
idwk (T ∷ Ψ) = q T (idwk Ψ)


infixl 3 _∘w_
_∘w_ : Wk i Ψ′ Ψ → Wk i Ψ″ Ψ′ → Wk i Ψ″ Ψ
ε ∘w γ′          = γ′
p T γ ∘w q T′ γ′ = p T′ (γ ∘w γ′)
q T γ ∘w q T′ γ′ = q T′ (γ ∘w γ′)
γ ∘w p T′ γ′     = p T′ (γ ∘w γ′)


-- Weakening applications
-------------------------

gwk-∈ : T ∈ Ψ → Wk i Φ Ψ → T ∈ Φ
gwk-∈ T∈Ψ (p _ γ)      = 1+ (gwk-∈ T∈Ψ γ)
gwk-∈ 0d (q _ γ)       = 0d
gwk-∈ (1+ T∈Ψ) (q _ γ) = 1+ (gwk-∈ T∈Ψ γ)

instance
  ∈-gwk-mono : Monotone (λ Ψ → T ∈ Ψ) (Wk i)
  ∈-gwk-mono = record { _[_] = gwk-∈ }


gwk : Exp i Ψ Γ T → GWk Φ Ψ → Exp i Φ Γ T
gwk (v0 Ψwf Γwf T∈Γ) γ = v0 (proj₁ (gwk-validity γ)) Γwf T∈Γ
gwk (v1 Ψwf Γwf T∈Γ) γ = v1 (proj₁ (gwk-validity γ)) Γwf T∈Γ
gwk (u0 Ψwf Γwf T∈Ψ) γ = u0 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
gwk (u1 Ψwf Γwf T∈Ψ) γ = u1 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
gwk (zero0 Ψwf Γwf) γ  = zero0 (proj₁ (gwk-validity γ)) Γwf
gwk (zero1 Ψwf Γwf) γ  = zero1 (proj₁ (gwk-validity γ)) Γwf
gwk (succ t) γ         = succ (gwk t γ)
gwk (Λ t) γ            = Λ (gwk t γ)
gwk (t $ s) γ          = gwk t γ $ gwk s γ
gwk (box Γwf t) γ      = box Γwf (gwk t γ)
gwk (letbox s t) γ
  with validity _ s
...  | _ , _ , □ S     = letbox (gwk s γ) (gwk t (q S γ))

instance
  gwk-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GWk
  gwk-mono = record { _[_] = gwk }


mutual
  gwk-nf : Nf Ψ Γ T → GWk Φ Ψ → Nf Φ Γ T
  gwk-nf (zero1 Ψwf Γwf) γ = zero1 (proj₁ (gwk-validity γ)) Γwf
  gwk-nf (succ w) γ        = succ (gwk-nf w γ)
  gwk-nf (Λ w) γ           = Λ (gwk-nf w γ)
  gwk-nf (box Γwf t) γ     = box Γwf (t [ γ ])
  gwk-nf (ne v) γ          = ne (gwk-ne v γ)

  gwk-ne : Ne Ψ Γ T → GWk Φ Ψ → Ne Φ Γ T
  gwk-ne (v1 Ψwf Γwf T∈Γ) γ = v1 (proj₁ (gwk-validity γ)) Γwf T∈Γ
  gwk-ne (u1 Ψwf Γwf T∈Ψ) γ = u1 (proj₁ (gwk-validity γ)) Γwf (T∈Ψ [ γ ])
  gwk-ne (v $ w) γ          = gwk-ne v γ $ gwk-nf w γ
  gwk-ne (letbox v w) γ
    with ne-validity v
  ... | _ , _ , □ S         = letbox (gwk-ne v γ) (gwk-nf w (q S γ))

instance
  gwk-nf-mono : Monotone (λ Ψ → Nf Ψ Γ T) GWk
  gwk-nf-mono = record { _[_] = gwk-nf }

  gwk-ne-mono : Monotone (λ Ψ → Ne Ψ Γ T) GWk
  gwk-ne-mono = record { _[_] = gwk-ne }


mutual
  lwk-nf : Nf Ψ Γ T → LWk Δ Γ → Nf Ψ Δ T
  lwk-nf (zero1 Ψwf Γwf) τ = zero1 Ψwf (proj₁ (lwk-validity τ))
  lwk-nf (succ w) τ        = succ (lwk-nf w τ)
  lwk-nf (Λ w) τ
    with nf-validity w
  ...  | _ , S ∷ _ , _     = Λ (lwk-nf w (q S τ))
  lwk-nf (box _ t) τ       = box (proj₁ (lwk-validity τ)) t
  lwk-nf (ne v) τ          = ne (lwk-ne v τ)

  lwk-ne : Ne Ψ Γ T → LWk Δ Γ → Ne Ψ Δ T
  lwk-ne (v1 Ψwf Γwf T∈Γ) τ = v1 Ψwf (proj₁ (lwk-validity τ)) (T∈Γ [ τ ])
  lwk-ne (u1 Ψwf Γwf T∈Ψ) τ = u1 Ψwf (proj₁ (lwk-validity τ)) T∈Ψ
  lwk-ne (v $ w) τ          = lwk-ne v τ $ lwk-nf w τ
  lwk-ne (letbox v w) τ
    with ne-validity v
  ... | _ , _ , □ S         = letbox (lwk-ne v τ) (lwk-nf w τ)


-- Weakenings between pairs of global and local contexts
--
-- This is the base category the presheaf model lives in.
---------------------------------------------------
AWk : Ctx × Ctx → Ctx × Ctx → Set
AWk (Ψ , Γ) (Φ , Δ) = GWk Ψ Φ × LWk Γ Δ


-- Applications of weakenings
-----------------------------

awk-nf : Nf Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Nf Φ Δ T
awk-nf w (γ , τ) = lwk-nf (w [ γ ]) τ

awk-ne : Ne Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Ne Φ Δ T
awk-ne w (γ , τ) = lwk-ne (w [ γ ]) τ

instance
  awk-nf-mono : Monotone (λ (Ψ , Γ) → Nf Ψ Γ T) AWk
  awk-nf-mono = record { _[_] = awk-nf }

  awk-ne-mono : Monotone (λ (Ψ , Γ) → Ne Ψ Γ T) AWk
  awk-ne-mono = record { _[_] = awk-ne }


-- Global substitutions
-----------------------

data GSubst : Ctx → Ctx → Set where
  [] : cores? Ψ → GSubst Ψ []
  _∷_ : Exp zer Ψ [] T → GSubst Ψ Φ → GSubst Ψ (T ∷ Φ)

variable
  σ σ′ σ″ : GSubst Φ Ψ

-- Validity of global substitutions
-----------------------------------

gsubst-validity : GSubst Ψ Φ → cores? Ψ × cores? Φ
gsubst-validity ([] Ψwf)     = Ψwf , []
gsubst-validity (t ∷ σ)
  with gsubst-validity σ | validity _ t
...  | Ψwf , Φwf | _ , _ , T = Ψwf , T ∷ Φwf

-- (Global) weakening of global substitutions
---------------------------------------------

gsubst-lookup : GSubst Ψ Φ → T ∈ Φ → Exp zer Ψ [] T
gsubst-lookup (t ∷ σ) 0d       = t
gsubst-lookup (t ∷ σ) (1+ T∈Φ) = gsubst-lookup σ T∈Φ

gsubst-wk : GSubst Ψ Φ → GWk Ψ′ Ψ → GSubst Ψ′ Φ
gsubst-wk ([] _) γ  = [] (proj₁ (gwk-validity γ))
gsubst-wk (t ∷ σ) γ = t [ γ ] ∷ gsubst-wk σ γ

instance
  gsubst-wk-mono : Monotone (λ Ψ → GSubst Ψ Φ) GWk
  gsubst-wk-mono = record { _[_] = gsubst-wk }

-- Applying global substitutions
---------------------------------

gsubst : Exp i Ψ Γ T → GSubst Φ Ψ → Exp i Φ Γ T
gsubst (v0 Ψwf Γwf T∈Γ) σ = v0 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
gsubst (v1 Ψwf Γwf T∈Γ) σ = v1 (proj₁ (gsubst-validity σ)) Γwf T∈Γ
gsubst (u0 Ψwf Γwf T∈Ψ) σ = lwk! (gsubst-lookup σ T∈Ψ) Γwf
gsubst (u1 Ψwf Γwf T∈Ψ) σ = lwk! (layer-lift (gsubst-lookup σ T∈Ψ)) Γwf
gsubst (zero0 Ψwf Γwf) σ  = zero0 (proj₁ (gsubst-validity σ)) Γwf
gsubst (zero1 Ψwf Γwf) σ  = zero1 (proj₁ (gsubst-validity σ)) Γwf
gsubst (succ t) σ         = succ (gsubst t σ)
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

-- Converting a global weakening to a global substitution
--------------------------------------------------

gwk-gsubst : GWk Ψ Φ → GSubst Ψ Φ
gwk-gsubst ε       = [] []
gwk-gsubst (p T γ) = gwk-gsubst γ [ p T (idwk (proj₁ (gwk-validity γ))) ]
gwk-gsubst (q T γ) = u0 (T ∷ proj₁ (gwk-validity γ)) [] 0d ∷ gwk-gsubst γ [ p T (idwk (proj₁ (gwk-validity γ))) ]

-- From this we can extract the identity global substitutions.

gid : cores? Ψ → GSubst Ψ Ψ
gid Ψwf = gwk-gsubst (idwk Ψwf)


-- Interpretations of types and contexts
----------------------------------------

⟦_⟧T : Typ → Ctx → Ctx → Set
⟦ N ⟧T Ψ Γ     = Nf Ψ Γ N
⟦ □ T ⟧T Ψ Γ   = Nf Ψ Γ (□ T)
⟦ S ⟶ T ⟧T Ψ Γ = ∀ {Φ Δ} → AWk (Φ , Δ) (Ψ , Γ) → ⟦ S ⟧T Φ Δ → ⟦ T ⟧T Φ Δ

⟦_⟧G : Ctx → Layer → Ctx → Set
⟦ Φ ⟧G zer Ψ = GWk Ψ Φ
⟦ Φ ⟧G one Ψ = GSubst Ψ Φ

⟦_⟧L : Ctx → Ctx → Ctx → Set
⟦ [] ⟧L Ψ Γ    = ⊤
⟦ T ∷ Δ ⟧L Ψ Γ = ⟦ T ⟧T Ψ Γ × ⟦ Δ ⟧L Ψ Γ

⟦_⟧A : Ctx × Ctx → Layer → Ctx → Ctx → Set
⟦ Φ , Δ ⟧A i Ψ Γ = ⟦ Φ ⟧G i Ψ × ⟦ Δ ⟧L Ψ Γ
