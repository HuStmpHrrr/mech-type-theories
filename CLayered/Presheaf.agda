{-# OPTIONS --without-K --safe #-}

module CLayered.Presheaf where

open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All.Properties

open import CLayered.Typ

open All′ using (lookup) public


record Monotone {C : Set} (A : C → Set) (R : C → C → Set) : Set where
  infixl 8 _[_]
  field
    _[_] : ∀ {c c′} → A c′ → R c c′ → A c

open Monotone {{...}} public


-- Definitions of expressions, normal forms and neutral forms
-------------------------------------------------------------

infixl 10 _$_

mutual

  data Exp : Layer → GCtx → LCtx → Typ → Set where
    var  : gwfs? Ψ → wfs? i Γ → T ∈ Γ → Exp i Ψ Γ T
    gvar : LSubst i Ψ Γ Δ → (Δ , T) ∈ Ψ → Exp i Ψ Γ T
    zero : gwfs? Ψ → wfs? i Γ → Exp i Ψ Γ N
    succ : Exp i Ψ Γ N → Exp i Ψ Γ N
    recn : Exp i Ψ Γ T → Exp i Ψ (T ∷ N ∷ Γ) T → Exp i Ψ Γ N → Exp i Ψ Γ T
    Λ    : Exp i Ψ (S ∷ Γ) T → Exp i Ψ Γ (S ⟶ T)
    _$_  : Exp i Ψ Γ (S ⟶ T) → Exp i Ψ Γ S → Exp i Ψ Γ T
    box  : types? Γ → Exp zer Ψ Δ T → Exp one Ψ Γ (□ Δ T)
    letb : Exp one Ψ Γ (□ Δ T) → Exp one ((Δ , T) ∷ Ψ) Γ T′ → Exp one Ψ Γ T′
    mat  : Exp one Ψ Γ (□ Δ T′) → Branches Ψ Γ T (Δ , T′) → Exp one Ψ Γ T

  data LSubst : Layer → GCtx → LCtx → LCtx → Set where
    []  : gwfs? Ψ → wfs? i Γ → LSubst i Ψ Γ []
    _∷_ : Exp i Ψ Γ T → LSubst i Ψ Γ Δ → LSubst i Ψ Γ (T ∷ Δ)

  -- We use ℕ to uniquely identify branch for each case.
  data Branch : ℕ → GCtx → LCtx → Typ → LCtx × Typ → Set where
    bvar  : cores? Δ → (T ∈ Δ → Exp one Ψ Γ T′) → Branch 0 Ψ Γ T′ (Δ , T)
    bzero : cores? Δ → Exp one Ψ Γ T′ → Branch 1 Ψ Γ T′ (Δ , N)
    bsucc : Exp one ((Δ , N) ∷ Ψ) Γ T′ → Branch 2 Ψ Γ T′ (Δ , N)
    bΛ    : Exp one ((S ∷ Δ , T) ∷ Ψ) Γ T′ → Branch 3 Ψ Γ T′ (Δ , S ⟶ T)
    -- This case is not the same as the paper because we cannot easily state that the
    -- body of this branch is the same for all S due to intrinsic syntax.
    --
    -- However, we are not too concerned about the difference here because this
    -- formulation is technically more general than the paper presentation, though
    -- impossible in simple types.
    b$    : (∀ {S} → core? S → Exp one ((Δ , S) ∷ (Δ , S ⟶ T) ∷ Ψ) Γ T′) → Branch 4 Ψ Γ T′ (Δ , T)
    brec  : Exp one ((Δ , N) ∷ (T ∷ N ∷ Δ , T) ∷ (Δ , T) ∷ Ψ) Γ T′ → Branch 5 Ψ Γ T′ (Δ , T)

  data Branches : GCtx → LCtx → Typ → LCtx × Typ → Set where
    bsN : Branch 0 Ψ Γ T (Δ , N) →
          Branch 1 Ψ Γ T (Δ , N) →
          Branch 2 Ψ Γ T (Δ , N) →
          Branch 4 Ψ Γ T (Δ , N) →
          Branch 5 Ψ Γ T (Δ , N) →
          Branches Ψ Γ T (Δ , N)
    bs⟶ : Branch 0 Ψ Γ T (Δ , S ⟶ T) →
          Branch 3 Ψ Γ T (Δ , S ⟶ T) →
          Branch 4 Ψ Γ T (Δ , S ⟶ T) →
          Branch 5 Ψ Γ T (Δ , S ⟶ T) →
          Branches Ψ Γ T (Δ , S ⟶ T)

mutual

  data Nf : GCtx → LCtx → Typ → Set where
    zero : gwfs? Ψ → wfs? one Γ → Nf Ψ Γ N
    succ : Nf Ψ Γ N → Nf Ψ Γ N
    Λ    : Nf Ψ (S ∷ Γ) T → Nf Ψ Γ (S ⟶ T)
    box  : types? Γ → Exp zer Ψ Δ T → Nf Ψ Γ (□ Δ T)
    ne   : Ne Ψ Γ T → Nf Ψ Γ T

  data Ne : GCtx → LCtx → Typ → Set where
    var    : gwfs? Ψ → wfs? one Γ → T ∈ Γ → Ne Ψ Γ T
    gvar   : NfLSubst Ψ Γ Δ → (Δ , T) ∈ Ψ → Ne Ψ Γ T
    recn   : Nf Ψ Γ T → Nf Ψ (T ∷ N ∷ Γ) T → Ne Ψ Γ N → Ne Ψ Γ T
    _$_    : Ne Ψ Γ (S ⟶ T) → Nf Ψ Γ S → Ne Ψ Γ T
    letb   : Ne Ψ Γ (□ Δ T) → Nf ((Δ , T) ∷ Ψ) Γ T′ → Ne Ψ Γ T′
    mat    : Ne Ψ Γ (□ Δ T′) → NfBranches Ψ Γ T (Δ , T′) → Ne Ψ Γ T
    matbox : LSubst zer Ψ Δ Γ′ → (Γ′ , T′) ∈ Ψ → NfBranches Ψ Γ T (Δ , T′) → Ne Ψ Γ T

  data NfLSubst : GCtx → LCtx → LCtx → Set where
    []  : gwfs? Ψ → wfs? one Γ → NfLSubst Ψ Γ []
    _∷_ : Nf Ψ Γ T → NfLSubst Ψ Γ Δ → NfLSubst Ψ Γ (T ∷ Δ)

  data NfBranch : ℕ → GCtx → LCtx → Typ → LCtx × Typ → Set where
    bvar  : cores? Δ → (T ∈ Δ → Nf Ψ Γ T′) → NfBranch 0 Ψ Γ T′ (Δ , T)
    bzero : cores? Δ → Nf Ψ Γ T′ → NfBranch 1 Ψ Γ T′ (Δ , N)
    bsucc : Nf ((Δ , N) ∷ Ψ) Γ T′ → NfBranch 2 Ψ Γ T′ (Δ , N)
    bΛ    : Nf ((S ∷ Δ , T) ∷ Ψ) Γ T′ → NfBranch 3 Ψ Γ T′ (Δ , S ⟶ T)
    b$    : (∀ {S} → core? S → Nf ((Δ , S) ∷ (Δ , S ⟶ T) ∷ Ψ) Γ T′) → NfBranch 4 Ψ Γ T′ (Δ , T)
    brec  : Nf ((Δ , N) ∷ (T ∷ N ∷ Δ , T) ∷ (Δ , T) ∷ Ψ) Γ T′ → NfBranch 5 Ψ Γ T′ (Δ , T)

  data NfBranches : GCtx → LCtx → Typ → LCtx × Typ → Set where
    bsN : NfBranch 0 Ψ Γ T (Δ , N) →
          NfBranch 1 Ψ Γ T (Δ , N) →
          NfBranch 2 Ψ Γ T (Δ , N) →
          NfBranch 4 Ψ Γ T (Δ , N) →
          NfBranch 5 Ψ Γ T (Δ , N) →
          NfBranches Ψ Γ T (Δ , N)
    bs⟶ : NfBranch 0 Ψ Γ T (Δ , S ⟶ T) →
          NfBranch 3 Ψ Γ T (Δ , S ⟶ T) →
          NfBranch 4 Ψ Γ T (Δ , S ⟶ T) →
          NfBranch 5 Ψ Γ T (Δ , S ⟶ T) →
          NfBranches Ψ Γ T (Δ , S ⟶ T)

variable
  t t′ t″ : Exp i Ψ Γ T
  s s′ s″ : Exp i Ψ Γ T
  δ δ′ δ″ : LSubst i Ψ Γ Δ
  n : ℕ
  ϕ ϕ′ ϕ″ : Branch n Ψ Γ T (Δ , T′)
  θ θ′ θ″ : LSubst i Ψ Γ Δ
  w w′ w″ : Nf Ψ Γ T
  v v′ v″ : Ne Ψ Γ T
  ψ ψ′ ψ″ : NfBranch n Ψ Γ T (Δ , T′)

-- Terms from layer 0 can be lifted to layer 1


mutual

  exp-lift : Exp zer Ψ Γ T → Exp one Ψ Γ T
  exp-lift (var Ψwf Γwf T∈Γ) = var Ψwf (wfs-lift Γwf) T∈Γ
  exp-lift (gvar δ T∈Ψ)      = gvar (lsubst-lift δ) T∈Ψ
  exp-lift (zero Ψwf Γwf)    = zero Ψwf (wfs-lift Γwf)
  exp-lift (succ t)          = exp-lift t
  exp-lift (recn s s′ t)     = recn (exp-lift s) (exp-lift s′) (exp-lift t)
  exp-lift (Λ t)             = Λ (exp-lift t)
  exp-lift (t $ s)           = exp-lift t $ exp-lift s

  lsubst-lift : LSubst zer Ψ Γ Δ → LSubst one Ψ Γ Δ
  lsubst-lift ([] Ψwf Γwf)   = [] Ψwf (wfs-lift Γwf)
  lsubst-lift (t ∷ δ) = exp-lift t ∷ lsubst-lift δ

exp-lift′ : Exp zer Ψ Γ T → Exp i Ψ Γ T
exp-lift′ {i = zer} t = t
exp-lift′ {i = one} t = exp-lift t


-- Syntactic validity
--
-- A well-typed term (nf, ne, resp.) must have valid contexts and type.
-----------------------------------------------------------------------

mutual

  validity : ∀ i → Exp i Ψ Γ T → gwfs? Ψ × wfs? i Γ × wf? i T
  validity i (var Ψwf Γwf T∈Γ)    = Ψwf , Γwf , lookup Γwf T∈Γ
  validity i (gvar δ T∈Ψ)
    with lsubst-validity _ δ
  ...  | Ψwf , Γwf , Δwf          = Ψwf , Γwf , wf-lift′ (proj₂ (lookup Ψwf T∈Ψ))
  validity i (zero Ψwf Γwf)       = Ψwf , Γwf , N
  validity i (succ t)             = validity i t
  validity i (recn s s′ t)        = validity i s
  validity i (Λ t)
    with validity _ t
  ...  | Ψwf , S ∷ Γwf , T        = Ψwf , Γwf , S ⟶ T
  validity i (t $ s)
    with validity _ t
  ...  | Ψwf , Γwf , S ⟶ T        = Ψwf , Γwf , T
  validity .one (box Γwf t)
    with validity _ t
  ...  | Ψwf , Δwf , T            = Ψwf , Γwf , □ Δwf T
  validity .one (letb s t)
    with validity _ t
  ... | _ ∷ Ψwf , Δwf , T         = Ψwf , Δwf , T
  validity .one (mat t bs)
    with validity _ t | bs
  ...  | Ψwf , Δwf , _
       | bsN _ (bzero _ t′) _ _ _ = Ψwf , Δwf , proj₂ (proj₂ (validity _ t′))
  ...  | Ψwf , Δwf , _
       | bs⟶ _ (bΛ t′) _ _        = Ψwf , Δwf , proj₂ (proj₂ (validity _ t′))

  lsubst-validity : ∀ i → LSubst i Ψ Γ Δ → gwfs? Ψ × wfs? i Γ × wfs? i Δ
  lsubst-validity i ([] Ψwf Γwf) = Ψwf , Γwf , []
  lsubst-validity i (t ∷ δ)
    with validity _ t | lsubst-validity _ δ
  ...  | Ψwf , Γwf , T | _ , _ , Δwf = Ψwf , Γwf , T ∷ Δwf


mutual
  nf-validity : Nf Ψ Γ T → gwfs? Ψ × types? Γ × type? T
  nf-validity (zero Ψwf Γwf) = Ψwf , Γwf , N
  nf-validity (succ w)       = nf-validity w
  nf-validity (Λ w)
    with nf-validity w
  ...  | Ψwf , S ∷ Γwf , T   = Ψwf , Γwf , S ⟶ T
  nf-validity (box Γwf t)
    with validity _ t
  ...  | Ψwf , Δwf , T       = Ψwf , Γwf , □ Δwf T
  nf-validity (ne v)         = ne-validity v

  ne-validity : Ne Ψ Γ T → gwfs? Ψ × types? Γ × type? T
  ne-validity (var Ψwf Γwf T∈Γ)  = Ψwf , Γwf , lookup Γwf T∈Γ
  ne-validity (gvar θ T∈Ψ)
    with nflsubst-validity θ
  ...  | Ψwf , Γwf , Δwf         = Ψwf , Γwf , wf-lift (proj₂ (lookup Ψwf T∈Ψ))
  ne-validity (recn w w′ v)      = nf-validity w
  ne-validity (v $ w)
    with ne-validity v
  ...  | Ψwf , Γwf , _ ⟶ T       = Ψwf , Γwf , T
  ne-validity (letb v w)
    with nf-validity w
  ...  | _ ∷ Ψwf , Δwf , T       = Ψwf , Δwf , T
  ne-validity (mat v bs)
    with ne-validity v | bs
  ...  | Ψwf , Γwf , T
       | bsN _ (bzero _ w) _ _ _ = Ψwf , Γwf , proj₂ (proj₂ (nf-validity w))
  ...  | Ψwf , Γwf , T
       | bs⟶ _ (bΛ w) _ _        = Ψwf , Γwf , proj₂ (proj₂ (nf-validity w))
  ne-validity (matbox δ T∈Ψ bs)
    with lsubst-validity _ δ | bs
  ...  | Ψwf , Γwf , Δwf
       | bsN _ (bzero _ w) _ _ _
       with nf-validity w
  ...     | _ , Γwf , T          = Ψwf , Γwf , T
  ne-validity (matbox δ T∈Ψ bs)
       | Ψwf , Γwf , Δwf
       | bs⟶ _ (bΛ w) _ _
       with nf-validity w
  ...     | _ , Γwf , T          = Ψwf , Γwf , T

  nflsubst-validity : NfLSubst Ψ Γ Δ → gwfs? Ψ × types? Γ × types? Δ
  nflsubst-validity ([] Ψwf Γwf) = Ψwf , Γwf , []
  nflsubst-validity (w ∷ θ)
    with nf-validity w | nflsubst-validity θ
  ...  | Ψwf , Γwf , T | _ , _ , Δwf = Ψwf , Γwf , T ∷ Δwf


-- Definition of weakenings
--
-- In simple types, we modularize weakenings for global and local contexts.
---------------------------------------------------------------------------

module _ {A : Set} (P : A → Set) where

  data Wk : List A → List A → Set where
    ε  : Wk [] []
    p  : ∀ {x xs ys} →
         P x →
         Wk xs ys →
         ----------------
         Wk (x ∷ xs) ys
    q  : ∀ {x xs ys} →
         P x →
         Wk xs ys →
         --------------------
         Wk (x ∷ xs) (x ∷ ys)


  -- Validity for weakenings
  --------------------------

  wk-validity : ∀ {xs ys} → Wk xs ys → All P xs × All P ys
  wk-validity ε    = [] , []
  wk-validity (p Px wk)
    with wk-validity wk
  ...  | Pxs , Pys = Px ∷ Pxs , Pys
  wk-validity (q Px wk)
    with wk-validity wk
  ...  | Pxs , Pys = Px ∷ Pxs , Px ∷ Pys


  -- Identity and composition of weakenings
  -----------------------------------------

  idwk : ∀ {xs} → All P xs → Wk xs xs
  idwk []         = ε
  idwk (px ∷ Pxs) = q px (idwk Pxs)

  wk-comp : ∀ {xs ys zs} → Wk xs ys → Wk zs xs → Wk zs ys
  wk-comp ε wk′               = wk′
  wk-comp (p px wk) (q _ wk′) = p px (wk-comp wk wk′)
  wk-comp (q px wk) (q _ wk′) = q px (wk-comp wk wk′)
  wk-comp wk (p px wk′)       = p px (wk-comp wk wk′)

  wk-lookup : ∀ {x xs ys} → x ∈ xs → Wk ys xs → x ∈ ys
  wk-lookup x∈xs (p py wk)      = 1+ (wk-lookup x∈xs wk)
  wk-lookup 0d (q px wk)        = 0d
  wk-lookup (1+ x∈xs) (q py wk) = 1+ (wk-lookup x∈xs wk)


infixl 3 _∘w_
_∘w_ : ∀ {A} {P : A → Set} {xs ys zs} → Wk P xs ys → Wk P zs xs → Wk P zs ys
_∘w_ = wk-comp _


GWk = Wk gwf?

LWk : Layer → LCtx → LCtx → Set
LWk i = Wk (wf? i)


variable
  γ γ′ γ″ : GWk Ψ Φ
  τ τ′ τ″ : LWk i Γ Δ


gwk-validity : GWk Ψ Φ → gwfs? Ψ × gwfs? Φ
gwk-validity = wk-validity _

lwk-validity : LWk i Γ Δ → wfs? i Γ × wfs? i Δ
lwk-validity = wk-validity _


-- Weakening applications
-------------------------

instance
  ∈-gwk-mono : Monotone (λ Ψ → (Δ , T) ∈ Ψ) GWk
  ∈-gwk-mono = record { _[_] = wk-lookup gwf? }

  ∈-lwk-mono : Monotone (λ Γ → T ∈ Γ) (LWk i)
  ∈-lwk-mono = record { _[_] = wk-lookup (wf? _) }


mutual
  gwk : Exp i Ψ Γ T → GWk Φ Ψ → Exp i Φ Γ T
  gwk (var Ψwf Γwf T∈Γ) γ           = var (proj₁ (gwk-validity γ)) Γwf T∈Γ
  gwk (gvar δ T∈Ψ) γ                = gvar (lsubst-gwk δ γ) (T∈Ψ [ γ ])
  gwk (zero Ψwf Γwf) γ              = zero (proj₁ (gwk-validity γ)) Γwf
  gwk (succ t) γ                    = succ (gwk t γ)
  gwk (recn s s′ t) γ               = recn (gwk s γ) (gwk s′ γ) (gwk t γ)
  gwk (Λ t) γ                       = Λ (gwk t γ)
  gwk (t $ s) γ                     = gwk t γ $ gwk s γ
  gwk (box Δwf t) γ                 = box Δwf (gwk t γ)
  gwk (letb s t) γ
    with validity _ s
  ...  | _ , _ , □ Δwf Twf          = letb (gwk s γ) (gwk t (q (Δwf , Twf) γ))
  gwk (mat t (bsN bv bz bs b br)) γ = mat (gwk t γ) (bsN (branch-gwk bv γ) (branch-gwk bz γ) (branch-gwk bs γ) (branch-gwk b γ) (branch-gwk br γ))
  gwk (mat t (bs⟶ bv bl b br)) γ    = mat (gwk t γ) (bs⟶ (branch-gwk bv γ) (branch-gwk bl γ) (branch-gwk b γ) (branch-gwk br γ))

  lsubst-gwk : LSubst i Ψ Γ Δ → GWk Φ Ψ → LSubst i Φ Γ Δ
  lsubst-gwk ([] Ψwf Γwf) γ = [] (proj₁ (gwk-validity γ)) Γwf
  lsubst-gwk (t ∷ θ) γ      = gwk t γ ∷ lsubst-gwk θ γ

  branch-gwk : Branch n Ψ Γ T (Δ , T′) → GWk Φ Ψ → Branch n Φ Γ T (Δ , T′)
  branch-gwk (bvar Δwf t) γ       = bvar Δwf (λ T′∈ → (gwk (t T′∈) γ))
  branch-gwk (bzero Δwf t) γ      = bzero Δwf (gwk t γ)
  branch-gwk (bsucc t) γ
    with validity _ t
  ...  | ΔN ∷ _ , _               = bsucc (gwk t (q ΔN γ))
  branch-gwk (bΛ t) γ
    with validity _ t
  ...  | ΔST ∷ _ , _              = bΛ (gwk t (q ΔST γ))
  branch-gwk (b$ {Δ} t) γ         = b$ helper
    where helper : core? S → Exp one ((Δ , S) ∷ (Δ , S ⟶ _) ∷ _) _ _
          helper S
            with validity _ (t S)
          ...  | ΔS ∷ ΔST ∷ _ , _ = gwk (t S) (q ΔS (q ΔST γ))
  branch-gwk (brec t) γ
    with validity _ t
  ...  | ΔN ∷ Δsu ∷ Δze ∷ _ , _   = brec (gwk t (q ΔN (q Δsu (q Δze γ))))

instance
  gwk-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GWk
  gwk-mono = record { _[_] = gwk }

  lsubst-gwk-mono : Monotone (λ Ψ → LSubst i Ψ Γ Δ) GWk
  lsubst-gwk-mono = record { _[_] = lsubst-gwk }

mutual

  nf-gwk : Nf Ψ Γ T → GWk Φ Ψ → Nf Φ Γ T
  nf-gwk (zero Ψwf Γwf) γ = zero (proj₁ (gwk-validity γ)) Γwf
  nf-gwk (succ w) γ       = succ (nf-gwk w γ)
  nf-gwk (Λ w) γ          = Λ (nf-gwk w γ)
  nf-gwk (box Δwf t) γ    = box Δwf (t [ γ ])
  nf-gwk (ne v) γ         = ne (ne-gwk v γ)

  ne-gwk : Ne Ψ Γ T → GWk Φ Ψ → Ne Φ Γ T
  ne-gwk (var Ψwf Γwf T∈Γ) γ                  = var (proj₁ (gwk-validity γ)) Γwf T∈Γ
  ne-gwk (gvar θ T∈Ψ) γ                       = gvar (nflsubst-gwk θ γ) (T∈Ψ [ γ ])
  ne-gwk (recn w w′ v) γ                      = recn (nf-gwk w γ) (nf-gwk w′ γ) (ne-gwk v γ)
  ne-gwk (v $ w) γ                            = ne-gwk v γ $ nf-gwk w γ
  ne-gwk (letb v w) γ
    with ne-validity v
  ...  | _ , _ , □ Δwf Twf                    = letb (ne-gwk v γ) (nf-gwk w (q (Δwf , Twf) γ))
  ne-gwk (mat v (bsN bv bz bs b br)) γ        = mat (ne-gwk v γ) (bsN (nfbranch-gwk bv γ) (nfbranch-gwk bz γ) (nfbranch-gwk bs γ) (nfbranch-gwk b γ) (nfbranch-gwk br γ))
  ne-gwk (mat v (bs⟶ bv bl b br)) γ           = mat (ne-gwk v γ) (bs⟶ (nfbranch-gwk bv γ) (nfbranch-gwk bl γ) (nfbranch-gwk b γ) (nfbranch-gwk br γ))
  ne-gwk (matbox δ T∈Ψ (bsN bv bz bs b br)) γ = matbox (δ [ γ ]) (T∈Ψ [ γ ]) (bsN (nfbranch-gwk bv γ) (nfbranch-gwk bz γ) (nfbranch-gwk bs γ) (nfbranch-gwk b γ) (nfbranch-gwk br γ))
  ne-gwk (matbox δ T∈Ψ (bs⟶ bv bl b br)) γ    = matbox (δ [ γ ]) (T∈Ψ [ γ ]) (bs⟶ (nfbranch-gwk bv γ) (nfbranch-gwk bl γ) (nfbranch-gwk b γ) (nfbranch-gwk br γ))

  nflsubst-gwk : NfLSubst Ψ Γ Δ → GWk Φ Ψ → NfLSubst Φ Γ Δ
  nflsubst-gwk ([] Ψwf Γwf) γ = [] (proj₁ (gwk-validity γ)) Γwf
  nflsubst-gwk (w ∷ θ) γ      = nf-gwk w γ ∷ nflsubst-gwk θ γ

  nfbranch-gwk : NfBranch n Ψ Γ T (Δ , T′) → GWk Φ Ψ → NfBranch n Φ Γ T (Δ , T′)
  nfbranch-gwk (bvar Δwf w) γ  = bvar Δwf (λ T′∈ → nf-gwk (w T′∈) γ)
  nfbranch-gwk (bzero Δwf w) γ = bzero Δwf (nf-gwk w γ)
  nfbranch-gwk (bsucc w) γ
    with nf-validity w
  ...  | ΔN ∷ _ , _          = bsucc (nf-gwk w (q ΔN γ))
  nfbranch-gwk (bΛ w) γ
    with nf-validity w
  ...  | ΔST ∷ _ , _         = bΛ (nf-gwk w (q ΔST γ))
  nfbranch-gwk (b$ {Δ} w) γ  = b$ helper
    where helper : core? S → Nf ((Δ , S) ∷ (Δ , S ⟶ _) ∷ _) _ _
          helper S
            with nf-validity (w S)
          ...  | ΔS ∷ ΔST ∷ _ , _ = nf-gwk (w S) (q ΔS (q ΔST γ))
  nfbranch-gwk (brec w) γ
    with nf-validity w
  ...  | ΔN ∷ Δsu ∷ Δze ∷ _ , _   = brec (nf-gwk w (q ΔN (q Δsu (q Δze γ))))

instance
  nf-gwk-mono : Monotone (λ Ψ → Nf Ψ Γ T) GWk
  nf-gwk-mono = record { _[_] = nf-gwk }

  ne-gwk-mono : Monotone (λ Ψ → Ne Ψ Γ T) GWk
  ne-gwk-mono = record { _[_] = ne-gwk }

  nflsubst-gwk-mono : Monotone (λ Ψ → NfLSubst Ψ Γ Δ) GWk
  nflsubst-gwk-mono = record { _[_] = nflsubst-gwk }


mutual
  lwk : Exp i Ψ Γ T → LWk i Δ Γ → Exp i Ψ Δ T
  lwk (var Ψwf Γwf T∈Γ) τ           = var Ψwf (proj₁ (lwk-validity τ)) (T∈Γ [ τ ])
  lwk (gvar δ T∈Ψ) τ                = gvar (lsubst-lwk δ τ) T∈Ψ
  lwk (zero Ψwf Γwf) τ              = zero Ψwf (proj₁ (lwk-validity τ))
  lwk (succ t) τ                    = succ (lwk t τ)
  lwk (recn s s′ t) τ
    with validity _ s
  ...  | _ , _ , Twf                = recn (lwk s τ) (lwk s′ (q Twf (q N τ))) (lwk t τ)
  lwk (Λ t) τ
    with validity _ t
  ...  | _ , S ∷ _ , _              = Λ (lwk t (q S τ))
  lwk (t $ s) τ                     = lwk t τ $ lwk s τ
  lwk (box Δ′wf t) τ                = box (proj₁ (lwk-validity τ)) t
  lwk (letb s t) τ                  = letb (lwk s τ) (lwk t τ)
  lwk (mat t (bsN bv bz bs b br)) τ = mat (lwk t τ) (bsN (branch-lwk bv τ) (branch-lwk bz τ) (branch-lwk bs τ) (branch-lwk b τ) (branch-lwk br τ))
  lwk (mat t (bs⟶ bv bl b br)) τ    = mat (lwk t τ) (bs⟶ (branch-lwk bv τ) (branch-lwk bl τ) (branch-lwk b τ) (branch-lwk br τ))

  lsubst-lwk : LSubst i Ψ Γ Δ′ → LWk i Δ Γ → LSubst i Ψ Δ Δ′
  lsubst-lwk ([] Ψwf Γwf) τ = [] Ψwf (proj₁ (lwk-validity τ))
  lsubst-lwk (t ∷ δ) τ      = lwk t τ ∷ lsubst-lwk δ τ

  branch-lwk : Branch n Ψ Γ T (Δ′ , T′) → LWk one Δ Γ → Branch n Ψ Δ T (Δ′ , T′)
  branch-lwk (bvar Δ′wf t) τ  = bvar Δ′wf (λ T′∈ → lwk (t T′∈) τ)
  branch-lwk (bzero Δ′wf t) τ = bzero Δ′wf (lwk t τ)
  branch-lwk (bsucc t) τ      = bsucc (lwk t τ)
  branch-lwk (bΛ t) τ         = bΛ (lwk t τ)
  branch-lwk (b$ t) τ         = b$ λ S → lwk (t S) τ
  branch-lwk (brec t) τ       = brec (lwk t τ)

instance
  lwk-mono : Monotone (λ Γ → Exp i Ψ Γ T) (LWk i)
  lwk-mono = record { _[_] = lwk }

  lsubst-lwk-mono : Monotone (λ Γ → LSubst i Ψ Γ Δ) (LWk i)
  lsubst-lwk-mono = record { _[_] = lsubst-lwk }


mutual
  nf-lwk : Nf Ψ Γ T → LWk one Δ Γ → Nf Ψ Δ T
  nf-lwk (zero Ψwf Γwf) τ = zero Ψwf (proj₁ (lwk-validity τ))
  nf-lwk (succ w) τ       = succ (nf-lwk w τ)
  nf-lwk (Λ w) τ
    with nf-validity w
  ...  | _ , S ∷ _ , _    = Λ (nf-lwk w (q S τ))
  nf-lwk (box Δwf t) τ    = box (proj₁ (lwk-validity τ)) t
  nf-lwk (ne v) τ         = ne (ne-lwk v τ)

  ne-lwk : Ne Ψ Γ T → LWk one Δ Γ → Ne Ψ Δ T
  ne-lwk (var Ψwf Γwf T∈Γ) τ                  = var Ψwf (proj₁ (lwk-validity τ)) (T∈Γ [ τ ])
  ne-lwk (gvar θ T∈Ψ) τ                       = gvar (nflsubst-lwk θ τ) T∈Ψ
  ne-lwk (recn w w′ v) τ
    with nf-validity w
  ...  | _ , _ , Twf                          = recn (nf-lwk w τ) (nf-lwk w′ (q Twf (q N τ))) (ne-lwk v τ)
  ne-lwk (letb v w) τ                         = letb (ne-lwk v τ) (nf-lwk w τ)
  ne-lwk (v $ w) τ                            = ne-lwk v τ $ nf-lwk w τ
  ne-lwk (mat v (bsN bv bz bs b br)) τ        = mat (ne-lwk v τ) (bsN (nfbranch-lwk bv τ) (nfbranch-lwk bz τ) (nfbranch-lwk bs τ) (nfbranch-lwk b τ) (nfbranch-lwk br τ))
  ne-lwk (mat v (bs⟶ bv bl b br)) τ           = mat (ne-lwk v τ) (bs⟶ (nfbranch-lwk bv τ) (nfbranch-lwk bl τ) (nfbranch-lwk b τ) (nfbranch-lwk br τ))
  ne-lwk (matbox δ T∈Ψ (bsN bv bz bs b br)) τ = matbox δ T∈Ψ (bsN (nfbranch-lwk bv τ) (nfbranch-lwk bz τ) (nfbranch-lwk bs τ) (nfbranch-lwk b τ) (nfbranch-lwk br τ))
  ne-lwk (matbox δ T∈Ψ (bs⟶ bv bl b br)) τ    = matbox δ T∈Ψ (bs⟶ (nfbranch-lwk bv τ) (nfbranch-lwk bl τ) (nfbranch-lwk b τ) (nfbranch-lwk br τ))

  nflsubst-lwk : NfLSubst Ψ Γ Δ′ → LWk one Δ Γ → NfLSubst Ψ Δ Δ′
  nflsubst-lwk ([] Ψwf Γwf) τ = [] Ψwf (proj₁ (lwk-validity τ))
  nflsubst-lwk (w ∷ θ) τ      = nf-lwk w τ ∷ nflsubst-lwk θ τ

  nfbranch-lwk : NfBranch n Ψ Γ T (Δ′ , T′) → LWk one Δ Γ → NfBranch n Ψ Δ T (Δ′ , T′)
  nfbranch-lwk (bvar Δ′wf w) τ  = bvar Δ′wf (λ T′∈ → nf-lwk (w T′∈) τ)
  nfbranch-lwk (bzero Δ′wf w) τ = bzero Δ′wf (nf-lwk w τ)
  nfbranch-lwk (bsucc w) τ      = bsucc (nf-lwk w τ)
  nfbranch-lwk (bΛ w) τ         = bΛ (nf-lwk w τ)
  nfbranch-lwk (b$ {Δ} w) τ     = b$ λ S → nf-lwk (w S) τ
  nfbranch-lwk (brec w) τ       = brec (nf-lwk w τ)

-- Weakenings between pairs of global and local contexts
--
-- This is the base category the presheaf model lives in.
---------------------------------------------------

AWk : GCtx × LCtx → GCtx × LCtx → Set
AWk (Ψ , Γ) (Φ , Δ) = GWk Ψ Φ × LWk one Γ Δ

awk-validity : AWk (Ψ , Γ) (Φ , Δ) → (gwfs? Ψ × types? Γ) × gwfs? Φ × types? Δ
awk-validity (γ , τ) = (proj₁ (gwk-validity γ) , proj₁ (lwk-validity τ)) , proj₂ (gwk-validity γ) , proj₂ (lwk-validity τ)


-- Identity and composition of weakenings
-----------------------------------------

idawk : gwfs? Ψ → types? Γ → AWk (Ψ , Γ) (Ψ , Γ)
idawk Ψwf Γwf = idwk _ Ψwf , idwk _ Γwf


infixl 3 _∘a_
_∘a_ : AWk (Ψ′ , Γ′) (Ψ , Γ) → AWk (Ψ″ , Γ″) (Ψ′ , Γ′) → AWk (Ψ″ , Γ″) (Ψ , Γ)
(γ , τ) ∘a (γ′ , τ′) = (γ ∘w γ′) , (τ ∘w τ′)


-- Applications of weakenings
-----------------------------

awk-nf : Nf Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Nf Φ Δ T
awk-nf w (γ , τ) = nf-lwk (w [ γ ]) τ

awk-ne : Ne Ψ Γ T → AWk (Φ , Δ) (Ψ , Γ) → Ne Φ Δ T
awk-ne w (γ , τ) = ne-lwk (w [ γ ]) τ

instance
  awk-nf-mono : Monotone (λ (Ψ , Γ) → Nf Ψ Γ T) AWk
  awk-nf-mono = record { _[_] = awk-nf }

  awk-ne-mono : Monotone (λ (Ψ , Γ) → Ne Ψ Γ T) AWk
  awk-ne-mono = record { _[_] = awk-ne }


-- Local substitutions
----------------------

lsubst-lookup : LSubst i Ψ Γ Δ → T ∈ Δ → Exp i Ψ Γ T
lsubst-lookup (t ∷ δ) 0d = t
lsubst-lookup (t ∷ δ) (1+ T∈Δ) = lsubst-lookup δ T∈Δ


mutual

  lsubst : Exp i Ψ Γ T → LSubst i Ψ Δ Γ → Exp i Ψ Δ T
  lsubst (var Ψwf Γwf T∈Γ) δ           = lsubst-lookup δ T∈Γ
  lsubst (gvar δ′ T∈Ψ) δ               = gvar (lsubst-comp δ′ δ) T∈Ψ
  lsubst (zero Ψwf Γwf) δ              = zero Ψwf (proj₁ (proj₂ (lsubst-validity _ δ)))
  lsubst (succ t) δ                    = succ (lsubst t δ)
  lsubst (recn s s′ t) δ
    with validity _ s | lsubst-validity _ δ
  ...  | Ψwf , _ , Twf
       | _ , Δwf , _                   = recn (lsubst s δ) (lsubst s′ (var Ψwf TNΔ 0d ∷ var Ψwf TNΔ 1d ∷ δ [ p Twf (p N (idwk _ Δwf)) ])) (lsubst t δ)
    where TNΔ                          = Twf ∷ N ∷ Δwf
  lsubst (Λ t) δ
    with validity _ t | lsubst-validity _ δ
  ...  | Ψwf , S ∷ _ , _
       | _ , Δwf , _                   = Λ (lsubst t (var Ψwf (S ∷ Δwf) 0d ∷ δ [ p S (idwk _ Δwf) ]))
  lsubst (t $ s) δ                     = lsubst t δ $ lsubst s δ
  lsubst (box Δ′wf t) δ                = box (proj₁ (proj₂ (lsubst-validity _ δ))) t
  lsubst (letb s t) δ
    with validity _ t
  ...  | Δ′Twf ∷ Ψwf , _               = letb (lsubst s δ) (lsubst t (δ [ p Δ′Twf (idwk _ Ψwf) ]))
  lsubst (mat t (bsN bv bz bs b br)) δ = mat (lsubst t δ) (bsN (branch-lsubst bv δ) (branch-lsubst bz δ) (branch-lsubst bs δ) (branch-lsubst b δ) (branch-lsubst br δ))
  lsubst (mat t (bs⟶ bv bl b br)) δ    = mat (lsubst t δ) (bs⟶ (branch-lsubst bv δ) (branch-lsubst bl δ) (branch-lsubst b δ) (branch-lsubst br δ))

  lsubst-comp : LSubst i Ψ Γ Δ′ → LSubst i Ψ Δ Γ → LSubst i Ψ Δ Δ′
  lsubst-comp ([] Ψwf Γwf) δ = [] Ψwf (proj₁ (proj₂ (lsubst-validity _ δ)))
  lsubst-comp (t ∷ δ′) δ     = lsubst t δ ∷ lsubst-comp δ′ δ

  branch-lsubst : Branch n Ψ Γ T (Δ′ , T′) → LSubst one Ψ Δ Γ → Branch n Ψ Δ T (Δ′ , T′)
  branch-lsubst (bvar Δ′wf t) δ     = bvar Δ′wf (λ T′∈ → lsubst (t T′∈) δ)
  branch-lsubst (bzero Δ′wf t) δ    = bzero Δ′wf (lsubst t δ)
  branch-lsubst (bsucc t) δ
    with validity _ t
  ...  | Δ′Nwf ∷ Ψwf , _            = bsucc (lsubst t (δ [ p Δ′Nwf (idwk _ Ψwf) ]))
  branch-lsubst (bΛ t) δ
    with validity _ t
  ...  | Δ′STwf ∷ Ψwf , _           = bΛ (lsubst t (δ [ p Δ′STwf (idwk _ Ψwf) ]))
  branch-lsubst (b$ t) δ            = b$ helper
    where helper : core? S → Exp one ((_ , S) ∷ (_ , S ⟶ _) ∷ _) _ _
          helper S
            with validity _ (t S)
          ...  | ΔS ∷ ΔST ∷ Δwf , _ = lsubst (t S) (δ [ p ΔS (p ΔST (idwk _ Δwf)) ])
  branch-lsubst (brec t) δ
    with validity _ t
  ...  | ΔN ∷ ΔNT ∷ ΔT ∷ Ψwf , _    = brec (lsubst t (δ [ p ΔN (p ΔNT (p ΔT (idwk _ Ψwf))) ]))

instance
  lsubst-mono : Monotone (λ Γ → Exp i Ψ Γ T) (LSubst i Ψ)
  lsubst-mono = record { _[_] = lsubst }


lsubst-id : gwfs? Ψ → wfs? i Γ → LSubst i Ψ Γ Γ
lsubst-id Ψwf []        = [] Ψwf []
lsubst-id Ψwf (T ∷ Γwf) = var Ψwf (T ∷ Γwf) 0d ∷ lsubst-id Ψwf Γwf [ p T (idwk _ Γwf) ]


-- Global substitutions
-----------------------

data GSubst : GCtx → GCtx → Set where
  [] : gwfs? Ψ → GSubst Ψ []
  _∷_ : Exp zer Ψ Γ T → GSubst Ψ Φ → GSubst Ψ ((Γ , T) ∷ Φ)

variable
  σ σ′ σ″ : GSubst Φ Ψ


-- Validity of global substitutions
-----------------------------------

gsubst-validity : GSubst Ψ Φ → gwfs? Ψ × gwfs? Φ
gsubst-validity ([] Ψwf)     = Ψwf , []
gsubst-validity (t ∷ σ)
  with gsubst-validity σ | validity _ t
...  | Ψwf , Φwf | _ , Γwf , T = Ψwf , (Γwf , T) ∷ Φwf


-- (Global) weakening of global substitutions
---------------------------------------------

gsubst-lookup : GSubst Ψ Φ → (Γ , T) ∈ Φ → Exp zer Ψ Γ T
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

mutual

  gsubst : Exp i Ψ Γ T → GSubst Φ Ψ → Exp i Φ Γ T
  gsubst (var Ψwf Γwf T∈Γ) σ           = var (proj₁ (gsubst-validity σ)) Γwf T∈Γ
  gsubst (gvar δ T∈Ψ) σ                = exp-lift′ (gsubst-lookup σ T∈Ψ) [ lsubst-gsubst δ σ ]
  gsubst (zero Ψwf Γwf) σ              = zero (proj₁ (gsubst-validity σ)) Γwf
  gsubst (succ t) σ                    = succ (gsubst t σ)
  gsubst (recn s s′ t) σ               = recn (gsubst s σ) (gsubst s′ σ) (gsubst t σ)
  gsubst (Λ t) σ                       = Λ (gsubst t σ)
  gsubst (t $ s) σ                     = gsubst t σ $ gsubst s σ
  gsubst (box Δwf t) σ                 = box Δwf (gsubst t σ)
  gsubst (letb s t) σ
    with validity _ t | gsubst-validity σ
  ...  | ΔT′ ∷ _ , _ | Φwf , _         = letb (gsubst s σ) (gsubst t (gvar (lsubst-id (ΔT′ ∷ Φwf) (proj₁ ΔT′)) 0d ∷ σ [ p ΔT′ (idwk _ Φwf) ]))
  gsubst (mat t (bsN bv bz bs b br)) σ = mat (gsubst t σ) (bsN (branch-gsubst bv σ) (branch-gsubst bz σ) (branch-gsubst bs σ) (branch-gsubst b σ) (branch-gsubst br σ))
  gsubst (mat t (bs⟶ bv bl b br)) σ    = mat (gsubst t σ) (bs⟶ (branch-gsubst bv σ) (branch-gsubst bl σ) (branch-gsubst b σ) (branch-gsubst br σ))

  lsubst-gsubst : LSubst i Ψ Γ Δ → GSubst Φ Ψ → LSubst i Φ Γ Δ
  lsubst-gsubst ([] Ψwf Γwf) σ = [] (proj₁ (gsubst-validity σ)) Γwf
  lsubst-gsubst (t ∷ δ) σ      = gsubst t σ ∷ lsubst-gsubst δ σ

  branch-gsubst : Branch n Ψ Γ T (Δ′ , T′) → GSubst Φ Ψ → Branch n Φ Γ T (Δ′ , T′)
  branch-gsubst (bvar Δ′wf t) σ  = bvar Δ′wf (λ T′∈ → gsubst (t T′∈) σ)
  branch-gsubst (bzero Δ′wf t) σ = bzero Δ′wf (gsubst t σ)
  branch-gsubst (bsucc t) σ
    with validity _ t | gsubst-validity σ
  ...  | ΔN ∷ _ , _ | Φwf , _    = bsucc (gsubst t (gvar (lsubst-id (ΔN ∷ Φwf) (proj₁ ΔN)) 0d ∷ (σ [ p ΔN (idwk _ Φwf) ])))
  branch-gsubst (bΛ t) σ
    with validity _ t | gsubst-validity σ
  ...  | ΔST ∷ _ , _ | Φwf , _   = bΛ (gsubst t (gvar (lsubst-id (ΔST ∷ Φwf) (proj₁ ΔST)) 0d ∷ σ [ p ΔST (idwk _ Φwf) ]))
  branch-gsubst (b$ t) σ         = b$ helper
    where helper : core? S → _
          helper S
            with validity _ (t S) | gsubst-validity σ
          ...  | ΔS ∷ ΔST ∷ _ , _ | Φwf , _ = gsubst (t S) ( gvar (lsubst-id (ΔS ∷ ΔST ∷ Φwf) (proj₁ ΔST)) 0d
                                                           ∷ gvar (lsubst-id (ΔS ∷ ΔST ∷ Φwf) (proj₁ ΔST)) 1d
                                                           ∷ σ [ p ΔS (p ΔST (idwk _ Φwf)) ])
  branch-gsubst (brec t) σ
    with validity _ t | gsubst-validity σ
  ...  | ΔN ∷ ΔNT ∷ ΔT ∷ _ , _ | Φwf , _    = brec (gsubst t (gvar lid₀ 0d ∷ gvar lid₁ 1d ∷ gvar lid₀ 2d
                                                             ∷ σ [ p ΔN (p ΔNT (p ΔT (idwk _ Φwf))) ]))
    where lid₀ = lsubst-id (ΔN ∷ ΔNT ∷ ΔT ∷ Φwf) (proj₁ ΔT)
          lid₁ = lsubst-id (ΔN ∷ ΔNT ∷ ΔT ∷ Φwf) (proj₁ ΔNT)

instance
  gsubst-mono : Monotone (λ Ψ → Exp i Ψ Γ T) GSubst
  gsubst-mono = record { _[_] = gsubst }

  lsubst-gsubst-mono : Monotone (λ Ψ → LSubst i Ψ Γ Δ) GSubst
  lsubst-gsubst-mono = record { _[_] = lsubst-gsubst }


-- Converting a global weakening to a global substitution
--------------------------------------------------

gwk-gsubst : GWk Ψ Φ → GSubst Ψ Φ
gwk-gsubst ε       = [] []
gwk-gsubst (p T γ) = gwk-gsubst γ [ p T (idwk _ (proj₁ (gwk-validity γ))) ]
gwk-gsubst (q T γ) = gvar (lsubst-id (T ∷ proj₁ (gwk-validity γ)) (proj₁ T)) 0d ∷ gwk-gsubst γ [ p T (idwk _ (proj₁ (gwk-validity γ))) ]

-- From this we can extract the identity global substitutions.

gid : gwfs? Ψ → GSubst Ψ Ψ
gid Ψwf = gwk-gsubst (idwk _ Ψwf)


-- Interpretations of types and contexts
----------------------------------------

⟦_⟧T : Typ → GCtx → LCtx → Set
⟦ N ⟧T Ψ Γ     = Nf Ψ Γ N
⟦ □ Δ T ⟧T Ψ Γ = Nf Ψ Γ (□ Δ T)
⟦ S ⟶ T ⟧T Ψ Γ = gwfs? Ψ × types? Γ × type? (S ⟶ T) × ∀ {Φ Δ} → AWk (Φ , Δ) (Ψ , Γ) → ⟦ S ⟧T Φ Δ → ⟦ T ⟧T Φ Δ

⟦_⟧G : GCtx → Layer → GCtx → Set
⟦ Φ ⟧G zer Ψ = GWk Ψ Φ
⟦ Φ ⟧G one Ψ = GSubst Ψ Φ

⟦_⟧L : LCtx → GCtx → LCtx → Set
⟦ [] ⟧L Ψ Γ    = gwfs? Ψ × types? Γ
⟦ T ∷ Δ ⟧L Ψ Γ = ⟦ T ⟧T Ψ Γ × ⟦ Δ ⟧L Ψ Γ

⟦_⟧A : GCtx × LCtx → Layer → GCtx → LCtx → Set
⟦ Φ , Δ ⟧A i Ψ Γ = ⟦ Φ ⟧G i Ψ × ⟦ Δ ⟧L Ψ Γ


-- validity of interpretations
------------------------------

T-validity : ∀ T → ⟦ T ⟧T Ψ Γ → gwfs? Ψ × types? Γ × type? T
T-validity N a                          = nf-validity a
T-validity (□ Δ T) a                    = nf-validity a
T-validity (S ⟶ T) (Ψwf , Γwf , ST , _) = Ψwf , Γwf , ST

G-validity : ∀ i → ⟦ Φ ⟧G i Ψ → gwfs? Φ × gwfs? Ψ
G-validity zer γ
  with gwk-validity γ
...  | Ψwf , Φwf = Φwf , Ψwf
G-validity one σ
  with gsubst-validity σ
...  | Ψwf , Φwf = Φwf , Ψwf

L-validity : ∀ Δ → ⟦ Δ ⟧L Ψ Γ → types? Δ × gwfs? Ψ × types? Γ
L-validity [] ρ        = [] , ρ
L-validity (T ∷ Δ) (a , ρ)
  with L-validity _ ρ
...  | Δwf , Ψwf , Γwf = proj₂ (proj₂ (T-validity T a)) ∷ Δwf , Ψwf , Γwf

A-validity : ⟦ Φ , Δ ⟧A i Ψ Γ → (gwfs? Φ × types? Δ) × gwfs? Ψ × types? Γ
A-validity (σ , ρ) = (proj₁ (G-validity _ σ) , proj₁ (L-validity _ ρ))
                   , proj₁ (proj₂ (L-validity _ ρ)) , proj₂ (proj₂ (L-validity _ ρ))


-- Monotonicity of interpretations
----------------------------------

T-mon : ∀ T → ⟦ T ⟧T Ψ Γ → AWk (Φ , Δ) (Ψ , Γ) → ⟦ T ⟧T Φ Δ
T-mon N a ξ                          = a [ ξ ]
T-mon (□ Δ′ T) a ξ                   = a [ ξ ]
T-mon (S ⟶ T) (Ψwf , Γwf , ST , f) ξ = proj₁ (proj₁ (awk-validity ξ)) , proj₂ (proj₁ (awk-validity ξ))
                                     , ST , λ ξ′ a → f (ξ ∘a ξ′) a


instance
  T-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ T ⟧T Ψ Γ) AWk
  T-mon-mono = record { _[_] = T-mon _ }

G-mon : ∀ i → ⟦ Φ ⟧G i Ψ → GWk Ψ′ Ψ → ⟦ Φ ⟧G i Ψ′
G-mon zer γ′ γ = γ′ ∘w γ
G-mon one σ γ  = σ [ γ ]


instance
  G-mon-mono : Monotone (⟦ Φ ⟧G i) GWk
  G-mon-mono = record { _[_] = G-mon _ }


L-mon : ∀ Γ′ → ⟦ Γ′ ⟧L Ψ Γ → AWk (Φ , Δ) (Ψ , Γ) → ⟦ Γ′ ⟧L Φ Δ
L-mon [] ρ ξ             = proj₁ (awk-validity ξ)
L-mon (T ∷ Γ′) (a , ρ) ξ = a [ ξ ] , L-mon Γ′ ρ ξ


instance
  L-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ Γ′ ⟧L Ψ Γ) AWk
  L-mon-mono = record { _[_] = L-mon _ }

  L-mon-mono′ : Monotone (λ Ψ → ⟦ Γ′ ⟧L Ψ Γ) GWk
  L-mon-mono′ = record { _[_] = λ ρ γ → L-mon _ ρ (γ , (idwk _ (proj₂ (proj₂ (L-validity _ ρ))))) }


A-mon : ⟦ Φ , Δ ⟧A i Ψ Γ → AWk (Ψ′ , Γ′) (Ψ , Γ) → ⟦ Φ , Δ ⟧A i Ψ′ Γ′
A-mon (σ , ρ) ξ@(γ , _) = σ [ γ ] , ρ [ ξ ]


instance
  A-mon-mono : Monotone (λ (Ψ , Γ) → ⟦ Φ , Δ ⟧A i Ψ Γ) AWk
  A-mon-mono = record { _[_] = A-mon }


-- Interpretation of expressions to natural transformations
-----------------------------------------------------------

L-lookup : T ∈ Δ → ⟦ Δ ⟧L Ψ Γ → ⟦ T ⟧T Ψ Γ
L-lookup 0d (a , _)       = a
L-lookup (1+ T∈Δ) (_ , ρ) = L-lookup T∈Δ ρ


mutual
  ↓ : ∀ T → ⟦ T ⟧T Ψ Γ → Nf Ψ Γ T
  ↓ N a                                 = a
  ↓ (□ Δ T) a                           = a
  ↓ (S ⟶ T) (Ψwf , Γwf , Swf ⟶ Twf , a) = Λ (↓ T (a (idwk _ Ψwf , p Swf (idwk _ Γwf)) (↑ S (var Ψwf (Swf ∷ Γwf) 0d))))

  ↑ : ∀ T → Ne Ψ Γ T → ⟦ T ⟧T Ψ Γ
  ↑ N v                        = ne v
  ↑ (□ Δ T) v                  = ne v
  ↑ (S ⟶ T) v
    with ne-validity v
  ...  | Ψwf , Γwf , Swf ⟶ Twf = Ψwf , Γwf , Swf ⟶ Twf
                               , λ ξ a → ↑ T ((v [ ξ ]) $ ↓ S a)

↓s : ∀ Δ → ⟦ Δ ⟧L Ψ Γ → NfLSubst Ψ Γ Δ
↓s [] ρ            = [] (proj₁ ρ) (proj₂ ρ)
↓s (T ∷ Δ) (a , ρ) = ↓ T a ∷ ↓s Δ ρ

-- For some reason, when we attempt to implement the following function
--
--    ⟦_;_⟧ : ∀ i → Exp i Φ Δ T → ⟦ Φ , Δ ⟧A i Ψ Γ → ⟦ T ⟧T Ψ Γ
--
-- by splitting on i and then Exp, Agda fails to realize that in the u1 case, i
-- actually decreases.
--
-- It seems that Agda considers Exp as the decreasing argument when i is an unifiable
-- argument.  For this reason, we are forced to interpret the expressions in two
-- separate functions according to their layers.

mutual

  ⟦_⟧0 : Exp zer Φ Δ T → ⟦ Φ , Δ ⟧A zer Ψ Γ → ⟦ T ⟧T Ψ Γ
  ⟦ var Φwf Δwf T∈Δ ⟧0 (γ , ρ)         = L-lookup T∈Δ ρ
  ⟦ gvar δ T∈Φ ⟧0 (γ , ρ)              = ↑ _ (gvar (↓s _ (⟦ δ ⟧0s (γ , ρ))) (T∈Φ [ γ ]))
  ⟦ zero Φwf Δwf ⟧0 (γ , ρ)
    with L-validity _ ρ
  ...  | _ , Ψwf , Γwf                 = zero Ψwf Γwf
  ⟦ succ t ⟧0 (γ , ρ)                  = succ (⟦ t ⟧0 (γ , ρ))
  ⟦ recn s s′ t ⟧0 (γ , ρ)             = rec0 s s′ (⟦ t ⟧0 (γ , ρ)) (γ , ρ)
  ⟦ Λ t ⟧0 (γ , ρ)
    with L-validity _ ρ | validity _ t
  ...  | _ , Ψwf , Γwf | _ , S ∷ _ , T = Ψwf , Γwf , wf-lift (S ⟶ T)
                                       , λ ξ@(γ′ , _) a → ⟦ t ⟧0 ((γ ∘w γ′) , a , ρ [ ξ ])
  ⟦ t $ s ⟧0 (γ , ρ)
    with ⟦ t ⟧0 (γ , ρ)
  ...  | Ψwf , Γwf , _ , f             = f (idawk Ψwf Γwf) (⟦ s ⟧0 (γ , ρ))

  ⟦_⟧0s : LSubst zer Φ Δ Δ′ → ⟦ Φ , Δ ⟧A zer Ψ Γ → ⟦ Δ′ ⟧L Ψ Γ
  ⟦ [] _ _ ⟧0s (γ , ρ) = proj₂ (L-validity _ ρ)
  ⟦ t ∷ δ ⟧0s (γ , ρ)  = ⟦ t ⟧0 (γ , ρ) , ⟦ δ ⟧0s (γ , ρ)

  rec0 : Exp zer Φ Δ T → Exp zer Φ (T ∷ N ∷ Δ) T → Nf Ψ Γ N → ⟦ Φ , Δ ⟧A zer Ψ Γ → ⟦ T ⟧T Ψ Γ
  rec0 s s′ (zero _ _) (γ , ρ)     = ⟦ s ⟧0 (γ , ρ)
  rec0 s s′ (succ w) (γ , ρ)       = ⟦ s′ ⟧0 (γ , rec0 s s′ w (γ , ρ) , w , ρ)
  rec0 s s′ (ne v) (γ , ρ)
    with L-validity _ ρ | validity _ s
  ...  | _ , Ψwf , Γwf | _ , _ , T = ↑ _ (recn (↓ _ (⟦ s ⟧0 (γ , ρ)))
                                               (↓ _ (⟦ s′ ⟧0 (γ , (↑ _ (var Ψwf (wf-lift T ∷ N ∷ Γwf) 0d)
                                                                  , ↑ _ (var Ψwf (wf-lift T ∷ N ∷ Γwf) 1d)
                                                                  , ρ [ idwk _ Ψwf
                                                                      , p (wf-lift T) (p N (idwk _ Γwf)) ]))))
                                               v)


mutual

  ⟦_⟧1 : Exp one Φ Δ T → ⟦ Φ , Δ ⟧A one Ψ Γ → ⟦ T ⟧T Ψ Γ
  ⟦ var Φwf Δwf T∈Δ ⟧1 (σ , ρ)          = L-lookup T∈Δ ρ
  ⟦ gvar δ T∈Φ ⟧1 (σ , ρ)
    with L-validity _ ρ
  ...  | _ , Ψwf , Γwf                  = ⟦ gsubst-lookup σ T∈Φ ⟧0 (idwk _ Ψwf , ⟦ δ ⟧1s (σ , ρ))
  ⟦ zero Φwf Δwf ⟧1 (σ , ρ)
    with L-validity _ ρ
  ...  | _ , Ψwf , Γwf                  = zero Ψwf Γwf
  ⟦ succ t ⟧1 (σ , ρ)                   = succ (⟦ t ⟧1 (σ , ρ))
  ⟦ recn s s′ t ⟧1 (σ , ρ)              = rec1 s s′ (⟦ t ⟧1 (σ , ρ)) (σ , ρ)
  ⟦ Λ t ⟧1 (σ , ρ)
    with L-validity _ ρ | validity _ t
  ...  | _ , Ψwf , Γwf | _ , S ∷ _ , T  = Ψwf , Γwf , S ⟶ T
                                       , λ ξ@(γ , _) a → ⟦ t ⟧1 (σ [ γ ] , a , ρ [ ξ ])
  ⟦ t $ s ⟧1 (σ , ρ)
    with ⟦ t ⟧1 (σ , ρ)
  ...  | Ψwf , Γwf , _ , f              = f (idawk Ψwf Γwf) (⟦ s ⟧1 (σ , ρ))
  ⟦ box Δ′wf t ⟧1 (σ , ρ)               = box (proj₂ (proj₂ (L-validity _ ρ))) (t [ σ ])
  ⟦ letb s t ⟧1 (σ , ρ)
    with ⟦ s ⟧1 (σ , ρ)
  ...  | box Δ′wf s                     = ⟦ t ⟧1 (s ∷ σ , ρ)
  ...  | ne v
       with L-validity _ ρ | validity _ t
  ...     | _ , Ψwf , Γwf | ΔT′ ∷ _ , _ = ↑ _ (letb v (↓ _ (⟦ t ⟧1 (gvar (lsubst-id (ΔT′ ∷ Ψwf) (proj₁ ΔT′)) 0d ∷ σ [ wk ] , ρ [ wk ]))))
    where wk = p ΔT′ (idwk _ Ψwf)
  ⟦ mat t bs ⟧1 (σ , ρ)
    with ⟦ t ⟧1 (σ , ρ) | bs
  ...  | ne v | bsN bv bz bs b br       = ↑ _ (mat v (bsN (nfbranch bv (σ , ρ)) (nfbranch bz (σ , ρ)) (nfbranch bs (σ , ρ)) (nfbranch b (σ , ρ)) (nfbranch br (σ , ρ))))
  ...  | ne v | bs⟶ bv bl b br          = ↑ _ (mat v (bs⟶ (nfbranch bv (σ , ρ)) (nfbranch bl (σ , ρ)) (nfbranch b (σ , ρ)) (nfbranch br (σ , ρ))))
  ...  | box Δ′wf s | bs                = match s bs (σ , ρ)

  ⟦_⟧1s : LSubst one Φ Δ Δ′ → ⟦ Φ , Δ ⟧A one Ψ Γ → ⟦ Δ′ ⟧L Ψ Γ
  ⟦ [] _ _ ⟧1s (γ , ρ) = proj₂ (L-validity _ ρ)
  ⟦ t ∷ δ ⟧1s (γ , ρ)  = ⟦ t ⟧1 (γ , ρ) , ⟦ δ ⟧1s (γ , ρ)

  rec1 : Exp one Φ Δ T → Exp one Φ (T ∷ N ∷ Δ) T → Nf Ψ Γ N → ⟦ Φ , Δ ⟧A one Ψ Γ → ⟦ T ⟧T Ψ Γ
  rec1 s s′ (zero _ _) (σ , ρ)     = ⟦ s ⟧1 (σ , ρ)
  rec1 s s′ (succ w) (σ , ρ)       = ⟦ s′ ⟧1 (σ , rec1 s s′ w (σ , ρ) , w , ρ)
  rec1 s s′ (ne v) (σ , ρ)
    with L-validity _ ρ | validity _ s
  ...  | _ , Ψwf , Σwf | _ , _ , T = ↑ _ (recn (↓ _ (⟦ s ⟧1 (σ , ρ)))
                                               (↓ _ (⟦ s′ ⟧1 (σ , (↑ _ (var Ψwf (T ∷ N ∷ Σwf) 0d)
                                                                  , ↑ _ (var Ψwf (T ∷ N ∷ Σwf) 1d)
                                                                  , ρ [ idwk _ Ψwf
                                                                      , p T (p N (idwk _ Σwf)) ]))))
                                               v)

  match : Exp zer Ψ Δ′ T′ → Branches Φ Δ T (Δ′ , T′) → ⟦ Φ , Δ ⟧A one Ψ Γ → ⟦ T ⟧T Ψ Γ
  match (var Ψwf Δ′wf T′∈Δ′) (bsN (bvar _ t) _ _ _ _) (σ , ρ) = ⟦ t T′∈Δ′ ⟧1 (σ , ρ)
  match (var Ψwf Δ′wf T′∈Δ′) (bs⟶ (bvar _ t) _ _ _) (σ , ρ)   = ⟦ t T′∈Δ′ ⟧1 (σ , ρ)
  match (zero Ψwf Δ′wf) (bsN _ (bzero _ t) _ _ _) (σ , ρ)     = ⟦ t ⟧1 (σ , ρ)
  match (succ s) (bsN _ _ (bsucc t) _ _) (σ , ρ)              = ⟦ t ⟧1 (s ∷ σ , ρ)
  match (recn s s′ s″) (bsN _ _ _ _ (brec t)) (σ , ρ)         = ⟦ t ⟧1 (s″ ∷ s′ ∷ s ∷ σ , ρ)
  match (recn s s′ s″) (bs⟶ _ _ _ (brec t)) (σ , ρ)           = ⟦ t ⟧1 (s″ ∷ s′ ∷ s ∷ σ , ρ)
  match (Λ s) (bs⟶ _ (bΛ t) _ _) (σ , ρ)                      = ⟦ t ⟧1 (s ∷ σ , ρ)
  match (s $ s′) (bsN _ _ _ (b$ t) _) (σ , ρ)
    with validity _ s
  ...  | _ , _ , S ⟶ _                                        = ⟦ t S ⟧1 (s′ ∷ s ∷ σ , ρ)
  match (s $ s′) (bs⟶ _ _ (b$ t) _) (σ , ρ)
    with validity _ s
  ...  | _ , _ , S ⟶ _                                        = ⟦ t S ⟧1 (s′ ∷ s ∷ σ , ρ)
  match (gvar δ T′∈Ψ) (bsN bv bz bs b br) (σ , ρ)             = ↑ _ (matbox δ T′∈Ψ (bsN (nfbranch bv (σ , ρ)) (nfbranch bz (σ , ρ)) (nfbranch bs (σ , ρ)) (nfbranch b (σ , ρ)) (nfbranch br (σ , ρ))))
  match (gvar δ T′∈Ψ) (bs⟶ bv bl b br) (σ , ρ)                = ↑ _ (matbox δ T′∈Ψ (bs⟶ (nfbranch bv (σ , ρ)) (nfbranch bl (σ , ρ)) (nfbranch b (σ , ρ)) (nfbranch br (σ , ρ))))

  nfbranch : Branch n Φ Δ T (Δ′ , T′) → ⟦ Φ , Δ ⟧A one Ψ Γ → NfBranch n Ψ Γ T (Δ′ , T′)
  nfbranch (bvar Δ′wf t) (σ , ρ)            = bvar Δ′wf (λ T′∈ → ↓ _ (⟦ t T′∈ ⟧1 (σ , ρ)))
  nfbranch (bzero Δ′wf t) (σ , ρ)           = bzero Δ′wf (↓ _ (⟦ t ⟧1 (σ , ρ)))
  nfbranch (bsucc t) (σ , ρ)
    with validity _ t | gsubst-validity σ
  ...  | ΔN ∷ _ , _ | Φwf , _               = bsucc (↓ _ (⟦ t ⟧1 (gvar (lsubst-id (ΔN ∷ Φwf) (proj₁ ΔN)) 0d ∷ σ [ wk ] , ρ [ wk ])))
    where wk = p ΔN (idwk _ Φwf)
  nfbranch (bΛ t) (σ , ρ)
    with validity _ t | gsubst-validity σ
  ...  | ΔST ∷ _ , _ | Φwf , _              = bΛ (↓ _ (⟦ t ⟧1 (gvar (lsubst-id (ΔST ∷ Φwf) (proj₁ ΔST)) 0d ∷ σ [ wk ] , ρ [ wk ])))
    where wk = p ΔST (idwk _ Φwf)
  nfbranch (brec t) (σ , ρ)
    with validity _ t | gsubst-validity σ
  ...  | ΔN ∷ ΔNT ∷ ΔT ∷ _ , _ | Φwf , _    = brec (↓ _ (⟦ t ⟧1 (gvar lid₀ 0d ∷ gvar lid₁ 1d ∷ gvar lid₀ 2d ∷ σ [ wk ] , ρ [ wk ])))
    where lid₀ = lsubst-id (ΔN ∷ ΔNT ∷ ΔT ∷ Φwf) (proj₁ ΔT)
          lid₁ = lsubst-id (ΔN ∷ ΔNT ∷ ΔT ∷ Φwf) (proj₁ ΔNT)
          wk   = p ΔN (p ΔNT (p ΔT (idwk _ Φwf)))
  nfbranch (b$ t) (σ , ρ)                   = b$ helper
    where helper : core? S → _
          helper S
            with validity _ (t S) | gsubst-validity σ
          ...  | ΔS ∷ ΔST ∷ _ , _ | Φwf , _ = ↓ _ (⟦ t S ⟧1 (gvar lid 0d ∷ gvar lid 1d ∷ σ [ wk ] , ρ [ wk ]))
            where wk  = p ΔS (p ΔST (idwk _ Φwf))
                  lid = lsubst-id (ΔS ∷ ΔST ∷ Φwf) (proj₁ ΔS)

-- Then we force a definition of ⟦_;_⟧ decreasing by layer i

⟦_;_⟧ : ∀ i → Exp i Φ Δ T → ⟦ Φ , Δ ⟧A i Ψ Γ → ⟦ T ⟧T Ψ Γ
⟦ zer ; t ⟧ = ⟦ t ⟧0
⟦ one ; t ⟧ = ⟦ t ⟧1


-- Definition of NbE
--------------------

↑L : gwfs? Ψ → types? Γ → ⟦ Γ ⟧L Ψ Γ
↑L Ψwf []        = Ψwf , []
↑L Ψwf (T ∷ Γwf) = ↑ _ (var Ψwf (T ∷ Γwf) 0d) , ↑L Ψwf Γwf [ idwk _ Ψwf , (p T (idwk _ Γwf)) ]

nbe : Exp one Ψ Γ T → Nf Ψ Γ T
nbe t
  with validity _ t
...  | Ψwf , Γwf , _ = ↓ _ (⟦ one ; t ⟧ (gid Ψwf , ↑L Ψwf Γwf))
