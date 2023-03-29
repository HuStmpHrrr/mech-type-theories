{-# OPTIONS --without-K --safe #-}

module CVar.Syntax where

open import Level hiding (zero; suc)

open import Lib public

-- A is monotonic relative to B
record Monotone {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  infixl 4.5 _[_]
  field
    _[_] : A → B → A

open Monotone {{...}} public


infixr 5 _⟶_ ctx⇒_

mutual

  -- types
  data Typ : Set where
    N     : Typ
    _⟶_   : Typ → Typ → Typ
    □     : LCtx → Typ → Typ
    ctx⇒_ : Typ → Typ

  data LCtx : Set where
    [] : LCtx
    cv : ℕ → LCtx
    _∷_ : Typ → LCtx → LCtx


-- a global binding
data Bnd : Set where
  ctx : Bnd
  _,_ : LCtx → Typ → Bnd


GCtx : Set
GCtx = List Bnd


data Layer : Set where
  𝟘 𝟙 : Layer


data Wk : Set where
  id  : Wk
  p q : Wk → Wk


Gwk = Wk

Lwk = Wk

infixl 3 _∘w_

_∘w_ : Wk → Wk → Wk
id ∘w γ′    = γ′
p γ ∘w q γ′ = p (γ ∘w γ′)
q γ ∘w q γ′ = q (γ ∘w γ′)
γ ∘w id     = γ
γ ∘w p γ′   = p (γ ∘w γ′)


∘w-id : ∀ γ → (γ ∘w id) ≡ γ
∘w-id id    = refl
∘w-id (p γ) = refl
∘w-id (q γ) = refl

∘w-p : ∀ γ γ′ → (γ ∘w p γ′) ≡ p (γ ∘w γ′)
∘w-p id γ′    = refl
∘w-p (p γ) γ′ = refl
∘w-p (q γ) γ′ = refl

∘w-assoc : ∀ γ γ′ γ″ → ((γ ∘w γ′) ∘w γ″) ≡ (γ ∘w (γ′ ∘w γ″))
∘w-assoc id γ′ γ″          = refl
∘w-assoc γ id γ″
  rewrite ∘w-id γ          = refl
∘w-assoc γ γ′ id
  rewrite ∘w-id (γ ∘w γ′)
        | ∘w-id γ′         = refl
∘w-assoc γ γ′ (p γ″)
  rewrite ∘w-p γ′ γ″
        | ∘w-p (γ ∘w γ′) γ″
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc γ (p γ′) (q γ″)
  rewrite ∘w-p γ γ′
        | ∘w-p γ (γ′ ∘w γ″)
        | ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (p γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl
∘w-assoc (q γ) (q γ′) (q γ″)
  rewrite ∘w-assoc γ γ′ γ″ = refl

wk-x : ℕ → Wk → ℕ
wk-x x id          = x
wk-x x (p γ)       = suc (wk-x x γ)
wk-x 0 (q γ)       = 0
wk-x (suc x) (q γ) = suc (wk-x x γ)

mutual

  gwk-ty : Typ → Gwk → Typ
  gwk-ty N γ        = N
  gwk-ty (S ⟶ T) γ  = gwk-ty S γ ⟶ gwk-ty T γ
  gwk-ty (□ Γ T) γ  = □ (gwk-lc Γ γ) (gwk-ty T γ)
  gwk-ty (ctx⇒ T) γ = ctx⇒ gwk-ty T (q γ)

  gwk-lc : LCtx → Gwk → LCtx
  gwk-lc [] γ       = []
  gwk-lc (cv x) γ   = cv (wk-x x γ)
  gwk-lc (T ∷ lc) γ = gwk-ty T γ ∷ gwk-lc lc γ

instance
  gwk-t-mon : Monotone Typ Gwk
  gwk-t-mon = record { _[_] = gwk-ty }

  gwk-lc-mon : Monotone LCtx Gwk
  gwk-lc-mon = record { _[_] = gwk-lc }


gwk-bnd : Bnd → Gwk → Bnd
gwk-bnd ctx γ = ctx
gwk-bnd (Γ , T) γ = Γ [ γ ] , T [ γ ]

instance
  gwk-bnd-mon : Monotone Bnd Gwk
  gwk-bnd-mon = record { _[_] = gwk-bnd }


-- Identity of Global Weakenings

gwk-id-x : ∀ n x → wk-x x (repeat q n id) ≡ x
gwk-id-x n zero    = helper n
  where helper : ∀ n → wk-x zero (repeat q n id) ≡ zero
        helper zero    = refl
        helper (suc n) = refl
gwk-id-x zero (suc x)  = refl
gwk-id-x (suc n) (suc x)
  rewrite gwk-id-x n x = refl

mutual
  gwk-id-ty : ∀ n (T : Typ) → T [ repeat q n id ] ≡ T
  gwk-id-ty _ N                 = refl
  gwk-id-ty n (S ⟶ T)
    rewrite gwk-id-ty n S
          | gwk-id-ty n T       = refl
  gwk-id-ty n (□ Γ T)
    rewrite gwk-id-lc n Γ
          | gwk-id-ty n T       = refl
  gwk-id-ty n (ctx⇒ T)
    rewrite gwk-id-ty (suc n) T = refl

  gwk-id-lc : ∀ n (Γ : LCtx) → Γ [ repeat q n id ] ≡ Γ
  gwk-id-lc n []          = refl
  gwk-id-lc n (cv x)
    rewrite gwk-id-x n x  = refl
  gwk-id-lc n (T ∷ Γ)
    rewrite gwk-id-ty n T
          | gwk-id-lc n Γ = refl


gwk-id-bnd : (B : Bnd) → B [ id ] ≡ B
gwk-id-bnd ctx          = refl
gwk-id-bnd (Γ , T)
  rewrite gwk-id-lc 0 Γ
        | gwk-id-ty 0 T = refl


variable
  i : Layer
  Ψ Ψ′ Ψ″ : GCtx
  Φ Φ′ Φ″ : GCtx
  Γ Γ′ Γ″ : LCtx
  Δ Δ′ Δ″ : LCtx
  T T′ T″ : Typ
  S S′ S″ : Typ
  γ γ′ γ″ : Gwk
  τ τ′ τ″ : Lwk
  x x′ x″ : ℕ


-- Composition of Global Weakenings

gwk-x-comp : ∀ x γ γ′ → wk-x (wk-x x γ) γ′ ≡ wk-x x (γ ∘w γ′)
gwk-x-comp x id γ′              = refl
gwk-x-comp x (p γ) id           = refl
gwk-x-comp x (p γ) (p γ′)
  rewrite gwk-x-comp x (p γ) γ′ = refl
gwk-x-comp x (p γ) (q γ′)
  rewrite gwk-x-comp x γ γ′     = refl
gwk-x-comp x (q γ) id           = refl
gwk-x-comp x (q γ) (p γ′)
  rewrite gwk-x-comp x (q γ) γ′ = refl
gwk-x-comp zero (q γ) (q γ′)    = refl
gwk-x-comp (suc x) (q γ) (q γ′)
  rewrite gwk-x-comp x γ γ′     = refl


mutual
  gwk-ty-comp : ∀ (T : Typ) γ γ′ → T [ γ ] [ γ′ ] ≡ T [ γ ∘w γ′ ]
  gwk-ty-comp N γ γ′                   = refl
  gwk-ty-comp (S ⟶ T) γ γ′
    rewrite gwk-ty-comp S γ γ′
          | gwk-ty-comp T γ γ′         = refl
  gwk-ty-comp (□ Γ T) γ γ′
    rewrite gwk-lc-comp Γ γ γ′
          | gwk-ty-comp T γ γ′         = refl
  gwk-ty-comp (ctx⇒ T) γ γ′
    rewrite gwk-ty-comp T (q γ) (q γ′) = refl

  gwk-lc-comp : ∀ (Γ : LCtx) γ γ′ → Γ [ γ ] [ γ′ ] ≡ Γ [ γ ∘w γ′ ]
  gwk-lc-comp [] γ γ′          = refl
  gwk-lc-comp (cv x) γ γ′
    rewrite gwk-x-comp x γ γ′  = refl
  gwk-lc-comp (T ∷ Γ) γ γ′
    rewrite gwk-ty-comp T γ γ′
          | gwk-lc-comp Γ γ γ′ = refl

gwk-bnd-comp : ∀ (B : Bnd) γ γ′ → B [ γ ] [ γ′ ] ≡ B [ γ ∘w γ′ ]
gwk-bnd-comp ctx γ γ′        = refl
gwk-bnd-comp (Γ , T) γ γ′
  rewrite gwk-lc-comp Γ γ γ′
        | gwk-ty-comp T γ γ′ = refl


infix 2 _∶_∈G_
data _∶_∈G_ : ℕ → Bnd → GCtx → Set where
  here  : ∀ {B} → 0 ∶ B [ p id ] ∈G B ∷ Ψ
  there : ∀ {B B′} → x ∶ B ∈G Ψ → suc x ∶ B [ p id ] ∈G B′ ∷ Ψ


infix 4 ⊢_ _⊢C[_]_ _⊢[_]_

mutual

  -- well-formedness of global contexts
  data ⊢_ : GCtx → Set where
    ⊢[]  : ⊢ []
    ⊢ctx : ⊢ Ψ → ⊢ ctx ∷ Ψ
    ⊢v   : Ψ ⊢C[ 𝟘 ] Γ → Ψ ⊢[ 𝟘 ] T → ⊢ (Γ , T) ∷ Ψ

  -- well-formedness of local contexts
  data _⊢C[_]_ : GCtx → Layer → LCtx → Set where
    ⊢[]  : ⊢ Ψ → Ψ ⊢C[ i ] []
    ⊢ctx : ⊢ Ψ → x ∶ ctx ∈G Ψ → Ψ ⊢C[ i ] cv x
    ⊢v   : Ψ ⊢C[ i ] Γ → Ψ ⊢[ i ] T → Ψ ⊢C[ i ] T ∷ Γ

  -- well-formedness of types
  data _⊢[_]_ : GCtx → Layer → Typ → Set where
    ⊢N : ⊢ Ψ → Ψ ⊢[ i ] N
    ⊢⟶ : Ψ ⊢[ i ] S → Ψ ⊢[ i ] T → Ψ ⊢[ i ] S ⟶ T
    ⊢□ : Ψ ⊢C[ 𝟘 ] Δ → Ψ ⊢[ 𝟘 ] T → Ψ ⊢[ 𝟙 ] □ Δ T
    ⊢⇒ : ctx ∷ Ψ ⊢[ 𝟙 ] T → Ψ ⊢[ 𝟙 ] ctx⇒ T


infix 4 _⊢_ _⊆l_

data _⊢_ : GCtx → Bnd → Set where
  ctx-wf : ⊢ Ψ → Ψ ⊢ ctx
  b-wf   : Ψ ⊢C[ 𝟘 ] Γ → Ψ ⊢[ 𝟘 ] T → Ψ ⊢ (Γ , T)

data _⊆l_ : LCtx → LCtx → Set where
  id-cv : cv x ⊆l cv x
  id-[] : [] ⊆l []
  cv-[] : cv x ⊆l []
  cons  : Γ ⊆l Δ → T ∷ Γ ⊆l T ∷ Δ


infix 4 _⊢gw_∶_ _﹔_⊢lw[_]_∶_

data _⊢gw_∶_ : GCtx → Gwk → GCtx → Set where
  id-wf : ⊢ Ψ →
          Ψ ⊢gw id ∶ Ψ
  p-wf  : ∀ {B} →
          Ψ ⊢gw γ ∶ Φ →
          Ψ ⊢ B →
          B ∷ Ψ ⊢gw p γ ∶ Φ
  q-wf  : ∀ {B} →
          Ψ ⊢gw γ ∶ Φ →
          Φ ⊢ B →
          Ψ ⊢ B [ γ ] →
          (B [ γ ]) ∷ Ψ ⊢gw q γ ∶ B ∷ Φ

data _﹔_⊢lw[_]_∶_ : GCtx → LCtx → Layer → Lwk → LCtx → Set where
  id-wf : Ψ ⊢C[ i ] Γ →
          Γ ⊆l Δ →
          Ψ ﹔ Γ ⊢lw[ i ] id ∶ Δ
  p-wf  : Ψ ﹔ Γ ⊢lw[ i ] τ ∶ Δ →
          Ψ ⊢[ i ] T →
          Ψ ﹔ T ∷ Γ ⊢lw[ i ] p τ ∶ Δ
  q-wf  : Ψ ﹔ Γ ⊢lw[ i ] τ ∶ Δ →
          Ψ ⊢[ i ] T →
          Ψ ﹔ T ∷ Γ ⊢lw[ i ] q τ ∶ T ∷ Δ


bnd-wf : ∀ {B} → Ψ ⊢ B → ⊢ B ∷ Ψ
bnd-wf (ctx-wf ⊢Ψ)  = ⊢ctx ⊢Ψ
bnd-wf (b-wf ⊢Γ ⊢T) = ⊢v ⊢Γ ⊢T

⊢gw-inv : Ψ ⊢gw γ ∶ Φ → ⊢ Ψ × ⊢ Φ
⊢gw-inv (id-wf ⊢Ψ) = ⊢Ψ , ⊢Ψ
⊢gw-inv (p-wf ⊢γ ⊢B)
  with ⊢gw-inv ⊢γ
...  | _ , ⊢Φ      = bnd-wf ⊢B , ⊢Φ
⊢gw-inv (q-wf ⊢γ ⊢B ⊢B′)
  with ⊢gw-inv ⊢γ
...  | _ , ⊢Φ      = bnd-wf ⊢B′ , bnd-wf ⊢B


-- Global Weakening Lemmas

there-gwk : ∀ {B B′} → x ∶ B [ γ ] ∈G Ψ → suc x ∶ B [ p γ ] ∈G B′ ∷ Ψ
there-gwk {_} {γ} {_} {B} x∈
  with gwk-bnd-comp B γ (p id)
...  | eq
     rewrite ∘w-p γ id
           | ∘w-id γ
           | sym eq = there x∈

here-gwk : ∀ {B} → 0 ∶ B [ p γ ] ∈G (B [ γ ]) ∷ Ψ
here-gwk {γ} {_} {B}
  with gwk-bnd-comp B γ (p id)
...  | eq
     rewrite ∘w-p γ id
           | ∘w-id γ
           | sym eq = here

x-gwk : ∀ {x B} → Ψ ⊢gw γ ∶ Φ → x ∶ B ∈G Φ → wk-x x γ ∶ B [ γ ] ∈G Ψ
x-gwk {B = B} (id-wf ⊢Ψ) B∈
  rewrite gwk-id-bnd B                = B∈
x-gwk (p-wf ⊢γ ⊢B′) B∈              = there-gwk (x-gwk ⊢γ B∈)
x-gwk (q-wf {_} {γ} {B = B} ⊢γ ⊢B ⊢B′) here
  rewrite gwk-bnd-comp B (p id) (q γ) = here-gwk
x-gwk (q-wf {_} {γ} ⊢γ ⊢B ⊢B′) (there {B = B} B∈)
  rewrite gwk-bnd-comp B (p id) (q γ) = there-gwk (x-gwk ⊢γ B∈)


mutual

  lctx-gwk : Φ ⊢C[ i ] Γ → Ψ ⊢gw γ ∶ Φ → Ψ ⊢C[ i ] Γ [ γ ]
  lctx-gwk (⊢[] ⊢Φ) ⊢γ       = ⊢[] (proj₁ (⊢gw-inv ⊢γ))
  lctx-gwk (⊢ctx ⊢Φ ctx∈) ⊢γ = ⊢ctx (proj₁ (⊢gw-inv ⊢γ)) (x-gwk ⊢γ ctx∈)
  lctx-gwk (⊢v ⊢Γ ⊢T) ⊢γ     = ⊢v (lctx-gwk ⊢Γ ⊢γ) (ty-gwk ⊢T ⊢γ)

  ty-gwk : Φ ⊢[ i ] T → Ψ ⊢gw γ ∶ Φ → Ψ ⊢[ i ] T [ γ ]
  ty-gwk (⊢N _) ⊢γ                  = ⊢N (proj₁ (⊢gw-inv ⊢γ))
  ty-gwk (⊢⟶ ⊢S ⊢T) ⊢γ              = ⊢⟶ (ty-gwk ⊢S ⊢γ) (ty-gwk ⊢T ⊢γ)
  ty-gwk (⊢□ ⊢Γ ⊢T) ⊢γ              = ⊢□ (lctx-gwk ⊢Γ ⊢γ) (ty-gwk ⊢T ⊢γ)
  ty-gwk {_} {_} {_} {_} {γ} (⊢⇒ ⊢T) ⊢γ
    with ⊢gw-inv ⊢γ
  ...  | ⊢Ψ , ⊢Φ = ⊢⇒ (ty-gwk ⊢T (q-wf ⊢γ (ctx-wf ⊢Φ) (ctx-wf ⊢Ψ)))


bnd-gwk : ∀ {B} → Ψ ⊢gw γ ∶ Φ → Φ ⊢ B → Ψ ⊢ B [ γ ]
bnd-gwk ⊢γ (ctx-wf ⊢Ψ)  = ctx-wf (proj₁ (⊢gw-inv ⊢γ))
bnd-gwk ⊢γ (b-wf ⊢Γ ⊢T) = b-wf (lctx-gwk ⊢Γ ⊢γ) (ty-gwk ⊢T ⊢γ)

⊆l-gwk : Γ ⊆l Δ → Ψ ⊢gw γ ∶ Φ → Γ [ γ ] ⊆l Δ [ γ ]
⊆l-gwk id-cv ⊢γ      = id-cv
⊆l-gwk id-[] ⊢γ      = id-[]
⊆l-gwk cv-[] ⊢γ      = cv-[]
⊆l-gwk (cons Γ⊆Δ) ⊢γ = cons (⊆l-gwk Γ⊆Δ ⊢γ)

q-wf′ : ∀ {B} →
        Ψ ⊢gw γ ∶ Φ →
        Φ ⊢ B →
        (B [ γ ]) ∷ Ψ ⊢gw q γ ∶ B ∷ Φ
q-wf′ ⊢γ ⊢B = q-wf ⊢γ ⊢B (bnd-gwk ⊢γ ⊢B)

gwk-𝟘 : (γ : Gwk) → Ψ ⊢[ 𝟘 ] T → T [ γ ] ≡ T
gwk-𝟘 _ (⊢N _)       = refl
gwk-𝟘 γ (⊢⟶ ⊢S ⊢T)
  rewrite gwk-𝟘 γ ⊢S
        | gwk-𝟘 γ ⊢T = refl


lwk-gwk : Ψ ⊢gw γ ∶ Φ → Φ ﹔ Γ ⊢lw[ i ] τ ∶ Δ → Ψ ﹔ Γ [ γ ] ⊢lw[ i ] τ ∶ Δ [ γ ]
lwk-gwk ⊢γ (id-wf ⊢Γ Γ⊆Δ) = id-wf (lctx-gwk ⊢Γ ⊢γ) (⊆l-gwk Γ⊆Δ ⊢γ)
lwk-gwk ⊢γ (p-wf ⊢τ ⊢T)   = p-wf (lwk-gwk ⊢γ ⊢τ) (ty-gwk ⊢T ⊢γ)
lwk-gwk ⊢γ (q-wf ⊢τ ⊢T)   = q-wf (lwk-gwk ⊢γ ⊢τ) (ty-gwk ⊢T ⊢γ)

-- Presupposition

mutual

  presup-l : Ψ ⊢C[ i ] Γ → ⊢ Ψ
  presup-l (⊢[] ⊢Ψ)      = ⊢Ψ
  presup-l (⊢ctx ⊢Ψ x∈Ψ) = ⊢Ψ
  presup-l (⊢v ⊢Γ ⊢T)    = presup-ty ⊢T

  presup-ty : Ψ ⊢[ i ] T → ⊢ Ψ
  presup-ty (⊢N ⊢Ψ)    = ⊢Ψ
  presup-ty (⊢⟶ ⊢S ⊢T) = presup-ty ⊢T
  presup-ty (⊢□ ⊢Γ ⊢T) = presup-l ⊢Γ
  presup-ty (⊢⇒ ⊢T)
    with presup-ty ⊢T
  ...  | ⊢ctx ⊢Ψ       = ⊢Ψ


infixl 10 _$_ _$c_

mutual

  data Trm : Set where
    var    : ℕ → Trm
    gvar   : ℕ → LSubst → Trm
    zero   : Trm
    succ   : Trm → Trm
    Λ      : Trm → Trm
    _$_    : Trm → Trm → Trm
    box    : Trm → Trm
    letbox : LCtx → Trm → Trm → Trm
    Λc     : Trm → Trm
    _$c_   : Trm → LCtx → Trm

  data LSubst : Set where
    wk  : ℕ → LSubst
    []  : LSubst
    _∷_ : Trm → LSubst → LSubst


variable
  t t′ t″ : Trm
  s s′ s″ : Trm
  δ δ′ δ″ : LSubst


mutual

  gwk-trm : Trm → Gwk → Trm
  gwk-trm (var x) γ        = var x
  gwk-trm (gvar x δ) γ     = gvar (wk-x x γ) (gwk-lsubst δ γ)
  gwk-trm zero γ           = zero
  gwk-trm (succ t) γ       = succ (gwk-trm t γ)
  gwk-trm (Λ t) γ          = Λ (gwk-trm t γ)
  gwk-trm (t $ s) γ        = gwk-trm t γ $ gwk-trm s γ
  gwk-trm (box t) γ        = box (gwk-trm t γ)
  gwk-trm (letbox Γ t s) γ = letbox (Γ [ γ ]) (gwk-trm t γ) (gwk-trm s (q γ))
  gwk-trm (Λc t) γ         = Λc (gwk-trm t (q γ))
  gwk-trm (t $c Γ) γ       = gwk-trm t γ $c (Γ [ γ ])


  gwk-lsubst : LSubst → Gwk → LSubst
  gwk-lsubst (wk x) γ  = wk (wk-x x γ)
  gwk-lsubst [] γ      = []
  gwk-lsubst (t ∷ δ) γ = gwk-trm t γ ∷ gwk-lsubst δ γ

instance
  gwk-trm-mon : Monotone Trm Gwk
  gwk-trm-mon = record { _[_] = gwk-trm }

  gwk-lsubst-mon : Monotone LSubst Gwk
  gwk-lsubst-mon = record { _[_] = gwk-lsubst }

mutual

  lwk-trm : Trm → Lwk → Trm
  lwk-trm (var x) τ        = var (wk-x x τ)
  lwk-trm (gvar x δ) τ     = gvar x (lwk-lsubst δ τ)
  lwk-trm zero τ           = zero
  lwk-trm (succ t) τ       = succ (lwk-trm t τ)
  lwk-trm (Λ t) τ          = Λ (lwk-trm t (q τ))
  lwk-trm (t $ s) τ        = lwk-trm t τ $ lwk-trm s τ
  lwk-trm (box t) τ        = box t
  lwk-trm (letbox Γ s t) τ = letbox Γ (lwk-trm s τ) (lwk-trm t τ)
  lwk-trm (Λc t) τ         = Λc (lwk-trm t τ)
  lwk-trm (t $c Γ) τ       = lwk-trm t τ $c Γ

  lwk-lsubst : LSubst → Lwk → LSubst
  lwk-lsubst (wk x) τ  = wk x
  lwk-lsubst [] τ      = []
  lwk-lsubst (t ∷ δ) τ = lwk-trm t τ ∷ lwk-lsubst δ τ

-- Global Substitutions

data GSub : Set where
  ctx : LCtx → GSub
  trm : Trm → GSub

GSubst : Set
GSubst = List GSub

variable
  σ σ′ σ″ : GSubst

gwk-gsub : GSubst → Gwk → GSubst
gwk-gsub σ γ = L.map (λ { (ctx Γ) → ctx (Γ [ γ ]) ; (trm t) → trm (t [ γ ]) }) σ

instance
  gwk-gsub-mon : Monotone GSubst Gwk
  gwk-gsub-mon = record { _[_] = gwk-gsub }

gsub-ty-x : ℕ → GSubst → LCtx
gsub-ty-x x σ
  with lookup σ x
... | just (ctx Γ) = Γ
... | just (trm _) = []
...  | nothing     = []


mutual
  gsub-ty : Typ → GSubst → Typ
  gsub-ty N σ        = N
  gsub-ty (S ⟶ T) σ  = gsub-ty S σ ⟶ gsub-ty T σ
  gsub-ty (□ Γ T) σ  = □ (gsub-lc Γ σ) (gsub-ty T σ)
  gsub-ty (ctx⇒ T) σ = ctx⇒ gsub-ty T (ctx (cv 0) ∷ (σ [ p id ]))

  gsub-lc : LCtx → GSubst → LCtx
  gsub-lc [] σ      = []
  gsub-lc (cv x) σ  = gsub-ty-x x σ
  gsub-lc (T ∷ Γ) σ = gsub-ty T σ ∷ gsub-lc Γ σ

instance
  gsub-ty-mon : Monotone Typ GSubst
  gsub-ty-mon = record { _[_] = gsub-ty }

  gsub-lc-mon : Monotone LCtx GSubst
  gsub-lc-mon = record { _[_] = gsub-lc }


lsub-x : ℕ → LSubst → Trm
lsub-x x (wk _)        = zero
lsub-x x []            = zero
lsub-x zero (t ∷ δ)    = t
lsub-x (suc x) (t ∷ δ) = lsub-x x δ


lsub-id : LCtx → LSubst
lsub-id []      = []
lsub-id (cv x)  = wk x
lsub-id (T ∷ Γ) = var 0 ∷ lwk-lsubst (lsub-id Γ) (p id)

gsub-id : GCtx → GSubst
gsub-id []            = []
gsub-id (ctx ∷ Ψ)     = ctx (cv 0) ∷ (gsub-id Ψ [ p id ])
gsub-id ((Γ , T) ∷ Ψ) = trm (gvar 0 (lsub-id Γ)) ∷ (gsub-id Ψ [ p id ])


infixl 3 _∘l_

mutual

  lsub-trm : Trm → LSubst → Trm
  lsub-trm (var x) δ        = lsub-x x δ
  lsub-trm (gvar x δ′) δ    = gvar x (δ′ ∘l δ)
  lsub-trm zero δ           = zero
  lsub-trm (succ t) δ       = succ (lsub-trm t δ)
  lsub-trm (Λ t) δ          = Λ (lsub-trm t (var 0 ∷ lwk-lsubst δ (p id)))
  lsub-trm (t $ s) δ        = lsub-trm t δ $ lsub-trm s δ
  lsub-trm (box t) δ        = box t
  lsub-trm (letbox Γ s t) δ = letbox Γ (lsub-trm s δ) (lsub-trm t (δ [ p id ]))
  lsub-trm (Λc t) δ         = Λc (lsub-trm t (δ [ p id ]))
  lsub-trm (t $c Γ) δ       = lsub-trm t δ $c Γ

  _∘l_ : LSubst → LSubst → LSubst
  wk x ∘l δ′    = wk x
  [] ∘l δ′      = []
  (t ∷ δ) ∘l δ′ = lsub-trm t δ′ ∷ (δ ∘l δ′)


gsub-trm-x : ℕ → GSubst → Trm
gsub-trm-x x σ
  with lookup σ x
... | just (ctx _) = zero
... | just (trm t) = t
... | nothing      = zero

mutual
  gsub-trm : Trm → GSubst → Trm
  gsub-trm (var x) σ        = var x
  gsub-trm (gvar x δ) σ     = lsub-trm (gsub-trm-x x σ) (gsub-lsubst δ σ)
  gsub-trm zero σ           = zero
  gsub-trm (succ t) σ       = succ (gsub-trm t σ)
  gsub-trm (Λ t) σ          = Λ (gsub-trm t σ)
  gsub-trm (t $ s) σ        = gsub-trm t σ $ gsub-trm s σ
  gsub-trm (box t) σ        = box (gsub-trm t σ)
  gsub-trm (letbox Γ s t) σ = letbox (Γ [ σ ]) (gsub-trm s σ) (gsub-trm t (trm (gvar 0 (lsub-id Γ)) ∷ (σ [ p id ])))
  gsub-trm (Λc t) σ         = Λc (gsub-trm t (ctx (cv 0) ∷ (σ [ p id ])))
  gsub-trm (t $c Γ) σ       = gsub-trm t σ $c (Γ [ σ ])

  gsub-lsubst : LSubst → GSubst → LSubst
  gsub-lsubst (wk x) σ  = lsub-id (gsub-ty-x x σ)
  gsub-lsubst [] σ      = []
  gsub-lsubst (t ∷ δ) σ = gsub-trm t σ ∷ gsub-lsubst δ σ

instance
  gsub-trm-mon : Monotone Trm GSubst
  gsub-trm-mon = record { _[_] = gsub-trm }

  gsub-lsubst-mon : Monotone LSubst GSubst
  gsub-lsubst-mon = record { _[_] = gsub-lsubst }

infixr 5 _^^_

_^^_ : List Typ → LCtx → LCtx
[] ^^ Δ = Δ
(T ∷ Γ) ^^ Δ = T ∷ (Γ ^^ Δ)

infix 2 _∶_∈L_

data _∶_∈L_ : ℕ → Typ → LCtx → Set where
  here  : 0 ∶ T ∈L T ∷ Γ
  there : ∀ {x} → x ∶ T ∈L Γ → suc x ∶ T ∈L S ∷ Γ

∈L⇒wf : x ∶ T ∈L Γ → Ψ ⊢C[ i ] Γ → Ψ ⊢[ i ] T
∈L⇒wf here (⊢v ⊢Γ ⊢T)       = ⊢T
∈L⇒wf (there T∈) (⊢v ⊢Γ ⊢S) = ∈L⇒wf T∈ ⊢Γ

infix 4 _﹔_⊢[_]_∶_ _﹔_⊢s[_]_∶_

mutual
  data _﹔_⊢[_]_∶_ : GCtx → LCtx → Layer → Trm → Typ → Set where
    v-wf      : ∀ {x} →
                Ψ ⊢C[ i ] Γ →
                x ∶ T ∈L Γ →
                ------------------
                Ψ ﹔ Γ ⊢[ i ] var x ∶ T
    gv-wf     : ∀ {x} →
                x ∶ (Δ , T) ∈ Ψ →
                Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                ---------------------
                Ψ ﹔ Γ ⊢[ i ] gvar x δ ∶ T
    zero-wf   : Ψ ⊢C[ i ] Γ →
                ----------------------
                Ψ ﹔ Γ ⊢[ i ] zero ∶ N
    succ-wf   : Ψ ﹔ Γ ⊢[ i ] t ∶ N →
                ------------------------
                Ψ ﹔ Γ ⊢[ i ] succ t ∶ N
    Λ-wf      : Ψ ﹔ S ∷ Γ ⊢[ i ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ i ] Λ t ∶ S ⟶ T
    $-wf      : Ψ ﹔ Γ ⊢[ i ] t ∶ S ⟶ T →
                Ψ ﹔ Γ ⊢[ i ] s ∶ S →
                -------------------------
                Ψ ﹔ Γ ⊢[ i ] t $ s ∶ T
    box-wf    : Ψ ⊢C[ 𝟙 ] Γ →
                Ψ ﹔ Δ ⊢[ 𝟘 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] box t ∶ □ Δ T
    letbox-wf : Ψ ﹔ Γ ⊢[ 𝟙 ] s ∶ □ Δ T →
                (Δ , S) ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T [ p id ] →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] letbox Δ s t ∶ T
    Λc-wf     : ctx ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] Λc t ∶ ctx⇒ T
    $c-wf     : Ψ ﹔ Γ ⊢[ 𝟙 ] t ∶ ctx⇒ T →
                Ψ ⊢C[ 𝟘 ] Δ →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] t $c Δ ∶ T [ ctx Δ ∷ gsub-id Ψ ]


  data _﹔_⊢s[_]_∶_ : GCtx → LCtx → Layer → LSubst → LCtx → Set where
    wk-wf : ∀ {Δ} →
            Ψ ⊢C[ i ] Γ →
            Γ ≡ Δ ^^ cv x →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] wk x ∶ cv x
    []-wf : Ψ ⊢C[ i ] Γ →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] [] ∶ []
    ∷-wf  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
            Ψ ﹔ Γ ⊢[ i ] t ∶ T →
            ---------------------------
            Ψ ﹔ Γ ⊢s[ i ] t ∷ δ ∶ T ∷ Δ
