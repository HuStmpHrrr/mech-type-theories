{-# OPTIONS --without-K --safe #-}

module CVar.Syntax where

open import Level hiding (zero; suc)

open import Lib public

import Data.Nat.Properties as ℕₚ
open import Data.List.Properties as Lₚ


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

∘w-pid : ∀ γ → (γ ∘w p id) ≡ p γ
∘w-pid id    = refl
∘w-pid (p γ) = refl
∘w-pid (q γ) = refl

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

wk-x-repeat-p : ∀ x y → wk-x x (repeat p y id) ≡ y + x
wk-x-repeat-p x zero = refl
wk-x-repeat-p x (suc y) = cong suc (wk-x-repeat-p x y)

wk-x-repeat-p′ : ∀ x y → wk-x x (repeat p y id) ≡ x + y
wk-x-repeat-p′ x y = trans (wk-x-repeat-p x y) (ℕₚ.+-comm y x)

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
  B : Bnd

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


infix 4 ⊢_ _⊢l[_]_ _⊢[_]_

mutual

  -- well-formedness of global contexts
  data ⊢_ : GCtx → Set where
    ⊢[]  : ⊢ []
    ⊢ctx : ⊢ Ψ → ⊢ ctx ∷ Ψ
    ⊢∷   : Ψ ⊢l[ 𝟘 ] Γ → Ψ ⊢[ 𝟘 ] T → ⊢ (Γ , T) ∷ Ψ

  -- well-formedness of local contexts
  data _⊢l[_]_ : GCtx → Layer → LCtx → Set where
    ⊢[]  : ⊢ Ψ → Ψ ⊢l[ i ] []
    ⊢ctx : ⊢ Ψ → x ∶ ctx ∈G Ψ → Ψ ⊢l[ i ] cv x
    ⊢∷   : Ψ ⊢l[ i ] Γ → Ψ ⊢[ i ] T → Ψ ⊢l[ i ] T ∷ Γ

  -- well-formedness of types
  data _⊢[_]_ : GCtx → Layer → Typ → Set where
    ⊢N : ⊢ Ψ → Ψ ⊢[ i ] N
    ⊢⟶ : Ψ ⊢[ i ] S → Ψ ⊢[ i ] T → Ψ ⊢[ i ] S ⟶ T
    ⊢□ : Ψ ⊢l[ 𝟘 ] Δ → Ψ ⊢[ 𝟘 ] T → Ψ ⊢[ 𝟙 ] □ Δ T
    ⊢⇒ : ctx ∷ Ψ ⊢[ 𝟙 ] T → Ψ ⊢[ 𝟙 ] ctx⇒ T


-- Lifting Lemmas

mutual
  lift-lctx : Ψ ⊢l[ 𝟘 ] Γ → Ψ ⊢l[ 𝟙 ] Γ
  lift-lctx (⊢[] ⊢Ψ)       = ⊢[] ⊢Ψ
  lift-lctx (⊢ctx ⊢Ψ ctx∈) = ⊢ctx ⊢Ψ ctx∈
  lift-lctx (⊢∷ ⊢Γ ⊢T)     = ⊢∷ (lift-lctx ⊢Γ) (lift-ty ⊢T)

  lift-ty : Ψ ⊢[ 𝟘 ] T → Ψ ⊢[ 𝟙 ] T
  lift-ty (⊢N ⊢Ψ)    = ⊢N ⊢Ψ
  lift-ty (⊢⟶ ⊢S ⊢T) = ⊢⟶ (lift-ty ⊢S) (lift-ty ⊢T)

lift-lctx′ : Ψ ⊢l[ i ] Γ → Ψ ⊢l[ 𝟙 ] Γ
lift-lctx′ {_} {𝟘} ⊢Γ = lift-lctx ⊢Γ
lift-lctx′ {_} {𝟙} ⊢Γ = ⊢Γ

lift-ty′ : Ψ ⊢[ i ] T → Ψ ⊢[ 𝟙 ] T
lift-ty′ {_} {𝟘} ⊢T = lift-ty ⊢T
lift-ty′ {_} {𝟙} ⊢T = ⊢T

lift-lctx″ : ∀ i → Ψ ⊢l[ 𝟘 ] Γ → Ψ ⊢l[ i ] Γ
lift-lctx″ 𝟘 ⊢Γ = ⊢Γ
lift-lctx″ 𝟙 ⊢Γ = lift-lctx ⊢Γ

lift-ty″ : ∀ i → Ψ ⊢[ 𝟘 ] T → Ψ ⊢[ i ] T
lift-ty″ 𝟘 ⊢T = ⊢T
lift-ty″ 𝟙 ⊢T = lift-ty ⊢T

infix 4 _⊢_ _⊆l_

data _⊢_ : GCtx → Bnd → Set where
  ctx-wf : ⊢ Ψ → Ψ ⊢ ctx
  b-wf   : Ψ ⊢l[ 𝟘 ] Γ → Ψ ⊢[ 𝟘 ] T → Ψ ⊢ (Γ , T)

data _⊆l_ : LCtx → LCtx → Set where
  id-cv : cv x ⊆l cv x
  id-[] : [] ⊆l []
  cv-[] : cv x ⊆l []
  cons  : Γ ⊆l Δ → T ∷ Γ ⊆l T ∷ Δ


-- Typing of Global and Local Weakenings

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
  id-wf : Ψ ⊢l[ i ] Γ →
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
bnd-wf (b-wf ⊢Γ ⊢T) = ⊢∷ ⊢Γ ⊢T

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

  lctx-gwk : Φ ⊢l[ i ] Γ → Ψ ⊢gw γ ∶ Φ → Ψ ⊢l[ i ] Γ [ γ ]
  lctx-gwk (⊢[] ⊢Φ) ⊢γ       = ⊢[] (proj₁ (⊢gw-inv ⊢γ))
  lctx-gwk (⊢ctx ⊢Φ ctx∈) ⊢γ = ⊢ctx (proj₁ (⊢gw-inv ⊢γ)) (x-gwk ⊢γ ctx∈)
  lctx-gwk (⊢∷ ⊢Γ ⊢T) ⊢γ     = ⊢∷ (lctx-gwk ⊢Γ ⊢γ) (ty-gwk ⊢T ⊢γ)

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

  presup-l : Ψ ⊢l[ i ] Γ → ⊢ Ψ
  presup-l (⊢[] ⊢Ψ)      = ⊢Ψ
  presup-l (⊢ctx ⊢Ψ x∈Ψ) = ⊢Ψ
  presup-l (⊢∷ ⊢Γ ⊢T)    = presup-ty ⊢T

  presup-ty : Ψ ⊢[ i ] T → ⊢ Ψ
  presup-ty (⊢N ⊢Ψ)    = ⊢Ψ
  presup-ty (⊢⟶ ⊢S ⊢T) = presup-ty ⊢T
  presup-ty (⊢□ ⊢Γ ⊢T) = presup-l ⊢Γ
  presup-ty (⊢⇒ ⊢T)
    with presup-ty ⊢T
  ...  | ⊢ctx ⊢Ψ       = ⊢Ψ

-- Convenient Lemmas

gwk-repeat : ∀ Φ → ⊢ Φ ++ Ψ → Φ ++ Ψ ⊢gw repeat p (L.length Φ) id ∶ Ψ
gwk-repeat [] ⊢Ψ                     = id-wf ⊢Ψ
gwk-repeat (.ctx ∷ Φ) (⊢ctx ⊢ΦΨ)     = p-wf (gwk-repeat Φ ⊢ΦΨ) (ctx-wf ⊢ΦΨ)
gwk-repeat (.(_ , _) ∷ Φ) (⊢∷ ⊢Γ ⊢T) = p-wf (gwk-repeat Φ (presup-l ⊢Γ)) (b-wf ⊢Γ ⊢T)

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


-- Composition of Global Weakenings

mutual
  gwk-trm-comp : ∀ (t : Trm) γ γ′ → t [ γ ] [ γ′ ] ≡ t [ γ ∘w γ′ ]
  gwk-trm-comp (var x) γ γ′        = refl
  gwk-trm-comp (gvar x δ) γ γ′     = cong₂ gvar (gwk-x-comp x γ γ′) (gwk-lsubst-comp δ γ γ′)
  gwk-trm-comp zero γ γ′           = refl
  gwk-trm-comp (succ t) γ γ′       = cong succ (gwk-trm-comp t γ γ′)
  gwk-trm-comp (Λ t) γ γ′          = cong Λ (gwk-trm-comp t γ γ′)
  gwk-trm-comp (t $ s) γ γ′        = cong₂ _$_ (gwk-trm-comp t γ γ′) (gwk-trm-comp s γ γ′)
  gwk-trm-comp (box t) γ γ′        = cong box (gwk-trm-comp t γ γ′)
  gwk-trm-comp (letbox Γ s t) γ γ′ = cong₃ letbox (gwk-lc-comp Γ γ γ′) (gwk-trm-comp s γ γ′) (gwk-trm-comp t (q γ) (q γ′))
  gwk-trm-comp (Λc t) γ γ′         = cong Λc (gwk-trm-comp t (q γ) (q γ′))
  gwk-trm-comp (t $c Γ) γ γ′       = cong₂ _$c_ (gwk-trm-comp t γ γ′) (gwk-lc-comp Γ γ γ′)

  gwk-lsubst-comp : ∀ (δ : LSubst) γ γ′ → δ [ γ ] [ γ′ ] ≡ δ [ γ ∘w γ′ ]
  gwk-lsubst-comp (wk x) γ γ′  = cong wk (gwk-x-comp x γ γ′)
  gwk-lsubst-comp [] γ γ′      = refl
  gwk-lsubst-comp (t ∷ δ) γ γ′ = cong₂ _∷_ (gwk-trm-comp t γ γ′) (gwk-lsubst-comp δ γ γ′)


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

-- Composition of Global Weakenings

gwk-gsub-comp : ∀ (σ : GSubst) γ γ′ → σ [ γ ] [ γ′ ] ≡ σ [ γ ∘w γ′ ]
gwk-gsub-comp [] γ γ′ = refl
gwk-gsub-comp (ctx Γ ∷ σ) γ γ′ = cong₂ _∷_ (cong ctx (gwk-lc-comp Γ γ γ′)) (gwk-gsub-comp σ γ γ′)
gwk-gsub-comp (trm t ∷ σ) γ γ′ = cong₂ _∷_ (cong trm (gwk-trm-comp t γ γ′)) (gwk-gsub-comp σ γ γ′)

-- Global Substitutions of Types

gsub-ty-x : ℕ → GSubst → LCtx
gsub-ty-x x []             = []
gsub-ty-x zero (ctx Γ ∷ σ) = Γ
gsub-ty-x zero (trm _ ∷ σ) = []
gsub-ty-x (suc x) (_ ∷ σ)  = gsub-ty-x x σ


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


gwk-gsub-ty-x : ∀ x σ (γ : Gwk) → gsub-ty-x x σ [ γ ] ≡ gsub-ty-x x (σ [ γ ])
gwk-gsub-ty-x x [] γ             = refl
gwk-gsub-ty-x zero (ctx Γ ∷ σ) γ = refl
gwk-gsub-ty-x zero (trm _ ∷ σ) γ = refl
gwk-gsub-ty-x (suc x) (_ ∷ σ) γ  = gwk-gsub-ty-x x σ γ

mutual
  ty-gsubst-gwk : (T : Typ) (σ : GSubst) (γ : Gwk) → T [ σ ] [ γ ] ≡ T [ σ [ γ ] ]
  ty-gsubst-gwk N σ γ        = refl
  ty-gsubst-gwk (S ⟶ T) σ γ  = cong₂ _⟶_ (ty-gsubst-gwk S σ γ) (ty-gsubst-gwk T σ γ)
  ty-gsubst-gwk (□ Γ T) σ γ  = cong₂ □ (lctx-gsubst-gwk Γ σ γ) (ty-gsubst-gwk T σ γ)
  ty-gsubst-gwk (ctx⇒ T) σ γ = cong ctx⇒_ (trans (ty-gsubst-gwk T (ctx (cv 0) ∷ gwk-gsub σ (p id)) (q γ))
                                                 (cong (λ σ → T [ ctx (cv 0) ∷ σ ])
                                                       (trans (gwk-gsub-comp σ (p id) (q γ))
                                                       (sym (trans (gwk-gsub-comp σ γ (p id))
                                                                   (cong (σ [_]) (∘w-pid γ)))))))

  lctx-gsubst-gwk : (Γ : LCtx) (σ : GSubst) (γ : Gwk) → Γ [ σ ] [ γ ] ≡ Γ [ σ [ γ ] ]
  lctx-gsubst-gwk [] σ γ      = refl
  lctx-gsubst-gwk (cv x) σ γ  = gwk-gsub-ty-x x σ γ
  lctx-gsubst-gwk (T ∷ Γ) σ γ = cong₂ _∷_ (ty-gsubst-gwk T σ γ) (lctx-gsubst-gwk Γ σ γ)


lsub-x : ℕ → LSubst → Trm
lsub-x x (wk _)        = zero
lsub-x x []            = zero
lsub-x zero (t ∷ δ)    = t
lsub-x (suc x) (t ∷ δ) = lsub-x x δ


infixr 5 _^^_

_^^_ : List Typ → LCtx → LCtx
[] ^^ Δ = Δ
(T ∷ Γ) ^^ Δ = T ∷ (Γ ^^ Δ)

lsub-wk : (y : ℕ) (Δ : LCtx) → LSubst
lsub-wk y []      = []
lsub-wk y (cv x)  = wk x
lsub-wk y (T ∷ Δ) = var y ∷ lsub-wk (1 + y) Δ

lsub-id : LCtx → LSubst
lsub-id Γ = lsub-wk 0 Γ


gsub-wk : (y : ℕ) (Ψ : GCtx) → GSubst
gsub-wk y []            = []
gsub-wk y (ctx ∷ Ψ)     = ctx (cv y) ∷ gsub-wk (1 + y) Ψ
gsub-wk y ((Γ , T) ∷ Ψ) = trm (gvar y (lsub-id Γ [ repeat p (1 + y) id ])) ∷ gsub-wk (1 + y) Ψ

gsub-id : GCtx → GSubst
gsub-id Ψ = gsub-wk 0 Ψ

-- gsub-id : GCtx → GSubst
-- gsub-id []            = []
-- gsub-id (ctx ∷ Ψ)     = ctx (cv 0) ∷ (gsub-id Ψ [ p id ])
-- gsub-id ((Γ , T) ∷ Ψ) = trm (gvar 0 (lsub-id Γ)) ∷ (gsub-id Ψ [ p id ])


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


infix 2 _∶_∈L_

data _∶_∈L_ : ℕ → Typ → LCtx → Set where
  here  : 0 ∶ T ∈L T ∷ Γ
  there : ∀ {x} → x ∶ T ∈L Γ → suc x ∶ T ∈L S ∷ Γ

∈L⇒wf : x ∶ T ∈L Γ → Ψ ⊢l[ i ] Γ → Ψ ⊢[ i ] T
∈L⇒wf here (⊢∷ ⊢Γ ⊢T)       = ⊢T
∈L⇒wf (there T∈) (⊢∷ ⊢Γ ⊢S) = ∈L⇒wf T∈ ⊢Γ

infix 4 _﹔_⊢[_]_∶_ _﹔_⊢s[_]_∶_

mutual
  data _﹔_⊢[_]_∶_ : GCtx → LCtx → Layer → Trm → Typ → Set where
    v-wf      : ∀ {x} →
                Ψ ⊢l[ i ] Γ →
                x ∶ T ∈L Γ →
                ------------------
                Ψ ﹔ Γ ⊢[ i ] var x ∶ T
    gv-wf     : ∀ {x} →
                x ∶ (Δ , T) ∈G Ψ →
                Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                ---------------------
                Ψ ﹔ Γ ⊢[ i ] gvar x δ ∶ T
    zero-wf   : Ψ ⊢l[ i ] Γ →
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
    box-wf    : Ψ ⊢l[ 𝟙 ] Γ →
                Ψ ﹔ Δ ⊢[ 𝟘 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] box t ∶ □ Δ T
    letbox-wf : Ψ ﹔ Γ ⊢[ 𝟙 ] s ∶ □ Δ S →
                Ψ ⊢l[ 𝟘 ] Δ →
                Ψ ⊢[ 𝟘 ] S →
                Ψ ⊢[ 𝟙 ] T →
                (Δ , S) ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T [ p id ] →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] letbox Δ s t ∶ T
    Λc-wf     : Ψ ⊢l[ 𝟙 ] Γ →
                ctx ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] Λc t ∶ ctx⇒ T
    $c-wf     : Ψ ﹔ Γ ⊢[ 𝟙 ] t ∶ ctx⇒ T →
                Ψ ⊢l[ 𝟘 ] Δ →
                ctx ∷ Ψ ⊢[ 𝟙 ] T →
                T′ ≡ T [ ctx Δ ∷ gsub-id Ψ ] →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] t $c Δ ∶ T′


  data _﹔_⊢s[_]_∶_ : GCtx → LCtx → Layer → LSubst → LCtx → Set where
    wk-wf : ∀ {Δ} →
            Ψ ⊢l[ i ] Γ →
            x ∶ ctx ∈G Ψ →
            Γ ≡ Δ ^^ cv x →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] wk x ∶ cv x
    []-wf : Ψ ⊢l[ i ] Γ →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] [] ∶ []
    ∷-wf  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
            Ψ ﹔ Γ ⊢[ i ] t ∶ T →
            ---------------------------
            Ψ ﹔ Γ ⊢s[ i ] t ∷ δ ∶ T ∷ Δ

-- Typing of Identity

^^-assoc : ∀ Γ Γ′ Δ → Γ ^^ Γ′ ^^ Δ ≡ (Γ ++ Γ′) ^^ Δ
^^-assoc [] Γ′ Δ      = refl
^^-assoc (T ∷ Γ) Γ′ Δ = cong (T ∷_) (^^-assoc Γ Γ′ Δ)

∈L-lookup : ∀ Γ T Δ → L.length Γ ∶ T ∈L Γ ^^ (T ∷ Δ)
∈L-lookup [] T Δ      = here
∈L-lookup (S ∷ Γ) T Δ = there (∈L-lookup Γ T Δ)

⊢lsub-wk-gen : ∀ Γ → Ψ ⊢l[ i ] (Γ ^^ Δ) → Ψ ⊢l[ i ] Δ → Ψ ﹔ Γ ^^ Δ ⊢s[ i ] lsub-wk (L.length Γ) Δ ∶ Δ
⊢lsub-wk-gen Γ ⊢ΓΔ (⊢[] ⊢Ψ)                    = []-wf ⊢ΓΔ
⊢lsub-wk-gen Γ ⊢ΓΔ (⊢ctx ⊢Ψ ctx∈)              = wk-wf ⊢ΓΔ ctx∈ refl
⊢lsub-wk-gen  {Ψ} {_} {T ∷ Δ} Γ ⊢ΓΔ (⊢∷ ⊢Δ ⊢T) = ∷-wf helper (v-wf ⊢ΓΔ (∈L-lookup _ _ _))
  where ⊢ΓΔ′ : Ψ ⊢l[ _ ] (Γ L.++ L.[ T ]) ^^ Δ
        ⊢ΓΔ′ = subst (Ψ ⊢l[ _ ]_) (^^-assoc Γ L.[ T ] Δ) ⊢ΓΔ
        helper : Ψ ﹔ Γ ^^ (T ∷ Δ) ⊢s[ _ ] lsub-wk (1 + L.length Γ) Δ ∶ Δ
        helper
          with ⊢lsub-wk-gen (Γ ++ L.[ T ]) ⊢ΓΔ′ ⊢Δ
        ...  | ⊢wk
             rewrite sym (^^-assoc Γ L.[ T ] Δ)
                   | Lₚ.length-++ Γ {L.[ T ]}
                   | ℕₚ.+-comm (L.length Γ) 1 = ⊢wk

⊢lsub-id : Ψ ⊢l[ i ] Γ → Ψ ﹔ Γ ⊢s[ i ] lsub-id Γ ∶ Γ
⊢lsub-id ⊢Γ = ⊢lsub-wk-gen [] ⊢Γ ⊢Γ

-- Global Substitutions

infix 4 _⊢_∶_

data _⊢_∶_ : GCtx → GSubst → GCtx → Set where
  []-wf  : ⊢ Ψ →
           -------------
           Ψ ⊢ [] ∶ []
  trm-wf : Ψ ⊢ σ ∶ Φ →
           Φ ⊢l[ 𝟘 ] Γ →
           Φ ⊢[ 𝟘 ] T →
           Ψ ﹔ Γ [ σ ] ⊢[ 𝟘 ] t ∶ T [ σ ] →
           ----------------------
           Ψ ⊢ trm t ∷ σ ∶ (Γ , T) ∷ Φ
  ctx-wf : Ψ ⊢ σ ∶ Φ →
           Ψ ⊢l[ 𝟘 ] Γ →
           ----------------------
           Ψ ⊢ ctx Γ ∷ σ ∶ ctx ∷ Φ


gsubst-inv : Ψ ⊢ σ ∶ Φ → ⊢ Ψ × ⊢ Φ
gsubst-inv ([]-wf ⊢Ψ) = ⊢Ψ , ⊢[]
gsubst-inv (trm-wf ⊢σ ⊢Γ ⊢T ⊢t)
  with gsubst-inv ⊢σ
...  | ⊢Ψ , ⊢Φ        = ⊢Ψ , ⊢∷ ⊢Γ ⊢T
gsubst-inv (ctx-wf ⊢σ ⊢Γ)
  with gsubst-inv ⊢σ
...  | ⊢Ψ , ⊢Φ        = ⊢Ψ , ⊢ctx ⊢Φ

gsub-q : GSubst → GSubst
gsub-q σ = ctx (cv 0) ∷ (σ [ p id ])

-- Useful Equations

mutual
  ty-gsub-wk≈gwk-gen : ∀ m n Ψ →
                       repeat (ctx ∷_) m Ψ ⊢[ i ] T →
                       T [ repeat gsub-q m (gsub-wk n Ψ) ] ≡ T [ repeat q m (repeat p n id) ]
  ty-gsub-wk≈gwk-gen m n Ψ (⊢N _)     = refl
  ty-gsub-wk≈gwk-gen m n Ψ (⊢⟶ ⊢S ⊢T) = cong₂ _⟶_ (ty-gsub-wk≈gwk-gen m n Ψ ⊢S) (ty-gsub-wk≈gwk-gen m n Ψ ⊢T)
  ty-gsub-wk≈gwk-gen m n Ψ (⊢□ ⊢Δ ⊢T) = cong₂ □ (lctx-gsub-wk≈gwk-gen m n Ψ ⊢Δ) (ty-gsub-wk≈gwk-gen m n Ψ ⊢T)
  ty-gsub-wk≈gwk-gen m n Ψ (⊢⇒ ⊢T)    = cong ctx⇒_ (ty-gsub-wk≈gwk-gen (1 + m) n Ψ ⊢T)

  lctx-gsub-wk≈gwk-gen : ∀ m n Ψ →
                         repeat (ctx ∷_) m Ψ ⊢l[ i ] Γ →
                         Γ [ repeat gsub-q m (gsub-wk n Ψ) ] ≡ Γ [ repeat q m (repeat p n id) ]
  lctx-gsub-wk≈gwk-gen m n Ψ (⊢[] _)       = refl
  lctx-gsub-wk≈gwk-gen m n Ψ (⊢ctx _ ctx∈) = helper m ctx∈ refl
    where helper : ∀ m {n} {Ψ} {x} →
                     x ∶ B ∈G repeat (L._∷_ ctx) m Ψ → B ≡ ctx →
                     gsub-ty-x x (repeat gsub-q m (gsub-wk n Ψ)) ≡ cv (wk-x x (repeat q m (repeat p n id)))
          helper 0 (here {_} {ctx}) eq                                = cong cv (sym (wk-x-repeat-p′ 0 _))
          helper 0 {0} (there {_} {_} {ctx} {ctx} ctx∈) eq             = helper 0 {1} ctx∈ refl
          helper 0 {0} (there {_} {_} {ctx} {Γ , T} ctx∈) eq          = helper 0 {1} ctx∈ refl
          helper 0 {suc n} {_} {suc x} (there {_} {_} {ctx} {ctx} ctx∈) eq
            rewrite wk-x-repeat-p′ (suc x) n                           = trans (helper 0 {suc (suc n)} ctx∈ refl)
                                                                               (cong (λ y → cv (2 + y)) (wk-x-repeat-p′ x n))
          helper 0 {suc n} {_} {suc x} (there {_} {_} {ctx} {Γ , T} ctx∈) eq
            rewrite wk-x-repeat-p′ (suc x) n                           = trans (helper 0 {suc (suc n)} ctx∈ refl)
                                                                               (cong (λ y → cv (2 + y)) (wk-x-repeat-p′ x n))
          helper (suc m) here eq                                       = refl
          helper (suc m) {n} {Ψ} {suc x} (there {_} {_} {ctx} ctx∈) eq = trans (sym (gwk-gsub-ty-x x (repeat gsub-q m (gsub-wk n Ψ)) (p id)))
                                                                               (cong (_[ p id ]) (helper m ctx∈ refl))

  lctx-gsub-wk≈gwk-gen m n Ψ (⊢∷ ⊢Γ ⊢T)    = cong₂ _∷_ (ty-gsub-wk≈gwk-gen m n Ψ ⊢T) (lctx-gsub-wk≈gwk-gen m n Ψ ⊢Γ)


ty-gsub-wk≈gwk : ∀ n Ψ →
                 Ψ ⊢[ i ] T →
                 T [ gsub-wk n Ψ ] ≡ T [ repeat p n id ]
ty-gsub-wk≈gwk n Ψ ⊢T = ty-gsub-wk≈gwk-gen 0 n Ψ ⊢T

lctx-gsub-wk≈gwk : ∀ n Ψ →
                   Ψ ⊢l[ i ] Γ →
                   Γ [ gsub-wk n Ψ ] ≡ Γ [ repeat p n id ]
lctx-gsub-wk≈gwk n Ψ ⊢Γ = lctx-gsub-wk≈gwk-gen 0 n Ψ ⊢Γ

gsub-ty-x-wk : ∀ y →
               x ∶ B ∈G Ψ →
               B ≡ ctx →
               gsub-ty-x x (gsub-wk y Ψ) ≡ cv (x + y)
gsub-ty-x-wk y (here {_} {ctx}) eq             = refl
gsub-ty-x-wk y (there {B = ctx} {ctx} B∈) eq   = trans (gsub-ty-x-wk (1 + y) B∈ refl) (cong cv (ℕₚ.+-suc _ y))
gsub-ty-x-wk y (there {B = ctx} {Γ , T} B∈) eq = trans (gsub-ty-x-wk (1 + y) B∈ refl) (cong cv (ℕₚ.+-suc _ y))

gsub-ty-x-wk′ : ∀ y →
                x ∶ ctx ∈G Ψ →
                gsub-ty-x x (gsub-wk y Ψ) ≡ cv (y + x)
gsub-ty-x-wk′ y ctx∈ = trans (gsub-ty-x-wk y ctx∈ refl) (cong cv (ℕₚ.+-comm _ y))

gsub-ty-x-id : x ∶ ctx ∈G Ψ →
               gsub-ty-x x (gsub-id Ψ) ≡ cv x
gsub-ty-x-id = gsub-ty-x-wk′ 0

gsub-ty-x-gwk : x ∶ ctx ∈G Ψ →
                Φ ⊢gw γ ∶ Ψ →
                gsub-ty-x x (gsub-id Ψ) [ γ ] ≡ gsub-ty-x (wk-x x γ) (gsub-id Φ)
gsub-ty-x-gwk ctx∈ ⊢γ
  rewrite gsub-ty-x-id (x-gwk ⊢γ ctx∈)
        | gsub-ty-x-id ctx∈ = refl

gwk-gsub-id-q-x : ∀ n Γ →
                  x ∶ B ∈G repeat (ctx ∷_) n (ctx ∷ Ψ) →
                  B ≡ ctx →
                  Φ ⊢gw γ ∶ Ψ →
                  gsub-ty-x x (repeat gsub-q n (ctx Γ ∷ gsub-id Ψ)) [ repeat q n γ ] ≡ gsub-ty-x (wk-x x (repeat q n (q γ))) (repeat gsub-q n (ctx (Γ [ γ ]) ∷ gsub-id Φ))
gwk-gsub-id-q-x zero Γ here eq ⊢γ = refl
gwk-gsub-id-q-x zero Γ (there {B = ctx} ctx∈) eq ⊢γ = gsub-ty-x-gwk ctx∈ ⊢γ
gwk-gsub-id-q-x (suc n) Γ (here {_} {ctx}) eq ⊢γ = refl
gwk-gsub-id-q-x (suc n) Γ (there {B = ctx} ctx∈) eq ⊢γ = trans (cong (_[ repeat q (1 + n) _ ]) (sym (gwk-gsub-ty-x _ (repeat gsub-q n (ctx Γ ∷ gsub-id _)) (p id))))
                                                         (trans (gwk-lc-comp (gsub-ty-x _ (repeat gsub-q n (ctx Γ L.∷ gsub-id _))) (p id) (repeat q (1 + n) _))
                                                         (trans (cong (gwk-lc (gsub-ty-x _ (repeat gsub-q n (ctx Γ ∷ gsub-id _)))) (sym (∘w-pid (repeat q n _))))
                                                         (trans (sym (gwk-lc-comp (gsub-ty-x _ (repeat gsub-q n (ctx Γ L.∷ gsub-id _))) (repeat q n _) (p id)))
                                                         (trans (cong (λ σ → σ [ p id ]) (gwk-gsub-id-q-x n Γ ctx∈ refl ⊢γ))
                                                                (gwk-gsub-ty-x (wk-x _ (repeat q n (q _))) (repeat gsub-q n (ctx (Γ [ _ ]) ∷ gsub-id _)) (p id))))))

mutual
  gwk-gsub-id-q-ty : ∀ n Γ →
                    repeat (ctx ∷_) n (ctx ∷ Ψ) ⊢[ i ] T →
                    Φ ⊢gw γ ∶ Ψ →
                    T [ repeat gsub-q n (ctx Γ ∷ gsub-id Ψ) ] [ repeat q n γ ] ≡ T [ repeat q n (q γ) ] [ repeat gsub-q n (ctx (Γ [ γ ]) ∷ gsub-id Φ) ]
  gwk-gsub-id-q-ty n Γ (⊢N x) ⊢γ     = refl
  gwk-gsub-id-q-ty n Γ (⊢⟶ ⊢S ⊢T) ⊢γ = cong₂ _⟶_ (gwk-gsub-id-q-ty n Γ ⊢S ⊢γ) (gwk-gsub-id-q-ty n Γ ⊢T ⊢γ)
  gwk-gsub-id-q-ty n Γ (⊢□ ⊢Δ ⊢T) ⊢γ = cong₂ □ (gwk-gsub-id-q-lctx n Γ ⊢Δ ⊢γ) (gwk-gsub-id-q-ty n Γ ⊢T ⊢γ)
  gwk-gsub-id-q-ty n Γ (⊢⇒ ⊢T) ⊢γ    = cong ctx⇒_ (gwk-gsub-id-q-ty (suc n) Γ ⊢T ⊢γ)

  gwk-gsub-id-q-lctx : ∀ n Γ →
                       repeat (ctx ∷_) n (ctx ∷ Ψ) ⊢l[ i ] Δ →
                       Φ ⊢gw γ ∶ Ψ →
                       Δ [ repeat gsub-q n (ctx Γ ∷ gsub-id Ψ) ] [ repeat q n γ ] ≡ Δ [ repeat q n (q γ) ] [ repeat gsub-q n (ctx (Γ [ γ ]) ∷ gsub-id Φ) ]
  gwk-gsub-id-q-lctx n Γ (⊢[] _) ⊢γ       = refl
  gwk-gsub-id-q-lctx n Γ (⊢ctx _ ctx∈) ⊢γ = gwk-gsub-id-q-x n Γ ctx∈ refl ⊢γ
  gwk-gsub-id-q-lctx n Γ (⊢∷ ⊢Δ ⊢T) ⊢γ    = cong₂ _∷_ (gwk-gsub-id-q-ty n Γ ⊢T ⊢γ) (gwk-gsub-id-q-lctx n Γ ⊢Δ ⊢γ)

gwk-gsub-id-ty : ∀ Γ →
                 ctx ∷ Ψ ⊢[ i ] T →
                 Φ ⊢gw γ ∶ Ψ →
                 T [ ctx Γ ∷ gsub-id Ψ ] [ γ ] ≡ T [ q γ ] [ ctx (Γ [ γ ]) ∷ gsub-id Φ ]
gwk-gsub-id-ty = gwk-gsub-id-q-ty 0

gwk-gsub-id-lctx : ∀ Γ →
                   ctx ∷ Ψ ⊢l[ i ] Δ →
                   Φ ⊢gw γ ∶ Ψ →
                   Δ [ ctx Γ ∷ gsub-id Ψ ] [ γ ] ≡ Δ [ q γ ] [ ctx (Γ [ γ ]) ∷ gsub-id Φ ]
gwk-gsub-id-lctx = gwk-gsub-id-q-lctx 0


mutual
  gsub-id-ty-gen : ∀ n →
                   repeat (ctx ∷_) n Ψ ⊢[ i ] T →
                   T [ repeat gsub-q n (gsub-id Ψ) ] ≡ T
  gsub-id-ty-gen n (⊢N _)     = refl
  gsub-id-ty-gen n (⊢⟶ ⊢S ⊢T) = cong₂ _⟶_ (gsub-id-ty-gen n ⊢S) (gsub-id-ty-gen n ⊢T)
  gsub-id-ty-gen n (⊢□ ⊢Γ ⊢T) = cong₂ □ (gsub-id-lctx-gen n ⊢Γ) (gsub-id-ty-gen n ⊢T)
  gsub-id-ty-gen n (⊢⇒ ⊢T)    = cong ctx⇒_ (gsub-id-ty-gen (suc n) ⊢T)

  gsub-id-lctx-gen : ∀ n →
                     repeat (ctx ∷_) n Ψ ⊢l[ i ] Γ →
                     Γ [ repeat gsub-q n (gsub-id Ψ) ] ≡ Γ
  gsub-id-lctx-gen n (⊢[] _)       = refl
  gsub-id-lctx-gen n ⊢Γ@(⊢ctx _ _) = trans (lctx-gsub-wk≈gwk-gen n 0 _ ⊢Γ) (cong cv (gwk-id-x n _))
  gsub-id-lctx-gen n (⊢∷ ⊢Γ ⊢T)    = cong₂ _∷_ (gsub-id-ty-gen n ⊢T) (gsub-id-lctx-gen n ⊢Γ)

gsub-id-ty : Ψ ⊢[ i ] T →
             T [ gsub-id Ψ ] ≡ T
gsub-id-ty = gsub-id-ty-gen 0

gsub-id-lctx : Ψ ⊢l[ i ] Γ →
               Γ [ gsub-id Ψ ] ≡ Γ
gsub-id-lctx = gsub-id-lctx-gen 0

-- Global Weakening of Terms and Local Substitutions

∈L-gwk : (γ : Gwk) → x ∶ T ∈L Γ → x ∶ T [ γ ] ∈L Γ [ γ ]
∈L-gwk γ here       = here
∈L-gwk γ (there T∈) = there (∈L-gwk γ T∈)

^^-gwk : (Γ : List Typ) (Δ : LCtx) (γ : Gwk) → (Γ ^^ Δ) [ γ ] ≡ L.map (_[ γ ]) Γ ^^ (Δ [ γ ])
^^-gwk [] Δ γ      = refl
^^-gwk (T ∷ Γ) Δ γ = cong (_ ∷_) (^^-gwk Γ Δ γ)

mutual
  trm-gwk : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ′ ⊢gw γ ∶ Ψ → Ψ′ ﹔ Γ [ γ ] ⊢[ i ] t [ γ ] ∶ T [ γ ]
  trm-gwk (v-wf ⊢Γ T∈) ⊢γ                   = v-wf (lctx-gwk ⊢Γ ⊢γ) (∈L-gwk _ T∈)
  trm-gwk (gv-wf T∈ ⊢δ) ⊢γ                  = gv-wf (x-gwk ⊢γ T∈) (lsubst-gwk ⊢δ ⊢γ)
  trm-gwk (zero-wf ⊢Γ) ⊢γ                   = zero-wf (lctx-gwk ⊢Γ ⊢γ)
  trm-gwk (succ-wf ⊢t) ⊢γ                   = succ-wf (trm-gwk ⊢t ⊢γ)
  trm-gwk (Λ-wf ⊢t) ⊢γ                      = Λ-wf (trm-gwk ⊢t ⊢γ)
  trm-gwk ($-wf ⊢t ⊢s) ⊢γ                   = $-wf (trm-gwk ⊢t ⊢γ) (trm-gwk ⊢s ⊢γ)
  trm-gwk (box-wf ⊢Γ ⊢t) ⊢γ                 = box-wf (lctx-gwk ⊢Γ ⊢γ) (trm-gwk ⊢t ⊢γ)
  trm-gwk {_} {Γ} {_} {_} {T} {_} {γ} (letbox-wf ⊢s ⊢Δ ⊢S ⊢T ⊢t) ⊢γ
    with trm-gwk ⊢t (q-wf′ ⊢γ (b-wf ⊢Δ ⊢S))
  ...  | ⊢t′
       rewrite gwk-lc-comp Γ (p id) (q γ)
             | gwk-ty-comp T (p id) (q γ)
             | sym (∘w-pid γ)
             | sym (gwk-lc-comp Γ γ (p id))
             | sym (gwk-ty-comp T γ (p id)) = letbox-wf (trm-gwk ⊢s ⊢γ) (lctx-gwk ⊢Δ ⊢γ) (ty-gwk ⊢S ⊢γ) (ty-gwk ⊢T ⊢γ) ⊢t′
  trm-gwk {_} {Γ} {_} {_} {T} {_} {γ} (Λc-wf ⊢Γ ⊢t) ⊢γ
    with trm-gwk ⊢t (q-wf′ ⊢γ (ctx-wf (proj₂ (⊢gw-inv ⊢γ))))
  ...  | ⊢t′
       rewrite gwk-lc-comp Γ (p id) (q γ)
             | sym (∘w-pid γ)
             | sym (gwk-lc-comp Γ γ (p id)) = Λc-wf (lctx-gwk ⊢Γ ⊢γ) ⊢t′
  trm-gwk ($c-wf ⊢t ⊢Δ ⊢T refl) ⊢γ          = $c-wf (trm-gwk ⊢t ⊢γ) (lctx-gwk ⊢Δ ⊢γ) (ty-gwk ⊢T (q-wf′ ⊢γ (ctx-wf ⊢Ψ))) (gwk-gsub-id-ty _ ⊢T ⊢γ)
    where ⊢Ψ = presup-l ⊢Δ

  lsubst-gwk : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → Ψ′ ⊢gw γ ∶ Ψ → Ψ′ ﹔ Γ [ γ ] ⊢s[ i ] δ [ γ ] ∶ Δ [ γ ]
  lsubst-gwk {γ = γ} (wk-wf {Δ = Δ} ⊢Γ ctx∈ refl) ⊢γ
    = wk-wf (lctx-gwk ⊢Γ ⊢γ) (x-gwk ⊢γ ctx∈) (^^-gwk Δ (cv _) γ)
  lsubst-gwk ([]-wf ⊢Γ) ⊢γ   = []-wf (lctx-gwk ⊢Γ ⊢γ)
  lsubst-gwk (∷-wf ⊢δ ⊢t) ⊢γ = ∷-wf (lsubst-gwk ⊢δ ⊢γ) (trm-gwk ⊢t ⊢γ)


-- Global weakening for Global Substitutions

gsubst-gwk : Ψ ⊢ σ ∶ Φ → Ψ′ ⊢gw γ ∶ Ψ → Ψ′ ⊢ σ [ γ ] ∶ Φ
gsubst-gwk ([]-wf ⊢Ψ) ⊢γ         = []-wf (proj₁ (⊢gw-inv ⊢γ))
gsubst-gwk {γ = γ} (trm-wf {_} {σ} {_} {Γ} {T} {t} ⊢σ ⊢Γ ⊢T ⊢t) ⊢γ
  with trm-gwk ⊢t ⊢γ
...  | ⊢t′
     rewrite lctx-gsubst-gwk Γ σ γ
           | ty-gsubst-gwk T σ γ = trm-wf (gsubst-gwk ⊢σ ⊢γ) ⊢Γ ⊢T ⊢t′
gsubst-gwk (ctx-wf ⊢σ ⊢Γ) ⊢γ     = ctx-wf (gsubst-gwk ⊢σ ⊢γ) (lctx-gwk ⊢Γ ⊢γ)


-- Global Substitution Lemma for Types and Local Contexts

lookup-lctx-gen : x ∶ B ∈G Φ → B ≡ ctx → Ψ ⊢ σ ∶ Φ → Ψ ⊢l[ 𝟘 ] gsub-ty-x x σ
lookup-lctx-gen here refl (ctx-wf ⊢σ ⊢Γ)                          = ⊢Γ
lookup-lctx-gen (there {_} {_} {ctx} ctx∈) refl (trm-wf ⊢σ _ _ _) = lookup-lctx-gen ctx∈ refl ⊢σ
lookup-lctx-gen (there {_} {_} {ctx} ctx∈) refl (ctx-wf ⊢σ _)     = lookup-lctx-gen ctx∈ refl ⊢σ

lookup-lctx : x ∶ ctx ∈G Φ → Ψ ⊢ σ ∶ Φ → Ψ ⊢l[ 𝟘 ] gsub-ty-x x σ
lookup-lctx ctx∈ ⊢σ = lookup-lctx-gen ctx∈ refl ⊢σ

lookup-lctx′ : x ∶ ctx ∈G Φ → Ψ ⊢ σ ∶ Φ → Ψ ⊢l[ i ] gsub-ty-x x σ
lookup-lctx′ ctx∈ ⊢σ = lift-lctx″ _ (lookup-lctx ctx∈ ⊢σ)

mutual
  ty-gsubst : Φ ⊢[ i ] T → Ψ ⊢ σ ∶ Φ → Ψ ⊢[ i ] T [ σ ]
  ty-gsubst (⊢N _) ⊢σ     = ⊢N (proj₁ (gsubst-inv ⊢σ))
  ty-gsubst (⊢⟶ ⊢S ⊢T) ⊢σ = ⊢⟶ (ty-gsubst ⊢S ⊢σ) (ty-gsubst ⊢T ⊢σ)
  ty-gsubst (⊢□ ⊢Γ ⊢T) ⊢σ = ⊢□ (lctx-gsubst ⊢Γ ⊢σ) (ty-gsubst ⊢T ⊢σ)
  ty-gsubst (⊢⇒ ⊢T) ⊢σ    = ⊢⇒ (ty-gsubst ⊢T (ctx-wf (gsubst-gwk ⊢σ (p-wf (id-wf ⊢Ψ) (ctx-wf ⊢Ψ))) (⊢ctx (⊢ctx ⊢Ψ) here)))
    where ⊢Ψ = proj₁ (gsubst-inv ⊢σ)

  lctx-gsubst : Φ ⊢l[ i ] Γ → Ψ ⊢ σ ∶ Φ → Ψ ⊢l[ i ] Γ [ σ ]
  lctx-gsubst (⊢[] ⊢Φ) ⊢σ       = ⊢[] (proj₁ (gsubst-inv ⊢σ))
  lctx-gsubst (⊢ctx ⊢Φ ctx∈) ⊢σ = lookup-lctx′ ctx∈ ⊢σ
  lctx-gsubst (⊢∷ ⊢Γ ⊢T) ⊢σ     = ⊢∷ (lctx-gsubst ⊢Γ ⊢σ) (ty-gsubst ⊢T ⊢σ)


-- Typing of Global Identity


∈G-gwk-lookup : ∀ Φ B Ψ → L.length Φ ∶ B [ repeat p (1 + L.length Φ) id ] ∈G Φ ++ (B ∷ Ψ)
∈G-gwk-lookup [] B Ψ = here
∈G-gwk-lookup (B′ ∷ Φ) B Ψ
  rewrite sym (gwk-bnd-comp B (repeat p (1 + L.length Φ) id) (p id))
  = there (∈G-gwk-lookup Φ B Ψ)

⊢gsub-q : Ψ ⊢ σ ∶ Φ → ctx ∷ Ψ ⊢ gsub-q σ ∶ ctx ∷ Φ
⊢gsub-q ⊢σ = ctx-wf (gsubst-gwk ⊢σ (p-wf (id-wf ⊢Ψ) (ctx-wf ⊢Ψ))) (⊢ctx (⊢ctx ⊢Ψ) here)
  where ⊢Ψ = proj₁ (gsubst-inv ⊢σ)

⊢gsub-wk-gen : ∀ Φ → ⊢ Φ ++ Ψ → ⊢ Ψ → Φ ++ Ψ ⊢ gsub-wk (L.length Φ) Ψ ∶ Ψ
⊢gsub-wk-gen {[]} Φ ⊢ΦΨ ⊢[]                 = []-wf ⊢ΦΨ
⊢gsub-wk-gen {.ctx ∷ Ψ} Φ ⊢ΦΨ (⊢ctx ⊢Ψ)     = ctx-wf helper (⊢ctx ⊢ΦΨ (∈G-gwk-lookup Φ ctx Ψ))
  where ⊢ΦΨ′ : ⊢ (Φ L.++ L.[ ctx ]) L.++ Ψ
        ⊢ΦΨ′ = subst ⊢_ (sym (++-assoc Φ L.[ ctx ] Ψ)) ⊢ΦΨ
        helper : Φ L.++ ctx L.∷ Ψ ⊢ gsub-wk (1 + L.length Φ) Ψ ∶ Ψ
        helper
          with ⊢gsub-wk-gen (Φ ++ L.[ ctx ]) ⊢ΦΨ′ ⊢Ψ
        ...  | ⊢wk
             rewrite ++-assoc Φ L.[ ctx ] Ψ
                   | Lₚ.length-++ Φ {L.[ ctx ]}
                   | ℕₚ.+-comm (L.length Φ) 1 = ⊢wk
⊢gsub-wk-gen {(Γ , T) ∷ Ψ} Φ ⊢ΦΨ (⊢∷ ⊢Γ ⊢T) = trm-wf helper ⊢Γ ⊢T helper′
  where ⊢ΦΨ′ : ⊢ (Φ L.++ _) L.++ Ψ
        ⊢ΦΨ′ = subst ⊢_ (sym (++-assoc Φ _ Ψ)) ⊢ΦΨ
        ⊢Ψ   = presup-l ⊢Γ
        ⊢wk  = gwk-repeat (Φ ++ L.[ Γ , T ]) ⊢ΦΨ′
        helper : Φ L.++ (Γ , T) L.∷ Ψ ⊢ gsub-wk (1 + L.length Φ) Ψ ∶ Ψ
        helper
          with ⊢gsub-wk-gen (Φ ++ L.[ Γ , T ]) ⊢ΦΨ′ ⊢Ψ
        ...  | ⊢wk
             rewrite ++-assoc Φ L.[ Γ , T ] Ψ
                   | Lₚ.length-++ Φ {L.[ Γ , T ]}
                   | ℕₚ.+-comm (L.length Φ) 1 = ⊢wk
        helper′ : Φ L.++ (Γ , T) L.∷ Ψ ﹔ Γ [ gsub-wk (1 + L.length Φ) Ψ ] ⊢[ 𝟘 ]
                         gvar (L.length Φ) (lsub-id Γ [ repeat p (1 + L.length Φ) id ]) ∶ T [ gsub-wk (1 + L.length Φ) Ψ ]
        helper′
          rewrite ty-gsub-wk≈gwk (1 + L.length Φ) _ ⊢T
                | lctx-gsub-wk≈gwk (1 + L.length Φ) _ ⊢Γ = gv-wf (∈G-gwk-lookup Φ (Γ , T) Ψ)
                                                                 (lsubst-gwk (⊢lsub-id ⊢Γ)
                                                                             (subst₂ (λ Ψ′ l → Ψ′ ⊢gw repeat p l id ∶ Ψ)
                                                                                     (Lₚ.++-assoc Φ L.[ Γ , T ] Ψ)
                                                                                     (trans (length-++ Φ {L.[ Γ , T ]}) (ℕₚ.+-comm _ 1))
                                                                                     ⊢wk))

⊢gsub-id : ⊢ Ψ → Ψ ⊢ gsub-id Ψ ∶ Ψ
⊢gsub-id ⊢Ψ = ⊢gsub-wk-gen [] ⊢Ψ ⊢Ψ


-- Presuposition of typing

∈G⇒wf-gen : x ∶ B ∈G Ψ → B ≡ (Γ , T) → ⊢ Ψ → Ψ ⊢l[ 𝟘 ] Γ × Ψ ⊢[ 𝟘 ] T
∈G⇒wf-gen here refl (⊢∷ ⊢Γ ⊢T) = lctx-gwk ⊢Γ ⊢pid , ty-gwk ⊢T ⊢pid
  where ⊢Ψ   = presup-l ⊢Γ
        ⊢pid = p-wf (id-wf ⊢Ψ) (b-wf ⊢Γ ⊢T)
∈G⇒wf-gen (there {_} {_} {_ , _} T∈) refl (⊢ctx ⊢Ψ)
  with ∈G⇒wf-gen T∈ refl ⊢Ψ
...  | ⊢Γ , ⊢T                 = lctx-gwk ⊢Γ ⊢pid , ty-gwk ⊢T ⊢pid
  where ⊢pid = p-wf (id-wf ⊢Ψ) (ctx-wf ⊢Ψ)
∈G⇒wf-gen (there {_} {_} {_ , _} T∈) refl (⊢∷ ⊢Δ ⊢S)
  with ∈G⇒wf-gen T∈ refl (presup-l ⊢Δ)
...  | ⊢Γ , ⊢T                 = lctx-gwk ⊢Γ ⊢pid , ty-gwk ⊢T ⊢pid
  where ⊢Ψ   = presup-l ⊢Δ
        ⊢pid = p-wf (id-wf ⊢Ψ) (b-wf ⊢Δ ⊢S)

∈G⇒wf : x ∶ Γ , T ∈G Ψ → ⊢ Ψ → Ψ ⊢l[ 𝟘 ] Γ × Ψ ⊢[ 𝟘 ] T
∈G⇒wf T∈ ⊢Ψ = ∈G⇒wf-gen T∈ refl ⊢Ψ

∈G⇒wf′ : ∀ i → x ∶ Γ , T ∈G Ψ → ⊢ Ψ → Ψ ⊢l[ i ] Γ × Ψ ⊢[ i ] T
∈G⇒wf′ 𝟘 T∈ ⊢Ψ = ∈G⇒wf T∈ ⊢Ψ
∈G⇒wf′ 𝟙 T∈ ⊢Ψ
  with ∈G⇒wf T∈ ⊢Ψ
...  | ⊢Γ , ⊢T = lift-lctx ⊢Γ , lift-ty ⊢T

mutual
  presup-trm : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ ⊢l[ i ] Γ × Ψ ⊢[ i ] T
  presup-trm (v-wf ⊢Γ T∈Γ)  = ⊢Γ , ∈L⇒wf T∈Γ ⊢Γ
  presup-trm (gv-wf T∈ ⊢δ)  = ⊢Γ , proj₂ (∈G⇒wf′ _ T∈ (presup-l ⊢Γ))
    where ⊢Γ = proj₁ (presup-lsub ⊢δ)
  presup-trm (zero-wf ⊢Γ)   = ⊢Γ , ⊢N (presup-l ⊢Γ)
  presup-trm (succ-wf ⊢t)   = presup-trm ⊢t
  presup-trm (Λ-wf ⊢t)
    with presup-trm ⊢t
  ...  | ⊢∷ ⊢Γ ⊢S , ⊢T      = ⊢Γ , ⊢⟶ ⊢S ⊢T
  presup-trm ($-wf ⊢s ⊢t)
    with presup-trm ⊢s
  ...  | ⊢Γ , ⊢⟶ ⊢S ⊢T      = ⊢Γ , ⊢T
  presup-trm (box-wf ⊢Γ ⊢t) = ⊢Γ , ⊢□ (proj₁ (presup-trm ⊢t)) (proj₂ (presup-trm ⊢t))
  presup-trm (letbox-wf ⊢s ⊢Δ ⊢S ⊢T ⊢t)
    with presup-trm ⊢s
  ...  | ⊢Γ , _             = ⊢Γ , ⊢T
  presup-trm (Λc-wf ⊢Γ ⊢t)  = ⊢Γ , ⊢⇒ (proj₂ (presup-trm ⊢t))
  presup-trm ($c-wf ⊢t ⊢Δ ⊢T refl)
    with presup-trm ⊢t
  ...  | ⊢Γ , _             = ⊢Γ , ty-gsubst ⊢T (ctx-wf (⊢gsub-id (presup-l ⊢Δ)) ⊢Δ)

  presup-lsub : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → Ψ ⊢l[ i ] Γ × Ψ ⊢l[ i ] Δ
  presup-lsub (wk-wf ⊢Γ ctx∈ eq) = ⊢Γ , ⊢ctx (presup-l ⊢Γ) ctx∈
  presup-lsub ([]-wf ⊢Γ)         = ⊢Γ , ⊢[] (presup-l ⊢Γ)
  presup-lsub (∷-wf ⊢δ ⊢t)
    with presup-lsub ⊢δ | presup-trm ⊢t
  ...  | ⊢Γ , ⊢Δ | _ , ⊢T        = ⊢Γ , ⊢∷ ⊢Δ ⊢T
