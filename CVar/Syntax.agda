{-# OPTIONS --without-K --safe #-}

module CVar.Syntax where

open import Level hiding (zero; suc)

open import Lib public

open import Data.Sum
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


lc-length : LCtx → ℕ
lc-length []      = 0
lc-length (cv x)  = 0
lc-length (_ ∷ Γ) = 1 + lc-length Γ

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

pid∘p*id : ∀ n → (p id ∘w repeat p n id) ≡ repeat p (1 + n) id
pid∘p*id zero    = refl
pid∘p*id (suc n) = cong p (pid∘p*id n)

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


lc-length-resp-gwk : (Γ : LCtx) (γ : Gwk) → lc-length (Γ [ γ ]) ≡ lc-length Γ
lc-length-resp-gwk [] γ = refl
lc-length-resp-gwk (cv x) γ = refl
lc-length-resp-gwk (_ ∷ Γ) γ = cong suc (lc-length-resp-gwk Γ γ)

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


-- Well-formedness of the Type-level

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


⊆l-refl : ∀ Γ → Γ ⊆l Γ
⊆l-refl []      = id-[]
⊆l-refl (cv x)  = id-cv
⊆l-refl (T ∷ Γ) = cons (⊆l-refl Γ)


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

-- Local weakenings are not in the most general form; we only need them for shifting
-- the de Bruijn indices.
data _﹔_⊢lw[_]_∶_ : GCtx → LCtx → Layer → Lwk → LCtx → Set where
  id-wf : Ψ ⊢l[ i ] Γ →
          Ψ ﹔ Γ ⊢lw[ i ] id ∶ Γ
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

⊢l-resp-⊆l : Ψ ⊢l[ i ] Γ → Γ ⊆l Δ → Ψ ⊢l[ i ] Δ
⊢l-resp-⊆l (⊢[] ⊢Ψ) id-[]        = ⊢[] ⊢Ψ
⊢l-resp-⊆l (⊢ctx ⊢Ψ ctx∈) id-cv  = ⊢ctx ⊢Ψ ctx∈
⊢l-resp-⊆l (⊢ctx ⊢Ψ ctx∈) cv-[]  = ⊢[] ⊢Ψ
⊢l-resp-⊆l (⊢∷ ⊢Γ ⊢T) (cons Γ⊆Δ) = ⊢∷ (⊢l-resp-⊆l ⊢Γ Γ⊆Δ) ⊢T

⊢lw-inv : Ψ ﹔ Γ ⊢lw[ i ] τ ∶ Δ → Ψ ⊢l[ i ] Γ × Ψ ⊢l[ i ] Δ
⊢lw-inv (id-wf ⊢Γ) = ⊢Γ , ⊢Γ
⊢lw-inv (p-wf ⊢τ ⊢T)
  with ⊢lw-inv ⊢τ
...  | ⊢Γ , ⊢Δ     = ⊢∷ ⊢Γ ⊢T , ⊢Δ
⊢lw-inv (q-wf ⊢τ ⊢T)
  with ⊢lw-inv ⊢τ
...  | ⊢Γ , ⊢Δ     = ⊢∷ ⊢Γ ⊢T , ⊢∷ ⊢Δ ⊢T


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
lwk-gwk ⊢γ (id-wf ⊢Γ)   = id-wf (lctx-gwk ⊢Γ ⊢γ)
lwk-gwk ⊢γ (p-wf ⊢τ ⊢T) = p-wf (lwk-gwk ⊢γ ⊢τ) (ty-gwk ⊢T ⊢γ)
lwk-gwk ⊢γ (q-wf ⊢τ ⊢T) = q-wf (lwk-gwk ⊢γ ⊢τ) (ty-gwk ⊢T ⊢γ)

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


gctx-++⁻ : ∀ Φ → ⊢ Φ ++ Ψ → ⊢ Ψ
gctx-++⁻ [] ⊢Ψ                   = ⊢Ψ
gctx-++⁻ (ctx ∷ Φ) (⊢ctx ⊢ΦΨ)    = gctx-++⁻ Φ ⊢ΦΨ
gctx-++⁻ ((_ , _) ∷ Φ) (⊢∷ ⊢Γ _) = gctx-++⁻ Φ (presup-l ⊢Γ)


-- Convenient Lemmas

infixl 3 _++q[_]_

_++q[_]_ : GCtx → Gwk → GCtx → GCtx
[] ++q[ γ ] Ψ    = Ψ
T ∷ Φ ++q[ γ ] Ψ = (T [ repeat q (L.length Φ) γ ]) ∷ (Φ ++q[ γ ] Ψ)


repeat-q-wf : ∀ Φ n →
              ⊢ Φ ++ Ψ →
              L.length Φ ≡ n →
              Ψ′ ⊢gw γ ∶ Ψ →
              (Φ ++q[ γ ] Ψ′) ⊢gw repeat q n γ ∶ Φ ++ Ψ
repeat-q-wf [] zero ⊢ΦΨ eq ⊢γ                     = ⊢γ
repeat-q-wf (.ctx ∷ Φ) (suc n) (⊢ctx ⊢ΦΨ) refl ⊢γ = q-wf′ (repeat-q-wf Φ n ⊢ΦΨ refl ⊢γ) (ctx-wf ⊢ΦΨ)
repeat-q-wf (._ ∷ Φ) (suc n) (⊢∷ ⊢Γ ⊢T) refl ⊢γ   = q-wf′ (repeat-q-wf Φ n ⊢ΦΨ refl ⊢γ) (b-wf ⊢Γ ⊢T)
  where ⊢ΦΨ = presup-l ⊢Γ

gwk-repeat : ∀ Φ → ⊢ Φ ++ Ψ → Φ ++ Ψ ⊢gw repeat p (L.length Φ) id ∶ Ψ
gwk-repeat [] ⊢Ψ                     = id-wf ⊢Ψ
gwk-repeat (.ctx ∷ Φ) (⊢ctx ⊢ΦΨ)     = p-wf (gwk-repeat Φ ⊢ΦΨ) (ctx-wf ⊢ΦΨ)
gwk-repeat (.(_ , _) ∷ Φ) (⊢∷ ⊢Γ ⊢T) = p-wf (gwk-repeat Φ (presup-l ⊢Γ)) (b-wf ⊢Γ ⊢T)

gwk-repeat′ : ∀ Φ n → ⊢ Φ ++ Ψ → L.length Φ ≡ n → Φ ++ Ψ ⊢gw repeat p n id ∶ Ψ
gwk-repeat′ Φ n ⊢ΦΨ refl = gwk-repeat Φ ⊢ΦΨ

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
    -- wk x n: a weakening for the contextual variable x with n p weakenings
    wk  : ℕ → ℕ → LSubst
    -- [] n: a weakening with p weakenings and domain local context ends with []
    []  : ℕ → LSubst
    -- []′ x n: a weakening with p weakenings and domain local context ends with cv x
    []′ : ℕ → ℕ → LSubst
    _∷_ : Trm → LSubst → LSubst


variable
  t t′ t″ : Trm
  s s′ s″ : Trm
  δ δ′ δ″ : LSubst

lsub-offset : LSubst → ℕ
lsub-offset (wk _ n)  = n
lsub-offset ([] n)    = n
lsub-offset ([]′ _ n) = n
lsub-offset (_ ∷ δ)   = lsub-offset δ

infixr 3 _+l_

_+l_ : List Trm → LSubst → LSubst
[] +l δ     = δ
t ∷ ts +l δ = t ∷ (ts +l δ)

lsub-offset-+l : ∀ ts δ → lsub-offset (ts +l δ) ≡ lsub-offset δ
lsub-offset-+l [] δ       = refl
lsub-offset-+l (t ∷ ts) δ = lsub-offset-+l ts δ

+l-assoc : ∀ ts ts′ δ → (ts +l ts′ +l δ) ≡ ((ts ++ ts′) +l δ)
+l-assoc [] ts′ δ       = refl
+l-assoc (t ∷ ts) ts′ δ = cong (t ∷_) (+l-assoc ts ts′ δ)


-- Global Weakening of Terms and Local Substitutions

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
  gwk-lsubst (wk x n) γ  = wk (wk-x x γ) n
  gwk-lsubst ([] n) γ    = [] n
  gwk-lsubst ([]′ x n) γ = []′ (wk-x x γ) n
  gwk-lsubst (t ∷ δ) γ   = gwk-trm t γ ∷ gwk-lsubst δ γ

instance
  gwk-trm-mon : Monotone Trm Gwk
  gwk-trm-mon = record { _[_] = gwk-trm }

  gwk-lsubst-mon : Monotone LSubst Gwk
  gwk-lsubst-mon = record { _[_] = gwk-lsubst }

mutual
  gwk-id-trm : ∀ n (t : Trm) → t [ repeat q n id ] ≡ t
  gwk-id-trm n (var x)    = refl
  gwk-id-trm n (gvar x δ) = cong₂ gvar (gwk-id-x n x) (gwk-id-lsubst n δ)
  gwk-id-trm n zero       = refl
  gwk-id-trm n (succ t)   = cong succ (gwk-id-trm n t)
  gwk-id-trm n (Λ t)      = cong Λ (gwk-id-trm n t)
  gwk-id-trm n (t $ s)    = cong₂ _$_ (gwk-id-trm n t) (gwk-id-trm n s)
  gwk-id-trm n (box t)    = cong box (gwk-id-trm n t)
  gwk-id-trm n (letbox Γ s t)
    rewrite gwk-id-lc n Γ = cong₂ (letbox Γ) (gwk-id-trm n s) (gwk-id-trm (1 + n) t)
  gwk-id-trm n (Λc t)     = cong Λc (gwk-id-trm (suc n) t)
  gwk-id-trm n (t $c Γ)   = cong₂ _$c_ (gwk-id-trm n t) (gwk-id-lc n Γ)

  gwk-id-lsubst : ∀ n (δ : LSubst) → δ [ repeat q n id ] ≡ δ
  gwk-id-lsubst n (wk x m)  = cong (λ y → wk y m) (gwk-id-x n x)
  gwk-id-lsubst n ([] m)    = refl
  gwk-id-lsubst n ([]′ x m) = cong (λ y → []′ y m) (gwk-id-x n x)
  gwk-id-lsubst n (t ∷ δ)   = cong₂ _∷_ (gwk-id-trm n t) (gwk-id-lsubst n δ)


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
  gwk-lsubst-comp (wk x n) γ γ′ = cong (λ y → wk y n) (gwk-x-comp x γ γ′)
  gwk-lsubst-comp ([] _) γ γ′   = refl
  gwk-lsubst-comp ([]′ x _) γ γ′
    rewrite gwk-x-comp x γ γ′   = refl
  gwk-lsubst-comp (t ∷ δ) γ γ′  = cong₂ _∷_ (gwk-trm-comp t γ γ′) (gwk-lsubst-comp δ γ γ′)


-- Local Weakening of Terms and Local Substitutions

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
  lwk-lsubst (wk x n) τ  = wk x (wk-x n τ)
  lwk-lsubst ([] n) τ    = [] (wk-x n τ)
  lwk-lsubst ([]′ x n) τ = []′ x (wk-x n τ)
  lwk-lsubst (t ∷ δ) τ   = lwk-trm t τ ∷ lwk-lsubst δ τ


-- Weakenings between Dual Contexts

Awk : Set
Awk = Gwk × Lwk

instance
  awk-trm-mon : Monotone Trm Awk
  awk-trm-mon = record { _[_] = λ t (γ , τ) → lwk-trm (gwk-trm t γ) τ }

  awk-lsubst-mon : Monotone LSubst Awk
  awk-lsubst-mon = record { _[_] = λ δ (γ , τ) → lwk-lsubst (gwk-lsubst δ γ) τ }


-- Global Substitutions

data GSub : Set where
  ctx : LCtx → GSub
  trm : Trm → GSub

GSubst : Set
GSubst = List GSub

variable
  σ σ′ σ″ : GSubst

gwk-gsub : GSub → Gwk → GSub
gwk-gsub (ctx Γ) γ = ctx (Γ [ γ ])
gwk-gsub (trm t) γ = trm (t [ γ ])

instance
  gwk-gsub-mon : Monotone GSub Gwk
  gwk-gsub-mon = record { _[_] = gwk-gsub }

gwk-gsubst : GSubst → Gwk → GSubst
gwk-gsubst σ γ = L.map (λ b → b [ γ ]) σ

instance
  gwk-gsubst-mon : Monotone GSubst Gwk
  gwk-gsubst-mon = record { _[_] = gwk-gsubst }

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

-- Global Substitutions and Global Weakenings Commute

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
  ty-gsubst-gwk (ctx⇒ T) σ γ = cong ctx⇒_ (trans (ty-gsubst-gwk T (ctx (cv 0) ∷ (σ [ p id ])) (q γ))
                                                 (cong (λ σ → T [ ctx (cv 0) ∷ σ ])
                                                       (trans (gwk-gsub-comp σ (p id) (q γ))
                                                       (sym (trans (gwk-gsub-comp σ γ (p id))
                                                                   (cong (σ [_]) (∘w-pid γ)))))))

  lctx-gsubst-gwk : (Γ : LCtx) (σ : GSubst) (γ : Gwk) → Γ [ σ ] [ γ ] ≡ Γ [ σ [ γ ] ]
  lctx-gsubst-gwk [] σ γ      = refl
  lctx-gsubst-gwk (cv x) σ γ  = gwk-gsub-ty-x x σ γ
  lctx-gsubst-gwk (T ∷ Γ) σ γ = cong₂ _∷_ (ty-gsubst-gwk T σ γ) (lctx-gsubst-gwk Γ σ γ)


-- Concatenation of Local Contexts

infixr 5 _^^_

_^^_ : List Typ → LCtx → LCtx
[] ^^ Δ = Δ
(T ∷ Γ) ^^ Δ = T ∷ (Γ ^^ Δ)

^^-assoc : ∀ Γ Γ′ Δ → Γ ^^ Γ′ ^^ Δ ≡ (Γ ++ Γ′) ^^ Δ
^^-assoc [] Γ′ Δ      = refl
^^-assoc (T ∷ Γ) Γ′ Δ = cong (T ∷_) (^^-assoc Γ Γ′ Δ)

^^-length-[] : ∀ Γ → lc-length (Γ ^^ []) ≡ L.length Γ
^^-length-[] []      = refl
^^-length-[] (_ ∷ Γ) = cong suc (^^-length-[] Γ)

^^-length-cv : ∀ Γ → lc-length (Γ ^^ cv x) ≡ L.length Γ
^^-length-cv []      = refl
^^-length-cv (_ ∷ Γ) = cong suc (^^-length-cv Γ)

^^-resp-length : ∀ Γ Δ → lc-length (Γ ^^ Δ) ≡ L.length Γ + lc-length Δ
^^-resp-length [] Δ      = refl
^^-resp-length (_ ∷ Γ) Δ = cong suc (^^-resp-length Γ Δ)

lsub-cv? : LSubst → ⊤ ⊎ ℕ
lsub-cv? (wk x _)  = inj₂ x
lsub-cv? ([] _)    = inj₁ _
lsub-cv? ([]′ x _) = inj₂ x
lsub-cv? (_ ∷ δ)   = lsub-cv? δ

lsub-cv?-+l : ∀ ts δ → lsub-cv? (ts +l δ) ≡ lsub-cv? δ
lsub-cv?-+l [] δ       = refl
lsub-cv?-+l (_ ∷ ts) δ = lsub-cv?-+l ts δ

lctx-cv? : LCtx → ⊤ ⊎ ℕ
lctx-cv? []      = inj₁ _
lctx-cv? (cv x)  = inj₂ x
lctx-cv? (_ ∷ Γ) = lctx-cv? Γ

cv-bound : Ψ ⊢l[ i ] Γ → ∀ {Δ} → Γ ≡ Δ ^^ cv x → x ∶ ctx ∈G Ψ
cv-bound (⊢[] ⊢Ψ) {[]} ()
cv-bound (⊢[] ⊢Ψ) {_ ∷ Δ} ()
cv-bound (⊢ctx ⊢Ψ ctx∈) {[]} refl = ctx∈
cv-bound (⊢∷ ⊢Γ ⊢T) {T ∷ Δ} refl  = cv-bound ⊢Γ refl

-- Local and Global Identities

lsub-wk : (y : ℕ) (Δ : LCtx) → LSubst
lsub-wk y []      = [] y
lsub-wk y (cv x)  = wk x y
lsub-wk y (T ∷ Δ) = var y ∷ lsub-wk (1 + y) Δ

lsub-id : LCtx → LSubst
lsub-id Γ = lsub-wk 0 Γ

gwk-lsub-wk : ∀ y Γ (γ : Gwk) → lsub-wk y Γ [ γ ] ≡ lsub-wk y (Γ [ γ ])
gwk-lsub-wk y [] γ      = refl
gwk-lsub-wk y (cv x) γ  = refl
gwk-lsub-wk y (T ∷ Γ) γ = cong (var y ∷_) (gwk-lsub-wk (suc y) Γ γ)

gwk-lsub-id : ∀ Γ (γ : Gwk) → lsub-id Γ [ γ ] ≡ lsub-id (Γ [ γ ])
gwk-lsub-id = gwk-lsub-wk 0

gsub-wk : (y : ℕ) (Ψ : GCtx) → GSubst
gsub-wk y []            = []
gsub-wk y (ctx ∷ Ψ)     = ctx (cv y) ∷ gsub-wk (1 + y) Ψ
gsub-wk y ((Γ , T) ∷ Ψ) = trm (gvar y (lsub-id Γ [ repeat p (1 + y) id ])) ∷ gsub-wk (1 + y) Ψ

gsub-id : GCtx → GSubst
gsub-id Ψ = gsub-wk 0 Ψ


-- Local Substitutions of Terms and Composition

lsub-x : ℕ → LSubst → Trm
lsub-x x (wk _ _)      = zero
lsub-x x ([] _)        = zero
lsub-x x ([]′ _ _)     = zero
lsub-x zero (t ∷ δ)    = t
lsub-x (suc x) (t ∷ δ) = lsub-x x δ

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
  wk x n ∘l δ′  = wk x (lsub-offset δ′)
  [] n ∘l δ′
    with lsub-cv? δ′
  ...  | inj₁ _ = [] (lsub-offset δ′)
  ...  | inj₂ x = []′ x (lsub-offset δ′)
  []′ x n ∘l δ′
    with lsub-cv? δ′
  ...  | inj₁ _ = [] (lsub-offset δ′)
  ...  | inj₂ x = []′ x (lsub-offset δ′)
  (t ∷ δ) ∘l δ′ = lsub-trm t δ′ ∷ (δ ∘l δ′)


lsub-wk-lwk-p* : ∀ x Γ n →
             lwk-lsubst (lsub-wk x Γ) (repeat p n id) ≡ lsub-wk (x + n) Γ
lsub-wk-lwk-p* x [] n                = cong [] (wk-x-repeat-p′ x n)
lsub-wk-lwk-p* x (cv y) n            = cong (wk y) (wk-x-repeat-p′ x n)
lsub-wk-lwk-p* x (T ∷ Γ) n
  rewrite wk-x-repeat-p′ x n
        | lsub-wk-lwk-p* (suc x) Γ n = refl

lsub-id-constr : ∀ T Γ →
                 var 0 ∷ lwk-lsubst (lsub-id Γ) (p id) ≡ lsub-id (T ∷ Γ)
lsub-id-constr T Γ
  rewrite lsub-wk-lwk-p* 0 Γ 1 = refl


-- Global Substitutions of Terms and Local Substitutions

gsub-trm-x : ℕ → GSubst → Trm
gsub-trm-x x []             = zero
gsub-trm-x zero (ctx _ ∷ σ) = zero
gsub-trm-x zero (trm t ∷ σ) = t
gsub-trm-x (suc x) (_ ∷ σ)  = gsub-trm-x x σ

mutual
  gsub-trm : Trm → GSubst → Trm
  gsub-trm (var x) σ        = var x
  gsub-trm (gvar x δ) σ     = lsub-trm (gsub-trm-x x σ) (gsub-lsubst δ σ)
  gsub-trm zero σ           = zero
  gsub-trm (succ t) σ       = succ (gsub-trm t σ)
  gsub-trm (Λ t) σ          = Λ (gsub-trm t σ)
  gsub-trm (t $ s) σ        = gsub-trm t σ $ gsub-trm s σ
  gsub-trm (box t) σ        = box (gsub-trm t σ)
  gsub-trm (letbox Γ s t) σ = letbox (Γ [ σ ]) (gsub-trm s σ) (gsub-trm t (trm (gvar 0 (lsub-id (Γ [ σ [ p id ] ]))) ∷ (σ [ p id ])))
  gsub-trm (Λc t) σ         = Λc (gsub-trm t (ctx (cv 0) ∷ (σ [ p id ])))
  gsub-trm (t $c Γ) σ       = gsub-trm t σ $c (Γ [ σ ])

  gsub-lsubst : LSubst → GSubst → LSubst
  gsub-lsubst (wk x n) σ = lwk-lsubst (lsub-id (gsub-ty-x x σ)) (repeat p n id)
  gsub-lsubst ([] n) σ   = [] n
  gsub-lsubst ([]′ x n) σ
    with gsub-ty-x x σ
  ...  | Γ
       with lctx-cv? Γ
  ...     | inj₁ _       = [] (lc-length Γ + n)
  ...     | inj₂ y       = []′ y (lc-length Γ + n)
  gsub-lsubst (t ∷ δ) σ  = gsub-trm t σ ∷ gsub-lsubst δ σ

instance
  gsub-trm-mon : Monotone Trm GSubst
  gsub-trm-mon = record { _[_] = gsub-trm }

  gsub-lsubst-mon : Monotone LSubst GSubst
  gsub-lsubst-mon = record { _[_] = gsub-lsubst }

gsubst-lsub-wk : ∀ y Γ (σ : GSubst) → lsub-wk y Γ [ σ ] ≡ lsub-wk y (Γ [ σ ])
gsubst-lsub-wk y [] σ      = refl
gsubst-lsub-wk y (cv x) σ  = lsub-wk-lwk-p* 0 (gsub-ty-x x σ) y
gsubst-lsub-wk y (T ∷ Γ) σ = cong (var y ∷_) (gsubst-lsub-wk (suc y) Γ σ)

gsubst-lsub-id : ∀ Γ (σ : GSubst) → lsub-id Γ [ σ ] ≡ lsub-id (Γ [ σ ])
gsubst-lsub-id = gsubst-lsub-wk 0

-- Global and Local Weakenings Commute

mutual
  trm-gwk-lwk-comm : ∀ (t : Trm) (γ : Gwk) τ → lwk-trm (t [ γ ]) τ ≡ lwk-trm t τ [ γ ]
  trm-gwk-lwk-comm (var x) γ τ        = refl
  trm-gwk-lwk-comm (gvar x δ) γ τ
    rewrite lsubst-gwk-lwk-comm δ γ τ = refl
  trm-gwk-lwk-comm zero γ τ           = refl
  trm-gwk-lwk-comm (succ t) γ τ       = cong succ (trm-gwk-lwk-comm t γ τ)
  trm-gwk-lwk-comm (Λ t) γ τ          = cong Λ (trm-gwk-lwk-comm t γ (q τ))
  trm-gwk-lwk-comm (t $ s) γ τ        = cong₂ _$_ (trm-gwk-lwk-comm t γ τ) (trm-gwk-lwk-comm s γ τ)
  trm-gwk-lwk-comm (box t) γ τ        = refl
  trm-gwk-lwk-comm (letbox Γ s t) γ τ = cong₂ (letbox (Γ [ γ ])) (trm-gwk-lwk-comm s γ τ) (trm-gwk-lwk-comm t (q γ) τ)
  trm-gwk-lwk-comm (Λc t) γ τ         = cong Λc (trm-gwk-lwk-comm t (q γ) τ)
  trm-gwk-lwk-comm (t $c Γ) γ τ       = cong (_$c (Γ [ γ ])) (trm-gwk-lwk-comm t γ τ)

  lsubst-gwk-lwk-comm : ∀ (δ : LSubst) (γ : Gwk) τ → lwk-lsubst (δ [ γ ]) τ ≡ lwk-lsubst δ τ [ γ ]
  lsubst-gwk-lwk-comm (wk x n) γ τ  = refl
  lsubst-gwk-lwk-comm ([] n) γ τ    = refl
  lsubst-gwk-lwk-comm ([]′ x n) γ τ = refl
  lsubst-gwk-lwk-comm (t ∷ δ) γ τ   = cong₂ _∷_ (trm-gwk-lwk-comm t γ τ) (lsubst-gwk-lwk-comm δ γ τ)


lsub-x-gwk : ∀ x δ (γ : Gwk) → lsub-x x δ [ γ ] ≡ lsub-x x (δ [ γ ])
lsub-x-gwk x (wk _ _) γ      = refl
lsub-x-gwk x ([] _) γ        = refl
lsub-x-gwk x ([]′ _ _) γ     = refl
lsub-x-gwk zero (t ∷ δ) γ    = refl
lsub-x-gwk (suc x) (t ∷ δ) γ = lsub-x-gwk x δ γ

lsub-offset-resp-gwk : ∀ δ (γ : Gwk) → lsub-offset (δ [ γ ]) ≡ lsub-offset δ
lsub-offset-resp-gwk (wk _ _) γ  = refl
lsub-offset-resp-gwk ([] _) γ    = refl
lsub-offset-resp-gwk ([]′ _ _) γ = refl
lsub-offset-resp-gwk (_ ∷ δ) γ   = lsub-offset-resp-gwk δ γ

lsub-cv?-gwk-ty : LSubst → Gwk → Set
lsub-cv?-gwk-ty δ γ
  with lsub-cv? δ | lsub-cv? (δ [ γ ])
... | inj₁ _ | inj₁ _ = ⊤
... | inj₁ _ | inj₂ _ = ⊥
... | inj₂ _ | inj₁ _ = ⊥
... | inj₂ x | inj₂ y = wk-x x γ ≡ y

lsub-cv?-gwk : ∀ δ γ → lsub-cv?-gwk-ty δ γ
lsub-cv?-gwk (wk x n) γ  = refl
lsub-cv?-gwk ([] n) γ    = tt
lsub-cv?-gwk ([]′ x n) γ = refl
lsub-cv?-gwk (t ∷ δ) γ   = lsub-cv?-gwk δ γ

mutual
  trm-lsubst-gwk : (t : Trm) (δ : LSubst) (γ : Gwk) → lsub-trm t δ [ γ ] ≡ lsub-trm (t [ γ ]) (δ [ γ ])
  trm-lsubst-gwk (var x) δ γ        = lsub-x-gwk x δ γ
  trm-lsubst-gwk (gvar x δ′) δ γ
    rewrite ∘l-gwk δ′ δ γ           = refl
  trm-lsubst-gwk zero δ γ           = refl
  trm-lsubst-gwk (succ t) δ γ       = cong succ (trm-lsubst-gwk t δ γ)
  trm-lsubst-gwk (Λ t) δ γ          = cong Λ (trans (trm-lsubst-gwk t (var 0 ∷ lwk-lsubst δ (p id)) γ)
                                                    (cong (λ δ → lsub-trm (t [ γ ]) (var 0 ∷ δ)) (sym (lsubst-gwk-lwk-comm δ γ (p id)))))
  trm-lsubst-gwk (t $ s) δ γ        = cong₂ _$_ (trm-lsubst-gwk t δ γ) (trm-lsubst-gwk s δ γ)
  trm-lsubst-gwk (box t) δ γ        = refl
  trm-lsubst-gwk (letbox Γ s t) δ γ = cong₂ (letbox (Γ [ γ ]))
                                            (trm-lsubst-gwk s δ γ)
                                            (trans (trm-lsubst-gwk t (δ [ p id ]) (q γ))
                                                   (cong (lsub-trm (t [ q γ ]))
                                                         (trans (gwk-lsubst-comp δ (p id) (q γ))
                                                                (sym (trans (gwk-lsubst-comp δ γ (p id))
                                                                            (cong (δ [_]) (∘w-pid γ)))))))
  trm-lsubst-gwk (Λc t) δ γ         = cong Λc (trans (trm-lsubst-gwk t (δ [ p id ]) (q γ))
                                                     (cong (lsub-trm (t [ q γ ]))
                                                           (trans (gwk-lsubst-comp δ (p id) (q γ))
                                                                  (sym (trans (gwk-lsubst-comp δ γ (p id))
                                                                              (cong (δ [_]) (∘w-pid γ)))))))
  trm-lsubst-gwk (t $c Γ) δ γ       = cong (_$c (Γ [ γ ])) (trm-lsubst-gwk t δ γ)

  ∘l-gwk : (δ′ δ : LSubst) (γ : Gwk) → (δ′ ∘l δ) [ γ ] ≡ ((δ′ [ γ ]) ∘l (δ [ γ ]))
  ∘l-gwk (wk x n) δ γ
    rewrite lsub-offset-resp-gwk δ γ      = refl
  ∘l-gwk ([] n) δ γ
    with lsub-cv? δ | lsub-cv? (δ [ γ ]) | lsub-cv?-gwk δ γ
  ...  | inj₁ _ | inj₁ _ | _              = sym (cong [] (lsub-offset-resp-gwk δ γ))
  ...  | inj₁ _ | inj₂ _ | ()
  ...  | inj₂ _ | inj₁ _ | ()
  ...  | inj₂ y | inj₂ .(wk-x y γ) | refl = sym (cong ([]′ _) (lsub-offset-resp-gwk δ γ))
  ∘l-gwk ([]′ x n) δ γ
    with lsub-cv? δ | lsub-cv? (δ [ γ ]) | lsub-cv?-gwk δ γ
  ...  | inj₁ _ | inj₁ _ | _              = sym (cong [] (lsub-offset-resp-gwk δ γ))
  ...  | inj₁ _ | inj₂ _ | ()
  ...  | inj₂ _ | inj₁ _ | ()
  ...  | inj₂ y | inj₂ .(wk-x y γ) | refl = sym (cong ([]′ _) (lsub-offset-resp-gwk δ γ))
  ∘l-gwk (t ∷ δ′) δ γ                     = cong₂ _∷_ (trm-lsubst-gwk t δ γ) (∘l-gwk δ′ δ γ)

-- Global Substitutions and Global Weakenings Commute

gwk-gsub-trm-x : ∀ x σ (γ : Gwk) → gsub-trm-x x σ [ γ ] ≡ gsub-trm-x x (σ [ γ ])
gwk-gsub-trm-x x [] γ                = refl
gwk-gsub-trm-x zero (ctx _ ∷ σ) γ    = refl
gwk-gsub-trm-x zero (trm t ∷ σ) γ    = refl
gwk-gsub-trm-x (suc x) (ctx _ ∷ σ) γ = gwk-gsub-trm-x x σ γ
gwk-gsub-trm-x (suc x) (trm t ∷ σ) γ = gwk-gsub-trm-x x σ γ

lctx-cv?-gwk-ty : LCtx → Gwk → Set
lctx-cv?-gwk-ty Γ γ
  with lctx-cv? Γ | lctx-cv? (Γ [ γ ])
... | inj₁ _ | inj₁ _ = ⊤
... | inj₁ _ | inj₂ _ = ⊥
... | inj₂ _ | inj₁ _ = ⊥
... | inj₂ x | inj₂ y = wk-x x γ ≡ y

lctx-cv?-gwk : ∀ Γ γ → lctx-cv?-gwk-ty Γ γ
lctx-cv?-gwk [] γ      = tt
lctx-cv?-gwk (cv x) γ  = refl
lctx-cv?-gwk (_ ∷ Γ) γ = lctx-cv?-gwk Γ γ

mutual
  trm-gsubst-gwk : (t : Trm) (σ : GSubst) (γ : Gwk) → t [ σ ] [ γ ] ≡ t [ σ [ γ ] ]
  trm-gsubst-gwk (var x) σ γ        = refl
  trm-gsubst-gwk (gvar x δ) σ γ
    rewrite trm-lsubst-gwk (gsub-trm-x x σ) (δ [ σ ]) γ
          | lsubst-gsubst-gwk δ σ γ = cong (λ t → lsub-trm t (δ [ σ [ γ ] ])) (gwk-gsub-trm-x x σ γ)
  trm-gsubst-gwk zero σ γ           = refl
  trm-gsubst-gwk (succ t) σ γ       = cong succ (trm-gsubst-gwk t σ γ)
  trm-gsubst-gwk (Λ t) σ γ          = cong Λ (trm-gsubst-gwk t σ γ)
  trm-gsubst-gwk (t $ s) σ γ        = cong₂ _$_ (trm-gsubst-gwk t σ γ) (trm-gsubst-gwk s σ γ)
  trm-gsubst-gwk (box t) σ γ        = cong box (trm-gsubst-gwk t σ γ)
  trm-gsubst-gwk (letbox Γ s t) σ γ
    rewrite lctx-gsubst-gwk Γ σ γ   = cong₂ (letbox (Γ [ σ [ γ ] ])) (trm-gsubst-gwk s σ γ)
                                            (trans
                                               (trm-gsubst-gwk t
                                                (trm (gvar 0 (lsub-id (Γ [ σ [ p id ] ]))) ∷ (σ [ p id ])) (q γ))
                                            (cong₂ (λ δ σ′ → t [ trm (gvar 0 δ) ∷ σ′ ])
                                                   (trans (gwk-lsub-id (Γ [ σ [ p id ] ]) (q γ))
                                                          (cong lsub-id (trans (lctx-gsubst-gwk Γ (σ [ p id ]) (q γ))
                                                                        (cong (Γ [_]) eq))))
                                                   eq))
    where eq = trans (gwk-gsub-comp σ (p id) (q γ))
                     (sym (trans (gwk-gsub-comp σ γ (p id))
                                 (cong (σ [_]) (∘w-pid γ))))
  trm-gsubst-gwk (Λc t) σ γ         = cong Λc (trans (trm-gsubst-gwk t (ctx (cv 0) ∷ (σ [ p id ])) (q γ))
                                              (cong (λ σ′ → t [ ctx (cv 0) ∷ σ′ ])
                                                    (trans (gwk-gsub-comp σ (p id) (q γ))
                                                           (sym (trans (gwk-gsub-comp σ γ (p id))
                                                                       (cong (σ [_]) (∘w-pid γ)))))))
  trm-gsubst-gwk (t $c Γ) σ γ       = cong₂ _$c_ (trm-gsubst-gwk t σ γ) (lctx-gsubst-gwk Γ σ γ)

  lsubst-gsubst-gwk : (δ : LSubst) (σ : GSubst) (γ : Gwk) → δ [ σ ] [ γ ] ≡ δ [ σ [ γ ] ]
  lsubst-gsubst-gwk (wk x n) σ γ
    rewrite sym (lsubst-gwk-lwk-comm (lsub-id (gsub-ty-x x σ)) γ (repeat p n id))
          | gwk-lsub-id (gsub-ty-x x σ) γ
          | gwk-gsub-ty-x x σ γ       = refl
  lsubst-gsubst-gwk ([] x) σ γ        = refl
  lsubst-gsubst-gwk ([]′ x n) σ γ
    with gsub-ty-x x σ | gsub-ty-x x (σ [ γ ]) | gwk-gsub-ty-x x σ γ
  ...  | Γ | .(Γ [ γ ]) | refl
       with lctx-cv? Γ | lctx-cv? (Γ [ γ ]) | lctx-cv?-gwk Γ γ
  ...  | inj₁ _ | inj₁ _ | tt
       rewrite lc-length-resp-gwk Γ γ = refl
  ...  | inj₁ _ | inj₂ _ | ()
  ...  | inj₂ _ | inj₁ _ | ()
  ...  | inj₂ x | inj₂ .(wk-x x γ) | refl
       rewrite lc-length-resp-gwk Γ γ = refl
  lsubst-gsubst-gwk (t ∷ δ) σ γ       = cong₂ _∷_ (trm-gsubst-gwk t σ γ) (lsubst-gsubst-gwk δ σ γ)


-- Cancellation of Substitutions

gsub-qn : ℕ → GSubst → GSubst
gsub-qn x σ = ctx (cv x) ∷ (σ [ p id ])

gsub-q : GSubst → GSubst
gsub-q = gsub-qn 0

++-comp : ∀ σ σ′ (γ γ′ : Gwk) → (σ ++ σ′) [ γ ] [ γ′ ] ≡ (σ ++ σ′) [ γ ∘w γ′ ]
++-comp [] σ′ γ γ′          = gwk-gsub-comp σ′ γ γ′
++-comp (ctx Γ ∷ σ) σ′ γ γ′
  rewrite gwk-lc-comp Γ γ γ′
        | ++-comp σ σ′ γ γ′ = refl
++-comp (trm t ∷ σ) σ′ γ γ′
  rewrite gwk-trm-comp t γ γ′
        | ++-comp σ σ′ γ γ′ = refl

gwk-++ : ∀ σ σ′ (γ : Gwk) → (σ ++ σ′) [ γ ] ≡ ((σ [ γ ]) ++ (σ′ [ γ ]))
gwk-++ [] σ′ γ      = refl
gwk-++ (ctx Γ ∷ σ) σ′ γ
  rewrite ++-comp σ σ′ (p id) γ
        | gwk-++ σ σ′ γ = refl
gwk-++ (trm t ∷ σ) σ′ γ
  rewrite ++-comp σ σ′ (p id) γ
        | gwk-++ σ σ′ γ = refl

q-p-gsub-ty-x : ∀ x n b σ σ′ →
                n ≡ L.length σ′ →
                gsub-ty-x (wk-x x (repeat q n (p id))) (σ′ ++ (b ∷ σ)) ≡ gsub-ty-x x (σ′ ++ σ)
q-p-gsub-ty-x x ._ b σ [] refl                 = refl
q-p-gsub-ty-x zero ._ b σ (ctx Γ ∷ σ′) refl    = refl
q-p-gsub-ty-x zero ._ b σ (trm _ ∷ σ′) refl    = refl
q-p-gsub-ty-x (suc x) ._ b σ (ctx Γ ∷ σ′) refl
  rewrite sym (gwk-gsub-ty-x x (σ′ ++ σ) (p id)) = q-p-gsub-ty-x x _ b σ σ′ refl
q-p-gsub-ty-x (suc x) ._ b σ (trm _ ∷ σ′) refl
  rewrite sym (gwk-gsub-ty-x x (σ′ ++ σ) (p id)) = q-p-gsub-ty-x x _ b σ σ′ refl

q-p-gsub-trm-x : ∀ x n b σ σ′ →
                 n ≡ L.length σ′ →
                 gsub-trm-x (wk-x x (repeat q n (p id))) (σ′ ++ (b ∷ σ)) ≡ gsub-trm-x x (σ′ ++ σ)
q-p-gsub-trm-x x ._ b σ [] refl = refl
q-p-gsub-trm-x zero ._ b σ (ctx _ ∷ σ′) refl = refl
q-p-gsub-trm-x zero ._ b σ (trm _ ∷ σ′) refl = refl
q-p-gsub-trm-x (suc x) ._ b σ (ctx _ ∷ σ′) refl
  rewrite sym (gwk-gsub-trm-x x (σ′ ++ σ) (p id)) = q-p-gsub-trm-x x _ b σ σ′ refl
q-p-gsub-trm-x (suc x) ._ b σ (trm _ ∷ σ′) refl
  rewrite sym (gwk-gsub-trm-x x (σ′ ++ σ) (p id)) = q-p-gsub-trm-x x _ b σ σ′ refl

gsub-resp-length : (Δ : List Typ) (σ : GSubst) → L.length (L.map _[ σ ] Δ) ≡ L.length Δ
gsub-resp-length [] σ      = refl
gsub-resp-length (_ ∷ Δ) σ = cong suc (gsub-resp-length Δ σ)

gwk-resp-length : (σ : GSubst) (γ : Gwk) → L.length (σ [ γ ]) ≡ L.length σ
gwk-resp-length [] γ          = refl
gwk-resp-length (ctx _ ∷ σ) γ = cong suc (gwk-resp-length σ γ)
gwk-resp-length (trm _ ∷ σ) γ = cong suc (gwk-resp-length σ γ)

mutual
  q-p-gsub-ty : ∀ (T : Typ) n (b : GSub) σ σ′ →
                n ≡ L.length σ′ →
                T [ repeat q n (p id) ] [ σ′ ++ (b ∷ σ) ] ≡ T [ σ′ ++ σ ]
  q-p-gsub-ty N n b σ σ′ eq          = refl
  q-p-gsub-ty (S ⟶ T) n b σ σ′ eq    = cong₂ _⟶_ (q-p-gsub-ty S n b σ σ′ eq) (q-p-gsub-ty T n b σ σ′ eq)
  q-p-gsub-ty (□ Γ T) n b σ σ′ eq    = cong₂ □ (q-p-gsub-lctx Γ n b σ σ′ eq) (q-p-gsub-ty T n b σ σ′ eq)
  q-p-gsub-ty (ctx⇒ T) n b σ σ′ eq
    rewrite gwk-++ σ′ σ (p id)
          | gwk-++ σ′ (b ∷ σ) (p id) = cong ctx⇒_ (q-p-gsub-ty T (suc n) (b [ p id ]) (σ [ p id ]) (gsub-q σ′)
                                                               (cong suc (trans eq (sym (gwk-resp-length σ′ (p id))))))

  q-p-gsub-lctx : ∀ (Γ : LCtx) n b σ σ′ →
                  n ≡ L.length σ′ →
                  Γ [ repeat q n (p id) ] [ σ′ ++ (b ∷ σ) ] ≡ Γ [ σ′ ++ σ ]
  q-p-gsub-lctx [] n b σ σ′ eq      = refl
  q-p-gsub-lctx (cv x) n b σ σ′ eq  = q-p-gsub-ty-x x n b σ σ′ eq
  q-p-gsub-lctx (T ∷ Γ) n b σ σ′ eq = cong₂ _∷_ (q-p-gsub-ty T n b σ σ′ eq) (q-p-gsub-lctx Γ n b σ σ′ eq)

p-gsub-ty : ∀ (T : Typ) b σ →
              T [ p id ] [ b ∷ σ ] ≡ T [ σ ]
p-gsub-ty T b σ = q-p-gsub-ty T 0 b σ [] refl

p-gsub-lctx : ∀ (Γ : LCtx) b σ →
              Γ [ p id ] [ b ∷ σ ] ≡ Γ [ σ ]
p-gsub-lctx Γ b σ = q-p-gsub-lctx Γ 0 b σ [] refl

p-gsub-lctx* : ∀ (Γ : LCtx) σ′ σ n →
               n ≡ L.length σ′ →
              Γ [ repeat p n id ] [ σ′ ++ σ ] ≡ Γ [ σ ]
p-gsub-lctx* Γ [] σ zero eq
  rewrite gwk-id-lc 0 Γ                                 = refl
p-gsub-lctx* Γ (b ∷ σ′) σ (suc n) refl
  rewrite sym (∘w-pid (repeat p n id))
        | sym (gwk-lc-comp Γ (repeat p n id) (p id))
        | p-gsub-lctx (Γ [ repeat p n id ]) b (σ′ ++ σ) = p-gsub-lctx* Γ σ′ σ n refl

mutual
  q-p-gsub-trm : ∀ (t : Trm) n (b : GSub) σ σ′ →
                 n ≡ L.length σ′ →
                 t [ repeat q n (p id) ] [ σ′ ++ (b ∷ σ) ] ≡ t [ σ′ ++ σ ]
  q-p-gsub-trm (var x) n b σ σ′ eq        = refl
  q-p-gsub-trm (gvar x δ) n b σ σ′ eq
    rewrite q-p-gsub-trm-x x n b σ σ′ eq
          | q-p-gsub-lsubst δ n b σ σ′ eq = refl
  q-p-gsub-trm zero n b σ σ′ eq           = refl
  q-p-gsub-trm (succ t) n b σ σ′ eq       = cong succ (q-p-gsub-trm t n b σ σ′ eq)
  q-p-gsub-trm (Λ t) n b σ σ′ eq          = cong Λ (q-p-gsub-trm t n b σ σ′ eq)
  q-p-gsub-trm (t $ s) n b σ σ′ eq        = cong₂ _$_ (q-p-gsub-trm t n b σ σ′ eq) (q-p-gsub-trm s n b σ σ′ eq)
  q-p-gsub-trm (box t) n b σ σ′ eq        = cong box (q-p-gsub-trm t n b σ σ′ eq)
  q-p-gsub-trm (letbox Γ s t) n b σ σ′ eq
    rewrite q-p-gsub-lctx Γ n b σ σ′ eq   = cong₂ (letbox (Γ [ σ′ ++ σ ])) (q-p-gsub-trm s n b σ σ′ eq) helper
      where helper : t [ repeat q (1 + n) (p id) ] [ trm (gvar 0 (lsub-id (Γ [ repeat q n (p id) ] [ (σ′ ++ b ∷ σ) [ p id ] ]))) ∷ ((σ′ ++ b ∷ σ) [ p id ]) ]
                     ≡ t [ trm (gvar 0 (lsub-id (Γ [ (σ′ ++ σ) [ p id ] ]))) ∷ ((σ′ ++ σ) [ p id ]) ]
            helper
              with trans eq (sym (gwk-resp-length σ′ (p id)))
            ...  | eq′
              rewrite gwk-++ σ′ (b ∷ σ) (p id)
                    | q-p-gsub-lctx Γ n (b [ p id ]) (σ [ p id ]) (σ′ [ p id ]) eq′
                    | gwk-++ σ′ σ (p id) = q-p-gsub-trm t (1 + n) (b [ p id ]) (σ [ p id ]) (trm (gvar 0 (lsub-id _)) ∷ (σ′ [ p id ])) (cong suc eq′)
  q-p-gsub-trm (Λc t) n b σ σ′ eq
    rewrite gwk-++ σ′ σ (p id)
           | gwk-++ σ′ (b ∷ σ) (p id)     = cong Λc (q-p-gsub-trm t (1 + n) (b [ p id ]) (σ [ p id ]) (ctx (cv 0) ∷ (σ′ [ p id ]))
                                                                  (cong suc (trans eq (sym (gwk-resp-length σ′ (p id))))))
  q-p-gsub-trm (t $c Γ) n b σ σ′ eq       = cong₂ _$c_ (q-p-gsub-trm t n b σ σ′ eq) (q-p-gsub-lctx Γ n b σ σ′ eq)

  q-p-gsub-lsubst : ∀ (δ : LSubst) n (b : GSub) σ σ′ →
                    n ≡ L.length σ′ →
                    δ [ repeat q n (p id) ] [ σ′ ++ (b ∷ σ) ] ≡ δ [ σ′ ++ σ ]
  q-p-gsub-lsubst (wk x m) n b σ σ′ eq
    rewrite q-p-gsub-ty-x x n b σ σ′ eq = refl
  q-p-gsub-lsubst ([] m) n b σ σ′ eq    = refl
  q-p-gsub-lsubst ([]′ x m) n b σ σ′ eq
    with gsub-ty-x (wk-x x (repeat q n (p id))) (σ′ ++ b ∷ σ) | gsub-ty-x x (σ′ ++ σ) | q-p-gsub-ty-x x n b σ σ′ eq
  ...  | _ | Γ | refl
       with lctx-cv? Γ
  ...     | inj₁ _                      = refl
  ...     | inj₂ y                      = refl
  q-p-gsub-lsubst (t ∷ δ) n b σ σ′ eq   = cong₂ _∷_ (q-p-gsub-trm t n b σ σ′ eq) (q-p-gsub-lsubst δ n b σ σ′ eq)

p-gsub-trm : ∀ (t : Trm) b σ →
             t [ p id ] [ b ∷ σ ] ≡ t [ σ ]
p-gsub-trm t b σ = q-p-gsub-trm t 0 b σ [] refl

p-gsub-lsubst : ∀ (δ : LSubst) b σ →
                δ [ p id ] [ b ∷ σ ] ≡ δ [ σ ]
p-gsub-lsubst δ b σ = q-p-gsub-lsubst δ 0 b σ [] refl

p-gsub-lsubst* : ∀ (δ : LSubst) σ′ σ n →
                 n ≡ L.length σ′ →
                 δ [ repeat p n id ] [ σ′ ++ σ ] ≡ δ [ σ ]
p-gsub-lsubst* δ [] σ zero eq
  rewrite gwk-id-lsubst 0 δ                               = refl
p-gsub-lsubst* δ (b ∷ σ′) σ (suc n) refl
  rewrite sym (∘w-pid (repeat p n id))
        | sym (gwk-lsubst-comp δ (repeat p n id) (p id))
        | p-gsub-lsubst (δ [ repeat p n id ]) b (σ′ ++ σ) = p-gsub-lsubst* δ σ′ σ n refl

-- Composition of Global Substitutions

infixl 3 _∘g_

_∘g_ : GSubst → GSubst → GSubst
[] ∘g σ′        = []
ctx Γ ∷ σ ∘g σ′ = ctx (Γ [ σ′ ]) ∷ (σ ∘g σ′)
trm t ∷ σ ∘g σ′ = trm (t [ σ′ ]) ∷ (σ ∘g σ′)

∘g-gwk : ∀ σ σ′ (γ : Gwk) → (σ ∘g σ′) [ γ ] ≡ (σ ∘g (σ′ [ γ ]))
∘g-gwk [] σ′ γ          = refl
∘g-gwk (ctx Γ ∷ σ) σ′ γ = cong₂ _∷_ (cong ctx (lctx-gsubst-gwk Γ σ′ γ)) (∘g-gwk σ σ′ γ)
∘g-gwk (trm t ∷ σ) σ′ γ = cong₂ _∷_ (cong trm (trm-gsubst-gwk t σ′ γ)) (∘g-gwk σ σ′ γ)

p-gsub-gsubst : ∀ σ b σ′ →
                (σ [ p id ] ∘g (b ∷ σ′)) ≡ (σ ∘g σ′)
p-gsub-gsubst [] b σ′          = refl
p-gsub-gsubst (ctx Γ ∷ σ) b σ′ = cong₂ _∷_ (cong ctx (p-gsub-lctx Γ b σ′)) (p-gsub-gsubst σ b σ′)
p-gsub-gsubst (trm t ∷ σ) b σ′ = cong₂ _∷_ (cong trm (p-gsub-trm t b σ′)) (p-gsub-gsubst σ b σ′)

gsub-ty-x-comp : ∀ x σ σ′ → gsub-ty-x x σ [ σ′ ] ≡ gsub-ty-x x (σ ∘g σ′)
gsub-ty-x-comp x [] σ′                = refl
gsub-ty-x-comp zero (ctx Γ ∷ σ) σ′    = refl
gsub-ty-x-comp zero (trm t ∷ σ) σ′    = refl
gsub-ty-x-comp (suc x) (ctx _ ∷ σ) σ′ = gsub-ty-x-comp x σ σ′
gsub-ty-x-comp (suc x) (trm _ ∷ σ) σ′ = gsub-ty-x-comp x σ σ′

mutual
  gsub-ty-comp : ∀ (T : Typ) σ σ′ → T [ σ ] [ σ′ ] ≡ T [ σ ∘g σ′ ]
  gsub-ty-comp N σ σ′        = refl
  gsub-ty-comp (S ⟶ T) σ σ′  = cong₂ _⟶_ (gsub-ty-comp S σ σ′) (gsub-ty-comp T σ σ′)
  gsub-ty-comp (□ Γ T) σ σ′  = cong₂ □ (gsub-lctx-comp Γ σ σ′) (gsub-ty-comp T σ σ′)
  gsub-ty-comp (ctx⇒ T) σ σ′ = cong ctx⇒_
                                    (trans
                                       (gsub-ty-comp T (ctx (cv 0) ∷ (σ [ p id ]))
                                        (ctx (cv 0) ∷ (σ′ [ p id ])))
                                       (cong (λ σ′ → T [ ctx (cv 0) ∷ σ′ ])
                                             (trans (p-gsub-gsubst σ (ctx (cv 0)) (σ′ [ p id ]))
                                                    (sym (∘g-gwk σ σ′ (p id))))))

  gsub-lctx-comp : ∀ (Γ : LCtx) σ σ′ → Γ [ σ ] [ σ′ ] ≡ Γ [ σ ∘g σ′ ]
  gsub-lctx-comp [] σ σ′      = refl
  gsub-lctx-comp (cv x) σ σ′  = gsub-ty-x-comp x σ σ′
  gsub-lctx-comp (t ∷ Γ) σ σ′ = cong₂ _∷_ (gsub-ty-comp t σ σ′) (gsub-lctx-comp Γ σ σ′)

-- Typing Judgments

infix 2 _∶_∈L_

data _∶_∈L_ : ℕ → Typ → LCtx → Set where
  here  : 0 ∶ T ∈L T ∷ Γ
  there : ∀ {x} → x ∶ T ∈L Γ → suc x ∶ T ∈L S ∷ Γ

∈L⇒wf : x ∶ T ∈L Γ → Ψ ⊢l[ i ] Γ → Ψ ⊢[ i ] T
∈L⇒wf here (⊢∷ ⊢Γ ⊢T)       = ⊢T
∈L⇒wf (there T∈) (⊢∷ ⊢Γ ⊢S) = ∈L⇒wf T∈ ⊢Γ

∈L-resp-⊆l : x ∶ T ∈L Γ → Δ ⊆l Γ → x ∶ T ∈L Δ
∈L-resp-⊆l here (cons Δ⊆Γ)       = here
∈L-resp-⊆l (there T∈) (cons Δ⊆Γ) = there (∈L-resp-⊆l T∈ Δ⊆Γ)

∈L-lwk : x ∶ T ∈L Γ → Ψ ﹔ Δ ⊢lw[ i ] τ ∶ Γ → wk-x x τ ∶ T ∈L Δ
∈L-lwk T∈ (id-wf _)            = T∈
∈L-lwk T∈ (p-wf ⊢τ _)          = there (∈L-lwk T∈ ⊢τ)
∈L-lwk here (q-wf ⊢τ ⊢S)       = here
∈L-lwk (there T∈) (q-wf ⊢τ ⊢S) = there (∈L-lwk T∈ ⊢τ)

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
    wk-wf : ∀ {Δ n} →
            Ψ ⊢l[ i ] Γ →
            x ∶ ctx ∈G Ψ →
            Γ ≡ Δ ^^ cv x →
            n ≡ lc-length Γ →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] wk x n ∶ cv x
    []-wf : ∀ {Δ n} →
            Ψ ⊢l[ i ] Γ →
            Γ ≡ Δ ^^ [] →
            n ≡ lc-length Γ →
            ------------------------
            Ψ ﹔ Γ ⊢s[ i ] [] n ∶ []
    []′-wf : ∀ {Δ n} →
            Ψ ⊢l[ i ] Γ →
            x ∶ ctx ∈G Ψ →
            Γ ≡ Δ ^^ cv x →
            n ≡ lc-length Γ →
            ---------------------------
            Ψ ﹔ Γ ⊢s[ i ] []′ x n ∶ []
    ∷-wf  : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
            Ψ ﹔ Γ ⊢[ i ] t ∶ T →
            ---------------------------
            Ψ ﹔ Γ ⊢s[ i ] t ∷ δ ∶ T ∷ Δ


lsubst-lc-length : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → lc-length Γ ≡ lsub-offset δ
lsubst-lc-length (wk-wf _ _ _ eq)  = sym eq
lsubst-lc-length ([]-wf _ _ eq)    = sym eq
lsubst-lc-length ([]′-wf _ _ _ eq) = sym eq
lsubst-lc-length (∷-wf ⊢δ _)       = lsubst-lc-length ⊢δ

lsub-^^-ty : LSubst → LCtx → List Typ → Set
lsub-^^-ty δ Γ Δ
  with lsub-cv? δ
...  | inj₁ _ = Γ ≡ Δ ^^ []
...  | inj₂ x = Γ ≡ Δ ^^ cv x

lsub-^^ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → ∃ λ Γ′ → lsub-^^-ty δ Γ Γ′
lsub-^^ (wk-wf ⊢Γ ctx∈ eq eq′) = -, eq
lsub-^^ ([]-wf ⊢Γ eq eq′)      = -, eq
lsub-^^ ([]′-wf ⊢Γ _ eq _)     = -, eq
lsub-^^ (∷-wf ⊢δ ⊢t)           = lsub-^^ ⊢δ

lctx-^^-ty : GCtx → LCtx → List Typ → Set
lctx-^^-ty Ψ Γ Δ
  with lctx-cv? Γ
...  | inj₁ _ = Γ ≡ Δ ^^ []
...  | inj₂ x = (x ∶ ctx ∈G Ψ) × Γ ≡ Δ ^^ cv x

lctx-^^ : Ψ ⊢l[ i ] Γ → ∃ λ Γ′ → lctx-^^-ty Ψ Γ Γ′
lctx-^^ (⊢[] ⊢Ψ)             = [] , refl
lctx-^^ (⊢ctx ⊢Ψ ctx∈)       = [] , ctx∈ , refl
lctx-^^ (⊢∷ {_} {_} {Γ} ⊢Γ ⊢T)
  with lctx-cv? Γ | lctx-^^ ⊢Γ
... | inj₁ _ | Δ , eq        = -, cong (_ ∷_) eq
... | inj₂ x | Δ , ctx∈ , eq = -, ctx∈ , cong (_ ∷_) eq


-- Lifting of Terms and Local Substitutions

mutual
  lift-trm : Ψ ﹔ Γ ⊢[ 𝟘 ] t ∶ T → Ψ ﹔ Γ ⊢[ 𝟙 ] t ∶ T
  lift-trm (v-wf ⊢Γ T∈)  = v-wf (lift-lctx ⊢Γ) T∈
  lift-trm (gv-wf T∈ ⊢δ) = gv-wf T∈ (lift-lsubst ⊢δ)
  lift-trm (zero-wf ⊢Γ)  = zero-wf (lift-lctx ⊢Γ)
  lift-trm (succ-wf ⊢t)  = succ-wf (lift-trm ⊢t)
  lift-trm (Λ-wf ⊢t)     = Λ-wf (lift-trm ⊢t)
  lift-trm ($-wf ⊢t ⊢s)  = $-wf (lift-trm ⊢t) (lift-trm ⊢s)

  lift-lsubst : Ψ ﹔ Γ ⊢s[ 𝟘 ] δ ∶ Δ → Ψ ﹔ Γ ⊢s[ 𝟙 ] δ ∶ Δ
  lift-lsubst (wk-wf ⊢Γ ctx∈ eq eq′)  = wk-wf (lift-lctx ⊢Γ) ctx∈ eq eq′
  lift-lsubst ([]-wf ⊢Γ eq eq′)       = []-wf (lift-lctx ⊢Γ) eq eq′
  lift-lsubst ([]′-wf ⊢Γ ctx∈ eq eq′) = []′-wf (lift-lctx ⊢Γ) ctx∈ eq eq′
  lift-lsubst (∷-wf ⊢δ ⊢t)            = ∷-wf (lift-lsubst ⊢δ) (lift-trm ⊢t)

lift-trm′ : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ ﹔ Γ ⊢[ 𝟙 ] t ∶ T
lift-trm′ {i = 𝟘} ⊢t = lift-trm ⊢t
lift-trm′ {i = 𝟙} ⊢t = ⊢t

lift-lsubst′ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → Ψ ﹔ Γ ⊢s[ 𝟙 ] δ ∶ Δ
lift-lsubst′ {i = 𝟘} ⊢δ = lift-lsubst ⊢δ
lift-lsubst′ {i = 𝟙} ⊢δ = ⊢δ

lift-trm″ : Ψ ﹔ Γ ⊢[ 𝟘 ] t ∶ T → Ψ ﹔ Γ ⊢[ i ] t ∶ T
lift-trm″ {i = 𝟘} ⊢t = ⊢t
lift-trm″ {i = 𝟙} ⊢t = lift-trm ⊢t

lift-lsubst″ : Ψ ﹔ Γ ⊢s[ 𝟘 ] δ ∶ Δ → Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ
lift-lsubst″ {i = 𝟘} ⊢δ = ⊢δ
lift-lsubst″ {i = 𝟙} ⊢δ = lift-lsubst ⊢δ

-- Typing of Identity

∈L-lookup : ∀ Γ T Δ → L.length Γ ∶ T ∈L Γ ^^ (T ∷ Δ)
∈L-lookup [] T Δ      = here
∈L-lookup (S ∷ Γ) T Δ = there (∈L-lookup Γ T Δ)

⊢lsub-wk-gen : ∀ Γ → Ψ ⊢l[ i ] (Γ ^^ Δ) → Ψ ⊢l[ i ] Δ → Ψ ﹔ Γ ^^ Δ ⊢s[ i ] lsub-wk (L.length Γ) Δ ∶ Δ
⊢lsub-wk-gen Γ ⊢ΓΔ (⊢[] ⊢Ψ)                    = []-wf ⊢ΓΔ refl (sym (^^-length-[] Γ))
⊢lsub-wk-gen Γ ⊢ΓΔ (⊢ctx ⊢Ψ ctx∈)              = wk-wf ⊢ΓΔ ctx∈ refl (sym (^^-length-cv Γ))
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

-- Useful Equations

gsub-qp : GCtx → ℕ → GCtx → GSubst
gsub-qp [] n Ψ            = gsub-wk n Ψ
gsub-qp (ctx ∷ Φ) n Ψ     = ctx (cv 0) ∷ (gsub-qp Φ n Ψ [ p id ])
gsub-qp ((Γ , T) ∷ Φ) n Ψ = trm (gvar 0 (lsub-id Γ [ p (repeat q (L.length Φ) (repeat p n id)) ])) ∷ (gsub-qp Φ n Ψ [ p id ])

gsub-wk≈gwk-ty-x-gen : ∀ Φ m n Ψ →
                       x ∶ B ∈G Φ ++ Ψ →
                       m ≡ L.length Φ →
                       B ≡ ctx →
                       gsub-ty-x x (gsub-qp Φ n Ψ) ≡ cv (wk-x x (repeat q m (repeat p n id)))
gsub-wk≈gwk-ty-x-gen [] zero n ._ (here {_} {ctx}) refl eq′ = cong cv (sym (wk-x-repeat-p′ 0 _))
gsub-wk≈gwk-ty-x-gen [] zero n ._ (there {x} {_} {ctx} {ctx} ctx∈) refl eq′
  with gsub-wk≈gwk-ty-x-gen [] zero (suc n) _ ctx∈ refl refl
...  | eq″
  rewrite wk-x-repeat-p′ (suc x) n
        | wk-x-repeat-p′ x n                                = eq″
gsub-wk≈gwk-ty-x-gen [] zero n ._ (there {x} {_} {ctx} {Γ , T} ctx∈) refl eq′
  with gsub-wk≈gwk-ty-x-gen [] zero (suc n) _ ctx∈ refl refl
...  | eq″
  rewrite wk-x-repeat-p′ (suc x) n
        | wk-x-repeat-p′ x n                                = eq″
gsub-wk≈gwk-ty-x-gen (ctx ∷ Φ) (suc m) n Ψ here eq eq′      = refl
gsub-wk≈gwk-ty-x-gen (ctx ∷ Φ) (suc m) n Ψ (there {x} {_} {ctx} ctx∈) refl eq′
  rewrite sym (gwk-gsub-ty-x x (gsub-qp Φ n Ψ) (p id))
        | gsub-wk≈gwk-ty-x-gen Φ m n Ψ ctx∈ refl refl       = refl
gsub-wk≈gwk-ty-x-gen ((Γ , T) ∷ Φ) (suc m) n Ψ (there {x} {_} {ctx} ctx∈) refl eq′
  rewrite sym (gwk-gsub-ty-x x (gsub-qp Φ n Ψ) (p id))
        | gsub-wk≈gwk-ty-x-gen Φ m n Ψ ctx∈ refl refl       = refl


mutual
  ty-gsub-wk≈gwk-gen : ∀ Φ m n Ψ →
                       Φ ++ Ψ ⊢[ i ] T →
                       m ≡ L.length Φ →
                       T [ gsub-qp Φ n Ψ ] ≡ T [ repeat q m (repeat p n id) ]
  ty-gsub-wk≈gwk-gen Φ m n Ψ (⊢N x) eq     = refl
  ty-gsub-wk≈gwk-gen Φ m n Ψ (⊢⟶ ⊢S ⊢T) eq = cong₂ _⟶_ (ty-gsub-wk≈gwk-gen Φ m n Ψ ⊢S eq) (ty-gsub-wk≈gwk-gen Φ m n Ψ ⊢T eq)
  ty-gsub-wk≈gwk-gen Φ m n Ψ (⊢□ ⊢Δ ⊢T) eq = cong₂ □ (lctx-gsub-wk≈gwk-gen Φ m n Ψ ⊢Δ eq) (ty-gsub-wk≈gwk-gen Φ m n Ψ ⊢T eq)
  ty-gsub-wk≈gwk-gen Φ m n Ψ (⊢⇒ ⊢T) eq    = cong ctx⇒_ (ty-gsub-wk≈gwk-gen (ctx ∷ Φ) (suc m) n Ψ ⊢T (cong suc eq))

  lctx-gsub-wk≈gwk-gen : ∀ Φ m n Ψ →
                         Φ ++ Ψ ⊢l[ i ] Γ →
                         m ≡ L.length Φ →
                         Γ [ gsub-qp Φ n Ψ ] ≡ Γ [ repeat q m (repeat p n id) ]
  lctx-gsub-wk≈gwk-gen Φ m n Ψ (⊢[] _) eq       = refl
  lctx-gsub-wk≈gwk-gen Φ m n Ψ (⊢ctx _ ctx∈) eq = gsub-wk≈gwk-ty-x-gen Φ m n Ψ ctx∈ eq refl
  lctx-gsub-wk≈gwk-gen Φ m n Ψ (⊢∷ ⊢Γ ⊢T) eq    = cong₂ _∷_ (ty-gsub-wk≈gwk-gen Φ m n Ψ ⊢T eq) (lctx-gsub-wk≈gwk-gen Φ m n Ψ ⊢Γ eq)


ty-gsub-wk≈gwk : ∀ n →
                 Ψ ⊢[ i ] T →
                 T [ gsub-wk n Ψ ] ≡ T [ repeat p n id ]
ty-gsub-wk≈gwk n ⊢T = ty-gsub-wk≈gwk-gen [] 0 n _ ⊢T refl

lctx-gsub-wk≈gwk : ∀ n →
                   Ψ ⊢l[ i ] Γ →
                   Γ [ gsub-wk n Ψ ] ≡ Γ [ repeat p n id ]
lctx-gsub-wk≈gwk n ⊢Γ = lctx-gsub-wk≈gwk-gen [] 0 n _ ⊢Γ refl

gsub-id-ty : Ψ ⊢[ i ] T →
             T [ gsub-id Ψ ] ≡ T
gsub-id-ty ⊢T
  rewrite ty-gsub-wk≈gwk 0 ⊢T = gwk-id-ty 0 _

gsub-id-lctx : Ψ ⊢l[ i ] Γ →
               Γ [ gsub-id Ψ ] ≡ Γ
gsub-id-lctx ⊢Γ
  rewrite lctx-gsub-wk≈gwk 0 ⊢Γ = gwk-id-lc 0 _

lsub-x-+l : ∀ ts t δ x →
                L.length ts ≡ x →
                lsub-x x (ts +l t ∷ δ) ≡ t
lsub-x-+l [] t δ zero eq            = refl
lsub-x-+l (s ∷ ts) t δ (suc x) refl = lsub-x-+l ts t δ x refl

lsub-wk-∘l-lsubst : ∀ ts n →
                    Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                    L.length ts ≡ n →
                    (lsub-wk n Δ ∘l (ts +l δ)) ≡ δ
lsub-wk-∘l-lsubst ts n (wk-wf {x = x} {Δ = Δ′} ⊢Γ ctx∈ refl refl) eq
  rewrite lsub-offset-+l ts (wk x (lc-length (Δ′ ^^ cv x))) = refl
lsub-wk-∘l-lsubst ts n ([]-wf {n = m} ⊢Γ eq′ eq″) eq
  rewrite lsub-cv?-+l ts ([] m)
        | lsub-offset-+l ts ([] m) = refl
lsub-wk-∘l-lsubst ts n ([]′-wf {x = x} {n = m} ⊢Γ ctx∈ eq′ eq″) eq
  rewrite lsub-cv?-+l ts ([]′ x m)
        | lsub-offset-+l ts ([]′ x m) = refl
lsub-wk-∘l-lsubst ts n (∷-wf {δ = δ} {t = t} ⊢δ ⊢t) refl
  rewrite lsub-x-+l ts t δ n refl
        | +l-assoc ts L.[ t ] δ
        | lsub-wk-∘l-lsubst (ts ++ L.[ t ]) (suc n) ⊢δ (trans (length-++ ts) (ℕₚ.+-comm (L.length ts) 1))
        = refl

lsub-id-∘lˡ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → (lsub-id Δ ∘l δ) ≡ δ
lsub-id-∘lˡ ⊢δ = lsub-wk-∘l-lsubst [] 0 ⊢δ refl

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

lsub-x-lwk : ∀ n →
             x ∶ T ∈L Γ →
             lsub-x x (lsub-wk n Γ) ≡ var (x + n)
lsub-x-lwk n here = refl
lsub-x-lwk n (there T∈)
  rewrite lsub-x-lwk (suc n) T∈ = cong var (ℕₚ.+-suc _ n)

lsub-offset-lsub-wk : ∀ n Γ →
                      lsub-offset (lsub-wk n Γ) ≡ lc-length Γ + n
lsub-offset-lsub-wk n []                = refl
lsub-offset-lsub-wk n (cv x)            = refl
lsub-offset-lsub-wk n (_ ∷ Γ)
  rewrite lsub-offset-lsub-wk (suc n) Γ = ℕₚ.+-suc (lc-length Γ) n

lsub-cv?-[] : ∀ n Δ →
              lsub-cv? (lsub-wk n (Δ ^^ [])) ≡ inj₁ _
lsub-cv?-[] n []      = refl
lsub-cv?-[] n (_ ∷ Δ) = lsub-cv?-[] (suc n) Δ

lsub-cv?-cv : ∀ n Δ x →
              lsub-cv? (lsub-wk n (Δ ^^ cv x)) ≡ inj₂ x
lsub-cv?-cv n [] x      = refl
lsub-cv?-cv n (_ ∷ Δ) x = lsub-cv?-cv (suc n) Δ x

mutual
  lsub-trm-lsub-id : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
                     lsub-trm t (lsub-id Γ) ≡ t
  lsub-trm-lsub-id (v-wf {x = x} ⊢Γ T∈)
    rewrite wk-x-repeat-p′ 0 x
          | lsub-x-lwk 0 T∈                      = cong var (ℕₚ.+-identityʳ x)
  lsub-trm-lsub-id (gv-wf T∈ ⊢δ)                 = cong (gvar _) (∘l-lsub-id ⊢δ)
  lsub-trm-lsub-id (zero-wf ⊢Γ)                  = refl
  lsub-trm-lsub-id (succ-wf ⊢t)                  = cong succ (lsub-trm-lsub-id ⊢t)
  lsub-trm-lsub-id (Λ-wf {_} {S} {Γ} {_} {t} ⊢t) = cong Λ (trans (cong (lsub-trm t) (lsub-id-constr S Γ)) (lsub-trm-lsub-id ⊢t))
  lsub-trm-lsub-id ($-wf ⊢t ⊢s)                  = cong₂ _$_ (lsub-trm-lsub-id ⊢t) (lsub-trm-lsub-id ⊢s)
  lsub-trm-lsub-id (box-wf ⊢Γ ⊢t)                = refl
  lsub-trm-lsub-id (letbox-wf {_} {Γ} {t = t} ⊢s ⊢Δ ⊢S ⊢T ⊢t) = cong₂ (letbox _) (lsub-trm-lsub-id ⊢s) (trans (cong (lsub-trm t) (gwk-lsub-id Γ (p id))) (lsub-trm-lsub-id ⊢t))
  lsub-trm-lsub-id (Λc-wf {_} {Γ} {t = t} ⊢Γ ⊢t) = cong Λc (trans (cong (lsub-trm t) (gwk-lsub-id Γ (p id))) (lsub-trm-lsub-id ⊢t))
  lsub-trm-lsub-id ($c-wf ⊢t ⊢Δ ⊢T eq)           = cong (_$c _) (lsub-trm-lsub-id ⊢t)

  ∘l-lsub-id : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
               (δ ∘l (lsub-id Γ)) ≡ δ
  ∘l-lsub-id {_} {Γ} (wk-wf ⊢Γ ctx∈ eq refl)
    rewrite lsub-offset-lsub-wk 0 Γ
          | ℕₚ.+-identityʳ (lc-length Γ) = refl
  ∘l-lsub-id ([]-wf {Δ = Δ} ⊢Γ refl refl)
    rewrite lsub-cv?-[] 0 Δ
          | lsub-offset-lsub-wk 0 (Δ ^^ [])
          | ℕₚ.+-identityʳ (lc-length (Δ ^^ []))   = refl
  ∘l-lsub-id ([]′-wf {x = x} {Δ = Δ} ⊢Γ ctx∈ refl refl)
    rewrite lsub-cv?-cv 0 Δ x
          | lsub-offset-lsub-wk 0 (Δ ^^ cv x)
          | ℕₚ.+-identityʳ (lc-length (Δ ^^ cv x)) = refl
  ∘l-lsub-id (∷-wf ⊢δ ⊢t)                          = cong₂ _∷_ (lsub-trm-lsub-id ⊢t) (∘l-lsub-id ⊢δ)


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
  lsubst-gwk {γ = γ} (wk-wf {Δ = Δ} ⊢Γ ctx∈ refl eq) ⊢γ
    = wk-wf (lctx-gwk ⊢Γ ⊢γ) (x-gwk ⊢γ ctx∈) (^^-gwk Δ (cv _) γ) (trans eq (sym (lc-length-resp-gwk (Δ ^^ cv _) γ)))
  lsubst-gwk {γ = γ} ([]-wf {_} {_} {Γ} ⊢Γ refl eq′) ⊢γ  = []-wf (lctx-gwk ⊢Γ ⊢γ) (^^-gwk _ [] γ) (trans eq′ (sym (lc-length-resp-gwk Γ γ)))
  lsubst-gwk {γ = γ} ([]′-wf {_} {_} {Γ} ⊢Γ ctx∈ refl eq′) ⊢γ = []′-wf (lctx-gwk ⊢Γ ⊢γ) (x-gwk ⊢γ ctx∈) (^^-gwk _ (cv _) γ) (trans eq′ (sym (lc-length-resp-gwk Γ γ)))
  lsubst-gwk (∷-wf ⊢δ ⊢t) ⊢γ = ∷-wf (lsubst-gwk ⊢δ ⊢γ) (trm-gwk ⊢t ⊢γ)


-- Global Weakening for Global Substitutions

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
          rewrite ty-gsub-wk≈gwk (1 + L.length Φ) ⊢T
                | lctx-gsub-wk≈gwk (1 + L.length Φ) ⊢Γ = gv-wf (∈G-gwk-lookup Φ (Γ , T) Ψ)
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
  presup-lsub (wk-wf ⊢Γ ctx∈ eq _) = ⊢Γ , ⊢ctx (presup-l ⊢Γ) ctx∈
  presup-lsub ([]-wf ⊢Γ _ _)       = ⊢Γ , ⊢[] (presup-l ⊢Γ)
  presup-lsub ([]′-wf ⊢Γ _ _ _)    = ⊢Γ , ⊢[] (presup-l ⊢Γ)
  presup-lsub (∷-wf ⊢δ ⊢t)
    with presup-lsub ⊢δ | presup-trm ⊢t
  ...  | ⊢Γ , ⊢Δ | _ , ⊢T          = ⊢Γ , ⊢∷ ⊢Δ ⊢T


-- Bridging Special Global Substitutions and Global Weakenings

gsub-wk≈gwk-trm-x-gen : ∀ Φ m n Ψ →
                        x ∶ B ∈G Φ ++ Ψ →
                        m ≡ L.length Φ →
                        B ≡ (Γ , T) →
                        gsub-trm-x x (gsub-qp Φ n Ψ) ≡ gvar (wk-x x (repeat q m (repeat p n id))) (lsub-id Γ [ repeat q m (repeat p n id) ])
gsub-wk≈gwk-trm-x-gen [] _ n ._ (here {_} {Γ , T}) refl refl
  rewrite wk-x-repeat-p′ 0 n
        | sym (gwk-lsub-id Γ (p id))
        | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat p n id)
        | pid∘p*id n = refl
gsub-wk≈gwk-trm-x-gen [] ._ n ._ (there {x} {_} {Γ , T} {ctx} B∈) refl refl
  with gsub-wk≈gwk-trm-x-gen [] _ (suc n) _ B∈ refl refl
...  | eq″
     rewrite wk-x-repeat-p′ (suc x) n
           | wk-x-repeat-p′ x n
           | sym (gwk-lsub-id Γ (p id))
           | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat p n id)
           | pid∘p*id n = eq″
gsub-wk≈gwk-trm-x-gen [] ._ n ._ (there {x} {_} {Γ , T} {_ , _} B∈) refl refl
  with gsub-wk≈gwk-trm-x-gen [] _ (suc n) _ B∈ refl refl
...  | eq″
     rewrite wk-x-repeat-p′ (suc x) n
           | wk-x-repeat-p′ x n
           | sym (gwk-lsub-id Γ (p id))
           | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat p n id)
           | pid∘p*id n = eq″
gsub-wk≈gwk-trm-x-gen (ctx ∷ Φ) (suc m) n Ψ (there  {x} {_} {Γ , T} B∈) refl refl
  rewrite sym (gwk-gsub-trm-x x (gsub-qp Φ n Ψ) (p id))
        | gsub-wk≈gwk-trm-x-gen Φ m n _ B∈ refl refl
        | sym (gwk-lsub-id Γ (p id))
        | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat q (suc m) (repeat p n id))
        | gwk-lsubst-comp (lsub-id Γ) (repeat q m (repeat p n id)) (p id)
        | ∘w-pid (repeat q m (repeat p n id)) = refl
gsub-wk≈gwk-trm-x-gen ((Γ , _) ∷ Φ) (suc m) n Ψ here refl refl
  rewrite sym (gwk-lsub-id Γ (p id))
        | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat q (suc m) (repeat p n id)) = refl
gsub-wk≈gwk-trm-x-gen ((_ , _) ∷ Φ) (suc m) n Ψ (there {x} {_} {Γ , T} B∈) refl refl
  rewrite sym (gwk-gsub-trm-x x (gsub-qp Φ n Ψ) (p id))
        | gsub-wk≈gwk-trm-x-gen Φ m n _ B∈ refl refl
        | sym (gwk-lsub-id Γ (p id))
        | gwk-lsubst-comp (lsub-id Γ) (p id) (repeat q (suc m) (repeat p n id))
        | gwk-lsubst-comp (lsub-id Γ) (repeat q m (repeat p n id)) (p id)
        | ∘w-pid (repeat q m (repeat p n id)) = refl

mutual
  trm-gsub-wk≈gwk-gen : ∀ Φ m n Ψ →
                        Φ ++ Ψ ﹔ Γ ⊢[ i ] t ∶ T →
                        m ≡ L.length Φ →
                        t [ gsub-qp Φ n Ψ ] ≡ t [ repeat q m (repeat p n id) ]
  trm-gsub-wk≈gwk-gen Φ m n Ψ (v-wf ⊢Γ T∈) eq          = refl
  trm-gsub-wk≈gwk-gen Φ m n Ψ (gv-wf {Δ = Δ} T∈ ⊢δ) eq
    rewrite lsubst-gsub-wk≈gwk-gen Φ m n Ψ ⊢δ eq
          | gsub-wk≈gwk-trm-x-gen Φ m n Ψ T∈ eq refl
          | gwk-lsub-id Δ (repeat q m (repeat p n id))
    with presup-lsub ⊢δ
  ...  | ⊢Γ , ⊢Δ
       with presup-l ⊢Γ
  ...     | ⊢ΦΨ                                        = cong (gvar _) (lsub-id-∘lˡ (lsubst-gwk ⊢δ (repeat-q-wf Φ m ⊢ΦΨ (sym eq) (gwk-repeat′ (repeat (ctx ∷_) n []) n (helper′ n) (helper n)))))
    where helper : ∀ n → L.length (repeat (ctx ∷_) n L.[]) ≡ n
          helper zero    = refl
          helper (suc n) = cong suc (helper n)
          ⊢Ψ = gctx-++⁻ Φ ⊢ΦΨ

          helper′ : ∀ n → ⊢ repeat (ctx L.∷_) n L.[] L.++ Ψ
          helper′ zero    = ⊢Ψ
          helper′ (suc n) = ⊢ctx (helper′ n)
  trm-gsub-wk≈gwk-gen Φ m n Ψ (zero-wf ⊢Γ) eq          = refl
  trm-gsub-wk≈gwk-gen Φ m n Ψ (succ-wf ⊢t) eq          = cong succ (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq)
  trm-gsub-wk≈gwk-gen Φ m n Ψ (Λ-wf ⊢t) eq             = cong Λ (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq)
  trm-gsub-wk≈gwk-gen Φ m n Ψ ($-wf ⊢t ⊢s) eq          = cong₂ _$_ (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq) (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢s eq)
  trm-gsub-wk≈gwk-gen Φ m n Ψ (box-wf ⊢Γ ⊢t) eq        = cong box (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq)
  trm-gsub-wk≈gwk-gen Φ m n Ψ (letbox-wf {Δ = Δ} {t = t} ⊢s ⊢Δ ⊢S ⊢T ⊢t) refl
    rewrite lctx-gsub-wk≈gwk-gen Φ m n Ψ ⊢Δ refl       = cong₂ (letbox (_ [ repeat q m (repeat p n id) ]))
                                                               (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢s refl)
                                                               (trans (cong (λ δ → t [ trm (gvar 0 δ) ∷ (gsub-qp Φ n Ψ [ p id ]) ])
                                                                            (trans (cong lsub-id (sym (lctx-gsubst-gwk Δ (gsub-qp Φ n Ψ) (p id))))
                                                                            (trans (cong (λ Δ′ → lsub-id (Δ′ [ p id ])) (lctx-gsub-wk≈gwk-gen Φ m n Ψ ⊢Δ refl))
                                                                            (trans (cong lsub-id (gwk-lc-comp _ (repeat q m (repeat p n id)) (p id)))
                                                                            (trans (cong (λ γ → lsub-id (_ [ γ ])) (∘w-pid (repeat q m (repeat p n id))))
                                                                                   (sym (gwk-lsub-id _ (p (repeat q m (repeat p n id))))))))))
                                                                      (trm-gsub-wk≈gwk-gen (_ ∷ Φ) (suc m) n Ψ ⊢t refl))
  trm-gsub-wk≈gwk-gen Φ m n Ψ (Λc-wf ⊢Γ ⊢t) eq         = cong Λc (trm-gsub-wk≈gwk-gen (ctx ∷ Φ) (suc m) n Ψ ⊢t (cong suc eq))
  trm-gsub-wk≈gwk-gen Φ m n Ψ ($c-wf ⊢t ⊢Δ ⊢S eq′) eq  = cong₂ _$c_ (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq) (lctx-gsub-wk≈gwk-gen Φ m n Ψ ⊢Δ eq)

  lsubst-gsub-wk≈gwk-gen : ∀ Φ m n Ψ →
                           Φ ++ Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                           m ≡ L.length Φ →
                           δ [ gsub-qp Φ n Ψ ] ≡ δ [ repeat q m (repeat p n id) ]
  lsubst-gsub-wk≈gwk-gen Φ m n Ψ (wk-wf ⊢Γ ctx∈ eq′ eq″) eq
    rewrite gsub-wk≈gwk-ty-x-gen Φ m n Ψ ctx∈ eq refl        = cong (wk _) (wk-x-repeat-p′ 0 _)
  lsubst-gsub-wk≈gwk-gen Φ m n Ψ ([]-wf ⊢Γ eq′ eq″) eq       = refl
  lsubst-gsub-wk≈gwk-gen Φ m n Ψ ([]′-wf ⊢Γ ctx∈ eq′ eq″) eq
    rewrite gsub-wk≈gwk-ty-x-gen Φ m n Ψ ctx∈ eq refl        = refl
  lsubst-gsub-wk≈gwk-gen Φ m n Ψ (∷-wf ⊢δ ⊢t) eq             = cong₂ _∷_ (trm-gsub-wk≈gwk-gen Φ m n Ψ ⊢t eq) (lsubst-gsub-wk≈gwk-gen Φ m n Ψ ⊢δ eq)


gsub-id-trm : Ψ ﹔ Γ ⊢[ i ] t ∶ T →
              t [ gsub-id Ψ ] ≡ t
gsub-id-trm ⊢t
  rewrite trm-gsub-wk≈gwk-gen [] 0 0 _ ⊢t refl = gwk-id-trm 0 _

gsub-id-lsubst : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
                 δ [ gsub-id Ψ ] ≡ δ
gsub-id-lsubst ⊢δ
  rewrite lsubst-gsub-wk≈gwk-gen [] 0 0 _ ⊢δ refl = gwk-id-lsubst 0 _

-- Identities of Composition of Global Substitutions

gsub-idʳ : Ψ ⊢ σ ∶ Φ →
           (σ ∘g gsub-id Ψ) ≡ σ
gsub-idʳ ([]-wf _)          = refl
gsub-idʳ (trm-wf ⊢σ _ _ ⊢t) = cong₂ _∷_ (cong trm (gsub-id-trm ⊢t)) (gsub-idʳ ⊢σ)
gsub-idʳ (ctx-wf ⊢σ ⊢Γ)     = cong₂ _∷_ (cong ctx (gsub-id-lctx ⊢Γ)) (gsub-idʳ ⊢σ)

gsub-trm-x-++ : ∀ σ′ t σ x →
                L.length σ′ ≡ x →
                gsub-trm-x x (σ′ ++ trm t ∷ σ) ≡ t
gsub-trm-x-++ [] t σ zero eq            = refl
gsub-trm-x-++ (_ ∷ σ′) t σ (suc x) refl = gsub-trm-x-++ σ′ t σ x refl

gsub-ty-x-++ : ∀ σ′ Γ σ x →
               L.length σ′ ≡ x →
               gsub-ty-x x (σ′ ++ ctx Γ ∷ σ) ≡ Γ
gsub-ty-x-++ [] Γ σ zero eq            = refl
gsub-ty-x-++ (_ ∷ σ′) Γ σ (suc x) refl = gsub-ty-x-++ σ′ Γ σ x refl

gsub-wk-gen :  ∀ σ′ n →
               Ψ ⊢ σ ∶ Φ →
               n ≡ L.length σ′ →
               (gsub-wk n Φ ∘g (σ′ ++ σ)) ≡ σ
gsub-wk-gen σ′ n ([]-wf ⊢Ψ) eq         = refl
gsub-wk-gen σ′ n (trm-wf {_} {σ} {_} {Γ} {t = t} ⊢σ _ _ ⊢t) eq
  with trans (cong suc eq) (trans (sym (ℕₚ.+-comm _ 1)) (sym (length-++ σ′)))
...  | eq′
     with gsub-wk-gen (σ′ ++ L.[ trm t ]) (suc n) ⊢σ eq′
...     | eq″
        rewrite gsub-trm-x-++ σ′ t σ n (sym eq)
              | sym (++-assoc σ′ L.[ trm t ] σ)
              | p-gsub-lsubst* (lsub-id Γ) (σ′ ++ L.[ trm t ]) σ (suc n) eq′
              | eq″
              | gsubst-lsub-id Γ σ
              | lsub-trm-lsub-id ⊢t = refl
gsub-wk-gen σ′ n (ctx-wf {_} {σ} {_} {Γ} ⊢σ ⊢Γ) eq
  with trans (cong suc eq) (trans (sym (ℕₚ.+-comm _ 1)) (sym (length-++ σ′)))
...  | eq′
     with gsub-wk-gen (σ′ ++ L.[ ctx Γ ]) (suc n) ⊢σ eq′
...     | eq″
        rewrite gsub-ty-x-++ σ′ Γ σ n (sym eq)
              | sym (++-assoc σ′ L.[ ctx Γ ] σ)
              | eq″ = refl

gsub-idˡ : Ψ ⊢ σ ∶ Φ →
           (gsub-id Φ ∘g σ) ≡ σ
gsub-idˡ ⊢σ = gsub-wk-gen [] 0 ⊢σ refl

-- Convenient Constructor for Letbox

letbox-wf′ : Ψ ﹔ Γ ⊢[ 𝟙 ] s ∶ □ Δ S →
             Ψ ⊢[ 𝟙 ] T →
             (Δ , S) ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T [ p id ] →
             -------------------------
             Ψ ﹔ Γ ⊢[ 𝟙 ] letbox Δ s t ∶ T
letbox-wf′ ⊢s ⊢T ⊢t
  with presup-trm ⊢s
... | _ , ⊢□ ⊢Δ ⊢S = letbox-wf ⊢s ⊢Δ ⊢S ⊢T ⊢t

-- Local Weakening of Terms and Local Substitutions

⊆l-cv : ∀ {Δ} → Γ′ ⊆l Γ → Γ ≡ Δ ^^ cv x → Γ′ ≡ Γ
⊆l-cv id-cv eq = refl
⊆l-cv id-[] eq = refl
⊆l-cv {Δ = []} cv-[] ()
⊆l-cv {Δ = _ ∷ Δ} cv-[] ()
⊆l-cv {Δ = []} (cons Γ′⊆Γ) ()
⊆l-cv {Δ = _ ∷ Δ} (cons Γ′⊆Γ) refl = cong (_ ∷_) (⊆l-cv Γ′⊆Γ refl)

⊢lw-cv : ∀ {Δ} → Ψ ﹔ Γ′ ⊢lw[ i ] τ ∶ Γ → Γ ≡ Δ ^^ cv x → ∃ λ Δ′ → Γ′ ≡ Δ′ ^^ cv x
⊢lw-cv (id-wf _) eq = -, eq
⊢lw-cv (p-wf ⊢τ ⊢T) eq
  with ⊢lw-cv ⊢τ eq
...  | _ , eq′      = -, cong (_ ∷_) eq′
⊢lw-cv {Δ = _ ∷ Δ} (q-wf ⊢τ ⊢T) refl
  with ⊢lw-cv ⊢τ refl
...  | _ , eq′      = -, cong (_ ∷_) eq′

⊢lw-[] : ∀ {Δ} → Ψ ﹔ Γ′ ⊢lw[ i ] τ ∶ Γ → Γ ≡ Δ ^^ [] → ∃ λ Δ′ → Γ′ ≡ Δ′ ^^ []
⊢lw-[] (id-wf _) eq = -, eq
⊢lw-[] (p-wf ⊢τ ⊢T) eq
  with ⊢lw-[] ⊢τ eq
...  | _ , eq′      = -, cong (_ ∷_) eq′
⊢lw-[] {Δ = _ ∷ Δ} (q-wf ⊢τ ⊢T) refl
  with ⊢lw-[] ⊢τ refl
...  | _ , eq′      = -, cong (_ ∷_) eq′

⊆l-resp-lc-length : Δ ⊆l Γ → lc-length Δ ≡ lc-length Γ
⊆l-resp-lc-length id-cv      = refl
⊆l-resp-lc-length id-[]      = refl
⊆l-resp-lc-length cv-[]      = refl
⊆l-resp-lc-length (cons Δ⊆Γ) = cong suc (⊆l-resp-lc-length Δ⊆Γ)

lc-length-lwk : ∀ {n} → Ψ ﹔ Δ ⊢lw[ i ] τ ∶ Γ → n ≡ lc-length Γ → wk-x n τ ≡ lc-length Δ
lc-length-lwk (id-wf _) eq     = eq
lc-length-lwk (p-wf ⊢τ _) eq   = cong suc (lc-length-lwk ⊢τ eq)
lc-length-lwk (q-wf ⊢τ _) refl = cong suc (lc-length-lwk ⊢τ refl)

mutual
  trm-lwk : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ ﹔ Δ ⊢lw[ i ] τ ∶ Γ → Ψ ﹔ Δ ⊢[ i ] lwk-trm t τ ∶ T
  trm-lwk (v-wf ⊢Γ T∈) ⊢τ                = v-wf (proj₁ (⊢lw-inv ⊢τ)) (∈L-lwk T∈ ⊢τ)
  trm-lwk (gv-wf T∈ ⊢δ) ⊢τ               = gv-wf T∈ (lsubst-lwk ⊢δ ⊢τ)
  trm-lwk (zero-wf ⊢Γ) ⊢τ                = zero-wf (proj₁ (⊢lw-inv ⊢τ))
  trm-lwk (succ-wf ⊢t) ⊢τ                = succ-wf (trm-lwk ⊢t ⊢τ)
  trm-lwk (Λ-wf ⊢t) ⊢τ
    with presup-trm ⊢t
  ... | ⊢∷ _ ⊢S , _                      = Λ-wf (trm-lwk ⊢t (q-wf ⊢τ ⊢S))
  trm-lwk ($-wf ⊢t ⊢s) ⊢τ                = $-wf (trm-lwk ⊢t ⊢τ) (trm-lwk ⊢s ⊢τ)
  trm-lwk (box-wf ⊢Γ ⊢t) ⊢τ              = box-wf (proj₁ (⊢lw-inv ⊢τ)) ⊢t
  trm-lwk (letbox-wf ⊢s ⊢Δ′ ⊢S ⊢T ⊢t) ⊢τ = letbox-wf′ (trm-lwk ⊢s ⊢τ) ⊢T (trm-lwk ⊢t (lwk-gwk (p-wf (id-wf (presup-ty ⊢T)) (b-wf ⊢Δ′ ⊢S)) ⊢τ))
  trm-lwk (Λc-wf ⊢Γ ⊢t) ⊢τ               = Λc-wf (proj₁ (⊢lw-inv ⊢τ)) (trm-lwk ⊢t (lwk-gwk (p-wf (id-wf (presup-l ⊢Γ)) (ctx-wf (presup-l ⊢Γ))) ⊢τ))
  trm-lwk ($c-wf ⊢t ⊢Δ′ ⊢T′ eq) ⊢τ       = $c-wf (trm-lwk ⊢t ⊢τ) ⊢Δ′ ⊢T′ eq

  lsubst-lwk : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → Ψ ﹔ Γ′ ⊢lw[ i ] τ ∶ Γ → Ψ ﹔ Γ′ ⊢s[ i ] lwk-lsubst δ τ ∶ Δ
  lsubst-lwk (wk-wf ⊢Γ ctx∈ eq eq′) ⊢τ
    with ⊢lw-cv ⊢τ eq
  ...  | _ , eq″                        = wk-wf (proj₁ (⊢lw-inv ⊢τ)) ctx∈ eq″ (lc-length-lwk ⊢τ eq′)
  lsubst-lwk ([]-wf ⊢Γ eq eq′) ⊢τ       = []-wf (proj₁ (⊢lw-inv ⊢τ)) (proj₂ (⊢lw-[] ⊢τ eq)) (lc-length-lwk ⊢τ eq′)
  lsubst-lwk ([]′-wf ⊢Γ ctx∈ eq eq′) ⊢τ = []′-wf (proj₁ (⊢lw-inv ⊢τ)) ctx∈ (proj₂ (⊢lw-cv ⊢τ eq)) (lc-length-lwk ⊢τ eq′)
  lsubst-lwk (∷-wf ⊢δ ⊢t) ⊢τ            = ∷-wf (lsubst-lwk ⊢δ ⊢τ) (trm-lwk ⊢t ⊢τ)


-- Local Substitutions of Terms and Composition

lsub-x-lookup : x ∶ T ∈L Γ → Ψ ﹔ Δ ⊢s[ i ] δ ∶ Γ → Ψ ﹔ Δ ⊢[ i ] lsub-x x δ ∶ T
lsub-x-lookup here (∷-wf ⊢δ ⊢t)      = ⊢t
lsub-x-lookup (there T∈) (∷-wf ⊢δ _) = lsub-x-lookup T∈ ⊢δ

lsubst-cv : Ψ ﹔ Γ′ ⊢s[ i ] δ ∶ Γ → ∀ {Δ} → Γ ≡ Δ ^^ cv x → ∃ λ Δ′ → Γ′ ≡ Δ′ ^^ cv x
lsubst-cv (wk-wf ⊢Γ′ ctx∈ eq′ _) {[]} refl = -, eq′
lsubst-cv ([]-wf ⊢Γ′ _ _) {[]} ()
lsubst-cv ([]′-wf ⊢Γ′ _ _ _) {[]} ()
lsubst-cv (∷-wf ⊢δ ⊢t) {T ∷ Δ} refl      = lsubst-cv ⊢δ refl

mutual
  trm-lsubst : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ ﹔ Δ ⊢s[ i ] δ ∶ Γ → Ψ ﹔ Δ ⊢[ i ] lsub-trm t δ ∶ T
  trm-lsubst (v-wf ⊢Γ T∈) ⊢δ               = lsub-x-lookup T∈ ⊢δ
  trm-lsubst (gv-wf T∈ ⊢δ′) ⊢δ             = gv-wf T∈ (lsubst-compose ⊢δ′ ⊢δ)
  trm-lsubst (zero-wf ⊢Γ) ⊢δ               = zero-wf (proj₁ (presup-lsub ⊢δ))
  trm-lsubst (succ-wf ⊢t) ⊢δ               = succ-wf (trm-lsubst ⊢t ⊢δ)
  trm-lsubst (Λ-wf ⊢t) ⊢δ
    with presup-lsub ⊢δ | presup-trm ⊢t
  ... | ⊢Δ , _ | ⊢∷ ⊢Γ ⊢S , _              = Λ-wf (trm-lsubst ⊢t (∷-wf (lsubst-lwk ⊢δ (p-wf (id-wf ⊢Δ) ⊢S)) (v-wf (⊢∷ ⊢Δ ⊢S) here)))
  trm-lsubst ($-wf ⊢t ⊢s) ⊢δ               = $-wf (trm-lsubst ⊢t ⊢δ) (trm-lsubst ⊢s ⊢δ)
  trm-lsubst (box-wf ⊢Δ ⊢t) ⊢δ             = box-wf (proj₁ (presup-lsub ⊢δ)) ⊢t
  trm-lsubst (letbox-wf ⊢s ⊢Δ ⊢S ⊢T ⊢t) ⊢δ = letbox-wf′ (trm-lsubst ⊢s ⊢δ) ⊢T (trm-lsubst ⊢t (lsubst-gwk ⊢δ (p-wf (id-wf (presup-l ⊢Δ)) (b-wf ⊢Δ ⊢S))))
  trm-lsubst (Λc-wf ⊢Γ ⊢t) ⊢δ              = Λc-wf (proj₁ (presup-lsub ⊢δ)) (trm-lsubst ⊢t (lsubst-gwk ⊢δ (p-wf (id-wf ⊢Ψ) (ctx-wf ⊢Ψ))))
    where ⊢Ψ = presup-l ⊢Γ
  trm-lsubst ($c-wf ⊢t ⊢Δ ⊢S eq) ⊢δ        = $c-wf (trm-lsubst ⊢t ⊢δ) ⊢Δ ⊢S eq

  lsubst-compose : Ψ ﹔ Γ′ ⊢s[ i ] δ ∶ Γ → Ψ ﹔ Γ″ ⊢s[ i ] δ′ ∶ Γ′ → Ψ ﹔ Γ″ ⊢s[ i ] δ ∘l δ′ ∶ Γ
  lsubst-compose (wk-wf ⊢Γ′ ctx∈ eq eq′) ⊢δ′ = wk-wf (proj₁ (presup-lsub ⊢δ′)) ctx∈ (proj₂ (lsubst-cv ⊢δ′ eq)) (sym (lsubst-lc-length ⊢δ′))
  lsubst-compose {δ′ = δ′} ([]-wf ⊢Γ′ eq eq′) ⊢δ′
    with lsub-cv? δ′ | lsub-^^ ⊢δ′
  ...  | inj₁ _ | Δ , eq″ = []-wf (proj₁ (presup-lsub ⊢δ′)) eq″ (sym (lsubst-lc-length ⊢δ′))
  ...  | inj₂ x | Δ , refl
       with presup-lsub ⊢δ′
  ...     | ⊢Γ″ , _       = []′-wf (proj₁ (presup-lsub ⊢δ′)) (cv-bound ⊢Γ″ refl) refl (sym (lsubst-lc-length ⊢δ′))
  lsubst-compose {δ′ = δ′} ([]′-wf ⊢Γ′ ctx∈ eq eq′) ⊢δ′
    with lsub-cv? δ′ | lsub-^^ ⊢δ′
  ...  | inj₁ _ | Δ , eq″ = []-wf (proj₁ (presup-lsub ⊢δ′)) eq″ (sym (lsubst-lc-length ⊢δ′))
  ...  | inj₂ x | Δ , refl
       with presup-lsub ⊢δ′
  ...     | ⊢Γ″ , _       = []′-wf (proj₁ (presup-lsub ⊢δ′)) (cv-bound ⊢Γ″ refl) refl (sym (lsubst-lc-length ⊢δ′))
  lsubst-compose (∷-wf ⊢δ ⊢t) ⊢δ′ = ∷-wf (lsubst-compose ⊢δ ⊢δ′) (trm-lsubst ⊢t ⊢δ′)


-- Global Substitutions of Terms and Local Substitutions

∈L-gsub : (σ : GSubst) →
          x ∶ T ∈L Γ →
          x ∶ T [ σ ] ∈L Γ [ σ ]
∈L-gsub σ here       = here
∈L-gsub σ (there T∈) = there (∈L-gsub σ T∈)

^^-gsub : (Γ : List Typ) (Δ : LCtx) (σ : GSubst) → (Γ ^^ Δ) [ σ ] ≡ L.map _[ σ ] Γ ^^ (Δ [ σ ])
^^-gsub [] Δ σ      = refl
^^-gsub (T ∷ Γ) Δ σ = cong (_ ∷_) (^^-gsub Γ Δ σ)

gsub-lookup : x ∶ B ∈G Ψ → B ≡ (Γ , T) → Ψ′ ⊢ σ ∶ Ψ → Ψ′ ﹔ Γ [ σ ] ⊢[ 𝟘 ] gsub-trm-x x σ ∶ T [ σ ]
gsub-lookup (here {_} {Γ , T}) refl (trm-wf {_} {σ} {t = t} ⊢σ _ _ ⊢t)
  rewrite p-gsub-lctx Γ (trm t) σ
        | p-gsub-ty T (trm t) σ = ⊢t
gsub-lookup (there {_} {_} {Δ , S} {.(_ , _)} B∈) refl (trm-wf {_} {σ} {t = t} ⊢σ _ _ _)
  rewrite p-gsub-lctx Δ (trm t) σ
        | p-gsub-ty S (trm t) σ = gsub-lookup B∈ refl ⊢σ
gsub-lookup (there {_} {_} {Δ , S} {.ctx} B∈) refl (ctx-wf {_} {σ} {_} {Γ} ⊢σ _)
  rewrite p-gsub-lctx Δ (ctx Γ) σ
        | p-gsub-ty S (ctx Γ) σ = gsub-lookup B∈ refl ⊢σ

p-wf* : ∀ Γ n →
        Ψ ⊢l[ i ] Γ ^^ Δ →
        n ≡ L.length Γ →
        Ψ ﹔ Γ ^^ Δ ⊢lw[ i ] repeat p n id ∶ Δ
p-wf* [] zero ⊢Δ eq                    = id-wf ⊢Δ
p-wf* (T ∷ Γ) (suc n) (⊢∷ ⊢ΓΔ ⊢T) refl = p-wf (p-wf* Γ n ⊢ΓΔ refl) ⊢T

mutual
  trm-gsubst : Ψ ﹔ Γ ⊢[ i ] t ∶ T → Ψ′ ⊢ σ ∶ Ψ → Ψ′ ﹔ Γ [ σ ] ⊢[ i ] t [ σ ] ∶ T [ σ ]
  trm-gsubst (v-wf ⊢Γ T∈) ⊢σ               = v-wf (lctx-gsubst ⊢Γ ⊢σ) (∈L-gsub _ T∈)
  trm-gsubst (gv-wf T∈ ⊢δ) ⊢σ              = trm-lsubst (lift-trm″ (gsub-lookup T∈ refl ⊢σ)) (lsubst-gsubst ⊢δ ⊢σ)
  trm-gsubst (zero-wf ⊢Γ) ⊢σ               = zero-wf (lctx-gsubst ⊢Γ ⊢σ)
  trm-gsubst (succ-wf ⊢t) ⊢σ               = succ-wf (trm-gsubst ⊢t ⊢σ)
  trm-gsubst (Λ-wf ⊢t) ⊢σ                  = Λ-wf (trm-gsubst ⊢t ⊢σ)
  trm-gsubst ($-wf ⊢t ⊢s) ⊢σ               = $-wf (trm-gsubst ⊢t ⊢σ) (trm-gsubst ⊢s ⊢σ)
  trm-gsubst (box-wf ⊢Δ ⊢t) ⊢σ             = box-wf (lctx-gsubst ⊢Δ ⊢σ) (trm-gsubst ⊢t ⊢σ)
  trm-gsubst {_} {Γ} {Ψ′ = Ψ′} {σ} (letbox-wf {Δ = Δ} {S} {T = T} {t = t} ⊢s ⊢Δ ⊢S ⊢T ⊢t) ⊢σ
    = letbox-wf′ (trm-gsubst ⊢s ⊢σ) (ty-gsubst ⊢T ⊢σ) helper
    where ⊢pid = p-wf (id-wf (proj₁ (gsubst-inv ⊢σ))) (b-wf (lctx-gsubst ⊢Δ ⊢σ) (ty-gsubst ⊢S ⊢σ))
          bound : 0 ∶ Δ [ σ [ p id ] ] , S [ σ [ p id ] ] ∈G (Δ [ σ ] , S [ σ ]) ∷ Ψ′
          bound
            rewrite sym (lctx-gsubst-gwk Δ σ (p id))
                  | sym (ty-gsubst-gwk S σ (p id)) = here
          ⊢t′ = trm-gsubst ⊢t (trm-wf (gsubst-gwk ⊢σ ⊢pid) ⊢Δ ⊢S (gv-wf bound (⊢lsub-id (lctx-gsubst ⊢Δ (gsubst-gwk ⊢σ ⊢pid)))))
          helper : (Δ [ σ ] , S [ σ ]) ∷ Ψ′ ﹔ Γ [ σ ] [ p id ] ⊢[ 𝟙 ]
                      t [ trm (gvar 0 (lsub-id (Δ [ σ [ p id ] ]))) ∷ (σ [ p id ]) ] ∶
                      T [ σ ] [ p id ]
          helper
            with ⊢t′
          ...  | ⊢t′
               rewrite p-gsub-lctx Γ (trm (gvar 0 (lsub-id (Δ [ σ [ p id ] ])))) (σ [ p id ])
                     | p-gsub-ty T (trm (gvar 0 (lsub-id (Δ [ σ [ p id ] ])))) (σ [ p id ])
                     | lctx-gsubst-gwk Γ σ (p id)
                     | ty-gsubst-gwk T σ (p id) = ⊢t′
  trm-gsubst {_} {Γ} {σ = σ} (Λc-wf {T = T} ⊢Δ ⊢t) ⊢σ
    with trm-gsubst ⊢t (⊢gsub-q ⊢σ)
  ...  | ⊢t′
       rewrite p-gsub-lctx Γ (ctx (cv 0)) (σ [ p id ])
             | p-gsub-ty T (ctx (cv 0)) (σ [ p id ])
             | sym (lctx-gsubst-gwk Γ σ (p id))
             | sym (ty-gsubst-gwk T σ (p id)) = Λc-wf (lctx-gsubst ⊢Δ ⊢σ) ⊢t′
  trm-gsubst {Ψ′ = Ψ′} {σ} ($c-wf {Ψ} {_} {t} {T} {Δ} ⊢t ⊢Δ ⊢S refl) ⊢σ
    = $c-wf (trm-gsubst ⊢t ⊢σ) (lctx-gsubst ⊢Δ ⊢σ) (ty-gsubst ⊢S (⊢gsub-q ⊢σ))
            (trans (gsub-ty-comp T (ctx Δ ∷ gsub-id Ψ) σ)
            (trans (cong (λ σ′ → T [ ctx (Δ [ σ ]) ∷ σ′ ]) (gsub-idˡ ⊢σ))
            (sym (trans (gsub-ty-comp T (ctx (cv 0) ∷ (σ [ p id ])) (ctx (Δ [ σ ]) ∷ gsub-id Ψ′))
                 (trans (cong (λ σ′ → T [ ctx (Δ [ σ ]) ∷ σ′ ]) (p-gsub-gsubst σ (ctx (Δ [ σ ])) (gsub-id Ψ′)))
                        (cong (λ σ′ → T [ ctx (Δ [ σ ]) ∷ σ′ ]) (gsub-idʳ ⊢σ)))))))

  lsubst-gsubst : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ → Ψ′ ⊢ σ ∶ Ψ → Ψ′ ﹔ Γ [ σ ] ⊢s[ i ] δ [ σ ] ∶ Δ [ σ ]
  lsubst-gsubst {σ = σ} (wk-wf {x = x} {Δ = Δ} ⊢Γ ctx∈ refl refl) ⊢σ
    rewrite ^^-gsub Δ (cv x) σ
          | ^^-length-cv {x} Δ = lsubst-lwk (⊢lsub-id (lookup-lctx′ ctx∈ ⊢σ))
                                            (p-wf* (L.map (_[ σ ]) Δ)
                                                   (L.length Δ)
                                                   (subst (_ ⊢l[ _ ]_) (^^-gsub Δ (cv x) σ) (lctx-gsubst ⊢Γ ⊢σ))
                                                   (sym (length-map _[ σ ] Δ)))
  lsubst-gsubst {σ = σ} ([]-wf {Δ = Δ} ⊢Γ refl refl) ⊢σ
    = []-wf (lctx-gsubst ⊢Γ ⊢σ) (^^-gsub Δ [] σ)
            (trans (^^-length-[] Δ)
            (sym (trans (cong lc-length (^^-gsub Δ [] σ))
                 (trans (^^-length-[] (L.map _[ σ ] Δ))
                        (gsub-resp-length Δ σ)))))
  lsubst-gsubst {_} {_} {i} {σ = σ} ([]′-wf {x = x} {Δ = Δ} {n} ⊢Γ ctx∈ refl eq′) ⊢σ
    with lctx-gsubst ⊢Γ ⊢σ
  ...  | ⊢Γσ
       rewrite ^^-gsub Δ (cv x) σ
       with gsub-ty-x x σ | lookup-lctx′ {i = i} ctx∈ ⊢σ
  ...     | Γ′ | ⊢Γ′
          with lctx-cv? Γ′ | lctx-^^ ⊢Γ′
  ...        | inj₁ _ | Δ′ , refl         = []-wf ⊢Γσ (^^-assoc (L.map _[ σ ] Δ) Δ′ [])
                                                  (trans (cong₂ _+_ (^^-length-[] Δ′) (trans eq′ (^^-length-cv Δ)))
                                                  (trans (ℕₚ.+-comm (L.length Δ′) _)
                                                  (trans (sym (cong₂ _+_ (gsub-resp-length Δ σ) (^^-length-[] Δ′)))
                                                         (sym (^^-resp-length (L.map _[ σ ] Δ) (Δ′ ^^ []))))))
  ...        | inj₂ y | Δ′ , ctx∈′ , refl = []′-wf ⊢Γσ ctx∈′ (^^-assoc (L.map _[ σ ] Δ) Δ′ (cv y))
                                                   (trans (cong₂ _+_ (^^-length-cv Δ′) (trans eq′ (^^-length-cv Δ)))
                                                   (trans (ℕₚ.+-comm (L.length Δ′) _)
                                                   (trans (sym (cong₂ _+_ (gsub-resp-length Δ σ) (^^-length-cv Δ′)))
                                                          (sym (^^-resp-length (L.map _[ σ ] Δ) (Δ′ ^^ cv y))))))
  lsubst-gsubst (∷-wf ⊢δ ⊢t) ⊢σ = ∷-wf (lsubst-gsubst ⊢δ ⊢σ) (trm-gsubst ⊢t ⊢σ)
