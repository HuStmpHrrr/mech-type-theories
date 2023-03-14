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


data Gwk : Set where
  id  : Gwk
  p q : Gwk → Gwk


infixl 3 _∘g_

_∘g_ : Gwk → Gwk → Gwk
id ∘g γ′    = γ′
p γ ∘g q γ′ = p (γ ∘g γ′)
q γ ∘g q γ′ = q (γ ∘g γ′)
γ ∘g id     = γ
γ ∘g p γ′   = p (γ ∘g γ′)


∘g-id : ∀ γ → (γ ∘g id) ≡ γ
∘g-id id    = refl
∘g-id (p γ) = refl
∘g-id (q γ) = refl

∘g-p : ∀ γ γ′ → (γ ∘g p γ′) ≡ p (γ ∘g γ′)
∘g-p id γ′    = refl
∘g-p (p γ) γ′ = refl
∘g-p (q γ) γ′ = refl

gwk-x : ℕ → Gwk → ℕ
gwk-x x id          = x
gwk-x x (p γ)       = suc (gwk-x x γ)
gwk-x 0 (q γ)       = 0
gwk-x (suc x) (q γ) = suc (gwk-x x γ)

mutual

  gwk-ty : Typ → Gwk → Typ
  gwk-ty N γ        = N
  gwk-ty (S ⟶ T) γ  = gwk-ty S γ ⟶ gwk-ty T γ
  gwk-ty (□ Γ T) γ  = □ (gwk-lc Γ γ) (gwk-ty T γ)
  gwk-ty (ctx⇒ T) γ = ctx⇒ gwk-ty T (q γ)

  gwk-lc : LCtx → Gwk → LCtx
  gwk-lc [] γ       = []
  gwk-lc (cv x) γ   = cv (gwk-x x γ)
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

gwk-id-x : ∀ n x → gwk-x x (repeat q n id) ≡ x
gwk-id-x n zero    = helper n
  where helper : ∀ n → gwk-x zero (repeat q n id) ≡ zero
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
  x x′ x″ : ℕ


-- Composition of Global Weakenings

gwk-x-comp : ∀ x γ γ′ → gwk-x (gwk-x x γ) γ′ ≡ gwk-x x (γ ∘g γ′)
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
  gwk-ty-comp : ∀ (T : Typ) γ γ′ → T [ γ ] [ γ′ ] ≡ T [ γ ∘g γ′ ]
  gwk-ty-comp N γ γ′                   = refl
  gwk-ty-comp (S ⟶ T) γ γ′
    rewrite gwk-ty-comp S γ γ′
          | gwk-ty-comp T γ γ′         = refl
  gwk-ty-comp (□ Γ T) γ γ′
    rewrite gwk-lc-comp Γ γ γ′
          | gwk-ty-comp T γ γ′         = refl
  gwk-ty-comp (ctx⇒ T) γ γ′
    rewrite gwk-ty-comp T (q γ) (q γ′) = refl

  gwk-lc-comp : ∀ (Γ : LCtx) γ γ′ → Γ [ γ ] [ γ′ ] ≡ Γ [ γ ∘g γ′ ]
  gwk-lc-comp [] γ γ′          = refl
  gwk-lc-comp (cv x) γ γ′
    rewrite gwk-x-comp x γ γ′  = refl
  gwk-lc-comp (T ∷ Γ) γ γ′
    rewrite gwk-ty-comp T γ γ′
          | gwk-lc-comp Γ γ γ′ = refl

gwk-bnd-comp : ∀ (B : Bnd) γ γ′ → B [ γ ] [ γ′ ] ≡ B [ γ ∘g γ′ ]
gwk-bnd-comp ctx γ γ′        = refl
gwk-bnd-comp (Γ , T) γ γ′
  rewrite gwk-lc-comp Γ γ γ′
        | gwk-ty-comp T γ γ′ = refl


infix 2 _∶_∈G_
data _∶_∈G_ : ℕ → Bnd → GCtx → Set where
  here  : ∀ {B} → 0 ∶ B [ p id ] ∈G B ∷ Ψ
  there : ∀ {B B′} → x ∶ B ∈G Ψ → suc x ∶ B [ p id ] ∈G B′ ∷ Ψ


infix 4 ⊢_ _⊢[_]_ _﹔_⊢[_]_

mutual

  -- well-formedness of global contexts
  data ⊢_ : GCtx → Set where
    ⊢[]  : ⊢ []
    ⊢ctx : ⊢ Ψ → ⊢ ctx ∷ Ψ
    ⊢v   : Ψ ﹔ Γ ⊢[ 𝟘 ] T → ⊢ (Γ , T) ∷ Ψ

  -- well-formedness of local contexts
  data _⊢[_]_ : GCtx → Layer → LCtx → Set where
    ⊢[]  : ⊢ Ψ → Ψ ⊢[ i ] []
    ⊢ctx : ⊢ Ψ → x ∶ ctx ∈G Ψ → Ψ ⊢[ i ] cv x
    ⊢v   : Ψ ﹔ Γ ⊢[ i ] T → Ψ ⊢[ i ] T ∷ Γ

  -- well-formedness of types
  data _﹔_⊢[_]_ : GCtx → LCtx → Layer → Typ → Set where
    ⊢N : Ψ ⊢[ i ] Γ → Ψ ﹔ Γ ⊢[ i ] N
    ⊢⟶ : Ψ ﹔ Γ ⊢[ i ] S → Ψ ﹔ Γ ⊢[ i ] T → Ψ ﹔ Γ ⊢[ i ] S ⟶ T
    ⊢□ : Ψ ⊢[ 𝟙 ] Γ → Ψ ﹔ Δ ⊢[ 𝟘 ] T → Ψ ﹔ Γ ⊢[ 𝟙 ] □ Δ T
    ⊢⇒ : Ψ ⊢[ 𝟙 ] Γ → ctx ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] T → Ψ ﹔ Γ ⊢[ 𝟙 ] ctx⇒ T


infix 4 _⊢_

data _⊢_ : GCtx → Bnd → Set where
  ctx-wf : ⊢ Ψ → Ψ ⊢ ctx
  b-wf   : Ψ ﹔ Γ ⊢[ 𝟘 ] T → Ψ ⊢ (Γ , T)


infix 4 _⊢gw_∶_

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


bnd-wf : ∀ {B} → Ψ ⊢ B → ⊢ B ∷ Ψ
bnd-wf (ctx-wf ⊢Ψ) = ⊢ctx ⊢Ψ
bnd-wf (b-wf ⊢T)   = ⊢v ⊢T

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
     rewrite ∘g-p γ id
           | ∘g-id γ
           | sym eq = there x∈

here-gwk : ∀ {B} → 0 ∶ B [ p γ ] ∈G (B [ γ ]) ∷ Ψ
here-gwk {γ} {_} {B}
  with gwk-bnd-comp B γ (p id)
...  | eq
     rewrite ∘g-p γ id
           | ∘g-id γ
           | sym eq = here

x-gwk : ∀ {x B} → Ψ ⊢gw γ ∶ Φ → x ∶ B ∈G Φ → gwk-x x γ ∶ B [ γ ] ∈G Ψ
x-gwk {B = B} (id-wf ⊢Ψ) B∈
  rewrite gwk-id-bnd B                = B∈
x-gwk (p-wf ⊢γ ⊢B′) B∈              = there-gwk (x-gwk ⊢γ B∈)
x-gwk (q-wf {_} {γ} {B = B} ⊢γ ⊢B ⊢B′) here
  rewrite gwk-bnd-comp B (p id) (q γ) = here-gwk
x-gwk (q-wf {_} {γ} ⊢γ ⊢B ⊢B′) (there {B = B} B∈)
  rewrite gwk-bnd-comp B (p id) (q γ) = there-gwk (x-gwk ⊢γ B∈)


mutual

  lctx-gwk : Φ ⊢[ i ] Γ → Ψ ⊢gw γ ∶ Φ → Ψ ⊢[ i ] Γ [ γ ]
  lctx-gwk (⊢[] ⊢Φ) ⊢γ       = ⊢[] (proj₁ (⊢gw-inv ⊢γ))
  lctx-gwk (⊢ctx ⊢Φ ctx∈) ⊢γ = ⊢ctx (proj₁ (⊢gw-inv ⊢γ)) (x-gwk ⊢γ ctx∈)
  lctx-gwk (⊢v ⊢T) ⊢γ        = ⊢v (ty-gwk ⊢T ⊢γ)

  ty-gwk : Φ ﹔ Γ ⊢[ i ] T → Ψ ⊢gw γ ∶ Φ → Ψ ﹔ Γ [ γ ] ⊢[ i ] T [ γ ]
  ty-gwk (⊢N ⊢Γ) ⊢γ    = ⊢N (lctx-gwk ⊢Γ ⊢γ)
  ty-gwk (⊢⟶ ⊢S ⊢T) ⊢γ = ⊢⟶ (ty-gwk ⊢S ⊢γ) (ty-gwk ⊢T ⊢γ)
  ty-gwk (⊢□ ⊢Γ ⊢T) ⊢γ = ⊢□ (lctx-gwk ⊢Γ ⊢γ) (ty-gwk ⊢T ⊢γ)
  ty-gwk {_} {Γ} {_} {_} {_} {γ} (⊢⇒ ⊢Γ ⊢T) ⊢γ
    with ty-gwk ⊢T (q-wf ⊢γ (ctx-wf (proj₂ (⊢gw-inv ⊢γ))) (ctx-wf (proj₁ (⊢gw-inv ⊢γ))))
       | gwk-lc-comp Γ γ (p id)
  ...  | ⊢T′ | eq
       rewrite gwk-lc-comp Γ (p id) (q γ)
             | ∘g-p γ id
             | ∘g-id γ
             | sym eq = ⊢⇒ (lctx-gwk ⊢Γ ⊢γ) ⊢T′


bnd-gwk : ∀ {B} → Ψ ⊢gw γ ∶ Φ → Φ ⊢ B → Ψ ⊢ B [ γ ]
bnd-gwk ⊢γ (ctx-wf ⊢Ψ) = ctx-wf (proj₁ (⊢gw-inv ⊢γ))
bnd-gwk ⊢γ (b-wf ⊢T)   = b-wf (ty-gwk ⊢T ⊢γ)

q-wf′ : ∀ {B} →
        Ψ ⊢gw γ ∶ Φ →
        Φ ⊢ B →
        (B [ γ ]) ∷ Ψ ⊢gw q γ ∶ B ∷ Φ
q-wf′ ⊢γ ⊢B = q-wf ⊢γ ⊢B (bnd-gwk ⊢γ ⊢B)


-- Presupposition

mutual

  presup-l : Ψ ⊢[ i ] Γ → ⊢ Ψ
  presup-l (⊢[] ⊢Ψ)      = ⊢Ψ
  presup-l (⊢ctx ⊢Ψ x∈Ψ) = ⊢Ψ
  presup-l (⊢v ⊢T)       = proj₁ (presup-ty ⊢T)

  presup-ty : Ψ ﹔ Γ ⊢[ i ] T → ⊢ Ψ × Ψ ⊢[ i ] Γ
  presup-ty (⊢N ⊢Γ)    = presup-l ⊢Γ , ⊢Γ
  presup-ty (⊢⟶ ⊢S ⊢T) = presup-ty ⊢T
  presup-ty (⊢□ ⊢Γ ⊢T) = presup-l ⊢Γ , ⊢Γ
  presup-ty (⊢⇒ ⊢Γ _)  = presup-l ⊢Γ , ⊢Γ


ty-wf-p : Ψ ﹔ Γ ⊢[ i ] T → Ψ ﹔ Γ ⊢[ i ] S → Ψ ﹔ S ∷ Γ ⊢[ i ] T
ty-wf-p (⊢N ⊢Γ) ⊢S     = ⊢N (⊢v ⊢S)
ty-wf-p (⊢⟶ ⊢T ⊢T′) ⊢S = ⊢⟶ (ty-wf-p ⊢T ⊢S) (ty-wf-p ⊢T′ ⊢S)
ty-wf-p (⊢□ ⊢Γ ⊢T) ⊢S  = ⊢□ (⊢v ⊢S) ⊢T
ty-wf-p (⊢⇒ ⊢Γ ⊢T) ⊢S  = ⊢⇒ (⊢v ⊢S) (ty-wf-p ⊢T (ty-gwk ⊢S (p-wf (id-wf (presup-l ⊢Γ)) (ctx-wf (presup-l ⊢Γ)))))


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
    letbox : Trm → Trm → Trm
    Λc     : Trm → Trm
    _$c_   : Trm → LCtx → Trm

  data LSubst : Set where
    wk  : LSubst
    []  : LSubst
    _∷_ : Trm → LSubst → LSubst


variable
  t t′ t″ : Trm
  s s′ s″ : Trm
  σ σ′ σ″ : LSubst


mutual

  gwk-trm : Trm → Gwk → Trm
  gwk-trm (var x) γ      = var x
  gwk-trm (gvar x σ) γ   = gvar (gwk-x x γ) (gwk-lsubst σ γ)
  gwk-trm zero γ         = zero
  gwk-trm (succ t) γ     = succ (gwk-trm t γ)
  gwk-trm (Λ t) γ        = Λ (gwk-trm t γ)
  gwk-trm (t $ s) γ      = gwk-trm t γ $ gwk-trm s γ
  gwk-trm (box t) γ      = box (gwk-trm t γ)
  gwk-trm (letbox t s) γ = letbox (gwk-trm t γ) (gwk-trm s (q γ))
  gwk-trm (Λc t) γ       = Λc (gwk-trm t (q γ))
  gwk-trm (t $c Γ) γ     = gwk-trm t γ $c (Γ [ γ ])


  gwk-lsubst : LSubst → Gwk → LSubst
  gwk-lsubst wk γ = wk
  gwk-lsubst [] γ = []
  gwk-lsubst (t ∷ σ) γ = gwk-trm t γ ∷ gwk-lsubst σ γ


infix 2 _∶_∈L_

data _∶_∈L_ : ℕ → Typ → LCtx → Set where
  here  : 0 ∶ T ∈L T ∷ Γ
  there : ∀ {x} → x ∶ T ∈L Γ → suc x ∶ T ∈L S ∷ Γ

-- ∈L⇒wf : x ∶ T ∈L Γ → Ψ ⊢[ i ] Γ → Ψ ﹔ Γ ⊢[ i ] T
-- ∈L⇒wf here (⊢v ⊢T) = {!⊢T!}
-- ∈L⇒wf (there T∈) (⊢v ⊢S) = {!∈L⇒wf T∈ (proj₂ (presup-ty ⊢S))!}

infix 4 _﹔_⊢[_]_∶_ _﹔_⊢s[_]_∶_

mutual
  data _﹔_⊢[_]_∶_ : GCtx → LCtx → Layer → Trm → Typ → Set where
    v-wf      : ∀ {x} →
                Ψ ⊢[ i ] Γ →
                x ∶ T ∈L Γ →
                ------------------
                Ψ ﹔ Γ ⊢[ i ] var x ∶ T
    gv-wf     : ∀ {x} →
                x ∶ (Δ , T) ∈ Ψ →
                Ψ ﹔ Γ ⊢s[ i ] σ ∶ Δ →
                ---------------------
                Ψ ﹔ Γ ⊢[ i ] gvar x σ ∶ T
    zero-wf   : Ψ ⊢[ i ] Γ →
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
    box-wf    : Ψ ⊢[ 𝟙 ] Γ →
                Ψ ﹔ Δ ⊢[ 𝟘 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] box t ∶ □ Δ T
    letbox-wf : Ψ ﹔ Γ ⊢[ 𝟙 ] s ∶ □ Δ T →
                Ψ ﹔ Γ ⊢[ 𝟙 ] T →
                (Δ , S) ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T [ p id ] →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] letbox s t ∶ T
    Λc-wf     : Ψ ﹔ Γ ⊢[ 𝟙 ] T →
                ctx ∷ Ψ ﹔ Γ [ p id ] ⊢[ 𝟙 ] t ∶ T →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] Λc t ∶ ctx⇒ T
    $c-wf     : Ψ ﹔ Γ ⊢[ 𝟙 ] t ∶ ctx⇒ T →
                Ψ ⊢[ 𝟙 ] Δ →
                -------------------------
                Ψ ﹔ Γ ⊢[ 𝟙 ] t $c Δ ∶ {!!}


  data _﹔_⊢s[_]_∶_ : GCtx → LCtx → Layer → LSubst → LCtx → Set where
