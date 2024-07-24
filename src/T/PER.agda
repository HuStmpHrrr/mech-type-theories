{-# OPTIONS --without-K --safe #-}

module T.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)

open import Lib
open import T.Statics
open import T.TypedSem

Ty : Set₁
Ty = D → D → Set

Ev : Set₁
Ev = Env → Set

infix 8 _∈!_
_∈!_ : D → Ty → Set
d ∈! T = T d d

Top : Df → Df → Set
Top d d′ = ∀ n → ∃ λ w → Rf n - d ↘ w × Rf n - d′ ↘ w

Bot : Dn → Dn → Set
Bot e e′ = ∀ n → ∃ λ u → Re n - e ↘ u × Re n - e′ ↘ u

l∈Bot : ∀ x → Bot (l x) (l x)
l∈Bot x n = v (n ∸ x ∸ 1) , Rl n x , Rl n x

$∈Bot : Bot e e′ → Top d d′ → Bot (e $ d) (e′ $ d′)
$∈Bot e⊥e′ d⊤d′ n
  with e⊥e′ n
     | d⊤d′ n
...  | u , ↘u , ↘u′
     | w , ↘w , ↘w′ = u $ w , R$ n ↘u ↘w , R$ n ↘u′ ↘w′

record _∙_≈_∙_∈[_⟶_] f e f′ e′ S T : Set where
  field
    fe      : D
    f′e′    : D
    ↘fe     : f ∙ ↑ S e ↘ fe
    ↘f′e′   : f′ ∙ ↑ S e′ ↘ f′e′
    fe⊤f′e′ : Top (↓ T fe) (↓ T f′e′)

module FApp {f e f′ e′ S T} (eq : f ∙ e ≈ f′ ∙ e′ ∈[ S ⟶ T ]) = _∙_≈_∙_∈[_⟶_] eq

↓F∈Top : (∀ {e e′} → Bot e e′ → f ∙ e ≈ f′ ∙ e′ ∈[ S ⟶ T ]) → Top (↓ (S ⟶ T) f) (↓ (S ⟶ T) f′)
↓F∈Top f n = let w , ↘w , ↘w′ = fe⊤f′e′ (suc n)
             in Λ w , RΛ n ↘fe ↘w , RΛ n ↘f′e′ ↘w′
  where open FApp (f (l∈Bot n))

rec∈Bot : Top d d′ → Top d″ d‴ → Bot e e′ → Bot (rec T d d″ e) (rec T d′ d‴ e′)
rec∈Bot d⊤d′ d″⊤d‴ e⊥e′ n
  with d⊤d′ n
     | d″⊤d‴ n
     | e⊥e′ n
...  | w  , d↘ , d′↘
     | w′ , d″↘ , d‴↘
     | u  , e↘ , e′↘  = rec _ w w′ u
                      , Rr n d↘ d″↘ e↘
                      , Rr n d′↘ d‴↘ e′↘

ze∈Top : Top (↓ N ze) (↓ N ze)
ze∈Top n = ze , Rze n , Rze n

su∈Top : Top (↓ N a) (↓ N b) → Top (↓ N (su a)) (↓ N (su b))
su∈Top a⊤b n
  with a⊤b n
...  | w , a↘ , b↘ = su w , Rsu n a↘ , Rsu n b↘

_≈_∈^_ : D → D → Typ → Set
a ≈ b ∈^ T = Top (↓ T a) (↓ T b)

↑_≈↑_∈~_ : Dn → Dn → Typ → Set
↑ e ≈↑ e′ ∈~ T = Bot e e′

infix 4 _⊩_
record _⊩_ T (A : Ty) : Set where
  field
    ~⊆ : ∀ {e e′} → ↑ e ≈↑ e′ ∈~ T → A (↑ T e) (↑ T e′)
    ⊆^ : ∀ {a b} → A a b → a ≈ b ∈^ T

record _∙_≈_∙_∈_ (f a f′ a′ : D) (T : Ty) : Set where
  constructor
    _-_-_-_-_

  field
    fa fa′ : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    faTfa′ : T fa fa′

module FAppIn {f a f′ a′ T} (r : f ∙ a ≈ f′ ∙ a′ ∈ T) = _∙_≈_∙_∈_ r

_≈_∈_⇒_ : D → D → Ty → Ty → Set
f ≈ f′ ∈ S ⇒ T =
  ∀ {a a′} → S a a′ → f ∙ a ≈ f′ ∙ a′ ∈ T

infixr 5 _⇒_
_⇒_ : Ty → Ty → Ty
(S ⇒ U) a b = a ≈ b ∈ S ⇒ U

F⊩ : ∀ {A B} → S ⊩ A → U ⊩ B → S ⟶ U ⊩ A ⇒ B
F⊩ {S} {U} {A} {B} SA UB = record
  { ~⊆ = ~⊆
  ; ⊆^ = ⊆^
  }
  where module SA = _⊩_ SA
        module UB = _⊩_ UB

        ~⊆ : ↑ e ≈↑ e′ ∈~ (S ⟶ U) → (A ⇒ B) (↑ (S ⟶ U) e) (↑ (S ⟶ U) e′)
        ~⊆ ⊥ aAa′ = record
          { fa     = [ U ] _ $′ ↓ S _
          ; fa′    = [ U ] _ $′ ↓ S _
          ; ↘fa    = $∙ S U _ _
          ; ↘fa′   = $∙ S U _ _
          ; faTfa′ = UB.~⊆ λ n → let u , e↘ , e′↘ = ⊥ n
                                     w , a↘ , a′↘ = SA.⊆^ aAa′ n
                                 in u $ w , R$ n e↘ a↘ , R$ n e′↘ a′↘
          }

        ⊆^ : (A ⇒ B) a b → a ≈ b ∈^ (S ⟶ U)
        ⊆^ aFb n = let w , ↘w , ↘w′ = UB.⊆^ app.faTfa′ (suc n)
                   in Λ w , RΛ n app.↘fa ↘w , RΛ n app.↘fa′ ↘w′
          where app = aFb (SA.~⊆ λ m → v (m ∸ n ∸ 1) , Rl m n , Rl m n)
                module app = FAppIn app

data _≈_∈N : Ty where
  ze-≈ : ze ≈ ze ∈N
  su-≈ : a ≈ a′ ∈N →
         -------------------
         su a ≈ su a′ ∈N
  ↑N   : ∀ {T′} →
         Bot e e′ →
         -------------------
         ↑ T e ≈ ↑ T′ e′ ∈N

⟦_⟧T : Typ → Ty
⟦ N ⟧T     = _≈_∈N
⟦ S ⟶ U ⟧T = ⟦ S ⟧T ⇒ ⟦ U ⟧T

N-sym : a ≈ b ∈N → b ≈ a ∈N
N-sym ze-≈      = ze-≈
N-sym (su-≈ ab) = su-≈ (N-sym ab)
N-sym (↑N ⊥)    = ↑N (λ n → let u , ↘u , ↘u′ = ⊥ n in u , ↘u′ , ↘u)

N-trans : a ≈ a′ ∈N → a′ ≈ a″ ∈N → a ≈ a″ ∈N
N-trans ze-≈      ze-≈       = ze-≈
N-trans (su-≈ eq) (su-≈ eq′) = su-≈ (N-trans eq eq′)
N-trans (↑N ⊥e)   (↑N ⊥e′)   = ↑N λ n → let u , ↘u , e′↘ = ⊥e n
                                            _ , e′↘′ , ↘u′ = ⊥e′ n
                                        in u , ↘u , subst (Re n - _ ↘_) (Re-det e′↘′ e′↘) ↘u′

⟦⟧-sym : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T b a
⟦⟧-sym N ab          = N-sym ab
⟦⟧-sym (S ⟶ U) ab ∈S = record
  { fa     = fa′
  ; fa′    = fa
  ; ↘fa    = ↘fa′
  ; ↘fa′   = ↘fa
  ; faTfa′ = ⟦⟧-sym U faTfa′
  }
  where open FAppIn (ab (⟦⟧-sym S ∈S))

⟦⟧-trans : ∀ T → ⟦ T ⟧T a a′ → ⟦ T ⟧T a′ a″ → ⟦ T ⟧T a a″
⟦⟧-trans N eq eq′                = N-trans eq eq′
⟦⟧-trans (S ⟶ U) fFf′ f′Ff″ xSy = record
  { fa     = fxUf′x.fa
  ; fa′    = f′xUf″y.fa′
  ; ↘fa    = fxUf′x.↘fa
  ; ↘fa′   = f′xUf″y.↘fa′
  ; faTfa′ = trans′ fxUf′x.faTfa′
                    (subst (λ a → ⟦ U ⟧T a _) (ap-det f′xUf″y.↘fa fxUf′x.↘fa′) f′xUf″y.faTfa′)
  }
  where trans′ : ∀ {a b d} → ⟦ U ⟧T a b → ⟦ U ⟧T b d → ⟦ U ⟧T a d
        trans′         = ⟦⟧-trans U
        xSx            = ⟦⟧-trans S xSy (⟦⟧-sym S xSy)
        module fxUf′x  = FAppIn (fFf′ xSx)
        module f′xUf″y = FAppIn (f′Ff″ xSy)

⟦⟧-PER : ∀ T → IsPartialEquivalence ⟦ T ⟧T
⟦⟧-PER T = record
  { sym   = ⟦⟧-sym T
  ; trans = ⟦⟧-trans T
  }

⟦⟧-PartialSetoid : Typ → PartialSetoid _ _
⟦⟧-PartialSetoid T = record
  { _≈_                  = ⟦ T ⟧T
  ; isPartialEquivalence = ⟦⟧-PER T
  }

⟦⟧≈refl : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T a a
⟦⟧≈refl T ab = ⟦⟧-trans T ab (⟦⟧-sym T ab)

⊩⟦N⟧ : N ⊩ ⟦ N ⟧T
⊩⟦N⟧ = record
  { ~⊆ = ↑N
  ; ⊆^ = ⊆^
  }
  where ⊆^ : a ≈ b ∈N → a ≈ b ∈^ N
        ⊆^ ze-≈ n           = ze , Rze n , Rze n
        ⊆^ (su-≈ aNb) n
          with ⊆^ aNb n
        ...  | w , ↘w , ↘w′ = su w , Rsu n ↘w , Rsu n ↘w′
        ⊆^ (↑N e⊥e′) n
          with e⊥e′ n
        ...  | u , e↘ , e′↘ = ne u , Rne n e↘ , Rne n e′↘

⊩⟦_⟧ : ∀ T → T ⊩ ⟦ T ⟧T
⊩⟦ N ⟧     = ⊩⟦N⟧
⊩⟦ S ⟶ U ⟧ = F⊩ ⊩⟦ S ⟧ ⊩⟦ U ⟧

Bot⇒⟦⟧ : ∀ T → Bot e e′ → ⟦ T ⟧T (↑ T e) (↑ T e′)
Bot⇒⟦⟧ T = _⊩_.~⊆ ⊩⟦ T ⟧

⟦⟧⇒Top : ∀ T → ⟦ T ⟧T a b → Top (↓ T a) (↓ T b)
⟦⟧⇒Top T = _⊩_.⊆^ ⊩⟦ T ⟧

infix 4 _≈_∈⟦_⟧ ⟦_⟧_≈⟦_⟧_∈_ ⟦_⟧_≈⟦_⟧_∈s_
_≈_∈⟦_⟧ : Env → Env → Ctx → Set
ρ ≈ ρ′ ∈⟦ Δ ⟧ = ∀ {x T} → x ∶ T ∈ Δ → ⟦ T ⟧T (ρ x) (ρ′ x)

ctx-ext : ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ T ⟧T a b → ρ ↦ a ≈ ρ′ ↦ b ∈⟦ T ∷ Γ ⟧
ctx-ext ρ≈ aTb here       = aTb
ctx-ext ρ≈ aTb (there ∈Γ) = ρ≈ ∈Γ

record ⟦_⟧_≈⟦_⟧_∈_ s ρ u ρ′ T : Set where
  field
    ⟦s⟧  : D
    ⟦t⟧  : D
    ↘⟦s⟧ : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ↘⟦t⟧ : ⟦ u ⟧ ρ′ ↘ ⟦t⟧
    sTt  : ⟦ T ⟧T ⟦s⟧ ⟦t⟧

module Intp {s ρ u ρ′ T} (r : ⟦ s ⟧ ρ ≈⟦ u ⟧ ρ′ ∈ T) = ⟦_⟧_≈⟦_⟧_∈_ r

record ⟦_⟧_≈⟦_⟧_∈s_ σ ρ τ ρ′ Γ : Set where
  field
    ⟦σ⟧  : Env
    ⟦τ⟧  : Env
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦τ⟧ : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    σΓτ  : ⟦σ⟧ ≈ ⟦τ⟧ ∈⟦ Γ ⟧

module Intps {σ ρ τ ρ′ Γ} (r : ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Γ) = ⟦_⟧_≈⟦_⟧_∈s_ r

infix 4 _⊨_≈_∶_ _⊨_∶_  _⊨s_≈_∶_ _⊨s_∶_
_⊨_≈_∶_ : Ctx → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = ∀ {ρ ρ′} → ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ t ⟧ ρ ≈⟦ t′ ⟧ ρ′ ∈ T

_⊨_∶_ : Ctx → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨s σ ≈ τ ∶ Δ = ∀ {ρ ρ′} → ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Δ

_⊨s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊨s σ ∶ Δ = Γ ⊨s σ ≈ σ ∶ Δ

infix 4 rec_,_,_≈rec_,_,_∈_
record rec_,_,_≈rec_,_,_∈_ a′ a″ a b′ b″ b T : Set where
  field
    ra    : D
    rb    : D
    ↘ra   : rec T , a′ , a″ , a ↘ ra
    ↘rb   : rec T , b′ , b″ , b ↘ rb
    raTrb : ⟦ T ⟧T ra rb

≈⟦⟧-sym : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
          ----------------
          ρ′ ≈ ρ ∈⟦ Γ ⟧
≈⟦⟧-sym ρ≈ {_} {T} T∈Γ = ⟦⟧-sym T (ρ≈ T∈Γ)

≈⟦⟧-refl : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
           ----------------
           ρ ≈ ρ ∈⟦ Γ ⟧
≈⟦⟧-refl ρ≈ {_} {T} T∈Γ = ⟦⟧≈refl T (ρ≈ T∈Γ)

≈-refl : Γ ⊨ t ∶ T →
         --------------
         Γ ⊨ t ≈ t ∶ T
≈-refl t = t

≈-sym : Γ ⊨ t ≈ t′ ∶ T →
        -------------------
        Γ ⊨ t′ ≈ t ∶ T
≈-sym {T = T} t≈ ρ≈ = record
  { ⟦s⟧  = ⟦t⟧
  ; ⟦t⟧  = ⟦s⟧
  ; ↘⟦s⟧ = ↘⟦t⟧
  ; ↘⟦t⟧ = ↘⟦s⟧
  ; sTt  = ⟦⟧-sym T sTt
  }
  where open Intp (t≈ (≈⟦⟧-sym ρ≈))

≈-trans : Γ ⊨ t ≈ t′ ∶ T →
          Γ ⊨ t′ ≈ t″ ∶ T →
          -------------------
          Γ ⊨ t ≈ t″ ∶ T
≈-trans {T = T} t≈ t′≈ ρ≈ = record
  { ⟦s⟧  = t≈′.⟦s⟧
  ; ⟦t⟧  = t≈″.⟦t⟧
  ; ↘⟦s⟧ = t≈′.↘⟦s⟧
  ; ↘⟦t⟧ = t≈″.↘⟦t⟧
  ; sTt  = ⟦⟧-trans T
                    t≈′.sTt
                    (subst (λ a → ⟦ T ⟧T a _) (⟦⟧-det t≈″.↘⟦s⟧ t≈′.↘⟦t⟧) t≈″.sTt)
  }
  where t≈′ = t≈ (≈⟦⟧-refl ρ≈)
        t≈″ = t′≈ ρ≈
        module t≈′ = Intp t≈′
        module t≈″ = Intp t≈″

≈⇒⊨ : Γ ⊨ t ≈ t′ ∶ T →
      ------------------
      Γ ⊨ t ∶ T
≈⇒⊨ t≈ = ≈-trans t≈ (≈-sym t≈)

v-≈ : ∀ {x} →
      x ∶ T ∈ Γ →
      ---------------
      Γ ⊨ v x ≈ v x ∶ T
v-≈ T∈Γ ρ≈ = record
  { ⟦s⟧  = _
  ; ⟦t⟧  = _
  ; ↘⟦s⟧ = ⟦v⟧ _
  ; ↘⟦t⟧ = ⟦v⟧ _
  ; sTt  = ρ≈ T∈Γ
  }

ze-≈′ : Γ ⊨ ze ≈ ze ∶ N
ze-≈′ ρ≈ = record
  { ⟦s⟧ = ze
  ; ⟦t⟧ = ze
  ; ↘⟦s⟧ = ⟦ze⟧
  ; ↘⟦t⟧ = ⟦ze⟧
  ; sTt = ze-≈
  }

su-cong : Γ ⊨ t ≈ t′ ∶ N →
          ---------------------
          Γ ⊨ su t ≈ su t′ ∶ N
su-cong t≈ ρ≈ = record
  { ⟦s⟧  = su ⟦s⟧
  ; ⟦t⟧  = su ⟦t⟧
  ; ↘⟦s⟧ = ⟦su⟧ ↘⟦s⟧
  ; ↘⟦t⟧ = ⟦su⟧ ↘⟦t⟧
  ; sTt  = su-≈ sTt
  }
  where open Intp (t≈ ρ≈)

Λ-cong : S ∷ Γ ⊨ t ≈ t′ ∶ T →
         ----------------------
         Γ ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
Λ-cong {S} {Γ} {t} {t′} {T} t≈ {ρ} {ρ′} ρ≈ = record
  { ⟦s⟧  = Λ _ _
  ; ⟦t⟧  = Λ _ _
  ; ↘⟦s⟧ = ⟦Λ⟧ _
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; sTt  = helper
  }
  where helper : (⟦ S ⟧T ⇒ ⟦ T ⟧T) (Λ t ρ) (Λ t′ ρ′)
        helper aSa′ = ⟦s⟧
                    - ⟦t⟧
                    - Λ∙ ↘⟦s⟧
                    - Λ∙ ↘⟦t⟧
                    - sTt
          where open Intp (t≈ (ctx-ext ρ≈ aSa′))

$-cong : Γ ⊨ r ≈ r′ ∶ S ⟶ T →
         Γ ⊨ s ≈ s′ ∶ S →
         ------------------------
         Γ ⊨ r $ s ≈ r′ $ s′ ∶ T
$-cong r≈ s≈ ρ≈ = record
  { ⟦s⟧  = rs.fa
  ; ⟦t⟧  = rs.fa′
  ; ↘⟦s⟧ = ⟦$⟧ r.↘⟦s⟧ s.↘⟦s⟧ rs.↘fa
  ; ↘⟦t⟧ = ⟦$⟧ r.↘⟦t⟧ s.↘⟦t⟧ rs.↘fa′
  ; sTt  = rs.faTfa′
  }
  where module r = Intp (r≈ ρ≈)
        module s = Intp (s≈ ρ≈)
        rs = r.sTt s.sTt
        module rs = FAppIn rs

[]-cong  : Γ ⊨s σ ≈ σ′ ∶ Δ →
           Δ ⊨ t ≈ t′ ∶ T →
           -----------------------------
           Γ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶ T
[]-cong σ≈ t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦t⟧  = ⟦t⟧
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦s⟧
  ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
  ; sTt  = sTt
  }
  where open Intps (σ≈ ρ≈)
        open Intp (t≈ σΓτ)

ze-[] : Γ ⊨s σ ∶ Δ →
        ------------------------
        Γ ⊨ ze [ σ ] ≈ ze ∶ N
ze-[] σ ρ≈ = record
  { ⟦s⟧  = ze
  ; ⟦t⟧  = ze
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ ⟦ze⟧
  ; ↘⟦t⟧ = ⟦ze⟧
  ; sTt  = ze-≈
  }
  where open Intps (σ ρ≈)

su-[] : Γ ⊨s σ ∶ Δ →
        Δ ⊨ t ∶ N →
        ------------------------
        Γ ⊨ su t [ σ ] ≈ su (t [ σ ]) ∶ N
su-[] σ t ρ≈ = record
  { ⟦s⟧  = su ⟦s⟧
  ; ⟦t⟧  = su ⟦t⟧
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦su⟧ ↘⟦s⟧)
  ; ↘⟦t⟧ = ⟦su⟧ (⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧)
  ; sTt  = su-≈ sTt
  }
  where open Intps (σ ρ≈)
        open Intp (t σΓτ)

Λ-[] : Γ ⊨s σ ∶ Δ →
       S ∷ Δ ⊨ t ∶ T →
       --------------------------------------------
       Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ S ⟶ T
Λ-[] σ t ρ≈ = record
  { ⟦s⟧  = Λ _ ⟦σ⟧
  ; ⟦t⟧  = Λ (_ [ q _ ]) _
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦Λ⟧ _)
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; sTt  = λ aSa′ →
    let open Intp (t (ctx-ext σΓτ aSa′))
    in ⟦s⟧
     - ⟦t⟧
     - Λ∙ ↘⟦s⟧
     - Λ∙ (⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦↑⟧ ↘⟦τ⟧) (⟦v⟧ 0)) ↘⟦t⟧)
     - sTt
  }
  where open Intps (σ ρ≈)

$-[] : Γ ⊨s σ ∶ Δ →
       Δ ⊨ r ∶ S ⟶ T →
       Δ ⊨ s ∶ S →
       ------------------------------------------------
       Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T
$-[] σ r s ρ≈ = record
  { ⟦s⟧  = fa
  ; ⟦t⟧  = fa′
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦$⟧ r.↘⟦s⟧ s.↘⟦s⟧ ↘fa)
  ; ↘⟦t⟧ = ⟦$⟧ (⟦[]⟧ ↘⟦τ⟧ r.↘⟦t⟧) (⟦[]⟧ ↘⟦τ⟧ s.↘⟦t⟧) ↘fa′
  ; sTt  = faTfa′
  }
  where open Intps (σ ρ≈)
        module r = Intp (r σΓτ)
        module s = Intp (s σΓτ)
        open FAppIn (r.sTt s.sTt)

↑-vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ----------------------------------
              S ∷ Γ ⊨ v x [ ↑ ] ≈ v (suc x) ∶ T
↑-vlookup {x = x} T∈Γ {ρ} {ρ′} ρ≈ = record
  { ⟦s⟧  = ρ (suc x)
  ; ⟦t⟧  = ρ′ (suc x)
  ; ↘⟦s⟧ = ⟦[]⟧ ⟦↑⟧ (⟦v⟧ x)
  ; ↘⟦t⟧ = ⟦v⟧ (suc x)
  ; sTt  = ρ≈ (there T∈Γ)
  }

[I] : Γ ⊨ t ∶ T →
      -------------------
      Γ ⊨ t [ I ] ≈ t ∶ T
[I] t∶T ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦t⟧  = ⟦t⟧
  ; ↘⟦s⟧ = ⟦[]⟧ ⟦I⟧ ↘⟦s⟧
  ; ↘⟦t⟧ = ↘⟦t⟧
  ; sTt  = sTt
  }
  where open Intp (t∶T ρ≈)

[∘] : Γ ⊨s τ ∶ Γ′ →
      Γ′ ⊨s σ ∶ Γ″ →
      Γ″ ⊨ t ∶ T →
      -------------------------------------------
      Γ ⊨ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T
[∘] τ≈ σ≈ t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦t⟧  = ⟦t⟧
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦∘⟧ τ≈.↘⟦σ⟧ σ≈.↘⟦σ⟧) ↘⟦s⟧
  ; ↘⟦t⟧ = ⟦[]⟧ τ≈.↘⟦τ⟧ (⟦[]⟧ σ≈.↘⟦τ⟧ ↘⟦t⟧)
  ; sTt  = sTt
  }
  where module τ≈ = Intps (τ≈ ρ≈)
        module σ≈ = Intps (σ≈ τ≈.σΓτ)
        open Intp (t≈ σ≈.σΓτ)

[,]-v0 : Γ ⊨s σ ∶ Δ →
         Γ ⊨ s ∶ S →
         -------------------------
         Γ ⊨ v 0 [ σ , s ] ≈ s ∶ S
[,]-v0 σ≈ s≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦t⟧  = ⟦t⟧
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) (⟦v⟧ 0)
  ; ↘⟦t⟧ = ↘⟦t⟧
  ; sTt  = sTt
  }
  where open Intps (σ≈ ρ≈)
        open Intp (s≈ ρ≈)

[,]-v-suc : ∀ {x} →
              Γ ⊨s σ ∶ Δ →
              Γ ⊨ s ∶ S →
              x ∶ T ∈ Δ →
              ----------------------------------------
              Γ ⊨ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T
[,]-v-suc {x = x} σ≈ s≈ T∈Δ ρ≈ = record
  { ⟦s⟧  = ⟦σ⟧ x
  ; ⟦t⟧  = ⟦τ⟧ x
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) (⟦v⟧ (suc x))
  ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ (⟦v⟧ x)
  ; sTt  = σΓτ T∈Δ
  }
  where open Intps (σ≈ ρ≈)
        open Intp (s≈ ρ≈)

↑-lookup : ∀ {x} →
           x ∶ T ∈ Γ →
           ----------------------------------
           S ∷ Γ ⊨ v x [ ↑ ] ≈ v (suc x) ∶ T
↑-lookup T∈Γ ρ≈ = record
  { ⟦s⟧  = _
  ; ⟦t⟧  = _
  ; ↘⟦s⟧ = ⟦[]⟧ ⟦↑⟧ (⟦v⟧ _)
  ; ↘⟦t⟧ = ⟦v⟧ (suc _)
  ; sTt  = ρ≈ (there T∈Γ)
  }

Λ-β : S ∷ Γ ⊨ t ∶ T →
      Γ ⊨ s ∶ S →
      ------------------------------
      Γ ⊨ Λ t $ s ≈ t [ I , s ] ∶ T
Λ-β t≈ s≈ ρ≈ = record
  { ⟦s⟧  = t≈.⟦s⟧
  ; ⟦t⟧  = t≈.⟦t⟧
  ; ↘⟦s⟧ = ⟦$⟧ (⟦Λ⟧ _) s≈.↘⟦s⟧ (Λ∙ t≈.↘⟦s⟧)
  ; ↘⟦t⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ s≈.↘⟦t⟧) t≈.↘⟦t⟧
  ; sTt  = t≈.sTt
  }
  where module s≈ = Intp (s≈ ρ≈)
        module t≈ = Intp (t≈ (ctx-ext ρ≈ s≈.sTt))

Λ-η : Γ ⊨ t ∶ S ⟶ T →
      ----------------------------------
      Γ ⊨ t ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T
Λ-η t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦t⟧  = Λ (_ $ v 0) _
  ; ↘⟦s⟧ = ↘⟦s⟧
  ; ↘⟦t⟧ = ⟦Λ⟧ _
  ; sTt  = λ aSa′ → let open FAppIn (sTt aSa′)
                    in fa
                    - fa′
                    - ↘fa
                    - Λ∙ (⟦$⟧ (⟦[]⟧ ⟦↑⟧ ↘⟦t⟧) (⟦v⟧ 0) ↘fa′)
                    - faTfa′
  }
  where open Intp (t≈ ρ≈)

rec-helper : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
                  (s≈ : ⟦ s ⟧ ρ ≈⟦ s′ ⟧ ρ′ ∈ T) →
                  (r≈ : ⟦ r ⟧ ρ ≈⟦ r′ ⟧ ρ′ ∈ N ⟶ T ⟶ T) →
                  a ≈ b ∈N →
                  rec Intp.⟦s⟧ s≈ , Intp.⟦s⟧ r≈ , a ≈rec Intp.⟦t⟧ s≈ , Intp.⟦t⟧ r≈ , b ∈ T
rec-helper ρ≈ s≈ r≈ ze-≈             = record
  { ra    = ⟦s⟧
  ; rb    = ⟦t⟧
  ; ↘ra   = rze
  ; ↘rb   = rze
  ; raTrb = sTt
  }
  where open Intp s≈
rec-helper ρ≈ s≈ r≈ (su-≈ a≈b)       = record
  { ra    = r″≈.fa
  ; rb    = r″≈.fa′
  ; ↘ra   = rsu ↘ra r′≈.↘fa r″≈.↘fa
  ; ↘rb   = rsu ↘rb r′≈.↘fa′ r″≈.↘fa′
  ; raTrb = r″≈.faTfa′
  }
  where open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ s≈ r≈ a≈b)
        module r≈  = Intp r≈
        r′≈        = r≈.sTt a≈b
        module r′≈ = FAppIn r′≈
        r″≈        = r′≈.faTfa′ raTrb
        module r″≈ = FAppIn r″≈
rec-helper {T = T} ρ≈ s≈ r≈ (↑N e⊥e′) = record
  { ra    = _
  ; rb    = _
  ; ↘ra   = rec
  ; ↘rb   = rec
  ; raTrb = Bot⇒⟦⟧ T λ n → let w  , ↘w  , ↘w′ = ⟦⟧⇒Top T s≈.sTt n
                               w′ , ↘w″ , ↘w‴ = ⟦⟧⇒Top (N ⟶ T ⟶ T) r≈.sTt n
                               u  , ↘u  , ↘u′ = e⊥e′ n
                           in rec T w w′ u
                            , Rr n ↘w ↘w″ ↘u
                            , Rr n ↘w′ ↘w‴ ↘u′
  }
  where module s≈ = Intp s≈
        module r≈ = Intp r≈

rec-cong : Γ ⊨ s ≈ s′ ∶ T →
           Γ ⊨ r ≈ r′ ∶ N ⟶ T ⟶ T →
           Γ ⊨ t ≈ t′ ∶ N →
           --------------------------------------
           Γ ⊨ rec T s r t ≈ rec T s′ r′ t′ ∶ T
rec-cong s≈ r≈ t≈ ρ≈ = record
  { ⟦s⟧  = ra
  ; ⟦t⟧  = rb
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ t≈.↘⟦s⟧ ↘ra
  ; ↘⟦t⟧ = ⟦rec⟧ s≈.↘⟦t⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ ↘rb
  ; sTt  = raTrb
  }
  where sρ≈ = s≈ ρ≈
        rρ≈ = r≈ ρ≈
        tρ≈ = t≈ ρ≈
        module s≈ = Intp sρ≈
        module r≈ = Intp rρ≈
        module t≈ = Intp tρ≈
        open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ sρ≈ rρ≈ t≈.sTt)

rec-β-ze : Γ ⊨ s ∶ T →
           Γ ⊨ r ∶ N ⟶ T ⟶ T →
           -------------------------
           Γ ⊨ rec T s r ze ≈ s ∶ T
rec-β-ze s≈ r≈ ρ≈ = record
  { ⟦s⟧  = s≈.⟦s⟧
  ; ⟦t⟧  = s≈.⟦t⟧
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ ⟦ze⟧ rze
  ; ↘⟦t⟧ = s≈.↘⟦t⟧
  ; sTt  = s≈.sTt
  }
  where module s≈ = Intp (s≈ ρ≈)
        module r≈ = Intp (r≈ ρ≈)

rec-β-su : Γ ⊨ s ∶ T →
           Γ ⊨ r ∶ N ⟶ T ⟶ T →
           Γ ⊨ t ∶ N →
           -----------------------------------------------------
           Γ ⊨ rec T s r (su t) ≈ r $ t $ (rec T s r t) ∶ T
rec-β-su s≈ r≈ t≈ ρ≈ = record
  { ⟦s⟧  = r″≈.fa
  ; ⟦t⟧  = r″≈.fa′
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ (⟦su⟧ t≈.↘⟦s⟧) (rsu ↘ra r′≈.↘fa r″≈.↘fa)
  ; ↘⟦t⟧ = ⟦$⟧ (⟦$⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ r′≈.↘fa′) (⟦rec⟧ s≈.↘⟦t⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ ↘rb) r″≈.↘fa′
  ; sTt  = r″≈.faTfa′
  }
  where module s≈  = Intp (s≈ ρ≈)
        module r≈  = Intp (r≈ ρ≈)
        module t≈  = Intp (t≈ ρ≈)
        open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ (s≈ ρ≈) (r≈ ρ≈) t≈.sTt)
        module r′≈ = FAppIn (r≈.sTt t≈.sTt)
        module r″≈ = FAppIn (r′≈.faTfa′ raTrb)

rec-[] : Γ ⊨s σ ∶ Δ →
         Δ ⊨ s ∶ T →
         Δ ⊨ r ∶ N ⟶ T ⟶ T →
         Δ ⊨ t ∶ N →
         -----------------------------------------------------------------
         Γ ⊨ rec T s r t [ σ ] ≈ rec T (s [ σ ]) (r [ σ ]) (t [ σ ]) ∶ T
rec-[] σ s r t ρ≈ = record
  { ⟦s⟧  = ra
  ; ⟦t⟧  = rb
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦rec⟧ s.↘⟦s⟧ r.↘⟦s⟧ t.↘⟦s⟧ ↘ra)
  ; ↘⟦t⟧ = ⟦rec⟧ (⟦[]⟧ ↘⟦τ⟧ s.↘⟦t⟧) (⟦[]⟧ ↘⟦τ⟧ r.↘⟦t⟧) (⟦[]⟧ ↘⟦τ⟧ t.↘⟦t⟧) ↘rb
  ; sTt  = raTrb
  }
  where open Intps (σ ρ≈)
        module s = Intp (s σΓτ)
        module r = Intp (r σΓτ)
        module t = Intp (t σΓτ)
        open rec_,_,_≈rec_,_,_∈_ (rec-helper σΓτ (s σΓτ) (r σΓτ) t.sTt)

s-≈-refl : Γ ⊨s σ ∶ Γ →
           ----------------
           Γ ⊨s σ ≈ σ ∶ Γ
s-≈-refl σ = σ

s-≈-sym : Γ ⊨s σ ≈ σ′ ∶ Δ →
          ------------------
          Γ ⊨s σ′ ≈ σ ∶ Δ
s-≈-sym σ≈ ρ≈ = record
  { ⟦σ⟧  = ⟦τ⟧
  ; ⟦τ⟧  = ⟦σ⟧
  ; ↘⟦σ⟧ = ↘⟦τ⟧
  ; ↘⟦τ⟧ = ↘⟦σ⟧
  ; σΓτ  = ≈⟦⟧-sym σΓτ
  }
  where open Intps (σ≈ (≈⟦⟧-sym ρ≈))

s-≈-trans : Γ ⊨s σ ≈ σ′ ∶ Δ →
            Γ ⊨s σ′ ≈ σ″ ∶ Δ →
            -------------------
            Γ ⊨s σ ≈ σ″ ∶ Δ
s-≈-trans σ≈ σ′≈ ρ≈ = record
  { ⟦σ⟧  = σ≈.⟦σ⟧
  ; ⟦τ⟧  = σ′≈.⟦τ⟧
  ; ↘⟦σ⟧ = σ≈.↘⟦σ⟧
  ; ↘⟦τ⟧ = σ′≈.↘⟦τ⟧
  ; σΓτ  = λ {_} {T} T∈Γ → ⟦⟧-trans T
                                    (σ≈.σΓτ T∈Γ)
                                    (subst (λ f → ⟦ T ⟧T (f _) _) (⟦⟧s-det σ′≈.↘⟦σ⟧ σ≈.↘⟦τ⟧) (σ′≈.σΓτ T∈Γ))
  }
  where module σ≈  = Intps (σ≈ (≈⟦⟧-refl ρ≈))
        module σ′≈ = Intps (σ′≈ ρ≈)

∘-cong : Γ ⊨s τ ≈ τ′ ∶ Γ′ →
         Γ′ ⊨s σ ≈ σ′ ∶ Γ″ →
         --------------------------
         Γ ⊨s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
∘-cong τ≈ σ≈ ρ≈ = record
  { ⟦σ⟧  = σ≈.⟦σ⟧
  ; ⟦τ⟧  = σ≈.⟦τ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ τ≈.↘⟦σ⟧ σ≈.↘⟦σ⟧
  ; ↘⟦τ⟧ = ⟦∘⟧ τ≈.↘⟦τ⟧ σ≈.↘⟦τ⟧
  ; σΓτ  = σ≈.σΓτ
  }
  where module τ≈ = Intps (τ≈ ρ≈)
        module σ≈ = Intps (σ≈ τ≈.σΓτ)

↑-≈ : S ∷ Γ ⊨s ↑ ≈ ↑ ∶ Γ
↑-≈ {ρ = ρ} {ρ′} ρ≈ = record
  { ⟦σ⟧  = drop ρ
  ; ⟦τ⟧  = drop ρ′
  ; ↘⟦σ⟧ = ⟦↑⟧
  ; ↘⟦τ⟧ = ⟦↑⟧
  ; σΓτ  = λ T∈Γ → ρ≈ (there T∈Γ)
  }

I-≈ : Γ ⊨s I ≈ I ∶ Γ
I-≈ ρ≈ = record
  { ⟦σ⟧  = _
  ; ⟦τ⟧  = _
  ; ↘⟦σ⟧ = ⟦I⟧
  ; ↘⟦τ⟧ = ⟦I⟧
  ; σΓτ  = ρ≈
  }

,-cong : Γ ⊨s σ ≈ σ′ ∶ Δ →
         Γ ⊨ s ≈ s′ ∶ S →
         -----------------------------
         Γ ⊨s σ , s ≈ σ′ , s′ ∶ S ∷ Δ
,-cong σ≈ s≈ ρ≈ = record
  { ⟦σ⟧  = σ≈.⟦σ⟧ ↦ s≈.⟦s⟧
  ; ⟦τ⟧  = σ≈.⟦τ⟧ ↦ s≈.⟦t⟧
  ; ↘⟦σ⟧ = ⟦,⟧ σ≈.↘⟦σ⟧ s≈.↘⟦s⟧
  ; ↘⟦τ⟧ = ⟦,⟧ σ≈.↘⟦τ⟧ s≈.↘⟦t⟧
  ; σΓτ  = helper
  }
  where module σ≈ = Intps (σ≈ ρ≈)
        module s≈ = Intp (s≈ ρ≈)
        helper : σ≈.⟦σ⟧ ↦ s≈.⟦s⟧ ≈ σ≈.⟦τ⟧ ↦ s≈.⟦t⟧ ∈⟦ _ ∷ _ ⟧
        helper here        = s≈.sTt
        helper (there T∈Δ) = σ≈.σΓτ T∈Δ

↑-∘-, : Γ ⊨s σ ∶ Δ →
        Γ ⊨ s ∶ S →
        --------------------------
        Γ ⊨s ↑ ∘ (σ , s) ≈ σ ∶ Δ
↑-∘-, σ s ρ≈ = record
  { ⟦σ⟧  = ⟦σ⟧
  ; ⟦τ⟧  = ⟦τ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) ⟦↑⟧
  ; ↘⟦τ⟧ = ↘⟦τ⟧
  ; σΓτ  = σΓτ
  }
  where open Intps (σ ρ≈)
        open Intp (s ρ≈)

I-∘ : Γ ⊨s σ ∶ Δ →
      --------------------
      Γ ⊨s I ∘ σ ≈ σ ∶ Δ
I-∘ σ ρ≈ = record
  { ⟦σ⟧  = ⟦σ⟧
  ; ⟦τ⟧  = ⟦τ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ ⟦I⟧
  ; ↘⟦τ⟧ = ↘⟦τ⟧
  ; σΓτ  = σΓτ
  }
  where open Intps (σ ρ≈)

∘-I : Γ ⊨s σ ∶ Δ →
      --------------------
      Γ ⊨s σ ∘ I ≈ σ ∶ Δ
∘-I σ ρ≈ = record
  { ⟦σ⟧  = ⟦σ⟧
  ; ⟦τ⟧  = ⟦τ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ ⟦I⟧ ↘⟦σ⟧
  ; ↘⟦τ⟧ = ↘⟦τ⟧
  ; σΓτ  = σΓτ
  }
  where open Intps (σ ρ≈)

∘-assoc : ∀ {Γ‴} →
          Γ′ ⊨s σ ∶ Γ →
          Γ″ ⊨s σ′ ∶ Γ′ →
          Γ‴ ⊨s σ″ ∶ Γ″ →
          ---------------------------------------
          Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
∘-assoc σ σ′ σ″ ρ≈ = record
  { ⟦σ⟧  = σ.⟦σ⟧
  ; ⟦τ⟧  = σ.⟦τ⟧
  ; ↘⟦σ⟧ = ⟦∘⟧ σ″.↘⟦σ⟧ (⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧)
  ; ↘⟦τ⟧ = ⟦∘⟧ (⟦∘⟧ σ″.↘⟦τ⟧ σ′.↘⟦τ⟧) σ.↘⟦τ⟧
  ; σΓτ  = σ.σΓτ
  }
  where module σ″ = Intps (σ″ ρ≈)
        module σ′ = Intps (σ′ σ″.σΓτ)
        module σ  = Intps (σ σ′.σΓτ)

I-ext : S ∷ Γ ⊨s I ≈ ↑ , v 0 ∶ S ∷ Γ
I-ext ρ≈ = record
  { ⟦σ⟧  = _
  ; ⟦τ⟧  = _
  ; ↘⟦σ⟧ = ⟦I⟧
  ; ↘⟦τ⟧ = ⟦,⟧ ⟦↑⟧ (⟦v⟧ 0)
  ; σΓτ  = helper ρ≈
  }
  where helper : ρ ≈ ρ′ ∈⟦ S ∷ Γ ⟧ → ρ ≈ drop ρ′ ↦ ρ′ 0 ∈⟦ S ∷ Γ ⟧
        helper ρ≈ here        = ρ≈ here
        helper ρ≈ (there T∈Γ) = ρ≈ (there T∈Γ)

,-ext : Γ ⊨s σ ∶ S ∷ Δ →
        --------------------------------------
        Γ ⊨s σ ≈ (↑ ∘ σ) , v 0 [ σ ] ∶ S ∷ Δ
,-ext σ ρ≈ = record
  { ⟦σ⟧  = ⟦σ⟧
  ; ⟦τ⟧  = drop ⟦τ⟧ ↦ ⟦τ⟧ 0
  ; ↘⟦σ⟧ = ↘⟦σ⟧
  ; ↘⟦τ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦τ⟧ ⟦↑⟧) (⟦[]⟧ ↘⟦τ⟧ (⟦v⟧ 0))
  ; σΓτ  = helper σΓτ
  }
  where open Intps (σ ρ≈)
        helper : ρ ≈ ρ′ ∈⟦ S ∷ Γ ⟧ → ρ ≈ drop ρ′ ↦ ρ′ 0 ∈⟦ S ∷ Γ ⟧
        helper ρ≈ here        = ρ≈ here
        helper ρ≈ (there T∈Γ) = ρ≈ (there T∈Γ)

Initial-refl : ∀ Γ → InitialEnv Γ ≈ InitialEnv Γ ∈⟦ Γ ⟧
Initial-refl (T ∷ Γ)  here        = Bot⇒⟦⟧ T (l∈Bot (L.length Γ))
Initial-refl .(_ ∷ _) (there T∈Γ) = Initial-refl _ T∈Γ

module Completeness where

  record Completeness′ n s ρ t ρ′ T : Set where
    field
      nf  : Nf
      nbs : Nbe n ρ s T nf
      nbt : Nbe n ρ′ t T nf

  Completeness : ℕ → Env → Exp → Exp → Typ → Set
  Completeness n ρ s t T = Completeness′ n s ρ t ρ T

  ⊨-conseq : Γ ⊨ s ≈ t ∶ T → ∀ n → ρ ≈ ρ′ ∈⟦ Γ ⟧ → Completeness′ n s ρ t ρ′ T
  ⊨-conseq {T = T} s≈ n ρ≈ =
    let (w , ↘w , ↘w′) = TTop T sTt n in
    record
    { nf  = w
    ; nbs = record
      { ⟦t⟧  = ⟦s⟧
      ; ↘⟦t⟧ = ↘⟦s⟧
      ; ↓⟦t⟧ = ↘w
      }
    ; nbt = record
      { ⟦t⟧  = ⟦t⟧
      ; ↘⟦t⟧ = ↘⟦t⟧
      ; ↓⟦t⟧ = ↘w′
      }
    }
    where open Intp (s≈ ρ≈)
          TTop : ∀ T → ⟦ T ⟧T a b → Top (↓ T a) (↓ T b)
          TTop T aTb = ⟦⟧⇒Top T aTb

  module T = Typing

  mutual
    sem-sound : Γ T.⊢ t ∶ T → Γ ⊨ t ∶ T
    sem-sound (T.vlookup T∈Γ) = v-≈ T∈Γ
    sem-sound T.ze-I          = ze-≈′
    sem-sound (T.su-I t)      = su-cong (sem-sound t)
    sem-sound (T.N-E s r t)   = rec-cong (sem-sound s) (sem-sound r) (sem-sound t)
    sem-sound (T.Λ-I t)       = Λ-cong (sem-sound t)
    sem-sound (T.Λ-E t s)     = $-cong (sem-sound t) (sem-sound s)
    sem-sound (T.t[σ] t σ)    = []-cong (sem-s-sound σ) (sem-sound t)

    sem-s-sound : Γ T.⊢s σ ∶ Δ → Γ ⊨s σ ∶ Δ
    sem-s-sound T.S-↑       = ↑-≈
    sem-s-sound T.S-I       = I-≈
    sem-s-sound (T.S-∘ σ δ) = ∘-cong (sem-s-sound σ) (sem-s-sound δ)
    sem-s-sound (T.S-, σ t) = ,-cong (sem-s-sound σ) (sem-sound t)

  completeness₀ : Γ T.⊢ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) t t T
  completeness₀ {Γ} t = ⊨-conseq (sem-sound t) (L.length Γ) (Initial-refl Γ)

  nbe-comp : Γ T.⊢ t ∶ T → ∃ λ w → Nbe (L.length Γ) (InitialEnv Γ) t T w
  nbe-comp t = nf , nbs
    where open Completeness′ (completeness₀ t)

  mutual
    ≈sem-sound : Γ T.⊢ s ≈ t ∶ T → Γ ⊨ s ≈ t ∶ T
    ≈sem-sound (T.v-≈ T∈Γ)                 = v-≈ T∈Γ
    ≈sem-sound T.ze-≈                      = ze-≈′
    ≈sem-sound (T.su-cong s≈t)             = su-cong (≈sem-sound s≈t)
    ≈sem-sound (T.rec-cong s≈s′ r≈r′ t≈t′) = rec-cong (≈sem-sound s≈s′) (≈sem-sound r≈r′) (≈sem-sound t≈t′)
    ≈sem-sound (T.Λ-cong s≈t)              = Λ-cong (≈sem-sound s≈t)
    ≈sem-sound (T.$-cong t≈t′ s≈s′)        = $-cong (≈sem-sound t≈t′) (≈sem-sound s≈s′)
    ≈sem-sound (T.[]-cong σ≈τ s≈t)         = []-cong (≈sem-s-sound σ≈τ) (≈sem-sound s≈t)
    ≈sem-sound (T.ze-[] σ)                 = ze-[] (sem-s-sound σ)
    ≈sem-sound (T.su-[] σ t)               = su-[] (sem-s-sound σ) (sem-sound t)
    ≈sem-sound (T.Λ-[] σ t)                = Λ-[] (sem-s-sound σ) (sem-sound t)
    ≈sem-sound (T.$-[] σ r s)              = $-[] (sem-s-sound σ) (sem-sound r) (sem-sound s)
    ≈sem-sound (T.rec-[] σ s r t)          = rec-[] (sem-s-sound σ) (sem-sound s) (sem-sound r) (sem-sound t)
    ≈sem-sound (T.rec-β-ze s r)            = rec-β-ze (sem-sound s) (sem-sound r)
    ≈sem-sound (T.rec-β-su s r t)          = rec-β-su (sem-sound s) (sem-sound r) (sem-sound t)
    ≈sem-sound (T.Λ-β t s)                 = Λ-β (sem-sound t) (sem-sound s)
    ≈sem-sound (T.Λ-η t)                   = Λ-η (sem-sound t)
    ≈sem-sound (T.[I] t)                   = [I] (sem-sound t)
    ≈sem-sound (T.↑-lookup T∈Γ)            = ↑-lookup T∈Γ
    ≈sem-sound (T.[∘] τ σ t)               = [∘] (sem-s-sound τ) (sem-s-sound σ) (sem-sound t)
    ≈sem-sound (T.[,]-v-ze σ t)            = [,]-v0 (sem-s-sound σ) (sem-sound t)
    ≈sem-sound (T.[,]-v-su σ t T∈Γ)        = [,]-v-suc (sem-s-sound σ) (sem-sound t) T∈Γ
    ≈sem-sound (T.≈-sym s≈t)               = ≈-sym (≈sem-sound s≈t)
    ≈sem-sound (T.≈-trans s≈t t≈t′)        = ≈-trans (≈sem-sound s≈t) (≈sem-sound t≈t′)

    ≈sem-s-sound : Γ T.⊢s σ ≈ τ ∶ Δ → Γ ⊨s σ ≈ τ ∶ Δ
    ≈sem-s-sound T.↑-≈                  = ↑-≈
    ≈sem-s-sound T.I-≈                  = I-≈
    ≈sem-s-sound (T.∘-cong σ≈σ′ τ≈τ′)   = ∘-cong (≈sem-s-sound σ≈σ′) (≈sem-s-sound τ≈τ′)
    ≈sem-s-sound (T.,-cong σ≈τ s≈t)     = ,-cong (≈sem-s-sound σ≈τ) (≈sem-sound s≈t)
    ≈sem-s-sound (T.↑-∘-, σ s)          = ↑-∘-, (sem-s-sound σ) (sem-sound s)
    ≈sem-s-sound (T.I-∘ σ)              = I-∘ (sem-s-sound σ)
    ≈sem-s-sound (T.∘-I σ)              = ∘-I (sem-s-sound σ)
    ≈sem-s-sound (T.∘-assoc σ σ′ σ″)    = ∘-assoc (sem-s-sound σ) (sem-s-sound σ′) (sem-s-sound σ″)
    ≈sem-s-sound (T.,-ext σ)            = ,-ext (sem-s-sound σ)
    ≈sem-s-sound (T.S-≈-sym σ≈τ)        = s-≈-sym (≈sem-s-sound σ≈τ)
    ≈sem-s-sound (T.S-≈-trans σ≈τ σ≈τ₁) = s-≈-trans (≈sem-s-sound σ≈τ) (≈sem-s-sound σ≈τ₁)

  completeness : Γ T.⊢ s ≈ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) s t T
  completeness {Γ} s≈t = ⊨-conseq (≈sem-sound s≈t) (L.length Γ) (Initial-refl Γ)
