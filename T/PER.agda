{-# OPTIONS --without-K --safe #-}

module T.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)

open import Lib
open import T.Statics
open import T.TypedSem

Ty : Set₁
Ty = D → D → Set

Ev : Set₁
Ev = Ctx → Set

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

↓↑N∈Top : Bot e e′ → Top (↓ N (↑ N e)) (↓ N (↑ N e′))
↓↑N∈Top e⊥e′ n
  with e⊥e′ n
...  | w , ↘w , ↘w′ = ne w , Rne n ↘w , Rne n ↘w′

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

module FAppIn {f a f′ a′ T} (r : f ∙ a ≈ f′ ∙ a′ ∈ T)  = _∙_≈_∙_∈_ r

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
  ↑N   : Bot e e′ →
         -------------------
         ↑ N e ≈ ↑ N e′ ∈N

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
_≈_∈⟦_⟧ : Ctx → Ctx → Env → Set
ρ ≈ ρ′ ∈⟦ Δ ⟧ = ∀ {x T} → x ∶ T ∈ Δ → ⟦ T ⟧T (ρ x) (ρ′ x)

ctx-ext : ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ T ⟧T a b → ρ ↦ a ≈ ρ′ ↦ b ∈⟦ T ∷ Γ ⟧
ctx-ext ρ≈ aTb here       = aTb
ctx-ext ρ≈ aTb (there ∈Γ) = ρ≈ ∈Γ

record ⟦_⟧_≈⟦_⟧_∈_ s ρ u ρ′ T : Set where
  field
    ⟦s⟧  : D
    ⟦u⟧  : D
    ↘⟦s⟧ : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ↘⟦u⟧ : ⟦ u ⟧ ρ′ ↘ ⟦u⟧
    sTu  : ⟦ T ⟧T ⟦s⟧ ⟦u⟧

module Intp {s ρ u ρ′ T} (r : ⟦ s ⟧ ρ ≈⟦ u ⟧ ρ′ ∈ T) = ⟦_⟧_≈⟦_⟧_∈_ r

record ⟦_⟧_≈⟦_⟧_∈s_ σ ρ τ ρ′ Γ : Set where
  field
    ⟦σ⟧  : Ctx
    ⟦τ⟧  : Ctx
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦τ⟧ : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    σΓτ  : ⟦σ⟧ ≈ ⟦τ⟧ ∈⟦ Γ ⟧

module Intps {σ ρ τ ρ′ Γ} (r : ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Γ) = ⟦_⟧_≈⟦_⟧_∈s_ r

infix 4 _⊨_≈_∶_ _⊨_∶_  _⊨s_≈_∶_ _⊨s_∶_
_⊨_≈_∶_ : Env → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = ∀ {ρ ρ′} → ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ t ⟧ ρ ≈⟦ t′ ⟧ ρ′ ∈ T

_⊨_∶_ : Env → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Env → Subst → Subst → Env → Set
Γ ⊨s σ ≈ τ ∶ Δ = ∀ {ρ ρ′} → ρ ≈ ρ′ ∈⟦ Γ ⟧ → ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s Δ

_⊨s_∶_ : Env → Subst → Env → Set
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
  { ⟦s⟧  = ⟦u⟧
  ; ⟦u⟧  = ⟦s⟧
  ; ↘⟦s⟧ = ↘⟦u⟧
  ; ↘⟦u⟧ = ↘⟦s⟧
  ; sTu  = ⟦⟧-sym T sTu
  }
  where open Intp (t≈ (≈⟦⟧-sym ρ≈))

≈-trans : Γ ⊨ t ≈ t′ ∶ T →
          Γ ⊨ t′ ≈ t″ ∶ T →
          -------------------
          Γ ⊨ t ≈ t″ ∶ T
≈-trans {T = T} t≈ t′≈ ρ≈ = record
  { ⟦s⟧  = t≈′.⟦s⟧
  ; ⟦u⟧  = t≈″.⟦u⟧
  ; ↘⟦s⟧ = t≈′.↘⟦s⟧
  ; ↘⟦u⟧ = t≈″.↘⟦u⟧
  ; sTu  = ⟦⟧-trans T
                    t≈′.sTu
                    (subst (λ a → ⟦ T ⟧T a _) (⟦⟧-det t≈″.↘⟦s⟧ t≈′.↘⟦u⟧) t≈″.sTu)
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
  ; ⟦u⟧  = _
  ; ↘⟦s⟧ = ⟦v⟧ _
  ; ↘⟦u⟧ = ⟦v⟧ _
  ; sTu  = ρ≈ T∈Γ
  }

ze-≈′ : Γ ⊨ ze ≈ ze ∶ N
ze-≈′ ρ≈ = record
  { ⟦s⟧ = ze
  ; ⟦u⟧ = ze
  ; ↘⟦s⟧ = ⟦ze⟧
  ; ↘⟦u⟧ = ⟦ze⟧
  ; sTu = ze-≈
  }

su-cong : Γ ⊨ t ≈ t′ ∶ N →
          ---------------------
          Γ ⊨ su t ≈ su t′ ∶ N
su-cong t≈ ρ≈ = record
  { ⟦s⟧  = su ⟦s⟧
  ; ⟦u⟧  = su ⟦u⟧
  ; ↘⟦s⟧ = ⟦su⟧ ↘⟦s⟧
  ; ↘⟦u⟧ = ⟦su⟧ ↘⟦u⟧
  ; sTu  = su-≈ sTu
  }
  where open Intp (t≈ ρ≈)

Λ-cong : S ∷ Γ ⊨ t ≈ t′ ∶ T →
         ----------------------
         Γ ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
Λ-cong {S} {Γ} {t} {t′} {T} t≈ {ρ} {ρ′} ρ≈ = record
  { ⟦s⟧  = Λ _ _
  ; ⟦u⟧  = Λ _ _
  ; ↘⟦s⟧ = ⟦Λ⟧ _
  ; ↘⟦u⟧ = ⟦Λ⟧ _
  ; sTu  = helper
  }
  where helper : (⟦ S ⟧T ⇒ ⟦ T ⟧T) (Λ t ρ) (Λ t′ ρ′)
        helper aSa′ = ⟦s⟧
                    - ⟦u⟧
                    - Λ∙ ↘⟦s⟧
                    - Λ∙ ↘⟦u⟧
                    - sTu
          where open Intp (t≈ (ctx-ext ρ≈ aSa′))

$-cong : Γ ⊨ r ≈ r′ ∶ S ⟶ T →
         Γ ⊨ s ≈ s′ ∶ S →
         ------------------------
         Γ ⊨ r $ s ≈ r′ $ s′ ∶ T
$-cong r≈ s≈ ρ≈ = record
  { ⟦s⟧  = rs.fa
  ; ⟦u⟧  = rs.fa′
  ; ↘⟦s⟧ = ⟦$⟧ r.↘⟦s⟧ s.↘⟦s⟧ rs.↘fa
  ; ↘⟦u⟧ = ⟦$⟧ r.↘⟦u⟧ s.↘⟦u⟧ rs.↘fa′
  ; sTu  = rs.faTfa′
  }
  where module r = Intp (r≈ ρ≈)
        module s = Intp (s≈ ρ≈)
        rs = r.sTu s.sTu
        module rs = FAppIn rs

[]-cong  : Γ ⊨s σ ≈ σ′ ∶ Δ →
           Δ ⊨ t ≈ t′ ∶ T →
           -----------------------------
           Γ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶ T
[]-cong σ≈ t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦u⟧  = ⟦u⟧
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦s⟧
  ; ↘⟦u⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦u⟧
  ; sTu  = sTu
  }
  where open Intps (σ≈ ρ≈)
        open Intp (t≈ σΓτ)

↑-vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ----------------------------------
              S ∷ Γ ⊨ v x [ ↑ ] ≈ v (suc x) ∶ T
↑-vlookup {x = x} T∈Γ {ρ} {ρ′} ρ≈ = record
  { ⟦s⟧  = ρ (suc x)
  ; ⟦u⟧  = ρ′ (suc x)
  ; ↘⟦s⟧ = ⟦[]⟧ ⟦↑⟧ (⟦v⟧ x)
  ; ↘⟦u⟧ = ⟦v⟧ (suc x)
  ; sTu  = ρ≈ (there T∈Γ)
  }

[I] : Γ ⊨ t ∶ T →
      -------------------
      Γ ⊨ t [ I ] ≈ t ∶ T
[I] t∶T ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦u⟧  = ⟦u⟧
  ; ↘⟦s⟧ = ⟦[]⟧ ⟦I⟧ ↘⟦s⟧
  ; ↘⟦u⟧ = ↘⟦u⟧
  ; sTu  = sTu
  }
  where open Intp (t∶T ρ≈)

[∘] : Γ ⊨s τ ∶ Γ′ →
      Γ′ ⊨s σ ∶ Γ″ →
      Γ″ ⊨ t ∶ T →
      -------------------------------------------
      Γ ⊨ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶ T
[∘] τ≈ σ≈ t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦u⟧  = ⟦u⟧
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦∘⟧ τ≈.↘⟦σ⟧ σ≈.↘⟦σ⟧) ↘⟦s⟧
  ; ↘⟦u⟧ = ⟦[]⟧ τ≈.↘⟦τ⟧ (⟦[]⟧ σ≈.↘⟦τ⟧ ↘⟦u⟧)
  ; sTu  = sTu
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
  ; ⟦u⟧  = ⟦u⟧
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) (⟦v⟧ 0)
  ; ↘⟦u⟧ = ↘⟦u⟧
  ; sTu  = sTu
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
  ; ⟦u⟧  = ⟦τ⟧ x
  ; ↘⟦s⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) (⟦v⟧ (suc x))
  ; ↘⟦u⟧ = ⟦[]⟧ ↘⟦τ⟧ (⟦v⟧ x)
  ; sTu  = σΓτ T∈Δ
  }
  where open Intps (σ≈ ρ≈)
        open Intp (s≈ ρ≈)

Λ-β : S ∷ Γ ⊨ t ∶ T →
      Γ ⊨ s ∶ S →
      ------------------------------
      Γ ⊨ Λ t $ s ≈ t [ I , s ] ∶ T
Λ-β t≈ s≈ ρ≈ = record
  { ⟦s⟧  = t≈.⟦s⟧
  ; ⟦u⟧  = t≈.⟦u⟧
  ; ↘⟦s⟧ = ⟦$⟧ (⟦Λ⟧ _) s≈.↘⟦s⟧ (Λ∙ t≈.↘⟦s⟧)
  ; ↘⟦u⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ s≈.↘⟦u⟧) t≈.↘⟦u⟧
  ; sTu  = t≈.sTu
  }
  where module s≈ = Intp (s≈ ρ≈)
        module t≈ = Intp (t≈ (ctx-ext ρ≈ s≈.sTu))

Λ-η : Γ ⊨ t ∶ S ⟶ T →
      ----------------------------------
      Γ ⊨ t ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T
Λ-η t≈ ρ≈ = record
  { ⟦s⟧  = ⟦s⟧
  ; ⟦u⟧  = Λ (_ $ v 0) _
  ; ↘⟦s⟧ = ↘⟦s⟧
  ; ↘⟦u⟧ = ⟦Λ⟧ _
  ; sTu  = λ aSa′ → let open FAppIn (sTu aSa′)
                    in fa
                    - fa′
                    - ↘fa
                    - Λ∙ (⟦$⟧ (⟦[]⟧ ⟦↑⟧ ↘⟦u⟧) (⟦v⟧ 0) ↘fa′)
                    - faTfa′
  }
  where open Intp (t≈ ρ≈)

rec-cong-helper : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
                  (s≈ : ⟦ s ⟧ ρ ≈⟦ s′ ⟧ ρ′ ∈ T) →
                  (r≈ : ⟦ r ⟧ ρ ≈⟦ r′ ⟧ ρ′ ∈ N ⟶ T ⟶ T) →
                  a ≈ b ∈N →
                  rec Intp.⟦s⟧ s≈ , Intp.⟦s⟧ r≈ , a ≈rec Intp.⟦u⟧ s≈ , Intp.⟦u⟧ r≈ , b ∈ T
rec-cong-helper ρ≈ s≈ r≈ ze-≈             = record
  { ra    = ⟦s⟧
  ; rb    = ⟦u⟧
  ; ↘ra   = rze
  ; ↘rb   = rze
  ; raTrb = sTu
  }
  where open Intp s≈
rec-cong-helper ρ≈ s≈ r≈ (su-≈ a≈b)       = record
  { ra    = r″≈.fa
  ; rb    = r″≈.fa′
  ; ↘ra   = rsu ↘ra r′≈.↘fa r″≈.↘fa
  ; ↘rb   = rsu ↘rb r′≈.↘fa′ r″≈.↘fa′
  ; raTrb = r″≈.faTfa′
  }
  where open rec_,_,_≈rec_,_,_∈_ (rec-cong-helper ρ≈ s≈ r≈ a≈b)
        module r≈  = Intp r≈
        r′≈        = r≈.sTu a≈b
        module r′≈ = FAppIn r′≈
        r″≈        = r′≈.faTfa′ raTrb
        module r″≈ = FAppIn r″≈
rec-cong-helper {T = T} ρ≈ s≈ r≈ (↑N e⊥e′) = record
  { ra    = _
  ; rb    = _
  ; ↘ra   = rec
  ; ↘rb   = rec
  ; raTrb = Bot⇒⟦⟧ T λ n → let w  , ↘w  , ↘w′ = ⟦⟧⇒Top T s≈.sTu n
                               w′ , ↘w″ , ↘w‴ = ⟦⟧⇒Top (N ⟶ T ⟶ T) r≈.sTu n
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
  ; ⟦u⟧  = rb
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ t≈.↘⟦s⟧ ↘ra
  ; ↘⟦u⟧ = ⟦rec⟧ s≈.↘⟦u⟧ r≈.↘⟦u⟧ t≈.↘⟦u⟧ ↘rb
  ; sTu  = raTrb
  }
  where sρ≈ = s≈ ρ≈
        rρ≈ = r≈ ρ≈
        tρ≈ = t≈ ρ≈
        module s≈ = Intp sρ≈
        module r≈ = Intp rρ≈
        module t≈ = Intp tρ≈
        open rec_,_,_≈rec_,_,_∈_ (rec-cong-helper ρ≈ sρ≈ rρ≈ t≈.sTu)

rec-β-ze : Γ ⊨ s ∶ T →
           Γ ⊨ r ∶ N ⟶ T ⟶ T →
           -------------------------
           Γ ⊨ rec T s r ze ≈ s ∶ T
rec-β-ze s≈ r≈ ρ≈ = record
  { ⟦s⟧  = s≈.⟦s⟧
  ; ⟦u⟧  = s≈.⟦u⟧
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ ⟦ze⟧ rze
  ; ↘⟦u⟧ = s≈.↘⟦u⟧
  ; sTu  = s≈.sTu
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
  ; ⟦u⟧  = r″≈.fa′
  ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ (⟦su⟧ t≈.↘⟦s⟧) (rsu ↘ra r′≈.↘fa r″≈.↘fa)
  ; ↘⟦u⟧ = ⟦$⟧ (⟦$⟧ r≈.↘⟦u⟧ t≈.↘⟦u⟧ r′≈.↘fa′) (⟦rec⟧ s≈.↘⟦u⟧ r≈.↘⟦u⟧ t≈.↘⟦u⟧ ↘rb) r″≈.↘fa′
  ; sTu  = r″≈.faTfa′
  }
  where module s≈  = Intp (s≈ ρ≈)
        module r≈  = Intp (r≈ ρ≈)
        module t≈  = Intp (t≈ ρ≈)
        open rec_,_,_≈rec_,_,_∈_ (rec-cong-helper ρ≈ (s≈ ρ≈) (r≈ ρ≈) t≈.sTu)
        module r′≈ = FAppIn (r≈.sTu t≈.sTu)
        module r″≈ = FAppIn (r′≈.faTfa′ raTrb)

s-≈-refl : Γ ⊨s σ ∶ Γ →
           ----------------
           Γ ⊨s σ ≈ σ ∶ Γ
s-≈-refl σ = σ

s-≈-sym : Γ ⊨s σ ≈ σ′ ∶ Γ →
          ------------------
          Γ ⊨s σ′ ≈ σ ∶ Γ
s-≈-sym σ≈ ρ≈ = record
  { ⟦σ⟧  = ⟦τ⟧
  ; ⟦τ⟧  = ⟦σ⟧
  ; ↘⟦σ⟧ = ↘⟦τ⟧
  ; ↘⟦τ⟧ = ↘⟦σ⟧
  ; σΓτ  = ≈⟦⟧-sym σΓτ
  }
  where open Intps (σ≈ (≈⟦⟧-sym ρ≈))

s-≈-trans : Γ ⊨s σ ≈ σ′ ∶ Γ →
            Γ ⊨s σ′ ≈ σ″ ∶ Γ →
            -------------------
            Γ ⊨s σ ≈ σ″ ∶ Γ
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
