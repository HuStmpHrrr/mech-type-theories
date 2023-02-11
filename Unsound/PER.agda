{-# OPTIONS --without-K --safe #-}

module Unsound.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)

open import Lib
open import Unsound.Statics
open import Unsound.TypedSem

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

data _≈_∈Bo : Ty where
  tru-≈ : tru ≈ tru ∈Bo
  fls-≈ : fls ≈ fls ∈Bo
  ↑Bo   : ∀ {T′} →
          Bot e e′ →
          -------------------
          ↑ T e ≈ ↑ T′ e′ ∈Bo

⟦_⟧T : Typ → Ty
⟦ Bo ⟧T     = _≈_∈Bo
⟦ S ⟶ U ⟧T = ⟦ S ⟧T ⇒ ⟦ U ⟧T

Bo-sym : a ≈ b ∈Bo → b ≈ a ∈Bo
Bo-sym tru-≈ = tru-≈
Bo-sym fls-≈ = fls-≈
Bo-sym (↑Bo ⊥) = ↑Bo (λ n → let u , ↘u , ↘u′ = ⊥ n in u , ↘u′ , ↘u)

Bo-trans : a ≈ a′ ∈Bo → a′ ≈ a″ ∈Bo → a ≈ a″ ∈Bo
Bo-trans tru-≈ tru-≈        = tru-≈
Bo-trans fls-≈ fls-≈        = fls-≈
Bo-trans (↑Bo ⊥e) (↑Bo ⊥e′) = ↑Bo λ n → let u , ↘u , e′↘ = ⊥e n
                                            _ , e′↘′ , ↘u′ = ⊥e′ n
                                        in u , ↘u , subst (Re n - _ ↘_) (Re-det e′↘′ e′↘) ↘u′

⟦⟧-sym : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T b a
⟦⟧-sym Bo ab         = Bo-sym ab
⟦⟧-sym (S ⟶ U) ab ∈S = record
  { fa     = fa′
  ; fa′    = fa
  ; ↘fa    = ↘fa′
  ; ↘fa′   = ↘fa
  ; faTfa′ = ⟦⟧-sym U faTfa′
  }
  where open FAppIn (ab (⟦⟧-sym S ∈S))

⟦⟧-trans : ∀ T → ⟦ T ⟧T a a′ → ⟦ T ⟧T a′ a″ → ⟦ T ⟧T a a″
⟦⟧-trans Bo eq eq′              = Bo-trans eq eq′
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

⊩⟦Bo⟧ : Bo ⊩ ⟦ Bo ⟧T
⊩⟦Bo⟧ = record
  { ~⊆ = ↑Bo
  ; ⊆^ = ⊆^
  }
  where ⊆^ : a ≈ b ∈Bo → a ≈ b ∈^ Bo
        ⊆^ tru-≈ n          = tru , Rtru n , Rtru n
        ⊆^ fls-≈ n          = fls , Rfls n , Rfls n
        ⊆^ (↑Bo e⊥e′) n
          with e⊥e′ n
        ...  | u , e↘ , e′↘ = ne u , Rne n e↘ , Rne n e′↘

⊩⟦_⟧ : ∀ T → T ⊩ ⟦ T ⟧T
⊩⟦ Bo ⟧     = ⊩⟦Bo⟧
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

tru-≈′ : Γ ⊨ tru ≈ tru ∶ Bo
tru-≈′ ρ≈ = record
  { ⟦s⟧ = tru
  ; ⟦t⟧ = tru
  ; ↘⟦s⟧ = ⟦tru⟧
  ; ↘⟦t⟧ = ⟦tru⟧
  ; sTt = tru-≈
  }

fls-≈′ : Γ ⊨ fls ≈ fls ∶ Bo
fls-≈′ ρ≈ = record
  { ⟦s⟧ = fls
  ; ⟦t⟧ = fls
  ; ↘⟦s⟧ = ⟦fls⟧
  ; ↘⟦t⟧ = ⟦fls⟧
  ; sTt = fls-≈
  }

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


tru-[] : Γ ⊨s σ ∶ Δ →
         ------------------------
         Γ ⊨ tru [ σ ] ≈ tru ∶ Bo
tru-[] σ ρ≈ = record
  { ⟦s⟧  = tru
  ; ⟦t⟧  = tru
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ ⟦tru⟧
  ; ↘⟦t⟧ = ⟦tru⟧
  ; sTt  = tru-≈
  }
  where open Intps (σ ρ≈)


fls-[] : Γ ⊨s σ ∶ Δ →
         ------------------------
         Γ ⊨ fls [ σ ] ≈ fls ∶ Bo
fls-[] σ ρ≈ = record
  { ⟦s⟧  = fls
  ; ⟦t⟧  = fls
  ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ ⟦fls⟧
  ; ↘⟦t⟧ = ⟦fls⟧
  ; sTt  = fls-≈
  }
  where open Intps (σ ρ≈)

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



-- Initial-refl : ∀ Γ → InitialEnv Γ ≈ InitialEnv Γ ∈⟦ Γ ⟧
-- Initial-refl (T ∷ Γ)  here        = Bot⇒⟦⟧ T (l∈Bot (L.length Γ))
-- Initial-refl .(_ ∷ _) (there T∈Γ) = Initial-refl _ T∈Γ

-- module Completeness where

--   record Completeness′ n s ρ t ρ′ T : Set where
--     field
--       nf  : Nf
--       nbs : Nbe n ρ s T nf
--       nbt : Nbe n ρ′ t T nf

--   Completeness : ℕ → Env → Exp → Exp → Typ → Set
--   Completeness n ρ s t T = Completeness′ n s ρ t ρ T

--   ⊨-conseq : Γ ⊨ s ≈ t ∶ T → ∀ n → ρ ≈ ρ′ ∈⟦ Γ ⟧ → Completeness′ n s ρ t ρ′ T
--   ⊨-conseq {T = T} s≈ n ρ≈ =
--     let (w , ↘w , ↘w′) = TTop T sTt n in
--     record
--     { nf  = w
--     ; nbs = record
--       { ⟦t⟧  = ⟦s⟧
--       ; ↘⟦t⟧ = ↘⟦s⟧
--       ; ↓⟦t⟧ = ↘w
--       }
--     ; nbt = record
--       { ⟦t⟧  = ⟦t⟧
--       ; ↘⟦t⟧ = ↘⟦t⟧
--       ; ↓⟦t⟧ = ↘w′
--       }
--     }
--     where open Intp (s≈ ρ≈)
--           TTop : ∀ T → ⟦ T ⟧T a b → Top (↓ T a) (↓ T b)
--           TTop T aTb = ⟦⟧⇒Top T aTb

--   module T = Typing

--   mutual
--     sem-sound : Γ T.⊢ t ∶ T → Γ ⊨ t ∶ T
--     sem-sound (T.vlookup T∈Γ) = v-≈ T∈Γ
--     sem-sound T.tru-I         = tru-≈′
--     sem-sound T.fls-I         = fls-≈′
--     sem-sound (T.Λ-I t)       = Λ-cong (sem-sound t)
--     sem-sound (T.Λ-E t s)     = $-cong (sem-sound t) (sem-sound s)
--     sem-sound (T.t[σ] t σ)    = []-cong (sem-s-sound σ) (sem-sound t)

--     sem-s-sound : Γ T.⊢s σ ∶ Δ → Γ ⊨s σ ∶ Δ
--     sem-s-sound T.S-↑       = ↑-≈
--     sem-s-sound T.S-I       = I-≈
--     sem-s-sound (T.S-∘ σ δ) = ∘-cong (sem-s-sound σ) (sem-s-sound δ)
--     sem-s-sound (T.S-, σ t) = ,-cong (sem-s-sound σ) (sem-sound t)

--   completeness₀ : Γ T.⊢ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) t t T
--   completeness₀ {Γ} t = ⊨-conseq (sem-sound t) (L.length Γ) (Initial-refl Γ)

--   nbe-comp : Γ T.⊢ t ∶ T → ∃ λ w → Nbe (L.length Γ) (InitialEnv Γ) t T w
--   nbe-comp t = nf , nbs
--     where open Completeness′ (completeness₀ t)

--   mutual
--     ≈sem-sound : Γ T.⊢ s ≈ t ∶ T → Γ ⊨ s ≈ t ∶ T
--     ≈sem-sound (T.v-≈ T∈Γ)                 = v-≈ T∈Γ
--     ≈sem-sound T.tru-≈                     = tru-≈′
--     ≈sem-sound T.fls-≈                     = fls-≈′
--     ≈sem-sound (T.Λ-cong s≈t)              = Λ-cong (≈sem-sound s≈t)
--     ≈sem-sound (T.$-cong t≈t′ s≈s′)        = $-cong (≈sem-sound t≈t′) (≈sem-sound s≈s′)
--     ≈sem-sound (T.[]-cong σ≈τ s≈t)         = []-cong (≈sem-s-sound σ≈τ) (≈sem-sound s≈t)
--     ≈sem-sound (T.tru-[] σ)                = tru-[] (sem-s-sound σ)
--     ≈sem-sound (T.fls-[] σ)                = fls-[] (sem-s-sound σ)
--     ≈sem-sound (T.Λ-[] σ t)                = Λ-[] (sem-s-sound σ) (sem-sound t)
--     ≈sem-sound (T.$-[] σ r s)              = $-[] (sem-s-sound σ) (sem-sound r) (sem-sound s)
--     ≈sem-sound (T.Λ-β t s)                 = Λ-β (sem-sound t) (sem-sound s)
--     ≈sem-sound (T.Λ-η t)                   = Λ-η (sem-sound t)
--     ≈sem-sound (T.[I] t)                   = [I] (sem-sound t)
--     ≈sem-sound (T.↑-lookup T∈Γ)            = ↑-lookup T∈Γ
--     ≈sem-sound (T.[∘] τ σ t)               = [∘] (sem-s-sound τ) (sem-s-sound σ) (sem-sound t)
--     ≈sem-sound (T.[,]-v-ze σ t)            = [,]-v0 (sem-s-sound σ) (sem-sound t)
--     ≈sem-sound (T.[,]-v-su σ t T∈Γ)        = [,]-v-suc (sem-s-sound σ) (sem-sound t) T∈Γ
--     ≈sem-sound (T.≈-sym s≈t)               = ≈-sym (≈sem-sound s≈t)
--     ≈sem-sound (T.≈-trans s≈t t≈t′)        = ≈-trans (≈sem-sound s≈t) (≈sem-sound t≈t′)

--     ≈sem-s-sound : Γ T.⊢s σ ≈ τ ∶ Δ → Γ ⊨s σ ≈ τ ∶ Δ
--     ≈sem-s-sound T.↑-≈                  = ↑-≈
--     ≈sem-s-sound T.I-≈                  = I-≈
--     ≈sem-s-sound (T.∘-cong σ≈σ′ τ≈τ′)   = ∘-cong (≈sem-s-sound σ≈σ′) (≈sem-s-sound τ≈τ′)
--     ≈sem-s-sound (T.,-cong σ≈τ s≈t)     = ,-cong (≈sem-s-sound σ≈τ) (≈sem-sound s≈t)
--     ≈sem-s-sound (T.↑-∘-, σ s)          = ↑-∘-, (sem-s-sound σ) (sem-sound s)
--     ≈sem-s-sound (T.I-∘ σ)              = I-∘ (sem-s-sound σ)
--     ≈sem-s-sound (T.∘-I σ)              = ∘-I (sem-s-sound σ)
--     ≈sem-s-sound (T.∘-assoc σ σ′ σ″)    = ∘-assoc (sem-s-sound σ) (sem-s-sound σ′) (sem-s-sound σ″)
--     ≈sem-s-sound (T.,-ext σ)            = ,-ext (sem-s-sound σ)
--     ≈sem-s-sound (T.S-≈-sym σ≈τ)        = s-≈-sym (≈sem-s-sound σ≈τ)
--     ≈sem-s-sound (T.S-≈-trans σ≈τ σ≈τ₁) = s-≈-trans (≈sem-s-sound σ≈τ) (≈sem-s-sound σ≈τ₁)

--   completeness : Γ T.⊢ s ≈ t ∶ T → Completeness (L.length Γ) (InitialEnv Γ) s t T
--   completeness {Γ} s≈t = ⊨-conseq (≈sem-sound s≈t) (L.length Γ) (Initial-refl Γ)
