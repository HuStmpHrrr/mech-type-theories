{-# OPTIONS --without-K --safe #-}

module STLCSubst.Semantics.PER where


open import Level using (0ℓ)
open import Relation.Binary using (Rel; PartialSetoid; IsPartialEquivalence)
open import Relation.Binary.PropositionalEquality using (_≗_)

open import Lib
open import STLCSubst.Statics
open import STLCSubst.Statics.Properties
open import STLCSubst.Semantics.Definitions

Ty : Set₁
Ty = Rel D 0ℓ

infix 3 _≈_∈_ _∈!_
_≈_∈_ : ∀ {ℓ} {A : Set ℓ} → A → A → Rel A 0ℓ → Set
x ≈ y ∈ R = R x y

_∈!_ : ∀ {ℓ} {A : Set ℓ} → A → Rel A 0ℓ → Set
x ∈! R = x ≈ x ∈ R

Top : Rel Df 0ℓ
Top d d′ = ∀ n → ∃ λ w → Rf n - d ↘ w × Rf n - d′ ↘ w

Bot : Rel Dn 0ℓ
Bot e e′ = ∀ n → ∃ λ u → Re n - e ↘ u × Re n - e′ ↘ u

l∈Bot : ∀ x → Bot (l x) (l x)
l∈Bot x n = v (n ∸ x ∸ 1) , Rl n x , Rl n x

$∈Bot : e ≈ e′ ∈ Bot  → d ≈ d′ ∈ Top → e $ d ≈ e′ $ d′ ∈ Bot
$∈Bot e≈e′ d≈d′ n
  with e≈e′ n
     | d≈d′ n
...  | u , ↘u , ↘u′
     | w , ↘w , ↘w′ = u $ w , R$ n ↘u ↘w , R$ n ↘u′ ↘w′

record _∙_≈_∙_∈[_⟶_] f e f′ e′ S T : Set where
  field
    fe      : D
    f′e′    : D
    ↘fe     : f ∙ ↑ S e ↘ fe
    ↘f′e′   : f′ ∙ ↑ S e′ ↘ f′e′
    fe≈f′e′ : ↓ T fe ≈ ↓ T f′e′ ∈ Top

module FApp {f e f′ e′ S T} (eq : f ∙ e ≈ f′ ∙ e′ ∈[ S ⟶ T ]) = _∙_≈_∙_∈[_⟶_] eq

↓F∈Top : (∀ {e e′} → e ≈ e′ ∈ Bot → f ∙ e ≈ f′ ∙ e′ ∈[ S ⟶ T ]) → ↓ (S ⟶ T) f ≈ ↓ (S ⟶ T) f′ ∈ Top
↓F∈Top f n = let w , ↘w , ↘w′ = fe≈f′e′ (suc n)
             in Λ w , RΛ n ↘fe ↘w , RΛ n ↘f′e′ ↘w′
  where open FApp (f (l∈Bot n))

ze∈Top : ↓ N ze ≈ ↓ N ze ∈ Top
ze∈Top n = ze , Rze n , Rze n

su∈Top : ↓ N a ≈ ↓ N b ∈ Top → ↓ N (su a) ≈ ↓ N (su b) ∈ Top
su∈Top a≈b n
  with a≈b n
...  | w , a↘ , b↘ = su w , Rsu n a↘ , Rsu n b↘


infix 3 _≈_∈^_ ↑_≈↑_∈_

_≈_∈^_ : D → D → Typ → Set
a ≈ b ∈^ T = ↓ T a ≈ ↓ T b ∈ Top

↑_≈↑_∈_ : Dn → Dn → Typ → Set
↑ e ≈↑ e′ ∈ T = e ≈ e′ ∈ Bot

infix 4 _⊩_
record _⊩_ T (A : Ty) : Set where
  field
    ~⊆ : ∀ {e e′} → ↑ e ≈↑ e′ ∈ T → ↑ T e ≈ ↑ T e′ ∈ A
    ⊆^ : ∀ {a b} → A a b → a ≈ b ∈^ T

record [_∙_≈_∙_]∈_ (f a f′ a′ : D) (T : Ty) : Set where
  constructor
    _-_-_-_-_

  field
    fa fa′ : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    fa≈fa′ : fa ≈ fa′ ∈ T

module FAppIn {f a f′ a′ T} (r : [ f ∙ a ≈ f′ ∙ a′ ]∈ T) = [_∙_≈_∙_]∈_ r

infix 10 _⇒_
_⇒_ : Ty → Ty → Ty
(S ⇒ T) f f′ =
  ∀ {a a′} → a ≈ a′ ∈ S → [ f ∙ a ≈ f′ ∙ a′ ]∈ T

F⊩ : ∀ {A B} → S ⊩ A → U ⊩ B → S ⟶ U ⊩ A ⇒ B
F⊩ {S} {U} {A} {B} SA UB = record
  { ~⊆ = ~⊆
  ; ⊆^ = ⊆^
  }
  where module SA = _⊩_ SA
        module UB = _⊩_ UB

        ~⊆ : ↑ e ≈↑ e′ ∈ S ⟶ U → ↑ (S ⟶ U) e ≈ ↑ (S ⟶ U) e′ ∈ A ⇒ B
        ~⊆ e≈e′ a≈a′ = record
          { fa     = [ U ] _ $′ ↓ S _
          ; fa′    = [ U ] _ $′ ↓ S _
          ; ↘fa    = $∙ S U _ _
          ; ↘fa′   = $∙ S U _ _
          ; fa≈fa′ = UB.~⊆ λ n → let u , e↘ , e′↘ = e≈e′ n
                                     w , a↘ , a′↘ = SA.⊆^ a≈a′ n
                                 in u $ w , R$ n e↘ a↘ , R$ n e′↘ a′↘
          }

        ⊆^ : a ≈ b ∈ A ⇒ B → a ≈ b ∈^ S ⟶ U
        ⊆^ a≈b n = let w , ↘w , ↘w′ = UB.⊆^ app.fa≈fa′ (suc n)
                   in Λ w , RΛ n app.↘fa ↘w , RΛ n app.↘fa′ ↘w′
          where app = a≈b (SA.~⊆ λ m → v (m ∸ n ∸ 1) , Rl m n , Rl m n)
                module app = FAppIn app

data _≈_∈N : Ty where
  ze-≈ : ze ≈ ze ∈N
  su-≈ : a ≈ a′ ∈N →
         -------------------
         su a ≈ su a′ ∈N
  ↑N   : ∀ {T′} →
         e ≈ e′ ∈ Bot →
         -------------------
         ↑ T e ≈ ↑ T′ e′ ∈N

⟦_⟧T : Typ → Ty
⟦ N ⟧T     = _≈_∈N
⟦ S ⟶ U ⟧T = ⟦ S ⟧T ⇒ ⟦ U ⟧T

N-sym : a ≈ b ∈N → b ≈ a ∈N
N-sym ze-≈      = ze-≈
N-sym (su-≈ a≈b) = su-≈ (N-sym a≈b)
N-sym (↑N e≈e′) = ↑N (λ n → let u , ↘u , ↘u′ = e≈e′ n in u , ↘u′ , ↘u)

N-trans : a ≈ a′ ∈N → a′ ≈ a″ ∈N → a ≈ a″ ∈N
N-trans ze-≈      ze-≈       = ze-≈
N-trans (su-≈ eq) (su-≈ eq′) = su-≈ (N-trans eq eq′)
N-trans (↑N e≈e′) (↑N e′≈e″) = ↑N λ n → let u , ↘u   , e′↘ = e≈e′ n
                                            _ , e′↘′ , ↘u′ = e′≈e″ n
                                        in u , ↘u , subst (Re n - _ ↘_) (Re-det e′↘′ e′↘) ↘u′

⟦⟧-sym : ∀ T → a ≈ b ∈ ⟦ T ⟧T → b ≈ a ∈ ⟦ T ⟧T
⟦⟧-sym N a≈b          = N-sym a≈b
⟦⟧-sym (S ⟶ U) a≈b ∈S = record
  { fa     = fa′
  ; fa′    = fa
  ; ↘fa    = ↘fa′
  ; ↘fa′   = ↘fa
  ; fa≈fa′ = ⟦⟧-sym U fa≈fa′
  }
  where open FAppIn (a≈b (⟦⟧-sym S ∈S))

⟦⟧-trans : ∀ T → a ≈ a′ ∈ ⟦ T ⟧T → a′ ≈ a″ ∈ ⟦ T ⟧T → a ≈ a″ ∈ ⟦ T ⟧T
⟦⟧-trans N eq eq′                = N-trans eq eq′
⟦⟧-trans (S ⟶ U) f≈f′ f′≈f″ x≈y = record
  { fa     = fxUf′x.fa
  ; fa′    = f′xUf″y.fa′
  ; ↘fa    = fxUf′x.↘fa
  ; ↘fa′   = f′xUf″y.↘fa′
  ; fa≈fa′ = trans′ fxUf′x.fa≈fa′
                    (subst (λ a → ⟦ U ⟧T a _) (ap-det f′xUf″y.↘fa fxUf′x.↘fa′) f′xUf″y.fa≈fa′)
  }
  where trans′ : ∀ {a b d} → a ≈ b ∈ ⟦ U ⟧T → b ≈ d ∈ ⟦ U ⟧T → a ≈ d ∈ ⟦ U ⟧T
        trans′         = ⟦⟧-trans U
        xSx            = ⟦⟧-trans S x≈y (⟦⟧-sym S x≈y)
        module fxUf′x  = FAppIn (f≈f′ xSx)
        module f′xUf″y = FAppIn (f′≈f″ x≈y)

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

⟦⟧-refl : ∀ T → a ≈ b ∈ ⟦ T ⟧T → a ≈ a ∈ ⟦ T ⟧T
⟦⟧-refl T a≈b = ⟦⟧-trans T a≈b (⟦⟧-sym T a≈b)

⟦⟧-refl′ : ∀ T → a ≈ b ∈ ⟦ T ⟧T → b ≈ b ∈ ⟦ T ⟧T
⟦⟧-refl′ T a≈b = ⟦⟧-trans T (⟦⟧-sym T a≈b) a≈b


⊩⟦N⟧ : N ⊩ ⟦ N ⟧T
⊩⟦N⟧ = record
  { ~⊆ = ↑N
  ; ⊆^ = ⊆^
  }
  where ⊆^ : a ≈ b ∈N → a ≈ b ∈^ N
        ⊆^ ze-≈ n           = ze , Rze n , Rze n
        ⊆^ (su-≈ a≈b) n
          with ⊆^ a≈b n
        ...  | w , ↘w , ↘w′ = su w , Rsu n ↘w , Rsu n ↘w′
        ⊆^ (↑N e≈e′) n
          with e≈e′ n
        ...  | u , e↘ , e′↘ = ne u , Rne n e↘ , Rne n e′↘

⊩⟦_⟧ : ∀ T → T ⊩ ⟦ T ⟧T
⊩⟦ N ⟧     = ⊩⟦N⟧
⊩⟦ S ⟶ U ⟧ = F⊩ ⊩⟦ S ⟧ ⊩⟦ U ⟧

Bot⇒⟦⟧ : ∀ T → e ≈ e′ ∈ Bot → ↑ T e ≈ ↑ T e′ ∈ ⟦ T ⟧T
Bot⇒⟦⟧ T = _⊩_.~⊆ ⊩⟦ T ⟧

⟦⟧⇒Top : ∀ T →  a ≈ b ∈ ⟦ T ⟧T → ↓ T a ≈ ↓ T b ∈ Top
⟦⟧⇒Top T = _⊩_.⊆^ ⊩⟦ T ⟧

infix 4 ⟦_⟧_≈⟦_⟧_∈s[_]_ ⟦_⟧[_]_≈⟦_⟧[_]_∈_
⟦_⟧ : Ctx → Rel Env 0ℓ
⟦ Δ ⟧ ρ ρ′ = ∀ {x T} → x ∶ T ∈ Δ → ρ x ≈ ρ′ x ∈ ⟦ T ⟧T

⟦⟧-syms : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ′ ≈ ρ ∈ ⟦ Γ ⟧
⟦⟧-syms ρ≈ρ′ {_} {T} T∈Γ = ⟦⟧-sym T (ρ≈ρ′ T∈Γ)

⟦⟧-transs : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ′ ≈ ρ″ ∈ ⟦ Γ ⟧ → ρ ≈ ρ″ ∈ ⟦ Γ ⟧
⟦⟧-transs ρ≈ρ′ ρ′≈ρ″ {_} {T} T∈Γ = ⟦⟧-trans T (ρ≈ρ′ T∈Γ) (ρ′≈ρ″ T∈Γ)

⟦⟧-refls : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ ≈ ρ ∈ ⟦ Γ ⟧
⟦⟧-refls ρ≈ρ′ = ⟦⟧-transs ρ≈ρ′ (⟦⟧-syms ρ≈ρ′)

⟦⟧-refls′ : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ′ ≈ ρ′ ∈ ⟦ Γ ⟧
⟦⟧-refls′ ρ≈ρ′ = ⟦⟧-transs (⟦⟧-syms ρ≈ρ′) ρ≈ρ′

⟦⟧-transpˡ : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ ≗ ρ″ → ρ″ ≈ ρ′ ∈ ⟦ Γ ⟧
⟦⟧-transpˡ ρ≈ρ′ eq {x} T∈Γ
  rewrite sym (eq x) = ρ≈ρ′ T∈Γ

⟦⟧-transpʳ : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ρ′ ≗ ρ″ → ρ ≈ ρ″ ∈ ⟦ Γ ⟧
⟦⟧-transpʳ ρ≈ρ′ eq {x} T∈Γ
  rewrite sym (eq x) = ρ≈ρ′ T∈Γ

ctx-ext : ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → a ≈ b ∈ ⟦ T ⟧T → ρ ↦ a ≈ ρ′ ↦ b ∈ ⟦ T ∷ Γ ⟧
ctx-ext ρ≈ aTb here       = aTb
ctx-ext ρ≈ aTb (there ∈Γ) = ρ≈ ∈Γ

⟦⟧-wk : Γ ⊢w ϕ ∶ Δ → ρ ≈ ρ′ ∈ ⟦ Γ ⟧ → ⟦ ϕ ⟧w ρ ≈ ⟦ ϕ ⟧w ρ′ ∈ ⟦ Δ ⟧
⟦⟧-wk ⊢ϕ ρ≈ρ′ T∈Δ = ρ≈ρ′ (⊢ϕ T∈Δ)

record ⟦_⟧_≈⟦_⟧_∈s[_]_ σ ρ τ ρ′ (ϕ : Wk) Γ : Set where
  field
    {⟦σ⟧}  : Env
    {⟦τ⟧}  : Env
    {⟦σ⟧′} : Env
    {⟦τ⟧′} : Env
    ↘⟦σ⟧   : ⟦ σ [ ϕ ] ⟧s ρ ↘ ⟦σ⟧
    ↘⟦σ⟧′  : ⟦ σ ⟧s ⟦ ϕ ⟧w ρ ↘ ⟦σ⟧′
    ↘⟦τ⟧   : ⟦ τ [ ϕ ] ⟧s ρ′ ↘ ⟦τ⟧
    ↘⟦τ⟧′  : ⟦ τ ⟧s ⟦ ϕ ⟧w ρ′ ↘ ⟦τ⟧′
    σ≈σ′   : ⟦σ⟧ ≈ ⟦σ⟧′ ∈ ⟦ Γ ⟧
    σ≈τ    : ⟦σ⟧ ≈ ⟦τ⟧ ∈ ⟦ Γ ⟧
    τ≈τ′   : ⟦τ⟧ ≈ ⟦τ⟧′ ∈ ⟦ Γ ⟧

  σ≈τ′ : ⟦σ⟧ ≈ ⟦τ⟧′ ∈ ⟦ Γ ⟧
  σ≈τ′ = ⟦⟧-transs σ≈τ τ≈τ′

  τ≈σ′ : ⟦τ⟧ ≈ ⟦σ⟧′ ∈ ⟦ Γ ⟧
  τ≈σ′ = ⟦⟧-transs (⟦⟧-syms σ≈τ) σ≈σ′

  σ′≈τ′ : ⟦σ⟧′ ≈ ⟦τ⟧′ ∈ ⟦ Γ ⟧
  σ′≈τ′ = ⟦⟧-transs (⟦⟧-syms σ≈σ′) σ≈τ′

module Intps {σ ρ τ ρ′ ϕ Γ} (r : ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s[ ϕ ] Γ) = ⟦_⟧_≈⟦_⟧_∈s[_]_ r

infix 4 _⊨_≈_∶_ _⊨_∶_  _⊨s_≈_∶_ _⊨s_∶_

_⊨s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨s σ ≈ τ ∶ Δ = ∀ {Γ′ ϕ ρ ρ′} → Γ′ ⊢w ϕ ∶ Γ → ρ ≈ ρ′ ∈ ⟦ Γ′ ⟧ → ⟦ σ ⟧ ρ ≈⟦ τ ⟧ ρ′ ∈s[ ϕ ] Δ

_⊨s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊨s σ ∶ Δ = Γ ⊨s σ ≈ σ ∶ Δ


record ⟦_⟧[_]_≈⟦_⟧[_]_∈_ s σ ρ u τ ρ′ T : Set where
  field
    {⟦s⟧}  : D
    {⟦s⟧′} : D
    {⟦t⟧}  : D
    {⟦t⟧′} : D
    {⟦σ⟧}  : Env
    {⟦τ⟧}  : Env
    ↘⟦s⟧   : ⟦ s [ σ ] ⟧ ρ ↘ ⟦s⟧
    ↘⟦σ⟧   : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦s⟧′  : ⟦ s ⟧ ⟦σ⟧ ↘ ⟦s⟧′
    ↘⟦t⟧   : ⟦ u [ τ ] ⟧ ρ′ ↘ ⟦t⟧
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ′ ↘ ⟦τ⟧
    ↘⟦t⟧′  : ⟦ u ⟧ ⟦τ⟧ ↘ ⟦t⟧′
    s≈s′   : ⟦s⟧ ≈ ⟦s⟧′ ∈ ⟦ T ⟧T
    s≈t    : ⟦s⟧ ≈ ⟦t⟧ ∈ ⟦ T ⟧T
    t≈t′   : ⟦t⟧ ≈ ⟦t⟧′ ∈ ⟦ T ⟧T

  s≈t′ : ⟦s⟧ ≈ ⟦t⟧′ ∈ ⟦ T ⟧T
  s≈t′ = ⟦⟧-trans T s≈t t≈t′

  t≈s′ : ⟦t⟧ ≈ ⟦s⟧′ ∈ ⟦ T ⟧T
  t≈s′ = ⟦⟧-trans T (⟦⟧-sym T s≈t) s≈s′

  s′≈t′ : ⟦s⟧′ ≈ ⟦t⟧′ ∈ ⟦ T ⟧T
  s′≈t′ = ⟦⟧-trans T (⟦⟧-sym T s≈s′) s≈t′

module Intp {s σ ρ u σ′ ρ′ T} (r : ⟦ s ⟧[ σ ] ρ ≈⟦ u ⟧[ σ′ ] ρ′ ∈ T) = ⟦_⟧[_]_≈⟦_⟧[_]_∈_ r

record ⟦_⟧_≈⟦_⟧_∈[_]w_ s ρ u ρ′ ϕ T : Set where
  field
    {⟦s⟧}  : D
    {⟦s⟧′} : D
    {⟦t⟧}  : D
    {⟦t⟧′} : D
    ↘⟦s⟧   : ⟦ s [ ϕ ] ⟧ ρ ↘ ⟦s⟧
    ↘⟦s⟧′  : ⟦ s ⟧ ⟦ ϕ ⟧w ρ ↘ ⟦s⟧′
    ↘⟦t⟧   : ⟦ u [ ϕ ] ⟧ ρ′ ↘ ⟦t⟧
    ↘⟦t⟧′  : ⟦ u ⟧ ⟦ ϕ ⟧w ρ′ ↘ ⟦t⟧′
    s≈s′   : ⟦s⟧ ≈ ⟦s⟧′ ∈ ⟦ T ⟧T
    s≈t    : ⟦s⟧ ≈ ⟦t⟧ ∈ ⟦ T ⟧T
    t≈t′   : ⟦t⟧ ≈ ⟦t⟧′ ∈ ⟦ T ⟧T

module Intpw {s ρ u ρ′ ϕ T} (r : ⟦ s ⟧ ρ ≈⟦ u ⟧ ρ′ ∈[ ϕ ]w T) = ⟦_⟧_≈⟦_⟧_∈[_]w_ r


_⊨_≈_∶_ : Ctx → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = ∀ {Γ′ σ σ′ ρ ρ′} → Γ′ ⊨s σ ≈ σ′ ∶ Γ → ρ ≈ ρ′ ∈ ⟦ Γ′ ⟧ → ⟦ t ⟧[ σ ] ρ ≈⟦ t′ ⟧[ σ′ ] ρ′ ∈ T

_⊨_∶_ : Ctx → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T
