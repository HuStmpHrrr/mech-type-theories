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

-- rec∈Bot : d ≈ d′ ∈ Top → d″ ≈ d‴ ∈ Top → e ≈ e′ ∈ Bot → rec T d d″ e ≈ rec T d′ d‴ e′ ∈ Bot
-- rec∈Bot d≈d′ d″≈d‴ e≈e′ n
--   with d≈d′ n
--      | d″≈d‴ n
--      | e≈e′ n
-- ...  | w  , d↘ , d′↘
--      | w′ , d″↘ , d‴↘
--      | u  , e↘ , e′↘  = rec _ w w′ u
--                       , Rr n d↘ d″↘ e↘
--                       , Rr n d′↘ d‴↘ e′↘

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

-- infix 4 rec_,_,_≈rec_,_,_∈_
-- record rec_,_,_≈rec_,_,_∈_ a′ a″ a b′ b″ b T : Set where
--   field
--     ra    : D
--     rb    : D
--     ↘ra   : rec T , a′ , a″ , a ↘ ra
--     ↘rb   : rec T , b′ , b″ , b ↘ rb
--     raTrb : ⟦ T ⟧T ra rb

-- ≈⟦⟧-sym : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
--           ----------------
--           ρ′ ≈ ρ ∈⟦ Γ ⟧
-- ≈⟦⟧-sym ρ≈ {_} {T} T∈Γ = ⟦⟧-sym T (ρ≈ T∈Γ)

-- ≈⟦⟧-refl : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
--            ----------------
--            ρ ≈ ρ ∈⟦ Γ ⟧
-- ≈⟦⟧-refl ρ≈ {_} {T} T∈Γ = ⟦⟧≈refl T (ρ≈ T∈Γ)

-- ≈-refl : Γ ⊨ t ∶ T →
--          --------------
--          Γ ⊨ t ≈ t ∶ T
-- ≈-refl t = t




-- rec-helper : ρ ≈ ρ′ ∈⟦ Γ ⟧ →
--                   (s≈ : ⟦ s ⟧ ρ ≈⟦ s′ ⟧ ρ′ ∈ T) →
--                   (r≈ : ⟦ r ⟧ ρ ≈⟦ r′ ⟧ ρ′ ∈ N ⟶ T ⟶ T) →
--                   a ≈ b ∈N →
--                   rec Intp.⟦s⟧ s≈ , Intp.⟦s⟧ r≈ , a ≈rec Intp.⟦t⟧ s≈ , Intp.⟦t⟧ r≈ , b ∈ T
-- rec-helper ρ≈ s≈ r≈ ze-≈             = record
--   { ra    = ⟦s⟧
--   ; rb    = ⟦t⟧
--   ; ↘ra   = rze
--   ; ↘rb   = rze
--   ; raTrb = s≈t
--   }
--   where open Intp s≈
-- rec-helper ρ≈ s≈ r≈ (su-≈ a≈b)       = record
--   { ra    = r″≈.fa
--   ; rb    = r″≈.fa′
--   ; ↘ra   = rsu ↘ra r′≈.↘fa r″≈.↘fa
--   ; ↘rb   = rsu ↘rb r′≈.↘fa′ r″≈.↘fa′
--   ; raTrb = r″≈.fa≈fa′
--   }
--   where open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ s≈ r≈ a≈b)
--         module r≈  = Intp r≈
--         r′≈        = r≈.s≈t a≈b
--         module r′≈ = FAppIn r′≈
--         r″≈        = r′≈.fa≈fa′ raTrb
--         module r″≈ = FAppIn r″≈
-- rec-helper {T = T} ρ≈ s≈ r≈ (↑N e≈e′) = record
--   { ra    = _
--   ; rb    = _
--   ; ↘ra   = rec
--   ; ↘rb   = rec
--   ; raTrb = Bot⇒⟦⟧ T λ n → let w  , ↘w  , ↘w′ = ⟦⟧⇒Top T s≈.s≈t n
--                                w′ , ↘w″ , ↘w‴ = ⟦⟧⇒Top (N ⟶ T ⟶ T) r≈.s≈t n
--                                u  , ↘u  , ↘u′ = e≈e′ n
--                            in rec T w w′ u
--                             , Rr n ↘w ↘w″ ↘u
--                             , Rr n ↘w′ ↘w‴ ↘u′
--   }
--   where module s≈ = Intp s≈
--         module r≈ = Intp r≈

-- rec-cong : Γ ⊨ s ≈ s′ ∶ T →
--            Γ ⊨ r ≈ r′ ∶ N ⟶ T ⟶ T →
--            Γ ⊨ t ≈ t′ ∶ N →
--            --------------------------------------
--            Γ ⊨ rec T s r t ≈ rec T s′ r′ t′ ∶ T
-- rec-cong s≈ r≈ t≈ ρ≈ = record
--   { ⟦s⟧  = ra
--   ; ⟦t⟧  = rb
--   ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ t≈.↘⟦s⟧ ↘ra
--   ; ↘⟦t⟧ = ⟦rec⟧ s≈.↘⟦t⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ ↘rb
--   ; s≈t  = raTrb
--   }
--   where sρ≈ = s≈ ρ≈
--         rρ≈ = r≈ ρ≈
--         tρ≈ = t≈ ρ≈
--         module s≈ = Intp sρ≈
--         module r≈ = Intp rρ≈
--         module t≈ = Intp tρ≈
--         open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ sρ≈ rρ≈ t≈.s≈t)

-- rec-β-ze : Γ ⊨ s ∶ T →
--            Γ ⊨ r ∶ N ⟶ T ⟶ T →
--            -------------------------
--            Γ ⊨ rec T s r ze ≈ s ∶ T
-- rec-β-ze s≈ r≈ ρ≈ = record
--   { ⟦s⟧  = s≈.⟦s⟧
--   ; ⟦t⟧  = s≈.⟦t⟧
--   ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ ⟦ze⟧ rze
--   ; ↘⟦t⟧ = s≈.↘⟦t⟧
--   ; s≈t  = s≈.s≈t
--   }
--   where module s≈ = Intp (s≈ ρ≈)
--         module r≈ = Intp (r≈ ρ≈)

-- rec-β-su : Γ ⊨ s ∶ T →
--            Γ ⊨ r ∶ N ⟶ T ⟶ T →
--            Γ ⊨ t ∶ N →
--            -----------------------------------------------------
--            Γ ⊨ rec T s r (su t) ≈ r $ t $ (rec T s r t) ∶ T
-- rec-β-su s≈ r≈ t≈ ρ≈ = record
--   { ⟦s⟧  = r″≈.fa
--   ; ⟦t⟧  = r″≈.fa′
--   ; ↘⟦s⟧ = ⟦rec⟧ s≈.↘⟦s⟧ r≈.↘⟦s⟧ (⟦su⟧ t≈.↘⟦s⟧) (rsu ↘ra r′≈.↘fa r″≈.↘fa)
--   ; ↘⟦t⟧ = ⟦$⟧ (⟦$⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ r′≈.↘fa′) (⟦rec⟧ s≈.↘⟦t⟧ r≈.↘⟦t⟧ t≈.↘⟦t⟧ ↘rb) r″≈.↘fa′
--   ; s≈t  = r″≈.fa≈fa′
--   }
--   where module s≈  = Intp (s≈ ρ≈)
--         module r≈  = Intp (r≈ ρ≈)
--         module t≈  = Intp (t≈ ρ≈)
--         open rec_,_,_≈rec_,_,_∈_ (rec-helper ρ≈ (s≈ ρ≈) (r≈ ρ≈) t≈.s≈t)
--         module r′≈ = FAppIn (r≈.s≈t t≈.s≈t)
--         module r″≈ = FAppIn (r′≈.fa≈fa′ raTrb)

-- rec-[] : Γ ⊨s σ ∶ Δ →
--          Δ ⊨ s ∶ T →
--          Δ ⊨ r ∶ N ⟶ T ⟶ T →
--          Δ ⊨ t ∶ N →
--          -----------------------------------------------------------------
--          Γ ⊨ rec T s r t [ σ ] ≈ rec T (s [ σ ]) (r [ σ ]) (t [ σ ]) ∶ T
-- rec-[] σ s r t ρ≈ = record
--   { ⟦s⟧  = ra
--   ; ⟦t⟧  = rb
--   ; ↘⟦s⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦rec⟧ s.↘⟦s⟧ r.↘⟦s⟧ t.↘⟦s⟧ ↘ra)
--   ; ↘⟦t⟧ = ⟦rec⟧ (⟦[]⟧ ↘⟦τ⟧ s.↘⟦t⟧) (⟦[]⟧ ↘⟦τ⟧ r.↘⟦t⟧) (⟦[]⟧ ↘⟦τ⟧ t.↘⟦t⟧) ↘rb
--   ; s≈t  = raTrb
--   }
--   where open Intps (σ ρ≈)
--         module s = Intp (s σ≈τ)
--         module r = Intp (r σ≈τ)
--         module t = Intp (t σ≈τ)
--         open rec_,_,_≈rec_,_,_∈_ (rec-helper σ≈τ (s σ≈τ) (r σ≈τ) t.s≈t)

-- s-≈-refl : Γ ⊨s σ ∶ Γ →
--            ----------------
--            Γ ⊨s σ ≈ σ ∶ Γ
-- s-≈-refl σ = σ

-- s-≈-sym : Γ ⊨s σ ≈ σ′ ∶ Δ →
--           ------------------
--           Γ ⊨s σ′ ≈ σ ∶ Δ
-- s-≈-sym σ≈ ρ≈ = record
--   { ⟦σ⟧  = ⟦τ⟧
--   ; ⟦τ⟧  = ⟦σ⟧
--   ; ↘⟦σ⟧ = ↘⟦τ⟧
--   ; ↘⟦τ⟧ = ↘⟦σ⟧
--   ; σ≈τ  = ≈⟦⟧-sym σ≈τ
--   }
--   where open Intps (σ≈ (≈⟦⟧-sym ρ≈))

-- s-≈-trans : Γ ⊨s σ ≈ σ′ ∶ Δ →
--             Γ ⊨s σ′ ≈ σ″ ∶ Δ →
--             -------------------
--             Γ ⊨s σ ≈ σ″ ∶ Δ
-- s-≈-trans σ≈ σ′≈ ρ≈ = record
--   { ⟦σ⟧  = σ≈.⟦σ⟧
--   ; ⟦τ⟧  = σ′≈.⟦τ⟧
--   ; ↘⟦σ⟧ = σ≈.↘⟦σ⟧
--   ; ↘⟦τ⟧ = σ′≈.↘⟦τ⟧
--   ; σ≈τ  = λ {_} {T} T∈Γ → ⟦⟧-trans T
--                                     (σ≈.σ≈τ T∈Γ)
--                                     (subst (λ f → ⟦ T ⟧T (f _) _) (⟦⟧s-det σ′≈.↘⟦σ⟧ σ≈.↘⟦τ⟧) (σ′≈.σ≈τ T∈Γ))
--   }
--   where module σ≈  = Intps (σ≈ (≈⟦⟧-refl ρ≈))
--         module σ′≈ = Intps (σ′≈ ρ≈)

-- ∘-cong : Γ ⊨s τ ≈ τ′ ∶ Γ′ →
--          Γ′ ⊨s σ ≈ σ′ ∶ Γ″ →
--          --------------------------
--          Γ ⊨s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
-- ∘-cong τ≈ σ≈ ρ≈ = record
--   { ⟦σ⟧  = σ≈.⟦σ⟧
--   ; ⟦τ⟧  = σ≈.⟦τ⟧
--   ; ↘⟦σ⟧ = ⟦∘⟧ τ≈.↘⟦σ⟧ σ≈.↘⟦σ⟧
--   ; ↘⟦τ⟧ = ⟦∘⟧ τ≈.↘⟦τ⟧ σ≈.↘⟦τ⟧
--   ; σ≈τ  = σ≈.σ≈τ
--   }
--   where module τ≈ = Intps (τ≈ ρ≈)
--         module σ≈ = Intps (σ≈ τ≈.σ≈τ)

-- ↑-≈ : S ∷ Γ ⊨s ↑ ≈ ↑ ∶ Γ
-- ↑-≈ {ρ = ρ} {ρ′} ρ≈ = record
--   { ⟦σ⟧  = drop ρ
--   ; ⟦τ⟧  = drop ρ′
--   ; ↘⟦σ⟧ = ⟦↑⟧
--   ; ↘⟦τ⟧ = ⟦↑⟧
--   ; σ≈τ  = λ T∈Γ → ρ≈ (there T∈Γ)
--   }

-- I-≈ : Γ ⊨s I ≈ I ∶ Γ
-- I-≈ ρ≈ = record
--   { ⟦σ⟧  = _
--   ; ⟦τ⟧  = _
--   ; ↘⟦σ⟧ = ⟦I⟧
--   ; ↘⟦τ⟧ = ⟦I⟧
--   ; σ≈τ  = ρ≈
--   }

-- ,-cong : Γ ⊨s σ ≈ σ′ ∶ Δ →
--          Γ ⊨ s ≈ s′ ∶ S →
--          -----------------------------
--          Γ ⊨s σ , s ≈ σ′ , s′ ∶ S ∷ Δ
-- ,-cong σ≈ s≈ ρ≈ = record
--   { ⟦σ⟧  = σ≈.⟦σ⟧ ↦ s≈.⟦s⟧
--   ; ⟦τ⟧  = σ≈.⟦τ⟧ ↦ s≈.⟦t⟧
--   ; ↘⟦σ⟧ = ⟦,⟧ σ≈.↘⟦σ⟧ s≈.↘⟦s⟧
--   ; ↘⟦τ⟧ = ⟦,⟧ σ≈.↘⟦τ⟧ s≈.↘⟦t⟧
--   ; σ≈τ  = helper
--   }
--   where module σ≈ = Intps (σ≈ ρ≈)
--         module s≈ = Intp (s≈ ρ≈)
--         helper : σ≈.⟦σ⟧ ↦ s≈.⟦s⟧ ≈ σ≈.⟦τ⟧ ↦ s≈.⟦t⟧ ∈⟦ _ ∷ _ ⟧
--         helper here        = s≈.s≈t
--         helper (there T∈Δ) = σ≈.σ≈τ T∈Δ

-- ↑-∘-, : Γ ⊨s σ ∶ Δ →
--         Γ ⊨ s ∶ S →
--         --------------------------
--         Γ ⊨s ↑ ∘ (σ , s) ≈ σ ∶ Δ
-- ↑-∘-, σ s ρ≈ = record
--   { ⟦σ⟧  = ⟦σ⟧
--   ; ⟦τ⟧  = ⟦τ⟧
--   ; ↘⟦σ⟧ = ⟦∘⟧ (⟦,⟧ ↘⟦σ⟧ ↘⟦s⟧) ⟦↑⟧
--   ; ↘⟦τ⟧ = ↘⟦τ⟧
--   ; σ≈τ  = σ≈τ
--   }
--   where open Intps (σ ρ≈)
--         open Intp (s ρ≈)

-- I-∘ : Γ ⊨s σ ∶ Δ →
--       --------------------
--       Γ ⊨s I ∘ σ ≈ σ ∶ Δ
-- I-∘ σ ρ≈ = record
--   { ⟦σ⟧  = ⟦σ⟧
--   ; ⟦τ⟧  = ⟦τ⟧
--   ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ ⟦I⟧
--   ; ↘⟦τ⟧ = ↘⟦τ⟧
--   ; σ≈τ  = σ≈τ
--   }
--   where open Intps (σ ρ≈)

-- ∘-I : Γ ⊨s σ ∶ Δ →
--       --------------------
--       Γ ⊨s σ ∘ I ≈ σ ∶ Δ
-- ∘-I σ ρ≈ = record
--   { ⟦σ⟧  = ⟦σ⟧
--   ; ⟦τ⟧  = ⟦τ⟧
--   ; ↘⟦σ⟧ = ⟦∘⟧ ⟦I⟧ ↘⟦σ⟧
--   ; ↘⟦τ⟧ = ↘⟦τ⟧
--   ; σ≈τ  = σ≈τ
--   }
--   where open Intps (σ ρ≈)

-- ∘-assoc : ∀ {Γ‴} →
--           Γ′ ⊨s σ ∶ Γ →
--           Γ″ ⊨s σ′ ∶ Γ′ →
--           Γ‴ ⊨s σ″ ∶ Γ″ →
--           ---------------------------------------
--           Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
-- ∘-assoc σ σ′ σ″ ρ≈ = record
--   { ⟦σ⟧  = σ.⟦σ⟧
--   ; ⟦τ⟧  = σ.⟦τ⟧
--   ; ↘⟦σ⟧ = ⟦∘⟧ σ″.↘⟦σ⟧ (⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧)
--   ; ↘⟦τ⟧ = ⟦∘⟧ (⟦∘⟧ σ″.↘⟦τ⟧ σ′.↘⟦τ⟧) σ.↘⟦τ⟧
--   ; σ≈τ  = σ.σ≈τ
--   }
--   where module σ″ = Intps (σ″ ρ≈)
--         module σ′ = Intps (σ′ σ″.σ≈τ)
--         module σ  = Intps (σ σ′.σ≈τ)

-- I-ext : S ∷ Γ ⊨s I ≈ ↑ , v 0 ∶ S ∷ Γ
-- I-ext ρ≈ = record
--   { ⟦σ⟧  = _
--   ; ⟦τ⟧  = _
--   ; ↘⟦σ⟧ = ⟦I⟧
--   ; ↘⟦τ⟧ = ⟦,⟧ ⟦↑⟧ (⟦v⟧ 0)
--   ; σ≈τ  = helper ρ≈
--   }
--   where helper : ρ ≈ ρ′ ∈⟦ S ∷ Γ ⟧ → ρ ≈ drop ρ′ ↦ ρ′ 0 ∈⟦ S ∷ Γ ⟧
--         helper ρ≈ here        = ρ≈ here
--         helper ρ≈ (there T∈Γ) = ρ≈ (there T∈Γ)

-- ,-ext : Γ ⊨s σ ∶ S ∷ Δ →
--         --------------------------------------
--         Γ ⊨s σ ≈ (↑ ∘ σ) , v 0 [ σ ] ∶ S ∷ Δ
-- ,-ext σ ρ≈ = record
--   { ⟦σ⟧  = ⟦σ⟧
--   ; ⟦τ⟧  = drop ⟦τ⟧ ↦ ⟦τ⟧ 0
--   ; ↘⟦σ⟧ = ↘⟦σ⟧
--   ; ↘⟦τ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦τ⟧ ⟦↑⟧) (⟦[]⟧ ↘⟦τ⟧ (⟦v⟧ 0))
--   ; σ≈τ  = helper σ≈τ
--   }
--   where open Intps (σ ρ≈)
--         helper : ρ ≈ ρ′ ∈⟦ S ∷ Γ ⟧ → ρ ≈ drop ρ′ ↦ ρ′ 0 ∈⟦ S ∷ Γ ⟧
--         helper ρ≈ here        = ρ≈ here
--         helper ρ≈ (there T∈Γ) = ρ≈ (there T∈Γ)

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
--     let (w , ↘w , ↘w′) = TTop T s≈t n in
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
--     sem-sound T.ze-I          = ze-≈′
--     sem-sound (T.su-I t)      = su-cong (sem-sound t)
--     sem-sound (T.N-E s r t)   = rec-cong (sem-sound s) (sem-sound r) (sem-sound t)
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
--     ≈sem-sound T.ze-≈                      = ze-≈′
--     ≈sem-sound (T.su-cong s≈t)             = su-cong (≈sem-sound s≈t)
--     ≈sem-sound (T.rec-cong s≈s′ r≈r′ t≈t′) = rec-cong (≈sem-sound s≈s′) (≈sem-sound r≈r′) (≈sem-sound t≈t′)
--     ≈sem-sound (T.Λ-cong s≈t)              = Λ-cong (≈sem-sound s≈t)
--     ≈sem-sound (T.$-cong t≈t′ s≈s′)        = $-cong (≈sem-sound t≈t′) (≈sem-sound s≈s′)
--     ≈sem-sound (T.[]-cong σ≈τ s≈t)         = []-cong (≈sem-s-sound σ≈τ) (≈sem-sound s≈t)
--     ≈sem-sound (T.ze-[] σ)                 = ze-[] (sem-s-sound σ)
--     ≈sem-sound (T.su-[] σ t)               = su-[] (sem-s-sound σ) (sem-sound t)
--     ≈sem-sound (T.Λ-[] σ t)                = Λ-[] (sem-s-sound σ) (sem-sound t)
--     ≈sem-sound (T.$-[] σ r s)              = $-[] (sem-s-sound σ) (sem-sound r) (sem-sound s)
--     ≈sem-sound (T.rec-[] σ s r t)          = rec-[] (sem-s-sound σ) (sem-sound s) (sem-sound r) (sem-sound t)
--     ≈sem-sound (T.rec-β-ze s r)            = rec-β-ze (sem-sound s) (sem-sound r)
--     ≈sem-sound (T.rec-β-su s r t)          = rec-β-su (sem-sound s) (sem-sound r) (sem-sound t)
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
