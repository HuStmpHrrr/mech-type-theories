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

⟦_⟧Γ : Env → Ev
⟦ []    ⟧Γ _ = ⊤
⟦ T ∷ Γ ⟧Γ ρ = ρ 0 ∈! ⟦ T ⟧T × ⟦ Γ ⟧Γ (drop ρ)

N-sym : a ≈ b ∈N → b ≈ a ∈N
N-sym ze-≈      = ze-≈
N-sym (su-≈ ab) = su-≈ (N-sym ab)
N-sym (↑N ⊥)    = ↑N (λ n → let u , ↘u , ↘u′ = ⊥ n in u , ↘u′ , ↘u)

N-trans : a ≈ a′ ∈N → a′ ≈ a″ ∈N → a ≈ a″ ∈N
N-trans ze-≈ ze-≈            = ze-≈
N-trans (su-≈ eq) (su-≈ eq′) = su-≈ (N-trans eq eq′)
N-trans (↑N ⊥e) (↑N ⊥e′)     = ↑N λ n → let u , ↘u , e′↘ = ⊥e n
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
  { fa     = fxUf′y.fa
  ; fa′    = f′xUf″y.fa′
  ; ↘fa    = fxUf′y.↘fa
  ; ↘fa′   = f′xUf″y.↘fa′
  ; faTfa′ = trans′ fxUf′y.faTfa′
            (trans′ (subst (λ a → ⟦ U ⟧T a fyUf′y.fa) (ap-det fyUf′y.↘fa′ fxUf′y.↘fa′) (⟦⟧-sym U fyUf′y.faTfa′))
            (trans′ (subst₂ ⟦ U ⟧T
                            (ap-det fyUf′x.↘fa fyUf′y.↘fa)
                            (ap-det fyUf′x.↘fa′ f′xUf″y.↘fa)
                            (fyUf′x.faTfa′))
                    f′xUf″y.faTfa′))
  }
  where trans′ : ∀ {a b d} → ⟦ U ⟧T a b → ⟦ U ⟧T b d → ⟦ U ⟧T a d
        trans′         = ⟦⟧-trans U
        ySx            = ⟦⟧-sym S xSy
        ySy            = ⟦⟧-trans S ySx xSy
        module fxUf′y  = FAppIn (fFf′ xSy)
        module fyUf′y  = FAppIn (fFf′ ySy)
        module fyUf′x  = FAppIn (fFf′ ySx)
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
