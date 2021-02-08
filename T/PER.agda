{-# OPTIONS --without-K --safe #-}

module T.PER where

open import Relation.Binary using (PartialSetoid; IsPartialEquivalence)

open import Lib
open import T.Statics
open import T.Semantics

Ty : Set₁
Ty = D → D → Set

Ev : Set₁
Ev = Ctx → Set

infix 8 _∈!_
_∈!_ : D → Ty → Set
d ∈! T = T d d

Top : Ty
Top d d′ = ∀ n → ∃ λ w → Rf n - d ↘ w × Rf n - d′ ↘ w

Bot : Dn → Dn → Set
Bot e e′ = ∀ n → ∃ λ u → Re n - e ↘ u × Re n - e′ ↘ u

data _≈_∈N : Ty where
  ze-≈ : ze ≈ ze ∈N
  su-≈ : d ≈ d′ ∈N →
         -------------------
         su d ≈ su d′ ∈N
  ne   : Bot e e′ →
         -----------------------------------------------
         ne e ≈ ne e′ ∈N

record _∙_≈_∙_∈_ (f a f′ a′ : D) (T : Ty) : Set where
  constructor
    _-_-_-_-_

  field
    fa fa′ : D
    ↘fa    : f ∙ a ↘ fa
    ↘fa′   : f′ ∙ a′ ↘ fa′
    faTfa′ : T fa fa′

module FApp {f a f′ a′ T} (r : f ∙ a ≈ f′ ∙ a′ ∈ T)  = _∙_≈_∙_∈_ r

_≈_∈_⇒_ : D → D → Ty → Ty → Set
f ≈ f′ ∈ S ⇒ T =
  ∀ {a a′} → S a a′ → f ∙ a ≈ f′ ∙ a′ ∈ T

infixr 5 _⇒_
_⇒_ : Ty → Ty → Ty
(S ⇒ U) a b = a ≈ b ∈ S ⇒ U

⟦_⟧T : Typ → Ty
⟦ N ⟧T     = _≈_∈N
⟦ S ⟶ U ⟧T = ⟦ S ⟧T ⇒ ⟦ U ⟧T

⟦_⟧Γ : Env → Ev
⟦ []    ⟧Γ _ = ⊤
⟦ T ∷ Γ ⟧Γ ρ = ρ 0 ∈! ⟦ T ⟧T × ⟦ Γ ⟧Γ (drop ρ)

N-sym : a ≈ b ∈N → b ≈ a ∈N
N-sym ze-≈      = ze-≈
N-sym (su-≈ ab) = su-≈ (N-sym ab)
N-sym (ne ⊥)    = ne (λ n → let u , ↘u , ↘u′ = ⊥ n in u , ↘u′ , ↘u)

⟦⟧-sym : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T b a
⟦⟧-sym N ab          = N-sym ab
⟦⟧-sym (S ⟶ U) ab ∈S = record
  { fa     = fa′
  ; fa′    = fa
  ; ↘fa    = ↘fa′
  ; ↘fa′   = ↘fa
  ; faTfa′ = ⟦⟧-sym U faTfa′
  }
  where open FApp (ab (⟦⟧-sym S ∈S))

N-trans : a ≈ b ∈N → b ≈ d ∈N → a ≈ d ∈N
N-trans ze-≈ ze-≈            = ze-≈
N-trans (su-≈ eq) (su-≈ eq′) = su-≈ (N-trans eq eq′)
N-trans (ne ⊥e) (ne ⊥e′)     = ne λ n → let u , ↘u , e′↘ = ⊥e n
                                            _ , e′↘′ , ↘u′ = ⊥e′ n
                                        in u , ↘u , subst (Re n - _ ↘_) (Re-det e′↘′ e′↘) ↘u′

⟦⟧-trans : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T b d → ⟦ T ⟧T a d
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
        module fxUf′y  = FApp (fFf′ xSy)
        module fyUf′y  = FApp (fFf′ ySy)
        module fyUf′x  = FApp (fFf′ ySx)
        module f′xUf″y = FApp (f′Ff″ xSy)

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

mutual
  Bot⇒⟦⟧ : ∀ T → Bot e e′ → ⟦ T ⟧T (ne e) (ne e′)
  Bot⇒⟦⟧     N       ⊥e             = ne ⊥e
  Bot⇒⟦⟧ {e} {e′} (S ⟶ U) ⊥e {x} {y} xSy = record
    { fa     = e $′ x
    ; fa′    = e′ $′ y
    ; ↘fa    = $∙ e x
    ; ↘fa′   = $∙ e′ y
    ; faTfa′ = Bot⇒⟦⟧ U λ n →
               let u , ↘u , ↘u′ = ⊥e n
                   w , x↘ , y↘  = ⟦⟧⇒Top S xSy n
               in u $ w , R$ n ↘u x↘ , R$ n ↘u′ y↘
    }

  ⟦⟧⇒Top : ∀ T → ⟦ T ⟧T d d′ → Top d d′
  ⟦⟧⇒Top N ze-≈ n                                              = ze , Rze n , Rze n
  ⟦⟧⇒Top N (su-≈ dTd′) n
    with ⟦⟧⇒Top N dTd′ n
  ...  | w , ↘w , ↘w′                                          = su w , Rsu n ↘w , Rsu n ↘w′
  ⟦⟧⇒Top N (ne ⊥e) n
    with ⊥e n
  ...  | u , ↘u , ↘u′                                          = ne u , Rne n ↘u , Rne n ↘u′
  ⟦⟧⇒Top (S ⟶ U) dTd′ n
    with dTd′ {l′ n} {l′ n} (Bot⇒⟦⟧ S λ m → -, Rl m n , Rl m n)
  ⟦⟧⇒Top (S ⟶ U) dTd′ n
       | fa - fa′ - Λ∙ ↘fa - Λ∙ ↘fa′ - faUfa′                   = let w , ↘w , ↘w′ = ⟦⟧⇒Top U faUfa′ (suc n)
                                                                  in Λ w , RΛ n ↘fa ↘w , RΛ n ↘fa′ ↘w′
  ⟦⟧⇒Top (S ⟶ U) dTd′ n
       | fa - .(e $′ l′ n) - Λ∙ x - $∙ e .(l′ n) - faUfa′
       with ⟦⟧⇒Top U faUfa′ n
  ... | u $′ _ , Rne .n (R$ .n f↘ a↘) , Rne .n (R$ .n ↘u _) = {!!}
  ⟦⟧⇒Top (S ⟶ U) dTd′ n
       | .(e $′ l′ n) - fa′ - $∙ e .(l′ n) - Λ∙ x - faUfa′      = {!!}
  ⟦⟧⇒Top (S ⟶ U) dTd′ n
       | _ - _ - $∙ e .(l′ n) - $∙ e′ .(l′ n) - faUfa′
       with ⟦⟧⇒Top U faUfa′ n
  ...     | .(_ $′ _) , Rne .n (R$ .n ↘w _) , Rne .n (R$ .n ↘w′ _) = -, Rne n ↘w , Rne n ↘w′
