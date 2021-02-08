{-# OPTIONS --without-K --safe #-}

module T.Equivalence where

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

module Refl where
  _≈_∈_⇒_ : D → D → Ty → Ty → Set
  f ≈ f′ ∈ S ⇒ T =
    ∀ {a} → S a a → ∃₂ λ b b′ → f ∙ a ↘ b × f′ ∙ a ↘ b′ × T b b′

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
  ⟦⟧-sym N ab                   = N-sym ab
  ⟦⟧-sym (S ⟶ U) ab ∈S
    with ab ∈S
  ...  | b , b′ , ↘b , ↘b′ , ∈U = b′ , b , ↘b′ , ↘b , ⟦⟧-sym U ∈U

  N-trans : a ≈ b ∈N → b ≈ d ∈N → a ≈ d ∈N
  N-trans ze-≈ ze-≈            = ze-≈
  N-trans (su-≈ eq) (su-≈ eq′) = su-≈ (N-trans eq eq′)
  N-trans (ne ⊥e) (ne ⊥e′)     = ne λ n → let u , ↘u , e′↘ = ⊥e n
                                              _ , e′↘′ , ↘u′ = ⊥e′ n
                                          in u , ↘u , subst (Re n - _ ↘_) (Re-det e′↘′ e′↘) ↘u′

  ⟦⟧-trans : ∀ T → ⟦ T ⟧T a b → ⟦ T ⟧T b d → ⟦ T ⟧T a d
  ⟦⟧-trans N eq eq′                = N-trans eq eq′
  ⟦⟧-trans (S ⟶ U) eq eq′ ∈S
    with eq ∈S | eq′ ∈S
  ...  | a  , b  , ↘a  , ↘b  , ∈U
       | a′ , b′ , ↘a′ , ↘b′ , ∈U′ = a , b′ , ↘a , ↘b′ , ⟦⟧-trans U (subst (⟦ U ⟧T a) (ap-det ↘b ↘a′) ∈U) ∈U′

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

  mutual
    Bot⇒⟦⟧ : ∀ T → Bot e e → ne e ∈! ⟦ T ⟧T
    Bot⇒⟦⟧     N       ⊥e        = ne ⊥e
    Bot⇒⟦⟧ {e} (S ⟶ U) ⊥e {a} ∈S = e $′ a
                                 , e $′ a
                                 , $∙ e a
                                 , $∙ e a
                                 , Bot⇒⟦⟧ U λ n → let u , ↘u , _   = ⊥e n
                                                      u′ , ↘u′ , _ = ⟦⟧⇒Top S ∈S n
                                                      ↘$           = R$ n ↘u ↘u′
                                                  in u $ u′ , ↘$ , ↘$

    ⟦⟧⇒Top : ∀ T → d ∈! ⟦ T ⟧T → d ∈! Top
    ⟦⟧⇒Top N ze-≈ n                                      = ze , Rze n , Rze n
    ⟦⟧⇒Top N (su-≈ d∈) n
      with ⟦⟧⇒Top N d∈ n
    ...  | w , ↘w , ↘w′                                  = su w , Rsu n ↘w , Rsu n ↘w′
    ⟦⟧⇒Top N (ne ⊥e) n
      with ⊥e n
    ...  | u , ↘u , ↘u′                                  = ne u , Rne n ↘u , Rne n ↘u′
    ⟦⟧⇒Top (S ⟶ U) d∈ n
      with d∈ {l′ n} (Bot⇒⟦⟧ S λ m → -, Rl m n , Rl m n)
    ...  | a , a′ , Λ∙ ↘a , Λ∙ ↘a′ , ∈U
         with ⟦⟧-det ↘a ↘a′
    ...     | refl                                       = let _ , w , w′ = ⟦⟧⇒Top U ∈U (suc n) in
                                                           -, RΛ n ↘a w , RΛ n ↘a′ w′
    ⟦⟧⇒Top (S ⟶ U) d∈ n
         | _ , _ , $∙ e .(l′ n) , $∙ .e .(l′ n) , ∈U
         with ⟦⟧⇒Top U ∈U n
    ... | _ , Rne .n (R$ .n e↘ _) , Rne .n (R$ .n e↘′ _) = -, Rne n e↘ , Rne n e↘′

  rec_,_,_∈_ : D → D → D → Ty → Set
  rec d′ , d″ , d ∈ T = ∃ λ b → b ∈! T × rec d′ , d″ , d ↘ b

  ⟦_⟧_∈_ : Exp → Ctx → Ty → Set
  ⟦ t ⟧ ρ ∈ T = ∃ λ b → b ∈! T × ⟦ t ⟧ ρ ↘ b

  ⟦_⟧s_∈_ : Subst → Ctx → Ev → Set
  ⟦ σ ⟧s ρ ∈ Γ = ∃ λ τ → Γ τ × ⟦ σ ⟧s ρ ↘ τ

  infix 4 _⊨_∶_ _⊨s_∶_
  _⊨_∶_ : Env → Exp → Typ → Set
  Γ ⊨ t ∶ T = ∀ ρ → ⟦ Γ ⟧Γ ρ → ⟦ t ⟧ ρ ∈ ⟦ T ⟧T

  _⊨s_∶_ : Env → Subst → Env → Set
  Γ ⊨s σ ∶ Δ = ∀ ρ → ⟦ Γ ⟧Γ ρ → ⟦ σ ⟧s ρ ∈ ⟦ Δ ⟧Γ

  vlookup : ∀ {x} →
            x ∶ T ∈ Γ →
            ------------
            Γ ⊨ v x ∶ T
  vlookup here        ρ (d , Γ)   = ρ 0 , d , ⟦v⟧ zero
  vlookup (there T∈Γ) ρ (_ , Γ)
    with vlookup T∈Γ (drop ρ) Γ
  ... | .(ρ (suc _)) , Tb , ⟦v⟧ _ = -, Tb , ⟦v⟧ (suc _)

  Λ-I : S ∷ Γ ⊨ t ∶ T →
        ---------------
        Γ ⊨ Λ t ∶ S ⟶ T
  Λ-I {S} {_} {t} t∶T ρ Γ = Λ t ρ
                          , (λ ∈S → let (dt , Td , ap) = t∶T (ρ ↦ _) (∈S , Γ)
                                    in dt , dt , Λ∙ ap , Λ∙ ap , Td)
                          , ⟦Λ⟧ t

  Λ-E : Γ ⊨ r ∶ S ⟶ T →
        Γ ⊨ s ∶ S →
        ----------------
        Γ ⊨ r $ s ∶ T
  Λ-E r∶F s∶S ρ Γ
    with r∶F ρ Γ | s∶S ρ Γ
  ...  | dr , Fr , ir
       | ds , Ss , is
       with Fr Ss
  ... | rs , _ , ap , ap′ , Trs = rs , subst _ (ap-det ap′ ap) Trs , ⟦$⟧ ir is ap

  ze-I : Γ ⊨ ze ∶ N
  ze-I ρ Γ = ze , ze-≈ , ⟦ze⟧

  su-I : Γ ⊨ t ∶ N →
         -------------
         Γ ⊨ su t ∶ N
  su-I t ρ Γ
    with t ρ Γ
  ...  | d , Nd , ↘d = su d , su-≈ Nd , ⟦su⟧ ↘d

  N-E-helper : ∀ {n} T →
               ⟦ Γ ⟧Γ ρ →
               (s∶T : ⟦ s ⟧ ρ ∈ ⟦ T ⟧T)
               (r∶F : ⟦ r ⟧ ρ ∈ ⟦ N ⟶ T ⟶ T ⟧T) →
               n ∈! ⟦ N ⟧T →
               rec proj₁ s∶T , proj₁ r∶F , n ∈ ⟦ T ⟧T
  N-E-helper T Γ (ds , Ts , _) r ze-≈               = ds , Ts , rze
  N-E-helper T Γ s r@(dr , Fr , ir) (su-≈ n)
    with N-E-helper T Γ s r n
  ...  | dn , Tn , rn
       with Fr n
  ...     | da , _ , ap , ap′ , Fr′
          with ap-det ap ap′
  ...        | refl
             with Fr′ Tn
  ...           | db , _ , ap″ , ap‴ , Tb
                with ap-det ap″ ap‴
  ...              | refl                           = db , Tb , rsu rn ap ap″
  N-E-helper T Γ (ds , Ts , _) (dr , Fr , _) (ne n) = rec′ ds dr _
                                                    , Bot⇒⟦⟧ T (λ m → let _ , ↘w , _  = ⟦⟧⇒Top T Ts m
                                                                          _ , ↘w′ , _ = ⟦⟧⇒Top (N ⟶ T ⟶ T) Fr m
                                                                          _ , ↘u , _  = n m
                                                                      in _
                                                                       , Rr m ↘w ↘w′ ↘u
                                                                       , Rr m ↘w ↘w′ ↘u)
                                                    , rec

  N-E : Γ ⊨ s ∶ T →
        Γ ⊨ r ∶ N ⟶ T ⟶ T →
        Γ ⊨ t ∶ N →
        ------------------------
        Γ ⊨ rec s r t ∶ T
  N-E {_} {_} {T} s∶T r∶R t∶N ρ Γ
    with s∶T ρ Γ
       | r∶R ρ Γ
       | t∶N ρ Γ
  ...  | s@(ds , Ts , is)
       | r@(dr , Fr , ir)
       | t@(dt , Nt , it)
       with N-E-helper T Γ s r Nt
  ...     | de , Te , ie = de , Te , ⟦rec⟧ is ir it ie

  t[σ] : Γ ⊨s σ ∶ Δ →
         Δ ⊨ t ∶ T →
         ---------------
         Γ ⊨ t [ σ ] ∶ T
  t[σ] σ t ρ Γ
    with σ ρ Γ
  ...  | δ , Δ , iδ
       with t δ Δ
  ...     | d , Td , id = d , Td , ⟦[]⟧ iδ id

  S-↑ : S ∷ Γ ⊨s ↑ ∶ Γ
  S-↑ ρ (⟦S⟧ , Γ) = drop ρ , Γ , ⟦↑⟧

  S-I : Γ ⊨s I ∶ Γ
  S-I ρ Γ = ρ , Γ , ⟦I⟧

  S-∘ : Γ ⊨s τ ∶ Γ′ →
        Γ′ ⊨s σ ∶ Γ″ →
        ---------------
        Γ ⊨s σ ∘ τ ∶ Γ″
  S-∘ τ σ ρ Γ
      with τ ρ Γ
  ... | γ′ , Γ′ , iγ′
      with σ γ′ Γ′
  ...    | γ″ , Γ″ , iγ″ = γ″ , Γ″ , ⟦∘⟧ iγ′ iγ″

  S-, : Γ ⊨s σ ∶ Δ →
        Γ ⊨ s ∶ S →
        --------------
        Γ ⊨s σ , s ∶ S ∷ Δ
  S-, σ s ρ Γ
    with σ ρ Γ
       | s ρ Γ
  ...  | δ , Δ , iδ
       | d , Sd , id = δ ↦ d , (Sd , Δ) , ⟦,⟧ iδ id

  infix 4 _⊩_≈_∈_ _⊨_≈_∶_

  record _⊩_≈_∈_ ρ s u (T : Ty) : Set where
    field
      ⟦s⟧  : D
      ⟦u⟧  : D
      ∈T   : T ⟦s⟧ ⟦u⟧
      ⟦s⟧↘ : ⟦ s ⟧ ρ ↘ ⟦s⟧
      ⟦u⟧↘ : ⟦ u ⟧ ρ ↘ ⟦u⟧

  _⊨_≈_∶_ : Env → Exp → Exp → Typ → Set
  Γ ⊨ s ≈ u ∶ T = ∀ ρ → ⟦ Γ ⟧Γ ρ → ρ ⊩ s ≈ u ∈ ⟦ T ⟧T

  ≈-refl : Γ ⊨ t ∶ T →
           --------------
           Γ ⊨ t ≈ t ∶ T
  ≈-refl {_} {_} {T} t ρ Γ
    with t ρ Γ
  ...  | dt , Tt , it = record
    { ⟦s⟧  = dt
    ; ⟦u⟧  = dt
    ; ∈T   = Tt
    ; ⟦s⟧↘ = it
    ; ⟦u⟧↘ = it
    }

  ≈-sym : Γ ⊨ t ≈ t′ ∶ T →
          -----------------
          Γ ⊨ t′ ≈ t ∶ T
  ≈-sym {T = T} t≈t′ ρ Γ
    with t≈t′ ρ Γ
  ...  | ⟦t≈t′⟧ = record
    { ⟦s⟧  = ⟦u⟧
    ; ⟦u⟧  = ⟦s⟧
    ; ∈T   = ⟦⟧-sym T ∈T
    ; ⟦s⟧↘ = ⟦u⟧↘
    ; ⟦u⟧↘ = ⟦s⟧↘
    }
    where open _⊩_≈_∈_ ⟦t≈t′⟧

  ≈-trans : Γ ⊨ t ≈ t′ ∶ T →
            Γ ⊨ t′ ≈ t″ ∶ T →
            ------------------
            Γ ⊨ t ≈ t″ ∶ T
  ≈-trans {T = T} t≈t′ t′≈t″ ρ Γ
    with t≈t′ ρ Γ | t′≈t″ ρ Γ
  ...  | ⟦t≈t′⟧ | ⟦t′≈t″⟧ = record
    { ⟦s⟧  = eq₁.⟦s⟧
    ; ⟦u⟧  = eq₂.⟦u⟧
    ; ∈T   = ⟦⟧-trans T eq₁.∈T (subst _ (⟦⟧-det eq₂.⟦s⟧↘ eq₁.⟦u⟧↘) eq₂.∈T)
    ; ⟦s⟧↘ = eq₁.⟦s⟧↘
    ; ⟦u⟧↘ = eq₂.⟦u⟧↘
    }
    where module eq₁ = _⊩_≈_∈_ ⟦t≈t′⟧
          module eq₂ = _⊩_≈_∈_ ⟦t′≈t″⟧

  su-cong : Γ ⊨ t ≈ t′ ∶ N →
            -------------------
            Γ ⊨ su t ≈ su t′ ∶ N
  su-cong t≈t′ ρ Γ
    with t≈t′ ρ Γ
  ...  | ⟦t≈t′⟧ = record
    { ⟦s⟧  = su ⟦s⟧
    ; ⟦u⟧  = su ⟦u⟧
    ; ∈T   = su-≈ ∈T
    ; ⟦s⟧↘ = ⟦su⟧ ⟦s⟧↘
    ; ⟦u⟧↘ = ⟦su⟧ ⟦u⟧↘
    }
    where open _⊩_≈_∈_ ⟦t≈t′⟧


module Gen where

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


  -- mutual
  --   Bot⇒⟦⟧ : ∀ T → Bot e e′ → ⟦ T ⟧T (ne e) (ne e′)
  --   Bot⇒⟦⟧     N       ⊥e             = ne ⊥e
  --   Bot⇒⟦⟧ {e} {e′} (S ⟶ U) ⊥e {x} {y} xSy = record
  --     { fa     = e $′ x
  --     ; fa′    = e′ $′ y
  --     ; ↘fa    = $∙ e x
  --     ; ↘fa′   = $∙ e′ y
  --     ; faTfa′ = Bot⇒⟦⟧ U λ n →
  --                let u , ↘u , ↘u′ = ⊥e n
  --                    w , x↘ , y↘  = ⟦⟧⇒Top S xSy n
  --                in u $ w , R$ n ↘u x↘ , R$ n ↘u′ y↘
  --     }

  --   -- we cannot prove this because read back fails to deal with η expansion
  --   ⟦⟧⇒Top : ∀ T → ⟦ T ⟧T d d′ → Top d d′
  --   ⟦⟧⇒Top N ze-≈ n                                              = ze , Rze n , Rze n
  --   ⟦⟧⇒Top N (su-≈ dTd′) n
  --     with ⟦⟧⇒Top N dTd′ n
  --   ...  | w , ↘w , ↘w′                                          = su w , Rsu n ↘w , Rsu n ↘w′
  --   ⟦⟧⇒Top N (ne ⊥e) n
  --     with ⊥e n
  --   ...  | u , ↘u , ↘u′                                          = ne u , Rne n ↘u , Rne n ↘u′
  --   ⟦⟧⇒Top (S ⟶ U) dTd′ n
  --     with dTd′ {l′ n} {l′ n} (Bot⇒⟦⟧ S λ m → -, Rl m n , Rl m n)
  --   ⟦⟧⇒Top (S ⟶ U) dTd′ n
  --        | fa - fa′ - Λ∙ ↘fa - Λ∙ ↘fa′ - faUfa′                   = let w , ↘w , ↘w′ = ⟦⟧⇒Top U faUfa′ (suc n)
  --                                                                   in Λ w , RΛ n ↘fa ↘w , RΛ n ↘fa′ ↘w′
  --   ⟦⟧⇒Top (S ⟶ U) dTd′ n
  --        | fa - .(e $′ l′ n) - Λ∙ x - $∙ e .(l′ n) - faUfa′
  --        with ⟦⟧⇒Top U faUfa′ n
  --   ... | u $′ _ , Rne .n (R$ .n f↘ a↘) , Rne .n (R$ .n ↘u _) = {!!}
  --   ⟦⟧⇒Top (S ⟶ U) dTd′ n
  --        | .(e $′ l′ n) - fa′ - $∙ e .(l′ n) - Λ∙ x - faUfa′      = {!!}
  --   ⟦⟧⇒Top (S ⟶ U) dTd′ n
  --        | _ - _ - $∙ e .(l′ n) - $∙ e′ .(l′ n) - faUfa′
  --        with ⟦⟧⇒Top U faUfa′ n
  --   ...     | .(_ $′ _) , Rne .n (R$ .n ↘w _) , Rne .n (R$ .n ↘w′ _) = -, Rne n ↘w , Rne n ↘w′
