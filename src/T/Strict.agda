{-# OPTIONS --without-K --safe #-}

module T.Strict where

open import Lib
open import T.Statics
open import T.Semantics

Ty : Set₁
Ty = D → Set

Ev : Set₁
Ev = Env → Set

Top : Ty
Top d = ∀ n → ∃ λ w → Rf n - d ↘ w

Bot : Dn → Set
Bot e = ∀ n → ∃ λ u → Re n - e ↘ u

data Nat : Ty where
  ze : Nat ze
  su : Nat d → Nat (su d)
  ne : Bot e → Nat (ne e)

infixr 5 _⇒_
_⇒_ : Ty → Ty → Ty
(A ⇒ B) f = ∀ a → A a → ∃ λ b → B b × f ∙ a ↘ b

⟦_⟧T : Typ → Ty
⟦ N     ⟧T = Nat
⟦ S ⟶ U ⟧T = ⟦ S ⟧T ⇒ ⟦ U ⟧T

mutual
  Bot⇒⟦⟧ : ∀ T → Bot e → ⟦ T ⟧T (ne e)
  Bot⇒⟦⟧     N       ⊥e      = ne ⊥e
  Bot⇒⟦⟧ {e} (S ⟶ U) ⊥e a Sa = e $′ a
                             , Bot⇒⟦⟧ U (λ n → let (e′ , e↘) = ⊥e n
                                                   (a′ , a↘) = ⟦⟧⇒Top S Sa n
                                               in e′ $ a′ , R$ n e↘ a↘)
                             , $∙ e a

  ⟦⟧⇒Top : ∀ T → ⟦ T ⟧T d → Top d
  ⟦⟧⇒Top N ze      n            = ze , Rze n
  ⟦⟧⇒Top N (su Td) n
    with ⟦⟧⇒Top N Td n
  ...  | w , d↘                 = su w , Rsu n d↘
  ⟦⟧⇒Top N (ne ⊥e) n
    with ⊥e n
  ...  | u , u↘                 = ne u , Rne n u↘
  ⟦⟧⇒Top (S ⟶ U) Td n
    with Td (l′ n) (Bot⇒⟦⟧ S λ m → -, Rl m n)
  ... | b , Ub , Λ∙ t↘          = -, RΛ n t↘ (proj₂ (⟦⟧⇒Top U Ub (suc n)))
  ... | .(e $′ l′ n) , Ub , $∙ e .(l′ n)
      with ⟦⟧⇒Top U Ub n
  ...    | _ , Rne .n (R$ .n e↘ _) = -, Rne n e↘

infix 4 _∙_∈_ rec_,_,_∈_ ⟦_⟧_∈_ ⟦_⟧s_∈_

_∙_∈_ : D → D → Ty → Set
f ∙ a ∈ T = ∃ λ b → T b × f ∙ a ↘ b

rec_,_,_∈_ : D → D → D → Ty → Set
rec d′ , d″ , d ∈ T = ∃ λ b → T b × rec d′ , d″ , d ↘ b

⟦_⟧_∈_ : Exp → Env → Ty → Set
⟦ t ⟧ ρ ∈ T = ∃ λ b → T b × ⟦ t ⟧ ρ ↘ b

⟦_⟧Γ : Ctx → Ev
⟦ []    ⟧Γ _ = ⊤
⟦ T ∷ Γ ⟧Γ ρ = ⟦ T ⟧T (ρ 0) × ⟦ Γ ⟧Γ (drop ρ)

⟦_⟧s_∈_ : Subst → Env → Ev → Set
⟦ σ ⟧s ρ ∈ Γ = ∃ λ τ → Γ τ × ⟦ σ ⟧s ρ ↘ τ

infix 4 _⊨_∶_ _⊨s_∶_
_⊨_∶_ : Ctx → Exp → Typ → Set
Γ ⊨ t ∶ T = ∀ ρ → ⟦ Γ ⟧Γ ρ → ⟦ t ⟧ ρ ∈ ⟦ T ⟧T

_⊨s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊨s σ ∶ Δ = ∀ ρ → ⟦ Γ ⟧Γ ρ → ⟦ σ ⟧s ρ ∈ ⟦ Δ ⟧Γ

-- Typing Rules

vlookup : ∀ {x} →
          x ∶ T ∈ Γ →
          ------------
          Γ ⊨ v x ∶ T
vlookup here ρ (d , Γ)        = ρ 0 , d , ⟦v⟧ zero
vlookup (there T∈Γ) ρ (_ , Γ)
  with vlookup T∈Γ (drop ρ) Γ
...  | .(ρ (suc _)) , Tb , ⟦v⟧ _ = -, Tb , ⟦v⟧ _

Λ-I : S ∷ Γ ⊨ t ∶ T →
      ---------------
      Γ ⊨ Λ t ∶ S ⟶ T
Λ-I {S} {_} {t} t∶T ρ Γ = Λ t ρ
                        , (λ a Sa → let (dt , Td , ap) = t∶T (ρ ↦ a) (Sa , Γ)
                                    in dt , Td , Λ∙ ap)
                        , ⟦Λ⟧ t

Λ-E : Γ ⊨ r ∶ S ⟶ T →
      Γ ⊨ s ∶ S →
      ---------------
      Γ ⊨ r $ s ∶ T
Λ-E r∶F s∶S ρ Γ
  with r∶F ρ Γ | s∶S ρ Γ
...  | dr , Fr , ir
     | ds , Ss , is
     with Fr ds Ss
...     | rs , Trs , ap = rs , Trs , ⟦$⟧ ir is ap

ze-I : Γ ⊨ ze ∶ N
ze-I ρ Γ = ze , ze , ⟦ze⟧

su-I : Γ ⊨ t ∶ N →
       -------------
       Γ ⊨ su t ∶ N
su-I t∶T ρ Γ
  with t∶T ρ Γ
...  | d , Nd , id = su d , su Nd , ⟦su⟧ id

N-E-helper : ∀ {n} →
             ⟦ Γ ⟧Γ ρ →
             (s∶T : ⟦ s ⟧ ρ ∈ ⟦ T ⟧T)
             (r∶F : ⟦ r ⟧ ρ ∈ ⟦ N ⟶ T ⟶ T ⟧T) →
             Nat n →
             rec proj₁ s∶T , proj₁ r∶F , n ∈ ⟦ T ⟧T
N-E-helper Γ (ds , Ts , _) r ze                          = ds , Ts , rze
N-E-helper {_} {_} {_} {T} Γ s r@(dr , Fr , ir) (su n)
  with N-E-helper {T = T} Γ s r n
...  | dn , Tn , rn
     with Fr _ n
...     | dr′ , Fr′ , ir′
        with Fr′ _ Tn
...        | dr″ , Fr″ , ir″                             = dr″ , Fr″ , rsu rn ir′ ir″
N-E-helper {T = T} Γ (ds , Ts , _) (dr , Fr , ir) (ne n) = rec′ ds dr _
                                                         , Bot⇒⟦⟧ T
                                                                  (λ m → -, Rr m (proj₂ (⟦⟧⇒Top T Ts m))
                                                                                 (proj₂ (⟦⟧⇒Top (N ⟶ T ⟶ T) Fr m))
                                                                                 (proj₂ (n m)))
                                                         , rec

N-E : Γ ⊨ s ∶ T →
      Γ ⊨ r ∶ N ⟶ T ⟶ T →
      Γ ⊨ t ∶ N →
      ------------------------
      Γ ⊨ rec T s r t ∶ T
N-E {_} {_} {T} s∶T r∶R t∶N ρ Γ
  with s∶T ρ Γ
     | r∶R ρ Γ
     | t∶N ρ Γ
...  | s@(ds , Ts , is)
     | r@(dr , Fr , ir)
     | t@(dt , Nt , it)
     with N-E-helper {T = T} Γ s r Nt
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

infix 4 _⊩_≈_∈_ _⊨_≈_∶_ _⊩s_≈_∈_ _⊨s_≈_∶_

record _⊩_≈_∈_ ρ s u (T : Ty) : Set where
  field
    ⟦s⟧  : D
    ⟦u⟧  : D
    ∈T   : T ⟦s⟧
    eq   : ⟦s⟧ ≡ ⟦u⟧
    ⟦s⟧↘ : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ⟦u⟧↘ : ⟦ u ⟧ ρ ↘ ⟦u⟧

_⊨_≈_∶_ : Ctx → Exp → Exp → Typ → Set
Γ ⊨ s ≈ u ∶ T = ∀ ρ → ⟦ Γ ⟧Γ ρ → ρ ⊩ s ≈ u ∈ ⟦ T ⟧T

record _⊩s_≈_∈_ ρ σ τ (Δ : Ev) : Set where
  field
    ⟦σ⟧  : Env
    ⟦τ⟧  : Env
    ∈Δ   : Δ ⟦σ⟧
    eq   : ⟦σ⟧ ≡ ⟦τ⟧
    ⟦σ⟧↘ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ⟦τ⟧↘ : ⟦ τ ⟧s ρ ↘ ⟦τ⟧

_⊨s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨s σ ≈ τ ∶ Δ = ∀ ρ → ⟦ Γ ⟧Γ ρ → ρ ⊩s τ ≈ τ ∈ ⟦ Δ ⟧Γ

≈-refl : Γ ⊨ t ∶ T →
         --------------
         Γ ⊨ t ≈ t ∶ T
≈-refl t ρ Γ
  with t ρ Γ
...  | dt , Tt , it = record
  { ⟦s⟧  = dt
  ; ⟦u⟧  = dt
  ; ∈T   = Tt
  ; eq   = refl
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
  ; ∈T   = subst ⟦ T ⟧T eq ∈T
  ; eq   = sym eq
  ; ⟦s⟧↘ = ⟦u⟧↘
  ; ⟦u⟧↘ = ⟦s⟧↘
  }
  where open _⊩_≈_∈_ ⟦t≈t′⟧

≈-trans : Γ ⊨ t ≈ t′ ∶ T →
          Γ ⊨ t′ ≈ t″ ∶ T →
          ------------------
          Γ ⊨ t ≈ t″ ∶ T
≈-trans t≈t′ t′≈t″ ρ Γ
  with t≈t′ ρ Γ | t′≈t″ ρ Γ
...  | ⟦t≈t′⟧ | ⟦t′≈t″⟧ = record
  { ⟦s⟧  = eq₁.⟦s⟧
  ; ⟦u⟧  = eq₂.⟦u⟧
  ; ∈T   = eq₁.∈T
  ; eq   = trans eq₁.eq (trans (⟦⟧-det eq₁.⟦u⟧↘ eq₂.⟦s⟧↘) eq₂.eq)
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
  ; ∈T   = su ∈T
  ; eq   = cong su eq
  ; ⟦s⟧↘ = ⟦su⟧ ⟦s⟧↘
  ; ⟦u⟧↘ = ⟦su⟧ ⟦u⟧↘
  }
  where open _⊩_≈_∈_ ⟦t≈t′⟧

$-cong : Γ ⊨ r ≈ r′ ∶ S ⟶ T →
         Γ ⊨ s ≈ s′ ∶ S →
         -----------------------
         Γ ⊨ r $ s ≈ r′ $ s′ ∶ T
$-cong {S = S} {T} r≈r′ s≈s′ ρ Γ
  with r≈r′ ρ Γ
     | s≈s′ ρ Γ
...  | ⟦r≈r′⟧ | ⟦s≈s′⟧    =
  let (rs , Trs , irs)    = eq₁.∈T eq₂.⟦s⟧ eq₂.∈T in
  let (rs′ , Trs′ , irs′) = eq₁.∈T eq₂.⟦u⟧ (subst ⟦ S ⟧T eq₂.eq eq₂.∈T) in
  record
  { ⟦s⟧  = rs
  ; ⟦u⟧  = rs′
  ; ∈T   = Trs
  ; eq   = eqpf eq₂.eq eq₂.∈T
  ; ⟦s⟧↘ = ⟦$⟧ eq₁.⟦s⟧↘ eq₂.⟦s⟧↘ irs
  ; ⟦u⟧↘ = ⟦$⟧ eq₁.⟦u⟧↘ eq₂.⟦u⟧↘ (subst (λ t → t ∙ _ ↘ _) eq₁.eq irs′)
  }
  where module eq₁ = _⊩_≈_∈_ ⟦r≈r′⟧
        module eq₂ = _⊩_≈_∈_ ⟦s≈s′⟧
        eqpf : ∀ {a b} (p : a ≡ b) (Sa : ⟦ S ⟧T a) →
                 proj₁ (eq₁.∈T a Sa) ≡ proj₁ (eq₁.∈T b (subst ⟦ S ⟧T p Sa))
        eqpf refl _ = refl

↑-vlookup : ∀ {x} →
              x ∶ T ∈ Γ →
              ----------------------------------
              S ∷ Γ ⊨ v x [ ↑ ] ≈ v (suc x) ∶ T
↑-vlookup {x = x} T∈Γ ρ (S , Γ) = record
  { ⟦s⟧  = ρ (suc x)
  ; ⟦u⟧  = ρ (suc x)
  ; ∈T   = helper ρ T∈Γ Γ
  ; eq   = refl
  ; ⟦s⟧↘ = ⟦[]⟧ ⟦↑⟧ (⟦v⟧ x)
  ; ⟦u⟧↘ = ⟦v⟧ (suc x)
  }
  where helper : ∀ {x Γ} ρ → x ∶ T ∈ Γ → ⟦ Γ ⟧Γ (drop ρ) → ⟦ T ⟧T (ρ (suc x))
        helper ρ here        (T , _) = T
        helper ρ (there T∈Γ) (_ , Γ) = helper (drop ρ) T∈Γ Γ

[I] : Γ ⊨ t ∶ T →
      -------------------
      Γ ⊨ t [ I ] ≈ t ∶ T
[I] t ρ Γ
  with t ρ Γ
...  | dt , Tt , it = record
  { ⟦s⟧  = dt
  ; ⟦u⟧  = dt
  ; ∈T   = Tt
  ; eq   = refl
  ; ⟦s⟧↘ = ⟦[]⟧ ⟦I⟧ it
  ; ⟦u⟧↘ = it
  }

[,]-v0 : Γ ⊨s σ ∶ Δ →
         Γ ⊨ s ∶ S →
         -------------------------
         Γ ⊨ v 0 [ σ , s ] ≈ s ∶ S
[,]-v0 σ s ρ Γ
  with σ ρ Γ
     | s ρ Γ
...  | dσ , Δσ , iσ
     | ds , Ss , is = record
  { ⟦s⟧  = ds
  ; ⟦u⟧  = ds
  ; ∈T   = Ss
  ; eq   = refl
  ; ⟦s⟧↘ = ⟦[]⟧ (⟦,⟧ iσ is) (⟦v⟧ 0)
  ; ⟦u⟧↘ = is
  }

[,]-v-suc : ∀ {x} →
              Γ ⊨s σ ∶ Δ →
              Γ ⊨ s ∶ S →
              x ∶ T ∈ Δ →
              ----------------------------------------
              Γ ⊨ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T
[,]-v-suc {x = x} σ s T∈Δ ρ Γ
  with σ ρ Γ
     | s ρ Γ
...  | dσ , Δσ , iσ
     | ds , Ss , is = record
  { ⟦s⟧  = dσ x
  ; ⟦u⟧  = dσ x
  ; ∈T   = helper T∈Δ dσ Δσ
  ; eq   = refl
  ; ⟦s⟧↘ = ⟦[]⟧ (⟦,⟧ iσ is) (⟦v⟧ (suc x))
  ; ⟦u⟧↘ = ⟦[]⟧ iσ (⟦v⟧ x)
  }
  where helper : ∀ {x T Δ} → x ∶ T ∈ Δ → (σ : Env) → ⟦ Δ ⟧Γ σ → ⟦ T ⟧T (σ x)
        helper here σ (T , _)         = T
        helper (there T∈Δ) σ (_ , Δσ) = helper T∈Δ (drop σ) Δσ

Λ-β : S ∷ Γ ⊨ t ∶ T →
      Γ ⊨ s ∶ S →
      ------------------------------
      Γ ⊨ Λ t $ s ≈ t [ I , s ] ∶ T
Λ-β t s ρ Γ
  with s ρ Γ
...  | ds , Ss , is
     with t (ρ ↦ ds) (Ss , Γ)
...     | dt , Tt , it = record
  { ⟦s⟧  = dt
  ; ⟦u⟧  = dt
  ; ∈T   = Tt
  ; eq   = refl
  ; ⟦s⟧↘ = ⟦$⟧ (⟦Λ⟧ _) is (Λ∙ it)
  ; ⟦u⟧↘ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ is) it
  }

-- Λ-cong : S ∷ Γ ⊨ t ≈ t′ ∶ T →
--          ------------------------------
--          Γ ⊨ Λ t ≈ Λ t′ ∶ S ⟶ T
-- Λ-cong {S = S} t ρ Γ
--   with t (ρ ↦ l′ 0) (Bot⇒⟦⟧ S (λ n → -, Rl n 0) , Γ)
-- ...  | t′ = record
--   { ⟦s⟧  = {!!}
--   ; ⟦u⟧  = {!!}
--   ; ∈T   = {!!}
--   ; eq   = {!!}
--   ; ⟦s⟧↘ = ⟦Λ⟧ _
--   ; ⟦u⟧↘ = ⟦Λ⟧ _
--   }
--   where open _⊩_≈_∈_ t′

-- Λ-η : Γ ⊨ t ∶ S ⟶ T →
--       ----------------------------------
--       Γ ⊨ t ≈ Λ (t [ ↑ ] $ v 0) ∶ S ⟶ T
-- Λ-η t ρ Γ
--   with t ρ Γ
-- ...  | dt , Ft , it = record
--   { ⟦s⟧  = dt
--   ; ⟦u⟧  = {!!}
--   ; ∈T   = {!!}
--   ; eq   = {!!}
--   ; ⟦s⟧↘ = it
--   ; ⟦u⟧↘ = ⟦Λ⟧ (_ [ ↑ ] $ v zero)
--   }
