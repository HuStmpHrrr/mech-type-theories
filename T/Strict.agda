{-# OPTIONS --without-K --safe #-}

module T.Strict where

open import Lib
open import T.Statics
open import T.Semantics

infix 4 _⊩_≈_∈_ _⊨_≈_∶_ _⊩s_≈_∈_ _⊨s_≈_∶_

record _⊩_≈_∈_ ρ s u (T : Ty) : Set where
  field
    ⟦s⟧  : D
    ⟦u⟧  : D
    ∈T   : T ⟦s⟧
    eq   : ⟦s⟧ ≡ ⟦u⟧
    ⟦s⟧↘ : ⟦ s ⟧ ρ ↘ ⟦s⟧
    ⟦u⟧↘ : ⟦ u ⟧ ρ ↘ ⟦u⟧

_⊨_≈_∶_ : Env → Exp → Exp → Typ → Set
Γ ⊨ s ≈ u ∶ T = ∀ ρ → ⟦ Γ ⟧Γ ρ → ρ ⊩ s ≈ u ∈ ⟦ T ⟧T

record _⊩s_≈_∈_ ρ σ τ (Δ : Ev) : Set where
  field
    ⟦σ⟧  : Ctx
    ⟦τ⟧  : Ctx
    ∈Δ   : Δ ⟦σ⟧
    eq   : ⟦σ⟧ ≡ ⟦τ⟧
    ⟦σ⟧↘ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ⟦τ⟧↘ : ⟦ τ ⟧s ρ ↘ ⟦τ⟧

_⊨s_≈_∶_ : Env → Subst → Subst → Env → Set
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
  where helper : ∀ {x T Δ} → x ∶ T ∈ Δ → (σ : Ctx) → ⟦ Δ ⟧Γ σ → ⟦ T ⟧T (σ x)
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
