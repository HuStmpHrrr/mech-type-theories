{-# OPTIONS --without-K --safe #-}

module Unbox.Gluing where

open import Lib hiding (lookup)

open import Data.List.Properties as Lₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Restricted

mt : Substs → UMoT
mt I        = vone
mt p        = vone
mt (σ , _)  = mt σ
mt (σ ； n) = ins (mt σ) n
mt (σ ∘ δ)  = mt σ ø mt δ

Glue : Set₁
Glue = Exp → D → Set

IGlue : Set₁
IGlue = Ctxs → Glue

record TopPred Ψ σ t a T : Set where
  field
    nf  : Nf
    ↘nf : Rf map len Ψ - ↓ T (a [ mt σ ]) ↘ nf
    ≈nf : Ψ ⊢ t [ σ ] ≈ Nf⇒Exp nf ∶ T

record Top T Ψ t a : Set where
  field
    t∶T  : Ψ ⊢ t ∶ T
    krip : Ψ′ ⊢r σ ∶ Ψ → TopPred Ψ′ σ t a T

record BotPred Ψ σ t c T : Set where
  field
    neu : Ne
    ↘ne : Re map len Ψ - c [ mt σ ] ↘ neu
    ≈ne : Ψ ⊢ t [ σ ] ≈ Ne⇒Exp neu ∶ T

record Bot T Ψ t c : Set where
  field
    t∶T  : Ψ ⊢ t ∶ T
    krip : Ψ′ ⊢r σ ∶ Ψ → BotPred Ψ′ σ t c T

data BotT T : IGlue where
  bne : Bot T Ψ t c → BotT T Ψ t (↑ T c)

record unbox-rel (P : IGlue) Γs Ψ σ t a : Set where
  field
    ua  : D
    ↘ua : unbox∙ len Γs , a [ mt σ ] ↘ ua
    rel : unbox (len Γs) (t [ σ ]) ∼ ua ∈ P (Γs ++⁺ Ψ)

record ■ (P : IGlue) T Ψ t a : Set where
  field
    t∶□ : Ψ ⊢ t ∶ □ T
    krip : ∀ Γs → Ψ′ ⊢r σ ∶ Ψ → unbox-rel P Γs Ψ′ σ t a

record ap-rel (P : IGlue) Ψ σ t s f a : Set where
  field
    fa   : D
    ↘fa  : f [ mt σ ] ∙ a ↘ fa
    rel  : (t [ σ ]) $ s ∼ fa ∈ P Ψ

record Fun (P Q : IGlue) S T Ψ t f : Set where
  field
    t∶⟶  : Ψ ⊢ t ∶ S ⟶ T
    krip : Ψ′ ⊢r σ ∶ Ψ → s ∼ a ∈ P Ψ′ → ap-rel Q Ψ′ σ t s f a

《_》T : Typ → IGlue
《 B 》T     = BotT B
《 S ⟶ T 》T = Fun 《 S 》T 《 T 》T S T
《 □ T 》T   = ■ 《 T 》T T

glu⇒⊢ : ∀ T → t ∼ a ∈ 《 T 》T Ψ → Ψ ⊢ t ∶ T
glu⇒⊢ B (bne t~a) = Bot.t∶T t~a
glu⇒⊢ (S ⟶ T) t~a = Fun.t∶⟶ t~a
glu⇒⊢ (□ T) t~a   = ■.t∶□ t~a

record Single Γ Ψ σ ρ : Set where
  field
    σ-wf  : Ψ ⊢s σ ∶ Γ ∷ []
    vlkup : ∀ {x} → x ∶ T ∈ Γ → v x [ σ ] ∼ lookup ρ x ∈ 《 T 》T Ψ

record Cons Γ Γs (R : Ctxs → Substs → Envs → Set) Ψ σ ρ : Set where
  field
    σ-wf  : Ψ ⊢s σ ∶ Γ ∷ Γs
    vlkup : ∀ {x} → x ∶ T ∈ Γ → v x [ σ ] ∼ lookup ρ x ∈ 《 T 》T Ψ
    Leq   : O σ 1 ≡ proj₁ (ρ 0)
    hds   : List Ctx
    Ψ|ρ0  : Ctxs
    Ψ≡    : Ψ ≡ hds ++⁺ Ψ|ρ0
    len≡  : len hds ≡ proj₁ (ρ 0)
    rel   : Tr σ 1 ∼ Tr ρ 1 ∈ R Ψ|ρ0

《_》Γs : List Ctx → Ctxs → Substs → Envs → Set
《 [] 》Γs Ψ σ ρ = ⊤
《 Γ ∷ [] 》Γs   = Single Γ
《 Γ ∷ Γs 》Γs   = Cons Γ Γs 《 Γs 》Γs

《_》Ψ : Ctxs → Ctxs → Substs → Envs → Set
《 Γ ∷ Γs 》Ψ = 《 Γ ∷ Γs 》Γs

glu⇒⊢s : σ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ → Ψ ⊢s σ ∶ Γ ∷ Γs
glu⇒⊢s {Γs = []} σ∼ρ     = σ-wf
  where open Single σ∼ρ
glu⇒⊢s {Γs = _ ∷ Γs} σ∼ρ = σ-wf
  where open Cons σ∼ρ

glu⇒vlookup : σ ∼ ρ ∈ 《 Γ ∷ Γs 》Ψ Ψ → ∀ {x} → x ∶ T ∈ Γ → v x [ σ ] ∼ lookup ρ x ∈ 《 T 》T Ψ
glu⇒vlookup {Γs = []} σ∼ρ     = vlkup
  where open Single σ∼ρ
glu⇒vlookup {Γs = x ∷ Γs} σ∼ρ = vlkup
  where open Cons σ∼ρ

infix 4 _⊩_∶_ _⊩s_∶_

record Intp Ψ (σ : Substs) ρ t T : Set where
  field
    ⟦t⟧  : D
    ↘⟦t⟧ : ⟦ t ⟧ ρ ↘ ⟦t⟧
    tσ∼  : t [ σ ] ∼ ⟦t⟧ ∈ 《 T 》T Ψ

_⊩_∶_ : Ctxs → Exp → Typ → Set
Ψ ⊩ t ∶ T = ∀ {Ψ′} σ ρ → σ ∼ ρ ∈ 《 Ψ 》Ψ Ψ′ → Intp Ψ′ σ ρ t T

record Intps Ψ σ′ ρ σ Ψ′ : Set where
  field
    ⟦σ⟧  : Envs
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    comp : σ ∘ σ′ ∼ ⟦σ⟧ ∈ 《 Ψ′ 》Ψ Ψ

_⊩s_∶_ : Ctxs → Substs → Ctxs → Set
Ψ ⊩s δ ∶ Ψ′ = ∀ {Ψ″} σ ρ → σ ∼ ρ ∈ 《 Ψ 》Ψ Ψ″ → Intps Ψ″ σ ρ δ Ψ′
