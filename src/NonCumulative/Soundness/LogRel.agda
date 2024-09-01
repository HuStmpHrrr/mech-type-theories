{-# OPTIONS --without-K --safe #-}

-- Definitions of logical relations for the gluing model and semantic judgments
module NonCumulative.Soundness.LogRel where

open import Lib hiding (lookup)
open import Data.Nat
open import Data.Nat.Properties

open import NonCumulative.Statics.Ascribed.Full public
open import NonCumulative.Semantics.Domain public
open import NonCumulative.Semantics.Evaluation public
open import NonCumulative.Semantics.PER public
open import NonCumulative.Soundness.Weakening public

-------------------------------------
-- Gluing models for terms and types

-- Gluing model for natural numbers
infix 4 _⊢_∶N®_∈Nat

data _⊢_∶N®_∈Nat : Ctx → Exp → D → Set where
  ze : Γ ⊢ t ≈ ze ∶[ 0 ] N →
       -----------------
       Γ ⊢ t ∶N® ze ∈Nat
  su : Γ ⊢ t ≈ su t′ ∶[ 0 ] N →
       Γ ⊢ t′ ∶N® a ∈Nat →
       --------------------
       Γ ⊢ t ∶N® su a ∈Nat
  ne : (c∈ : c ∈′ Bot) →
       (∀ {Δ σ} → Δ ⊢w σ ∶ Γ → let (u , _) = c∈ (len Δ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶[ 0 ] N) →
       -----------------------
       Γ ⊢ t ∶N® ↑ 0 N c ∈Nat

-- Helper concepts for the gluing model
--
-- These definitions are defined for the purpose of having more structural condition
-- management.  One can find unfolded definitions using conjunctions in the comments
-- near the definition of the gluing model.


-- Gluing model for Π

-- for reference, in the cumulative version
-- the paper rule is 
-- exists S T, Γ ⊢ R = Π S T ×
--             Γ ⊢ S ® A ×
--             ∀ (σ : Γ' ≤ Γ) s a, Γ' ⊢ s : S ® a ∈ A ⇒ Γ' ⊢ T [ σ ] · s ® F · a

-- (1) Δ ⊢ IT [ σ ] ® iA [ RI ≔ _ ⊢ _ ® iA ]
-- (2) ∀ {s a} (irel : Δ ⊢ s ∶ IT [ σ ] ® a ∈El i iA) (a∈ : a ∈′ El i iA) → Δ ⊢ OT [ σ , s ] ® ΠRT.T≈T′ (RT a∈) [ RS ≔ _ ⊢ _ ∶ _ ® _ ∈El i iA , RO ≔ (a∈ : a ∈′ El i iA) → _ ⊢ _ ® ΠRT.T≈T′ (RT a∈) ]
record ΠRel i j k Δ IT OT (σ : Subst)
            (i≡maxjk : i ≡ max j k)
            (univ : ∀ {l} → l < i → Ty)
            (jA : A ≈ B ∈ PERDef.𝕌 j (λ l<j → univ (ΠI≤ i≡maxjk l<j)))
            (RI : Ctx → Typ → Set)
            (RO : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA → Ctx → Typ → Set)
            (Rs : Ctx → Exp → Typ → D → Set) : Set where
  field
    IT-rel : RI Δ (IT [ σ ])
    OT-rel : Rs Δ s (IT [ σ ]) a → (a∈ : a ∈′ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA) → RO a∈ Δ (OT [ σ , s ∶ IT [ σ ] ↙ j ])

-- ∃ IT OT,
-- (1) Γ ⊢ Π (IT ↙ i) (OT ↙ j) ∶[ 1 + k ] Se k   
-- (2) (IT ↙ i) ∷ Γ ⊢ OT ∶[ 1 + i ] Se i × 
-- (3) ∀ {Δ σ} → Δ ⊢w σ ∶ Γ → ΠRel
record GluΠ i j k Γ T {A B}
            (i≡maxjk : i ≡ max j k)
            (univ : ∀ {l} → l < i → Ty)
            (jA : A ≈ B ∈ PERDef.𝕌 j (λ l<j → univ (ΠI≤ i≡maxjk l<j)))
            (RI : Ctx → Typ → Set)
            (RO : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA → Ctx → Typ → Set)
            (Rs : Ctx → Exp → Typ → D → Set) : Set where
  field
    IT   : Typ
    OT   : Typ
    -- need these two props or they are too difficult to invert
    ⊢IT  : Γ ⊢ IT ∶[ 1 + j ] Se j
    ⊢OT  : (IT ↙ j) ∷ Γ ⊢ OT ∶[ 1 + k ] Se k
    T≈   : Γ ⊢ T ≈ Π (IT ↙ j) (OT ↙ k) ∶[ 1 + i ] Se i
    krip : Δ ⊢w σ ∶ Γ → ΠRel i j k Δ IT OT σ i≡maxjk univ jA RI RO Rs


-- Gluing model for universes

-- ...
record GluU j i Γ t T A 
            (i≡1+j : i ≡ 1 + j)
            (univ : ∀ {l} → l < i → Ty)
            (R : A ∈′ PERDef.𝕌 j (λ {l} l<j → univ {l} (<-trans l<j (≤-reflexive (sym i≡1+j)))) → Set) : Set where
  field
    t∶T : Γ ⊢ t ∶[ i ] T
    T≈  : Γ ⊢ T ≈ Se j ∶[ 1 + i ] Se i
    A∈𝕌 : A ∈′ PERDef.𝕌 j (λ {l} l<j → univ {l} (<-trans l<j (≤-reflexive (sym i≡1+j))))
    rel : R A∈𝕌


-- Gluing model for L

-- no reference
record GluL i k j Γ T 
            (RU : Ctx → Typ → Set) : Set where
  field
    UT   : Typ
    -- need this ? 
    ⊢UT  : Γ ⊢ UT ∶[ 1 + k ] Se k
    T≈   : Γ ⊢ T ≈ Liftt j ( UT ↙ k ) ∶[ 1 + i ] Se i
    krip : Δ ⊢w σ ∶ Γ → RU Δ (UT [ σ ])


-- Gluing model for Λ

-- ∃ fa,
-- (1) f ∙ a ↘ fa
-- (2) Δ ⊢ t : T ® fa ∈El A ≈ B [ R$ ≔ _ ⊢ _ : _ ® _ ∈El A ≈ B ]
record ΛKripke Δ t T f a (R$ : Ctx → Exp → Typ → D → Set) : Set where
  field
    fa : D
    ↘fa : f ∙ a ↘ fa
    ®fa : R$ Δ t T fa

record ΛRel i j k Δ t IT OT (σ : Subst ) f
            (i≡maxjk : i ≡ max j k)
            (univ : ∀ {l} → l < i → Ty)
            (jA : A ≈ B ∈ PERDef.𝕌 j (λ i′<j → univ (ΠI≤ i≡maxjk i′<j)))
            (RI : Ctx → Typ → Set)
            (Rs : Ctx → Exp → Typ → D → Set)
            (R$ : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA → Ctx → Exp → Typ → D → Set) : Set where
  field
    IT-rel : RI Δ (IT [ σ ])
    ap-rel : Rs Δ s (IT [ σ ]) b → (b∈ : b ∈′ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA) → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) f b (R$ b∈)

  flipped-ap-rel : (b∈ : b ∈′ PERDef.El j (λ l<k → univ (ΠI≤ i≡maxjk l<k)) jA) → ∀ {s} → Rs Δ s (IT [ σ ]) b → ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) f b (R$ b∈)
  flipped-ap-rel b∈ R = ap-rel R b∈

record GluΛ i j k Γ t T a {A B T′ T″ ρ ρ′}
            (i≡maxjk : i ≡ max j k)
            (univ : ∀ {l} → l < i → Ty)
            (jA : A ≈ B ∈ PERDef.𝕌 j (λ i′<j → univ (ΠI≤ i≡maxjk i′<j)))
            (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ j′<k → univ (ΠI≤ i≡maxjk j′<k)) jA → ΠRT T′ (ρ ↦ a) T″ (ρ′ ↦ a′) (PERDef.𝕌 k (λ l<k → univ (ΠO≤ i≡maxjk l<k))))
            (RI : Ctx → Typ → Set)
            (Rs : Ctx → Exp → Typ → D → Set)
            (R$ : ∀ {a a′} → a ≈ a′ ∈  PERDef.El j (λ j′<k → univ (ΠI≤ i≡maxjk j′<k)) jA → Ctx → Exp → Typ → D → Set) : Set where
  field
    t∶T  : Γ ⊢ t ∶[ i ] T
    a∈El : a ∈′ PERDef.El i univ (Π i≡maxjk jA RT refl refl)
    IT   : Typ
    OT   : Typ
    -- need these two props or they are too difficult to invert
    ⊢IT  : Γ ⊢ IT ∶[ 1 + j ] Se j
    ⊢OT  : (IT ↙ j) ∷ Γ ⊢ OT ∶[ 1 + k ] Se k
    T≈   : Γ ⊢ T ≈ Π (IT ↙ j) (OT ↙ k) ∶[ 1 + i ] Se i
    krip : Δ ⊢w σ ∶ Γ → ΛRel i j k Δ t IT OT σ a i≡maxjk univ jA RI Rs R$


-- Gluing model for lifttt

-- ∃ ua, 
-- (1) unli∙ a ↘ ua 
-- (2) Δ ⊢ unlift t : T ® ua ∈El k A≈B 
record lKripke Δ t T a (Ru : Ctx → Exp → Typ → D → Set) : Set where
  field
    ua : D
    ↘ua : unli∙ a ↘ ua
    ®ua : Ru Δ t T ua

record Glul i j k Γ t T a 
            (i≡j+k : i ≡ j + k)
            (univ : ∀ {l} → l < i → Ty)
            (kA : A ≈ B ∈ PERDef.𝕌 k (λ l<k → univ (Li≤ i≡j+k l<k)))
            (Ru : Ctx → Exp → Typ → D → Set) : Set where
  field
    t∶T  : Γ ⊢ t ∶[ i ] T
    UT   : Typ
    ⊢UT  : Γ ⊢ UT ∶[ 1 + k ] Se k
    a∈El : a ∈′ PERDef.El i univ (L i≡j+k kA refl refl)
    T≈   : Γ ⊢ T ≈ Liftt j ( UT ↙ k ) ∶[ 1 + i ] Se i
    krip : Δ ⊢w σ ∶ Γ → lKripke Δ ((unlift t) [ σ ]) (UT [ σ ]) a Ru
    

-- Gluing model for neutral terms

-- ...
record GluNe i Γ t T 
             (c∈⊥ : c ∈′ Bot) 
             (C≈C′ : C ≈ C′ ∈ Bot) : Set where
  field
    t∶T : Γ ⊢ t ∶[ i ] T
    ⊢T  : Γ ⊢ T ∶[ 1 + i ] Se i
    krip : Δ ⊢w σ ∶ Γ →
           let V , _ = C≈C′ (len Δ)
               u , _ = c∈⊥ (len Δ)
           in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶[ 1 + i ] Se i
            × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶[ i ] T [ σ ]


-- -- The definition of the gluing model
-- --  
-- -- The gluing model has two relations:
-- --
-- -- Γ ⊢ T ® A≈B : T and A (and B) are related at level i. It is A≈B again due to the
-- -- proof relevant nature of NonCumulative.
-- --
-- -- Γ ⊢ t ∶ T ® a ∈El A≈B : t and a are related. t has type T and a is in El A≈B. T and
-- -- A≈B are related in level i.
module Glu where
  mutual
    ⟦_,_,_⟧_⊢_®_ : ∀ i → 
      (rc : ∀ {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set) → 
           (Univ : ∀ {j} → j < i → Ty) → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 i Univ → Set
    ⟦ i , rc , Univ ⟧ Γ ⊢ T ® ne C≈C′ j≡1+i j′≡1+i = Γ ⊢ T ∶[ 1 + i ] Se i × ∀ {Δ σ} → Δ ⊢w σ ∶ Γ → let V , _ = C≈C′ (len Δ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶[ 1 + i ] Se i
    ⟦ i , rc , Univ ⟧ Γ ⊢ T ® N i≡0 =  Γ ⊢ T ≈ N ∶[ 1 + i ] Se i
    ⟦ i , rc , Univ ⟧ Γ ⊢ T ® (U {j} i≡1+j j≡j′) = Γ ⊢ T ≈ Se j ∶[ 1 + i ] Se i
    ⟦ i , rc , Univ ⟧ Γ ⊢ T ® (Π {j = j} {k = k} i≡maxjk jA RT j≡j′ k≡k′) = GluΠ _ _ _ Γ T i≡maxjk Univ jA 
      (⟦ j , (λ l<j → rc (ΠI≤ i≡maxjk l<j)) , (λ l<j → Univ (ΠI≤ i≡maxjk l<j)) ⟧_⊢_® jA) 
      (λ a∈ → ⟦ k , (λ l<k → rc (ΠO≤ i≡maxjk l<k)) , (λ l<k → Univ (ΠO≤ i≡maxjk l<k)) ⟧_⊢_® ΠRT.T≈T′ (RT a∈)) 
      (⟦ j , (λ l<j → rc (ΠI≤ i≡maxjk l<j)) , (λ l<j → Univ (ΠI≤ i≡maxjk l<j)) ⟧_⊢_∶_®_∈El jA)
    ⟦ i , rc , Univ ⟧ Γ ⊢ T ® (L {j = j} {k = k} i≡j+k kA j≡j′ k≡k′) = GluL i k j Γ T
      (⟦ k , (λ l<k → rc (Li≤ i≡j+k l<k)) , (λ {l} l<k → Univ (Li≤ i≡j+k l<k)) ⟧_⊢_® kA)

    ⟦_,_,_⟧_⊢_∶_®_∈El_ : ∀ i (rc : ∀ {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set) 
            (Univ : ∀ {j} → j < i → Ty) →
             Ctx → Exp → Typ → D → A ≈ B ∈ PERDef.𝕌 i Univ → Set
    ⟦ i , rc , Univ ⟧ Γ ⊢ t ∶ T ® a ∈El (ne C≈C′ j≡1+i j'=1+i) = Σ (a ∈′ Neu i) λ { (ne c∈⊥ i′=i₁ i′=i₂) → GluNe i Γ t T c∈⊥ C≈C′ }
    ⟦ i , rc , Univ ⟧ Γ ⊢ t ∶ T ® a ∈El (N i≡0) = Γ ⊢ t ∶N® a ∈Nat × Γ ⊢ T ≈ N ∶[ 1 ] Se 0 
    ⟦ i , rc , Univ ⟧ Γ ⊢ t ∶ T ® a ∈El (U {j} i≡1+j j≡j′) = GluU j i Γ t T a i≡1+j Univ 
      λ a∈ → rc (≤-reflexive (sym i≡1+j)) (λ l<j → Univ (<-trans l<j (≤-reflexive (sym i≡1+j)))) Γ t a∈
    ⟦ i , rc , Univ ⟧ Γ ⊢ t ∶ T ® a ∈El (Π {j = j} {k = k} i≡maxjk jA RT j≡j′ k≡k′) = GluΛ _ _ _ Γ t T a i≡maxjk Univ jA RT 
      (⟦ j , (λ l<j → rc (ΠI≤ i≡maxjk l<j)) , (λ l<j → Univ (ΠI≤ i≡maxjk l<j)) ⟧_⊢_® jA) 
      (⟦ j , (λ l<j → rc (ΠI≤ i≡maxjk l<j)) , (λ l<j → Univ (ΠI≤ i≡maxjk l<j)) ⟧_⊢_∶_®_∈El jA) 
      λ a∈ → ⟦ k , (λ l<k → rc (ΠO≤ i≡maxjk l<k)) , (λ l<k → Univ (ΠO≤ i≡maxjk l<k)) ⟧_⊢_∶_®_∈El (ΠRT.T≈T′ (RT a∈))
    ⟦ i , rc , Univ ⟧ Γ ⊢ t ∶ T ® a ∈El L {j = j} {k = k} i≡j+k kA j≡j′ k≡k′ = Glul _ _ _ Γ t T a i≡j+k Univ kA
      ((⟦ k , (λ l<k → rc (Li≤ i≡j+k l<k)) , (λ {l} l<k → Univ (Li≤ i≡j+k l<k)) ⟧_⊢_∶_®_∈El kA))

-- Similar to the PER model, we tie the knot using well-founded induction.
Glu-wellfounded : ∀ i {j} (j<i : j < i) (univ : ∀ {l} → l < j → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 j univ → Set
Glu-wellfounded (suc i) {j} (s≤s j<i) univ =  Glu.⟦ _ , (λ {k} k<j univ₁ Γ T A≈B → Glu-wellfounded i (<-≤-trans k<j j<i) (λ l<k → univ₁ l<k) Γ T A≈B) , univ ⟧_⊢_®_ 

-- private
--   module G i = Glu i (Glu-wellfounded i)

infix 4 _⊢_®[_]_ _⊢_∶_®[_]_∈El_

-- T and A are related at level i
_⊢_®[_]_ : Ctx → Typ → ∀ i → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ T ®[ i ] A≈B = Glu.⟦ i , Glu-wellfounded _ , 𝕌-wellfounded _ ⟧ Γ ⊢ T ® A≈B

-- t of type T and a of type A are related at level i
_⊢_∶_®[_]_∈El_ : Ctx → Exp → Typ → ∀ i → D → A ≈ B ∈ 𝕌 i → Set
Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B = Glu.⟦ i , Glu-wellfounded _ , 𝕌-wellfounded _ ⟧ Γ ⊢ t ∶ T ® a ∈El A≈B


-- In the PER model, we have three extrema PERs: Bot, Top and TopT. They relates equal
-- neutral values, equal normal values and equal normal semantic types after readback,
-- respctively. Similarly, we need the same notions in the gluing model. We need:
--
-- ®↓         : t and c are related iff t and any readback of c are equivalent.
-- ®↑ (value) : t and a are related iff t and any readback of a are equivalent.
-- ®↑ (type)  : T and A are related iff T and any readback of A are equivalent.
infix 4 _⊢_∶_®↓[_]_∈El_ _⊢_∶_®↑[_]_∈El_  _⊢_®↑[_]_

record _⊢_∶_®↓[_]_∈El_ Γ t T i c (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ t ∶[ i ] T
    T∼A  : Γ ⊢ T ®[ i ] A≈B
    c∈⊥  : c ∈′ Bot
    krip : Δ ⊢w σ ∶ Γ → let u , _ = c∈⊥ (len Δ) in Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶[ i ] T [ σ ]

record _⊢_∶_®↑[_]_∈El_ Γ t T i a (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ t ∶[ i ] T
    T∼A  : Γ ⊢ T ®[ i ] A≈B
    a∈⊤  : ↓ i A a ≈ ↓ i B a ∈ Top
    krip : Δ ⊢w σ ∶ Γ → let w , _ = a∈⊤ (len Δ) in Δ ⊢ t [ σ ] ≈ Nf⇒Exp w ∶[ i ] T [ σ ]

record _⊢_®↑[_]_ Γ T i (A≈B : A ≈ B ∈ 𝕌 i) : Set where
  field
    t∶T  : Γ ⊢ T ∶[ 1 + i ] Se i
    A∈⊤  : A ≈ B ∈ TopT i
    krip : Δ ⊢w σ ∶ Γ → let W , _ = A∈⊤ (len Δ) in Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + i ] Se i


---------------------------------
-- Gluing model for substitutions

-- Helper predicates for each case of context stacks

-- R is always the gluing model for substitutions
record Glu∷ i Γ σ T Δ (ρ : Env) (R : Ctx → Subst → Env → Set) : Set where
  field
    ⊢σ   : Γ ⊢s σ ∶ (T ↙ i) ∷ Δ
    pσ   : Subst
    v0σ  : Exp
    ⟦T⟧  : D
    ≈pσ  : Γ ⊢s p σ ≈ pσ ∶ Δ
    ≈v0σ : Γ ⊢ v 0 [ σ ] ≈ v0σ ∶[ i ] T [ pσ ]
    ↘⟦T⟧ : ⟦ T ⟧ drop ρ ↘ ⟦T⟧
    T∈𝕌  : ⟦T⟧ ∈′ 𝕌 i
    t∼ρ0 : Γ ⊢ v0σ ∶ (T [ pσ ]) ®[ i ] (lookup ρ 0) ∈El T∈𝕌
    step : R Γ pσ (drop ρ)

-- On paper this predicate denotes Δ ⊢ T [ σ ] ®[ i ] ⟦T⟧(ρ)
record GluTyp i Δ T (σ : Subst) ρ : Set where
  field
    ⟦T⟧   : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
    T∼⟦T⟧ : Δ ⊢ T [ σ ] ®[ i ] T∈𝕌

-- The definition of gluing model for substitutions
--
-- Similar to the PER model where we use induction-recursion to relate the
-- interpretations of substitutions, here we also use induction-recursion to relate
-- substitutions and evaluation environments.
--
-- This definition is not seen in others' work (A. Abel, D. Gratzer, etc.), where the
-- gluing for substitutions are done by induction on simply the constructor of the
-- contexts (or context stacks in our case). This model will work for cumulative
-- universes in a set-theoretic model, because in these proof one crucial step after
-- proving cumulativity of the model is to take the limit of the universe level, and
-- then the universe level is not spoken of. In type theory, on the other hand, we
-- cannot take limits. This thus forces us to consider universe levels explicitly,
-- leading us to this more precise model.
--
-- Another benefit of this higher precision is that this model can be adapted to
-- non-cumulative universe pretty well. In aforementioned work, since the step of
-- taking limit is essential, the information about universe levels is gone. It
-- becomes unclear how one can easily remove the step of taking limits and adapt their
-- proofs to non-cumulativity. On the other hand, our model keeps track of unvierse
-- levels so there is no problem to obtain the level from our model whenever it is
-- needed.

infix 4 ⊩_ _⊢s_∶_®_

mutual

  -- This definition is almost the same as ⊢_ except that it has one more condition in
  -- ⊩∷.
  data ⊩_ : Ctx → Set where
    ⊩[] : ⊩ []
    ⊩∷  : ∀ {i} (⊩Γ : ⊩ Γ) →
          Γ ⊢ T ∶[ 1 + i ] Se i →
          -- This condition says, given any related σ and ρ, T[σ] and its evaluation
          -- are related at level i.
          (∀ {Δ σ ρ} → Δ ⊢s σ ∶ ⊩Γ ® ρ → GluTyp i Δ T σ ρ) →
          ⊩ ((T ↙ i) ∷ Γ)

  -- The gluing model for substitutions
  --
  -- This model glues substitutions and evaluation environments. It is recursive on ⊩_
  -- so this model is again inductive-recursive. We can see that in the ⊩∷ case, we
  -- use the universe level. This removes our need to take limits as done in a more
  -- set-thereotic setting.
  _⊢s_∶_®_ : Ctx → Subst → ⊩ Δ → Env → Set
  Δ ⊢s σ ∶ ⊩[] ® ρ                     = Δ ⊢s σ ∶ []
  Δ ⊢s σ ∶ ⊩∷ {Γ} {T} {i} ⊩Γ ⊢T gT ® ρ = Glu∷ i Δ σ T Γ ρ (_⊢s_∶ ⊩Γ ®_)

⊩⇒⊢ : ⊩ Γ → ⊢ Γ
⊩⇒⊢ ⊩[]          = ⊢[]
⊩⇒⊢ (⊩∷ ⊩Γ ⊢T _) = ⊢∷ (⊩⇒⊢ ⊩Γ) ⊢T

-- On paper this predicate denotes Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦ t ⟧(ρ) ∈El ⟦T⟧(ρ)
record GluExp i Δ t T (σ : Subst) ρ : Set where
  field
    ⟦T⟧   : D
    ⟦t⟧   : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    T∈𝕌   : ⟦T⟧ ∈′ 𝕌 i
    t∼⟦t⟧ : Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] ⟦t⟧ ∈El T∈𝕌

record GluSubst Δ τ (⊩Γ′ : ⊩ Γ′) σ ρ : Set where
  field
    ⟦τ⟧    : Env
    ↘⟦τ⟧   : ⟦ τ ⟧s ρ ↘ ⟦τ⟧
    τσ∼⟦τ⟧ : Δ ⊢s τ ∘ σ ∶ ⊩Γ′ ® ⟦τ⟧


------------------------------------
-- Definitions of semantic judgments

infix 4 _⊩_∶[_]_ _⊩s_∶_

record _⊩_∶[_]_ Γ t i T : Set where
  field
    ⊩Γ   : ⊩ Γ
    -- This level always remembers the level of T and thus allows easy adaptation to non-cumulativity.
    krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp i Δ t T σ ρ


record _⊩s_∶_ Γ τ Γ′ : Set where
  field
    ⊩Γ   : ⊩ Γ
    ⊩Γ′  : ⊩ Γ′
    krip : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluSubst Δ τ ⊩Γ′ σ ρ
          