{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Realizability (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Induction
open import Induction.WellFounded
open import Lib
open import kMLTT.Completeness.LogRel
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Readback

-- Simplify...
mutual
  realizability-Re-Acc : ∀ {i} →
                         Acc (_<_) i →
                         (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                         c ≈ c′ ∈ Bot →
                         ↑ A c ≈ ↑ A′ c′ ∈ El i A≈A′
  realizability-Re-Acc <i (ne C≈C′)     c≈c′ = ne c≈c′
  realizability-Re-Acc <i N             c≈c′ = ne c≈c′
  realizability-Re-Acc <i (U j<i refl)  c≈c′
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i         = ne c≈c′
  realizability-Re-Acc {□ A} {□ A′} {c} {c′} {i} <i (□ A≈A′) c≈c′ n κ = record
    { ua = unbox′ (A [ ins κ 1 ] [ ins vone n ]) n (c [ κ ])
    ; ub = unbox′ (A′ [ ins κ 1 ] [ ins vone n ]) n (c′ [ κ ])
    ; ↘ua = unbox∙ n
    ; ↘ub = unbox∙ n
    ; ua≈ub = ua≈ub
    }
    where
      unbox[c[κ]]≈unbox[c′[κ]] : unbox n (mtran-c c κ) ≈ unbox n (mtran-c c′ κ) ∈ Bot
      unbox[c[κ]]≈unbox[c′[κ]] ns κ′
        with c≈c′ (ns ∥ L κ′ n) (κ ø κ′ ∥ n)
      ... | u , c↘u , c′↘u
          rewrite Dn-comp c κ (κ′ ∥ n)
                | Dn-comp c′ κ (κ′ ∥ n) = unbox (L κ′ n) u , Ru ns (L κ′ n) c↘u , Ru ns (L κ′ n) c′↘u

      ua≈ub : unbox′ (A [ ins κ 1 ] [ ins vone n ]) n (c [ κ ]) ≈ unbox′ (A′ [ ins κ 1 ] [ ins vone n ]) n (c′ [ κ ]) ∈ El i (A≈A′ (ins κ n))
      ua≈ub
        rewrite D-ins-ins A κ n
              | D-ins-ins A′ κ n = realizability-Re-Acc <i (A≈A′ (ins κ n)) unbox[c[κ]]≈unbox[c′[κ]]
  realizability-Re-Acc {A = Π A T ρ} {A′ = Π A′ T′ ρ′} {c} {c′} <i (Π A≈A′ T≈T′) c≈c′ {a = b} {b = b′} κ b≈b′ = record
    { fa = [ ΠRT.⟦T⟧ (T≈T′ κ b≈b′) ] c [ κ ] $′ ↓ (A [ κ ]) b
    ; fa′ = [ ΠRT.⟦T′⟧ (T≈T′ κ b≈b′) ] c′ [ κ ] $′ ↓ (A′ [ κ ]) b′
    ; ↘fa = $∙ (A [ κ ]) (c [ κ ]) (ΠRT.↘⟦T⟧ (T≈T′ κ b≈b′))
    ; ↘fa′ = $∙ (A′ [ κ ]) (c′ [ κ ]) (ΠRT.↘⟦T′⟧ (T≈T′ κ b≈b′))
    ; fa≈fa′ = realizability-Re-Acc <i (ΠRT.T≈T′ (T≈T′ κ b≈b′)) c[κ]$b≈c′[κ]$b′
    }
    where
      c[κ]$b≈c′[κ]$b′ : c [ κ ] $ ↓ (A [ κ ]) b ≈ c′ [ κ ] $ ↓ (A′ [ κ ]) b′ ∈ Bot
      c[κ]$b≈c′[κ]$b′ ns κ′
        with c≈c′ ns (κ ø κ′) | realizability-Rf-Acc <i (A≈A′ κ) b≈b′ ns κ′
      ...  | u , c↘u , c′↘u   | w , b↘w , b′↘w
          rewrite Dn-comp c κ κ′
                | Dn-comp c′ κ κ′ = u $ w , R$ ns c↘u b↘w , R$ ns c′↘u b′↘w

  realizability-Rf-Acc : ∀ {i} →
                         Acc (_<_) i →
                         (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                         a ≈ a′ ∈ El i A≈A′ →
                         ↓ A a ≈ ↓ A′ a′ ∈ Top
  realizability-Rf-Acc <i (ne C≈C′)     (ne c≈c′) ns κ
    with c≈c′ ns κ
  ...  | u , c↘u , c′↘u                                = ne u , Rne ns c↘u , Rne ns c′↘u
  realizability-Rf-Acc <i N             ze        ns κ = ze , Rze ns , Rze ns
  realizability-Rf-Acc <i N             (su a≈a′) ns κ
    with realizability-Rf-Acc <i N a≈a′ ns κ
  ... | w , a↘w , a′↘w                                 = su w , Rsu ns a↘w , Rsu ns a′↘w
  realizability-Rf-Acc <i N             (ne c≈c′) ns κ
    with c≈c′ ns κ
  ...  | u , c↘u , c′↘u                                = ne u , RN ns c↘u , RN ns c′↘u
  realizability-Rf-Acc (acc <i) (U {j} j<i refl)  a≈a′
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i                  = realizability-Rty-Acc (<i j j<i) a≈a′
  realizability-Rf-Acc {A = □ A} {A′ = □ A′} <i (□ A≈A′) a≈a′ ns κ
    with a≈a′ 1 κ
  ...  | record
         { ua = ua
         ; ub = ua′
         ; ↘ua = ↘ua
         ; ↘ub = ↘ua′
         ; ua≈ub = ua≈ua′
         }
      with realizability-Rf-Acc <i (A≈A′ (ins κ 1)) ua≈ua′ (0 ∷⁺ ns) vone
  ...    | w , ua↘w , ua′↘w
        rewrite D-ap-vone (A [ ins κ 1 ])
              | D-ap-vone (A′ [ ins κ 1 ])
              | D-ap-vone ua
              | D-ap-vone ua′                                 = box w , R□ ns ↘ua ua↘w , R□ ns ↘ua′ ua′↘w
  realizability-Rf-Acc <i         (Π A≈A′ T≈T′) a≈a′           ns κ
    with realizability-Re-Acc <i (A≈A′ κ) (Bot-l (head ns))
  ...  | z≈z
      with a≈a′ κ z≈z
  ...    | record
           { fa = fa
           ; fa′ = fa′
           ; ↘fa = ↘fa
           ; ↘fa′ = ↘fa′
           ; fa≈fa′ = fa≈fa′
           }
        with realizability-Rf-Acc <i (ΠRT.T≈T′ (T≈T′ κ z≈z)) fa≈fa′ (inc ns) vone
  ...      | w , fa↘w , fa′↘w
          rewrite D-ap-vone fa
                | D-ap-vone fa′
                | D-ap-vone (ΠRT.⟦T⟧ (T≈T′ κ z≈z))
                | D-ap-vone (ΠRT.⟦T′⟧ (T≈T′ κ z≈z))          = Λ w , RΛ ns ↘fa (ΠRT.↘⟦T⟧ (T≈T′ κ z≈z)) fa↘w , RΛ ns ↘fa′ (ΠRT.↘⟦T′⟧ (T≈T′ κ z≈z)) fa′↘w

  realizability-Rty-Acc : ∀ {i} →
                      Acc (_<_) i →
                      (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                      ↓ (U i) A ≈ ↓ (U i) A′ ∈ Top
  realizability-Rty-Acc <i (ne C≈C′)     ns κ
    with C≈C′ ns κ
  ...  | V , C↘V , C′↘V                     = ne V , RU ns (Rne ns C↘V) , RU ns (Rne ns C′↘V)
  realizability-Rty-Acc <i N             ns κ = N , RU ns (RN ns) , RU ns (RN ns)
  realizability-Rty-Acc <i (U j<i refl)  ns κ = Se _ , RU ns (RU ns) , RU ns (RU ns)
  realizability-Rty-Acc {A = □ A} {A′ = □ A′} <i (□ A≈A′) ns κ
    with realizability-Rty-Acc <i (A≈A′ (ins κ 1)) (0 ∷⁺ ns) vone
  ...  | W , RU _ A↘W , RU _ A′↘W
      rewrite D-ap-vone (A [ ins κ 1 ])
            | D-ap-vone (A′ [ ins κ 1 ])                   = □ W , RU ns (R□ ns A↘W) , RU ns (R□ ns A′↘W)
  realizability-Rty-Acc {A = Π A _ _} {A′ = Π A′ _ _} <i (Π A≈A′ T≈T′) ns κ
    with realizability-Re-Acc <i (A≈A′ κ) (Bot-l (head ns))
  ...  | z≈z
      with realizability-Rty-Acc <i (A≈A′ κ) ns vone
  ...    | W , RU _ A↘W , RU _ A′↘W
        with realizability-Rty-Acc <i (ΠRT.T≈T′ (T≈T′ κ z≈z)) (inc ns) vone
  ...      | w , RU _ T↘w , RU _ T′↘w
          rewrite D-ap-vone (A [ κ ])
                | D-ap-vone (A′ [ κ ])
                | D-ap-vone (ΠRT.⟦T⟧ (T≈T′ κ z≈z))
                | D-ap-vone (ΠRT.⟦T′⟧ (T≈T′ κ z≈z)) = Π W w , RU ns (RΠ ns A↘W (ΠRT.↘⟦T⟧ (T≈T′ κ z≈z)) T↘w) , RU ns (RΠ ns A′↘W (ΠRT.↘⟦T′⟧ (T≈T′ κ z≈z)) T′↘w)

realizability : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                (c ≈ c′ ∈ Bot → ↑ A c ≈ ↑ A′ c′ ∈ El i A≈A′) × (a ≈ a′ ∈ El i A≈A′ → ↓ A a ≈ ↓ A′ a′ ∈ Top) × (↓ (U i) A ≈ ↓ (U i) A′ ∈ Top)
realizability A≈A′ = realizability-Re-Acc (<-wellFounded _) A≈A′ , realizability-Rf-Acc (<-wellFounded _) A≈A′ , realizability-Rty-Acc (<-wellFounded _) A≈A′
