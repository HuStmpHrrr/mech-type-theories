{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Realizability (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.LogRel
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Semantics.Readback

-- Simplify...
mutual
  realizability-Re : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                     c ≈ c′ ∈ Bot →
                     ↑ A c ≈ ↑ A′ c′ ∈ El i A≈A′
  realizability-Re (ne C≈C′)    c≈c′                              = ne c≈c′
  realizability-Re N            c≈c′                              = ne c≈c′
  realizability-Re (U j<i refl) c≈c′
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i                             = ne c≈c′
  realizability-Re {□ A} {□ A′} {c} {c′} {i} (□ A≈A′)     c≈c′ n κ = record
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
              | D-ins-ins A′ κ n = realizability-Re {i = i} (A≈A′ (ins κ n)) unbox[c[κ]]≈unbox[c′[κ]]
  realizability-Re (Π A≈A′ a≈a′)     c≈c′ κ a″≈a‴ = record
    { fa = {!!}
    ; fa′ = {!!}
    ; ↘fa = {!!}
    ; ↘fa′ = {!!}
    ; fa≈fa′ = {!!}
    }

  realizability-Rf : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                     a ≈ a′ ∈ El i A≈A′ →
                     ↓ A a ≈ ↓ A′ a′ ∈ Top
  realizability-Rf         (ne C≈C′)    (ne c≈c′) ns κ
    with c≈c′ ns κ
  ...  | u , c↘u , c′↘u                                = ne u , Rne ns c↘u , Rne ns c′↘u
  realizability-Rf         N            ze        ns κ = ze , Rze ns , Rze ns
  realizability-Rf {i = i} N            (su a≈a′) ns κ
    with realizability-Rf {i = i} N a≈a′ ns κ
  ... | w , a↘w , a′↘w                                 = su w , Rsu ns a↘w , Rsu ns a′↘w
  realizability-Rf         N            (ne c≈c′) ns κ
    with c≈c′ ns κ
  ...  | u , c↘u , c′↘u                                = ne u , RN ns c↘u , RN ns c′↘u
  realizability-Rf         (U j<i refl) a≈a′
    rewrite 𝕌-wellfounded-≡-𝕌 _ j<i                  = {!!}
  realizability-Rf         (□ x)        a≈a′      ns κ = {!!}
  realizability-Rf         (Π iA x)     a≈a′      ns κ = {!!}

  realizability-Rty : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i) →
                      ↓ (U i) A ≈ ↓ (U i) A′ ∈ Top
  realizability-Rty (ne C≈C′)    ns κ
    with C≈C′ ns κ
  ...  | V , C↘V , C′↘V               = ne V , RU ns (Rne ns C↘V) , RU ns (Rne ns C′↘V)
  realizability-Rty N            ns κ = N , RU ns (RN ns) , RU ns (RN ns)
  realizability-Rty (U j<i refl) ns κ = Se _ , RU ns (RU ns) , RU ns (RU ns)
  realizability-Rty (□ x)        ns κ = {!!}
  realizability-Rty (Π iA x)     ns κ = {!!}
