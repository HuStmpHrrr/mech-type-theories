{-# OPTIONS --without-K --safe #-}

module TypedComb.NBE where

open import Lib
open import TypedComb.Statics

open import Data.Unit

variable
  a b c d : Exp T

infix 3 _≈_
data _≈_ : Exp T → Exp T → Set where
  reflx   : a ≈ a
  symm    : a ≈ b → b ≈ a
  tran    : a ≈ b → b ≈ c → a ≈ c

  K-β     : K $ a $ b ≈ a
  S-β     : S $ a $ b $ c ≈ a $ c $ (b $ c)
  Rec-β₁  : Rec $ a $ b $ Ze ≈ a
  Rec-β₂  : Rec $ a $ b $ Su c ≈ b $ c $ (Rec $ a $ b $ c)

  Su-cong : a ≈ b → Su a ≈ Su b
  $-cong  : a ≈ b → c ≈ d → a $ c ≈ b $ d

data Nf : Typ → Set where
  K     : Nf (T ⟶ U ⟶ T)
  S     : Nf ((T ⟶ T′ ⟶ U) ⟶ (T ⟶ T′) ⟶ T ⟶ U)
  Ze    : Nf N
  Su    : Nf N → Nf N
  Rec   : Nf (T ⟶ (N ⟶ T ⟶ T) ⟶ N ⟶ T)
  K$    : Nf T → Nf (U ⟶ T)
  S$    : Nf (T ⟶ T′ ⟶ U) → Nf ((T ⟶ T′) ⟶ T ⟶ U)
  S$$   : Nf (T ⟶ T′ ⟶ U) → Nf (T ⟶ T′) → Nf (T ⟶ U)
  Rec$  : Nf T → Nf ((N ⟶ T ⟶ T) ⟶ N ⟶ T)
  Rec$$ : Nf T → Nf (N ⟶ T ⟶ T) → Nf (N ⟶ T)

Nf⇒Exp : Nf T → Exp T
Nf⇒Exp K           = K
Nf⇒Exp S           = S
Nf⇒Exp Ze          = Ze
Nf⇒Exp (Su t)      = Su (Nf⇒Exp t)
Nf⇒Exp Rec         = Rec
Nf⇒Exp (K$ t)      = K $ Nf⇒Exp t
Nf⇒Exp (S$ t)      = S $ Nf⇒Exp t
Nf⇒Exp (S$$ t u)   = S $ Nf⇒Exp t $ Nf⇒Exp u
Nf⇒Exp (Rec$ t)    = Rec $ Nf⇒Exp t
Nf⇒Exp (Rec$$ t u) = Rec $ Nf⇒Exp t $ Nf⇒Exp u

⟦_⟧ : Typ → Set
⟦ N ⟧     = Nf N
⟦ T ⟶ U ⟧ = Nf (T ⟶ U) × (⟦ T ⟧ → ⟦ U ⟧)

reify : ⟦ T ⟧ → Nf T
reify {N} ⟦T⟧         = ⟦T⟧
reify {T ⟶ U} (e , _) = e

rec : ⟦ T ⟧ → ⟦ N ⟶ T ⟶ T ⟧ → ⟦ N ⟧ → ⟦ T ⟧
rec t r Ze               = t
rec t r@(_ , ⟦r⟧) (Su n) = proj₂ (⟦r⟧ n) (rec t r n)

⟦_⟧ₑ : Exp T → ⟦ T ⟧
⟦ K ⟧ₑ     = K , λ t → K$ (reify t) , λ _ → t
⟦ S ⟧ₑ     = S , λ f@(fe , ⟦f⟧) → S$ fe , λ g@(ge , ⟦g⟧) → S$$ fe ge , λ t → proj₂ (⟦f⟧ t) (⟦g⟧ t)
⟦ t $ u ⟧ₑ = proj₂ ⟦ t ⟧ₑ ⟦ u ⟧ₑ
⟦ Ze ⟧ₑ    = Ze
⟦ Su e ⟧ₑ  = Su ⟦ e ⟧ₑ
⟦ Rec ⟧ₑ   = Rec , λ t → Rec$ (reify t) , λ r@(re , ⟦r⟧) → Rec$$ (reify t) re , rec t r

nbe : Exp T → Nf T
nbe t = reify ⟦ t ⟧ₑ

≈⇒⟦⟧ : a ≈ b → ⟦ a ⟧ₑ ≡ ⟦ b ⟧ₑ
≈⇒⟦⟧ reflx           = refl
≈⇒⟦⟧ (symm eq)       = sym (≈⇒⟦⟧ eq)
≈⇒⟦⟧ (tran eq eq′)   = trans (≈⇒⟦⟧ eq) (≈⇒⟦⟧ eq′)
≈⇒⟦⟧ K-β             = refl
≈⇒⟦⟧ S-β             = refl
≈⇒⟦⟧ Rec-β₁          = refl
≈⇒⟦⟧ Rec-β₂          = refl
≈⇒⟦⟧ (Su-cong eq)    = cong Su (≈⇒⟦⟧ eq)
≈⇒⟦⟧ ($-cong eq eq′) = cong₂ proj₂ (≈⇒⟦⟧ eq) (≈⇒⟦⟧ eq′)

≈⇒nbe≡ : a ≈ b → nbe a ≡ nbe b
≈⇒nbe≡ eq = cong reify (≈⇒⟦⟧ eq)

R : Exp T → Set
R′ : Exp T → Set

R t = (∃ λ t′ → t ≈ Nf⇒Exp t′) × R′ t

R′ {N} t     = ⊤
R′ {T ⟶ U} t = ∀ {s} → R s → R (t $ s)

R-resp-≈ : a ≈ b → R a → R b
R-resp-≈ {N} r ((t , eq) , _)       = (t , tran (symm r) eq) , tt
R-resp-≈ {T ⟶ U} r ((t , eq) , R′t) = (t , (tran (symm r) eq)) , λ Rs → R-resp-≈ ($-cong r reflx) (R′t Rs)

R-resp-≈′ : a ≈ b → R b → R a
R-resp-≈′ r Rb = R-resp-≈ (symm r) Rb

Rrec : R a → R b → (n : Nf N) → R (Rec $ a $ b $ Nf⇒Exp n)
Rrec {_} {a} {b} Ra _ Ze                = R-resp-≈′ Rec-β₁ Ra
Rrec {_} {a} {b} Ra Rb@(_ , R′b) (Su n) = R-resp-≈′ Rec-β₂ (proj₂ (R′b ((n , reflx) , tt)) (Rrec Ra Rb n))

Rt : (t : Exp T) → R t
Rt K                = (K , reflx) , λ Rs@((_ , eq) , _) → (K$ _ , $-cong reflx eq) , λ Ru → R-resp-≈′ K-β Rs
Rt S                = (S , reflx) , λ Rs@((_ , eq) , ⟦s⟧) → (S$ _ , $-cong reflx eq) , λ Ru@((_ , eq′) , ⟦u⟧) → (S$$ _ _ , $-cong ($-cong reflx eq) eq′) , λ Rt → R-resp-≈′ S-β (proj₂ (⟦s⟧ Rt) (⟦u⟧ Rt))
Rt (t $ u)          = proj₂ (Rt t) (Rt u)
Rt Ze               = (Ze , reflx) , tt
Rt (Su t) with Rt t
... | (t′ , eq) , _ = (Su t′ , Su-cong eq) , tt
Rt Rec              = (Rec , reflx) , (λ Rs@((_ , eq) , ⟦s⟧) → (Rec$ _ , $-cong reflx eq) , (λ Ru@((_ , eq′) , ⟦u⟧) → (Rec$$ _ _ , $-cong ($-cong reflx eq) eq′) , λ ((n , r) , _) → R-resp-≈′ ($-cong reflx r) (Rrec Rs Ru n)))

reify′ : ∀ {a : Exp T} → R a → Nf T
reify′ ((n , _) , _) = n

nbe′ : Exp T → Nf T
nbe′ t = reify′ (Rt t)

≈nbe′ : ∀ (e : Exp T) → e ≈ Nf⇒Exp (nbe′ e)
≈nbe′ e = let ((_ , eq) , _) = Rt e in eq

R-rel : {t : Exp T} → ⟦ T ⟧ → R t → Set
R-rel {N} {t} n ((n′ , _) , _)            = n ≡ n′
R-rel {T ⟶ U} {t} (n , f) ((n′ , _) , nf) = n ≡ n′ × (∀ {s} {⟦s⟧ : ⟦ T ⟧} {Rs : R s} → R-rel ⟦s⟧ Rs → R-rel (f ⟦s⟧) (nf Rs))

R-rel⇒eq : ∀ {s} {⟦s⟧ : ⟦ T ⟧} {Rs : R s} → R-rel ⟦s⟧ Rs → reify ⟦s⟧ ≡ reify′ Rs
R-rel⇒eq {N} r     = r
R-rel⇒eq {T ⟶ U} r = proj₁ r

R-resp-≈-rel : ∀ {s u} {⟦s⟧ : ⟦ T ⟧} {Rs : R s} (r : s ≈ u) → R-rel ⟦s⟧ Rs → R-rel ⟦s⟧ (R-resp-≈ r Rs)
R-resp-≈-rel {N} r rel           = rel
R-resp-≈-rel {T ⟶ U} r (eq , rf) = eq , λ rel → R-resp-≈-rel ($-cong r reflx) (rf rel)

rec-rel : {a : Exp T} {⟦a⟧ : ⟦ T ⟧} {Ra : R a} {b : Exp (N ⟶ T ⟶ T)} {⟦b⟧ : ⟦ N ⟶ T ⟶ T ⟧} {Rb : R b} →
          R-rel ⟦a⟧ Ra → R-rel ⟦b⟧ Rb → (n : Nf N) → R-rel (rec ⟦a⟧ ⟦b⟧ n) (Rrec Ra Rb n)
rec-rel ra rb Ze                = R-resp-≈-rel (symm Rec-β₁) ra
rec-rel ra rb@(eq , eqf) (Su n) = R-resp-≈-rel (symm Rec-β₂) (proj₂ (eqf refl) (rec-rel ra rb n))

intp-rel : (t : Exp T) → R-rel ⟦ t ⟧ₑ (Rt t)
intp-rel K       = refl , λ r → cong K$ (R-rel⇒eq r) , λ r′ → R-resp-≈-rel (symm K-β) r
intp-rel S       = refl , λ r → cong S$ (proj₁ r) , λ r′ → (cong₂ S$$ (proj₁ r) (proj₁ r′)) , λ r″ → R-resp-≈-rel (symm S-β) (proj₂ (proj₂ r r″) (proj₂ r′ r″))
intp-rel (t $ u) = proj₂ (intp-rel t) (intp-rel u)
intp-rel Ze      = refl
intp-rel (Su t)  = cong Su (intp-rel t)
intp-rel Rec     = refl , λ r → cong Rec$ (R-rel⇒eq r) , λ r′ → cong₂ Rec$$ (R-rel⇒eq r) (proj₁ r′) , λ { {_} {_} {((ns″ , rs″) , _)} refl → R-resp-≈-rel (symm ($-cong reflx rs″)) (rec-rel r r′ ns″) }

e≈nbe : (e : Exp T) → e ≈ Nf⇒Exp (nbe e)
e≈nbe e rewrite R-rel⇒eq (intp-rel e) = ≈nbe′ e

nbe≡⇒≈ : nbe a ≡ nbe b → a ≈ b
nbe≡⇒≈ eq = tran (e≈nbe _) (tran (subst (λ a → _ ≈ Nf⇒Exp a) eq reflx) (symm (e≈nbe _)))
