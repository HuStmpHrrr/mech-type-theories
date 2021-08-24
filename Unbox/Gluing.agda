{-# OPTIONS --without-K --safe #-}

module Unbox.Gluing where

open import Lib

open import Data.List.Properties as Lₚ

open import Unbox.Statics
open import Unbox.Semantics
open import Unbox.Restricted

mt : Substs → MTrans
mt I        = vone
mt (p σ)    = mt σ
mt (σ , _)  = mt σ
mt (σ ； n) = ins (mt σ) n
mt (σ ∘ δ)  = mt σ ø mt δ
