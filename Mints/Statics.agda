{-# OPTIONS --without-K --safe #-}

-- This module defines the syntax and typing rule of Mints
--
-- The syntax of Mints contains variables, natural numbers, dependent functions and □ modality
-- with explicit substitutions.
-- We use de Bruijn indices for name representation and employ β-η normal forms.
--
-- We have two sets of typing rules in this module (there is another set Mints.Soundness.Typing):
--
-- Mints.Statics.Concise: the true and golden set of typing rules
-- Mints.Statics.Full: an enriched set of typing rules which
--     1. is used to prove syntactic properties of Concise, and
--     2. serves as a "bridge" set of rules which connects Concise to yet another set of typing rules,
--        Mints.Soundness.Typing, which is required to overcome some technicalities encountered in the
--        soundness proof.
--
-- Concise and Full are proved equivalent in Mints.Statics.Equiv.
module Mints.Statics where

-- The Concise set of rules are the gold standard rules.
open import Mints.Statics.Concise public
