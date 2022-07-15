{-# OPTIONS --without-K --safe #-}

-- This module defines the syntax and typing rule of MLTT
--
-- The syntax of MLTT contains variables, natural numbers, and dependent functions
-- with explicit substitutions.
-- We use de Bruijn indices for name representation and employ β-η normal forms.
--
-- We have two sets of typing rules in this module (there is another set MLTT.Soundness.Typing):
--
-- MLTT.Statics.Concise: the true and golden set of typing rules
-- MLTT.Statics.Full: an enriched set of typing rules which
--     1. is used to prove syntactic properties of Concise, and
--     2. serves as a "bridge" set of rules which connects Concise to yet another set of typing rules,
--        MLTT.Soundness.Typing, which is required to overcome some technicalities encountered in the
--        soundness proof.
--
-- Concise and Full are proved equivalent in MLTT.Statics.Equiv.
module MLTT.Statics where

-- The Concise set of rules are the gold standard rules.
open import MLTT.Statics.Concise public
