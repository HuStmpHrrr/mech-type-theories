{-# OPTIONS --without-K --safe #-}

-- This module defines the syntax and typing rule of κMLTT
--
-- The syntax of κMLTT contains variables, natural numbers, dependent functions and □ modality
-- with explicit substitutions.
-- We use de Bruijn indices for name representation and employ β-η normal forms.
--
-- We have two sets of typing rules in this module (there is another set kMLTT.Soundness.Typing):
--
-- kMLTT.Statics.Concise: the true and golden set of typing rules
-- kMLTT.Statics.Full: an enriched set of typing rules which
--     1. is used to prove syntactic properties of Concise, and
--     2. serves as a "bridge" set of rules which connects Concise to yet another set of typing rules,
--        kMLTT.Soundness.Typing, which is required to overcome some technicalities encountered in the
--        soundness proof.
--
-- Concise and Full are proved equivalent in kMLTT.Statics.Equiv.
module kMLTT.Statics where

open import kMLTT.Statics.Concise public
