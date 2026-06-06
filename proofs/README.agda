module README where

-- Functional extensionality is postulated here.
-- It is used as a helper axiom for constructions in DecSets.
open import FunExt

-- Isomorphism primitives: bi-implication, type isomorphisms, and composition.
-- This is the core utility module used by both set and automata developments.
open import Isomorphism

-- Generic finiteness witnesses and closure properties.
-- Provides finite product, sum, and function-space constructions.
open import Finiteness

-- Generic set-level infrastructure over predicates.
-- Defines finiteness, powerset-style predicates, and helper constructions.
open import Sets

-- Formal languages over words, with algebraic operations and star.
-- This module provides the main language-theoretic interface used elsewhere.
open import Language

-- Deterministic automata and state equivalence machinery.
-- Includes quotient-style and representative-based constructions.
open import Automaton

-- Finite automata where states are explicit Fin indices.
-- Provides the finite-state counterpart to the deterministic automaton view.
open import FiniteAutomaton

-- Closure constructions for deterministic automata (product-style).
-- Contains union/intersection constructions and correctness statements.
open import Constructions

-- Nondeterministic automata and their language semantics.
-- Includes powerset construction and regular-operation constructions.
open import ND-Automaton

-- Regular expressions and their encoding into nondeterministic automata.
-- Proves correctness of the encoding wrt. denotational semantics.
open import Regular

-- Arden-style reasoning for solving language equations.
-- Contains the standalone formalization of Arden's lemma.
open import Arden

-- Grammar formalisms: phrase-structure and CFGs plus shared interface.
-- Derivation and generated-language modules are abstracted over this interface.
open import Grammar

-- Shared helper lemmas for CFG derivations.
-- Provides context closure, transitivity, and terminal-yield composition.
open import Grammar.DerivationHelpers

-- Derivation trees for context-free grammars.
-- Encodes production choices and terminal yields as indexed tree/forest data.
open import Grammar.DerivationTree

-- Leftmost derivations for CFGs and their generated-language equivalence.
-- Provides the leftmost reflexive-transitive closure used by CFG closures.
open import Grammar.Leftmost-Derivation

-- Concrete example grammars used for experimentation and sanity checks.
-- Provides sample CFG instances and explicit production tables.
open import Grammar.Example

-- Properties and conversions for grammar formalisms.
-- Includes the isomorphism statement relating CFG and phrase-structure views.
open import Grammar.Properties

-- Closure constructions for CFGs.
-- Contains union, concatenation, and Kleene-star grammar constructions.
open import Grammar.CFG-Closure

-- Decidable-set infrastructure modeled as Bool-valued predicates.
-- Mirrors core set operations and finiteness in the decidable setting.
open import DecSets

-- Decidable languages built from Bool-valued word predicates.
-- Provides decidable analogues of concatenation and Kleene-style operators.
open import DecLanguage

-- Deterministic automata over decidable sets/languages.
-- Supplies acceptance and behavioral equivalence in the Bool-based setting.
open import DecAutomaton

-- Nondeterministic automata in the decidable setting.
-- Includes constructions, finiteness preservation, and decidable powerset conversion.
open import DecND-Automaton
