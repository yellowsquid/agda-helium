------------------------------------------------------------------------
-- Agda Helium
--
-- All library modules, along with short descriptions.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Everything where

-- Definitions for more algebraic structures
import Helium.Algebra.Bundles

-- Relations between properties of functions when the underlying relation is a setoid
import Helium.Algebra.Consequences.Setoid

-- Construct algebras of vectors in a pointwise manner
import Helium.Algebra.Construct.Pointwise

-- More core algebraic definitions
import Helium.Algebra.Core

-- More properties of functions
import Helium.Algebra.Definitions

-- Ordering properties of functions
import Helium.Algebra.Ordered.Definitions

-- Definitions of ordered algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Helium.Algebra.Ordered.StrictTotal.Bundles

-- Some ordered algebraic structures (not packed up with sets,
-- operations, etc.)
import Helium.Algebra.Ordered.StrictTotal.Structures

-- Some more algebraic structures
import Helium.Algebra.Structures

-- Definition of types and operations used by the Armv8-M pseudocode.
import Helium.Data.Pseudocode

-- Definitions of a subset of Armv8-M instructions.
import Helium.Instructions

-- Denotational semantics of Armv8-M instructions.
import Helium.Semantics.Denotational

-- Base definitions for the denotational semantics.
import Helium.Semantics.Denotational.Core
