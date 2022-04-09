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

-- More core algebraic definitions
import Helium.Algebra.Core

-- Definitions of decidable algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Helium.Algebra.Decidable.Bundles

-- Construct decidable algebras of vectors in a pointwise manner
import Helium.Algebra.Decidable.Construct.Pointwise

-- Some decidable algebraic structures (not packed up with sets,
-- operations, etc.)
import Helium.Algebra.Decidable.Structures

-- More properties of functions
import Helium.Algebra.Definitions

-- Ordering properties of functions
import Helium.Algebra.Ordered.Definitions

-- Definitions of ordered algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Helium.Algebra.Ordered.StrictTotal.Bundles

-- Relations between algebraic properties of ordered structures
import Helium.Algebra.Ordered.StrictTotal.Consequences

-- Morphisms for ordered algebraic structures.
import Helium.Algebra.Ordered.StrictTotal.Morphism.Structures

-- Algebraic properties of ordered abelian groups
import Helium.Algebra.Ordered.StrictTotal.Properties.AbelianGroup

-- Algebraic properties of ordered commutative rings
import Helium.Algebra.Ordered.StrictTotal.Properties.CommutativeRing

-- Algebraic properties of ordered division rings
import Helium.Algebra.Ordered.StrictTotal.Properties.DivisionRing

-- Algebraic properties of ordered fields
import Helium.Algebra.Ordered.StrictTotal.Properties.Field

-- Algebraic properties of ordered groups
import Helium.Algebra.Ordered.StrictTotal.Properties.Group

-- Algebraic properties of ordered magmas
import Helium.Algebra.Ordered.StrictTotal.Properties.Magma

-- Algebraic properties of ordered monoids
import Helium.Algebra.Ordered.StrictTotal.Properties.Monoid

-- Algebraic properties of ordered rings
import Helium.Algebra.Ordered.StrictTotal.Properties.Ring

-- Algebraic properties of ordered semigroups
import Helium.Algebra.Ordered.StrictTotal.Properties.Semigroup

-- Some ordered algebraic structures (not packed up with sets,
-- operations, etc.)
import Helium.Algebra.Ordered.StrictTotal.Structures

-- Properties of almost groups
import Helium.Algebra.Properties.AlmostGroup

-- Some more algebraic structures
import Helium.Algebra.Structures

-- Definition of types and operations used by the Armv8-M pseudocode.
import Helium.Data.Pseudocode.Algebra

-- A proof of correctness for Barrett reduction.
import Helium.Data.Pseudocode.Algebra.Barrett

-- Algebraic properties of types used by the Armv8-M pseudocode.
import Helium.Data.Pseudocode.Algebra.Properties

-- Definition of the Armv8-M pseudocode.
import Helium.Data.Pseudocode.Core

-- Ways to modify pseudocode statements and expressions.
import Helium.Data.Pseudocode.Manipulate

-- Basic properties of the pseudocode data types
import Helium.Data.Pseudocode.Properties

-- Definition of instructions using the Armv8-M pseudocode.
import Helium.Instructions.Base

-- Definitions of the data for a subset of Armv8-M instructions.
import Helium.Instructions.Core

-- Implementation of Barrett reduction.
import Helium.Instructions.Instances.Barrett

-- Relational properties of strict total orders
import Helium.Relation.Binary.Properties.StrictTotalOrder

-- Semantics for the Armv8-M pseudocode using Hoare triples.
import Helium.Semantics.Axiomatic

-- Definition of assertions used in correctness triples
import Helium.Semantics.Axiomatic.Assertion

-- Base definitions for the axiomatic semantics
import Helium.Semantics.Axiomatic.Core

-- Definition of terms for use in assertions
import Helium.Semantics.Axiomatic.Term

-- Definition of Hoare triples
import Helium.Semantics.Axiomatic.Triple

-- Base definitions for the denotational semantics.
import Helium.Semantics.Denotational.Core

-- Ring solver tactic using integers as coefficients
import Helium.Tactic.CommutativeRing.NonReflective
