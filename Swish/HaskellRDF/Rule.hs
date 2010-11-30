{-# OPTIONS -XMultiParamTypeClasses #-}

--------------------------------------------------------------------------------
--
--  $Id: Rule.hs,v 1.8 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Rule
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a framework for defining inference rules
--  over some expression form.  It is intended to be used with
--  RDF graphs, but the structures aim to be quite generic with
--  respect to the expression forms allowed.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..), RuleMap
    , nullScope, nullFormula, nullRule
    , fwdCheckInference, bwdCheckInference
    , showsFormula, showsFormulae, showsWidth
    )
where

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI
    )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    )

import Swish.HaskellUtils.ShowM
    ( ShowM(..), showm )

import Swish.HaskellUtils.ListHelpers
    ( subset )

{- in Prelude????
import List
    ( union, intersect )

import Maybe
    ( isJust, fromJust )
-}

------------------------------------------------------------
--  Expressions
------------------------------------------------------------

-- |Expression is a type class for values over which proofs
--  may be constructed.
class (Eq ex) => Expression ex where
    -- |Is expression true in all interpretations?
    --  If so, then its truth is assumed without justification.
    isValid :: ex -> Bool

------------------------------------------------------------
--  Formula:  a named expression
------------------------------------------------------------

-- |A Formula is a named expression.
data Formula ex = Formula
    { formName :: ScopedName        -- ^ Name used for formula in proof chain
    , formExpr :: ex                -- ^ Named formula value
    } deriving Show

-- |Define equality of formulae as equality of formula names
instance Eq (Formula ex) where
    f1 == f2 = formName f1 == formName f2

-- |Define ordering of formulae based on formula names
instance Ord (Formula ex) where
    f1 <= f2 = formName f1 <= formName f2

instance LookupEntryClass (Formula ex) ScopedName (Formula ex)
    where
    newEntry (_,form) = form
    keyVal form = (formName form, form)

nullScope :: Namespace
nullScope = Namespace "null" "http://id.ninebynine.org/2003/Ruleset/null"

nullFormula :: Formula ex
nullFormula = Formula
    { formName = ScopedName nullScope "nullFormula"
    , formExpr = error "Null formula"
    }

-- testf1 = Formula "f1" ('f',1)
-- testf2 = Formula "f2" ('f',2)

-- |showsFormulae
--  Return a displayable form of a list of labelled formulae
showsFormulae :: (ShowM ex) => String -> [Formula ex] -> String -> ShowS
showsFormulae _       []     _     = id
showsFormulae newline [f]    after = showsFormula  newline f .
                                     showString    after
showsFormulae newline (f:fs) after = showsFormula  newline f .
                                     showString    newline .
                                     showsFormulae newline fs after

-- |showsFormula
--  Create a displayable form of a labelled formula
showsFormula :: (ShowM ex) => String -> Formula ex -> ShowS
showsFormula newline f =
    showsWidth 16 ("["++show (formName f)++"] ") .
    showms (newline++(replicate 16 ' ')) (formExpr f)

------------------------------------------------------------
--  Rule
------------------------------------------------------------

-- |Rule is a data type for inference rules that can be used
--  to construct a step in a proof.
data Rule ex = Rule
    -- |Name of rule, for use when displaying a proof
    { ruleName :: ScopedName
    -- |Forward application of a rule, takes a list of
    --  expressions and returns a list (possibly empty)
    --  of forward applications of the rule to combinations
    --  of the antecedent expressions.
    --  Note that all of the results returned can be assumed to
    --  be (simultaneously) true, given the antecedents provided.
    , fwdApply :: [ex] -> [ex]
    -- |Backward application of a rule, takes an expression
    --  and returns a list of alternative antecedents, each of
    --  which is a list of expressions that jointly yield the
    --  given consequence through application of the inference
    --  rule.  An empty list is returned if no antecedents
    --  will allow the consequence to be inferred.
    , bwdApply :: ex -> [[ex]]
    -- |Inference check.  Takes a list of antecedent expressions
    --  and a consequent expression, returning True if the
    --  consequence can be obtained from the antecedents by
    --  application of the rule.  When the antecedents and
    --  consequent are both given, this is generally more efficient
    --  that using either forward or backward chaining.
    --  Also, a particular rule may not fully support either
    --  forward or backward chaining, but all rules are required
    --  to fully support this function.
    --
    --  A default implementation based on forward chaining is
    --  given below.
    , checkInference :: [ex] -> ex -> Bool
    }

-- |Define equality of rules as equality of rule names
instance Eq (Rule ex) where
    r1 == r2 = ruleName r1 == ruleName r2

-- |Define ordering of rules based on rule names
instance Ord (Rule ex) where
    r1 <= r2 = ruleName r1 <= ruleName r2

instance Show (Rule ex) where
    show rl = "Rule "++show (ruleName rl)

instance LookupEntryClass (Rule ex) ScopedName (Rule ex)
    where
    newEntry (_,rule) = rule
    keyVal rule = (ruleName rule, rule)

type RuleMap ex = LookupMap (Rule ex)

fwdCheckInference :: (Eq ex) => Rule ex -> [ex] -> ex -> Bool
fwdCheckInference rule ante cons =
    (cons `elem` fwdApply rule ante)

bwdCheckInference :: (Eq ex) => Rule ex -> [ex] -> ex -> Bool
bwdCheckInference rule ante cons = any checkAnts (bwdApply rule cons)
    where
        checkAnts = all (`elem` ante)

nullRule :: Rule ex
nullRule = Rule
    { ruleName = ScopedName nullScope "nullRule"
    , fwdApply = \ _ -> []
    , bwdApply = \ _ -> []
    , checkInference = \ _ _ -> False
    }

------------------------------------------------------------
--  Shows formatting support functions
-----------------------------------------------------------

-- |Show a string left justified in a field of at least the specified
--  number of characters width.
showsWidth :: Int -> String -> ShowS
showsWidth wid str more = str++replicate pad ' '++more
    where
        pad = wid - length str


--------------------------------------------------------------------------------
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--
--  This file is part of Swish.
--
--  Swish is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or
--  (at your option) any later version.
--
--  Swish is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with Swish; if not, write to:
--    The Free Software Foundation, Inc.,
--    59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
--
--------------------------------------------------------------------------------
-- $Source: /file/cvsdev/HaskellRDF/Rule.hs,v $
-- $Author: graham $
-- $Revision: 1.8 $
-- $Log: Rule.hs,v $
-- Revision 1.8  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.7  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.6  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.5  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.4  2003/11/06 17:58:33  graham
-- About to rework Datatype to better support class-based reasoning.
--
-- Revision 1.3  2003/10/24 21:05:09  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
-- Revision 1.2  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.1  2003/09/30 20:00:46  graham
-- Add module Rule as common dependency for Proof and Ruleset
--
