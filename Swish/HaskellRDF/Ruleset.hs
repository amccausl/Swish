{-# OPTIONS -XMultiParamTypeClasses #-}

--------------------------------------------------------------------------------
--  $Id: Ruleset.hs,v 1.9 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Ruleset
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a ruleset data type, used to collect information
--  about a ruleset that may contribute torwards inferences in RDF;
--  e.g. RDF and RDFS are rulesets.
--
--  A ruleset consists of a namespace, a collection of axioms and
--  a collection of rules.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.Ruleset
    ( Ruleset(..), RulesetMap
    , makeRuleset, getRulesetNamespace, getRulesetAxioms, getRulesetRules
    , getRulesetAxiom, getRulesetRule
    , getContextAxiom, getMaybeContextAxiom
    , getContextRule,  getMaybeContextRule
    )
where

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI
    , matchName )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..)
    , fwdCheckInference
    , showsFormula, showsFormulae, showsWidth
    )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    , mapFindMaybe
    )

import Data.Maybe
    ( Maybe(..), isJust, fromJust, fromMaybe, listToMaybe, mapMaybe )

------------------------------------------------------------
--  Ruleset, having namespace, axioms and rules
------------------------------------------------------------

data Ruleset ex = Ruleset
    { rsNamespace :: Namespace
    , rsAxioms    :: [Formula ex]
    , rsRules     :: [Rule ex]
    }

instance Eq (Ruleset ex) where
    r1 == r2 = rsNamespace r1 == rsNamespace r2

instance LookupEntryClass (Ruleset ex) Namespace (Ruleset ex)
    where
        keyVal   r@(Ruleset k _ _) = (k,r)
        newEntry (_,r)             = r

type RulesetMap ex = LookupMap (Ruleset ex)

makeRuleset :: Namespace -> [Formula ex] -> [Rule ex] -> Ruleset ex
makeRuleset nsp fms rls = Ruleset
    { rsNamespace = nsp
    , rsAxioms    = fms
    , rsRules     = rls
    }

getRulesetNamespace :: Ruleset ex -> Namespace
getRulesetNamespace = rsNamespace

getRulesetAxioms :: Ruleset ex -> [Formula ex]
getRulesetAxioms = rsAxioms

getRulesetRules :: Ruleset ex -> [Rule ex]
getRulesetRules = rsRules

------------------------------------------------------------
--  Find a named axiom or rule in a ruleset or proof context
------------------------------------------------------------

getRulesetAxiom :: ScopedName -> Ruleset ex -> Maybe (Formula ex)
getRulesetAxiom nam rset =
    mapFindMaybe nam (LookupMap (getRulesetAxioms rset))
    -- listToMaybe $ filter ( (matchName nam) . formName ) $ getRulesetAxioms rset

getRulesetRule :: ScopedName -> Ruleset ex -> Maybe (Rule ex)
getRulesetRule nam rset =
    mapFindMaybe nam (LookupMap (getRulesetRules rset))
    -- listToMaybe $ filter ( (matchName nam) . ruleName ) $ getRulesetRules rset

getContextAxiom :: ScopedName -> Formula ex -> [Ruleset ex] -> Formula ex
getContextAxiom nam def rsets = fromMaybe def (getMaybeContextAxiom nam rsets)
    {-
    foldr (flip fromMaybe) def $ map (getRulesetAxiom nam) rsets
    -}

getMaybeContextAxiom :: ScopedName -> [Ruleset ex] -> Maybe (Formula ex)
getMaybeContextAxiom nam rsets =
    listToMaybe $ mapMaybe (getRulesetAxiom nam) rsets

getContextRule :: ScopedName -> Rule ex -> [Ruleset ex] -> Rule ex
getContextRule nam def rsets = fromMaybe def (getMaybeContextRule nam rsets)
    {-
    foldr (flip fromMaybe) def $ map (getRulesetRule nam) rsets
    -}

getMaybeContextRule :: ScopedName -> [Ruleset ex] -> Maybe (Rule ex)
getMaybeContextRule nam rsets =
    listToMaybe $ mapMaybe (getRulesetRule nam) rsets

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
-- $Source: /file/cvsdev/HaskellRDF/Ruleset.hs,v $
-- $Author: graham $
-- $Revision: 1.9 $
-- $Log: Ruleset.hs,v $
-- Revision 1.9  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.8  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.7  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.6  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.5  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.4  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.3  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.2  2003/09/30 20:02:40  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.1  2003/09/30 16:38:19  graham
-- Add Ruleset and RDFRuleset modules to provide proof context elements
--
