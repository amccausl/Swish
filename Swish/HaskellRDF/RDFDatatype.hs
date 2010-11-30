--------------------------------------------------------------------------------
--  $Id: RDFDatatype.hs,v 1.14 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFDatatype
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + existential types
--
--  This module defines the structures used by Swish to represent and
--  manipulate RDF datatypes.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFDatatype
    ( RDFDatatype
    , RDFDatatypeVal
    , RDFDatatypeMod
    , RDFModifierFn, RDFApplyModifier
    , makeRdfDtOpenVarBindingModify, makeRdfDtOpenVarBindingModifiers
    , applyRDFDatatypeMod
    , RDFDatatypeSub
    , fromRDFLabel, toRDFLabel, makeDatatypedLiteral
    )
where

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..)
    , isDatatyped
    , getLiteralText
    , RDFGraph
    )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding, nullRDFVarBinding
    , RDFVarBindingModify, RDFOpenVarBindingModify
    )

import Swish.HaskellRDF.Datatype
    ( Datatype -- , typeName, typeRules
    , DatatypeVal(..)
    , getDTMod
    , DatatypeMap(..)
    , DatatypeMod(..), ModifierFn
    , nullDatatypeMod
    , ApplyModifier
    , DatatypeSub(..)
    )

import Swish.HaskellRDF.Ruleset
    ( Ruleset(..)
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getQName
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    , boundVars, subBinding, makeVarBinding
    , applyVarBinding, joinVarBindings, addVarBinding
    , VarBindingModify(..)
    )

import Data.Maybe
    ( Maybe(..), fromMaybe, isJust, fromJust )

import Control.Monad
    ( liftM )

------------------------------------------------------------
--  Specialize datatype framework types for use with RDF
------------------------------------------------------------

-- |RDF datatype wrapper used with RDF graph values
--
type RDFDatatype = Datatype RDFGraph RDFLabel RDFLabel

-- |RDF datatype value used with RDF graph values
--
type RDFDatatypeVal vt = DatatypeVal RDFGraph vt RDFLabel RDFLabel

-- |RDF datatype modifier used with RDF graph values
--
type RDFDatatypeMod vt = DatatypeMod vt RDFLabel RDFLabel

-- |Describe a subtype/supertype relationship between a pair
--  of RDF datatypes.
--
type RDFDatatypeSub supvt subvt = DatatypeSub RDFGraph RDFLabel RDFLabel supvt subvt

-- |RDF value modifier function type
--
--  This indicates a modifier function that operates on RDFLabel values.
--
type RDFModifierFn = ModifierFn RDFLabel

-- |RDF value modifier application function type
--
--  This indicates a function that applies RDFModifierFn functions.
--
type RDFApplyModifier = ApplyModifier RDFLabel RDFLabel

--------------------------------------------------------------
--  Functions for creating datatype variable binding modifiers
--------------------------------------------------------------

-- |Create an RDFOpenVarBindingModify value.
--
--  dtval   is an RDFDatatype value containing details of the datatype
--          for which a variable binding modifier is created.
--  dtmod   is the data value modifier value that defines the calculations
--          that are used to implement a variable binding modifier.
--
--  The key purpose of this function is to "lift" the supplied
--  variable constraint functions from operating on data values directly
--  to a corresponding list of functions that operate on values contained
--  in RDF graph labels (i.e. RDF literal nodes).  It also applies
--  node type checking, such that if the actual RDF nodes supplied do
--  not contain appropriate values then the variable binding is not
--  accepted.
--
makeRdfDtOpenVarBindingModify ::
    RDFDatatypeVal vt -> RDFDatatypeMod vt -> RDFOpenVarBindingModify
makeRdfDtOpenVarBindingModify dtval dtmod =
    dmAppf dtmod (dmName dtmod) $ map (makeRDFModifierFn dtval) (dmModf dtmod)

-- |Create all RDFOpenVarBindingModify values for a given datatype value.
--  See makeRdfDtOpenVarBindingModify abovr.
--
--  dtval   is an RDFDatatype value containing details of the datatype
--          for which variable binding modifiers are created.
--
makeRdfDtOpenVarBindingModifiers ::
    RDFDatatypeVal vt -> [RDFOpenVarBindingModify]
makeRdfDtOpenVarBindingModifiers dtval =
    map (makeRdfDtOpenVarBindingModify dtval) (tvalMod dtval)

-- |Apply a datatype modifier using supplied RDF labels to a supplied
--  RDF variable binding.
--
applyRDFDatatypeMod ::
    RDFDatatypeVal vt -> RDFDatatypeMod vt -> [RDFLabel] -> [RDFVarBinding]
    -> [RDFVarBinding]
applyRDFDatatypeMod dtval dtmod lbs =
    vbmApply (makeRdfDtOpenVarBindingModify dtval dtmod lbs)

-- |Given details of a datatype and a single value constraint function,
--  return a new constraint function that operates on RDFLabel values.
--
--  The returned constraint function incorporates checks for appropriately
--  typed literal nodes, and returns similarly typed literal nodes.
--
makeRDFModifierFn ::
    RDFDatatypeVal vt -> ModifierFn vt -> RDFModifierFn
makeRDFModifierFn dtval fn ivs =
    let
        ivals = sequence $ map (rdfNodeExtract dtval) ivs
        ovals | isJust ivals = fn (fromJust ivals)
              | otherwise    = []
    in
        fromMaybe [] $ sequence $ map (rdfNodeInject dtval) ovals

-- |Extract datatyped value from RDFLabel value, or return Nothing.
--
rdfNodeExtract :: RDFDatatypeVal vt -> RDFLabel -> Maybe vt
rdfNodeExtract dtval node
    | isDatatyped dtname node = mapL2V dtmap $ getLiteralText node
    | otherwise               = Nothing
    where
        dtname = tvalName dtval
        dtmap  = tvalMap  dtval

-- |Return new RDF literal node with a representation of the supplied
--  value, or Nothing.
--
rdfNodeInject :: RDFDatatypeVal vt -> vt -> Maybe RDFLabel
rdfNodeInject dtval val = maybeNode valstr
    where
        valstr = mapV2L (tvalMap  dtval) val
        maybeNode Nothing    = Nothing
        maybeNode (Just str) = Just $ Lit str (Just (tvalName dtval))

------------------------------------------------------------
--  Helpers to map between datatype values and RDFLabels
------------------------------------------------------------

fromRDFLabel ::
    RDFDatatypeVal vt -> RDFLabel -> Maybe vt
fromRDFLabel dtv lab
    | isDatatyped dtnam lab = mapL2V dtmap $ getLiteralText lab
    | otherwise             = Nothing
    where
        dtnam = tvalName dtv
        dtmap = tvalMap dtv

toRDFLabel :: RDFDatatypeVal vt -> vt -> Maybe RDFLabel
toRDFLabel dtv =
    liftM (makeDatatypedLiteral dtnam) . mapV2L dtmap
    where
        dtnam = tvalName dtv
        dtmap = tvalMap dtv

makeDatatypedLiteral :: ScopedName -> String -> RDFLabel
makeDatatypedLiteral dtnam strval =
    Lit strval (Just dtnam)

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
-- $Source: /file/cvsdev/HaskellRDF/RDFDatatype.hs,v $
-- $Author: graham $
-- $Revision: 1.14 $
-- $Log: RDFDatatype.hs,v $
-- Revision 1.14  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.13  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.12  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.11  2003/12/08 17:29:19  graham
-- Moved OpenVarBinding type definitions from -Datatype to -VarBinding modules.
--
-- Revision 1.10  2003/11/28 00:17:55  graham
-- Datatype constraint test cases all passed.
--
-- Revision 1.9  2003/11/25 23:02:17  graham
-- Reworked datatype variable modifier logic.
-- Limited range of test cases so far all pass.
--
-- Revision 1.8  2003/11/24 22:13:09  graham
-- Working on reworking datatype variable modifiers to work with
-- revised datatype framework.
--
-- Revision 1.7  2003/11/14 21:48:35  graham
-- First cut cardinality-checked datatype-constraint rules to pass test cases.
-- Backward chaining is still to do.
--
-- Revision 1.6  2003/11/13 01:14:32  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.4  2003/11/11 21:02:55  graham
-- Working on datatype class-constraint inference rule.  Incomplete.
--
-- Revision 1.3  2003/11/07 21:45:47  graham
-- Started rework of datatype to use new DatatypeRel structure.
--
-- Revision 1.2  2003/10/24 21:05:08  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
-- Revision 1.1  2003/10/22 15:46:38  graham
-- Add RDFDatatype module.
--
