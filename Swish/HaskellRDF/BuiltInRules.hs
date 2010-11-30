--------------------------------------------------------------------------------
--  $Id: BuiltInRules.hs,v 1.2 2003/12/18 18:27:46 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  BuiltInRules
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module collects references and provides access to all of the
--  rulesets, variable binding modifiers and variable binding filters
--  built in to Swish.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.BuiltInRules
    ( findRDFOpenVarBindingModifier
    , rdfRulesetMap
    , allRulesets, allDatatypeRulesets
    )
where

import Swish.HaskellRDF.BuiltInDatatypes
    ( allDatatypes )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFOpenVarBindingModify
    , rdfVarBindingUriRef, rdfVarBindingBlank
    , rdfVarBindingLiteral
    , rdfVarBindingUntypedLiteral, rdfVarBindingTypedLiteral
    , rdfVarBindingXMLLiteral, rdfVarBindingDatatyped
    , rdfVarBindingMemberProp
    )

import Swish.HaskellRDF.RDFRuleset
    ( RDFRuleset, RDFRulesetMap )

import Swish.HaskellRDF.RDFProofContext
    ( rulesetRDF
    , rulesetRDFS
    , rulesetRDFD )

import Swish.HaskellRDF.VarBinding
    ( nullVarBindingModify
    , makeVarFilterModify
    , varFilterEQ, varFilterNE
    )

import Swish.HaskellRDF.Datatype
    ( typeRules
    , typeMkModifiers
    )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..)
    , mapFindMaybe
    )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..) )

------------------------------------------------------------
--  Declare variable binding filters list
------------------------------------------------------------

-- |List of rdfOpenVarBindingModify values for predefined filters
--
rdfVarBindingFilters :: [RDFOpenVarBindingModify]
rdfVarBindingFilters =
    [ filter1 rdfVarBindingUriRef
    , filter1 rdfVarBindingBlank
    , filter1 rdfVarBindingLiteral
    , filter1 rdfVarBindingUntypedLiteral
    , filter1 rdfVarBindingTypedLiteral
    , filter1 rdfVarBindingXMLLiteral
    , filter1 rdfVarBindingMemberProp
    , filter2 rdfVarBindingDatatyped
    -- , filterN nullVarBindingModify
    , filter2 varFilterEQ
    , filter2 varFilterNE
    ]
    where
        filter1 f lbs = makeVarFilterModify $ f (lbs!!0)
        filter2 f lbs = makeVarFilterModify $ f (lbs!!0) (lbs!!1)
        -- filterN f lbs = makeVarFilterModify $ f ...

------------------------------------------------------------
--  Declare variable binding modifiers map
------------------------------------------------------------

rdfVarBindingModifiers :: [RDFOpenVarBindingModify]
rdfVarBindingModifiers =
    [ nullVarBindingModify
    ]

------------------------------------------------------------
--  Find a named built-in OpenVarBindingModifier
------------------------------------------------------------

allOpenVarBindingModify :: [RDFOpenVarBindingModify]
allOpenVarBindingModify =
    rdfVarBindingFilters    ++
    rdfVarBindingModifiers  ++
    dtsVarBindingModifiers

-- dtsVarBindingModifiers = concatMap dtVarBindingModifiers allDatatypes
dtsVarBindingModifiers = concatMap typeMkModifiers allDatatypes

{-
dtVarBindingModifiers dtval =
    map (makeRdfDtOpenVarBindingModify dtval) (tvalMod dtval)
-}

findRDFOpenVarBindingModifier :: ScopedName -> Maybe RDFOpenVarBindingModify
findRDFOpenVarBindingModifier nam =
    mapFindMaybe nam (LookupMap allOpenVarBindingModify)

------------------------------------------------------------
--  Lookup map for built-in rulesets
------------------------------------------------------------

rdfRulesetMap :: RDFRulesetMap
rdfRulesetMap = LookupMap allRulesets

allRulesets :: [RDFRuleset]
allRulesets =
    [ rulesetRDF
    , rulesetRDFS
    , rulesetRDFD
    ]
    ++ allDatatypeRulesets

allDatatypeRulesets :: [RDFRuleset]
allDatatypeRulesets = map typeRules allDatatypes

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
-- $Source: /file/cvsdev/HaskellRDF/BuiltInRules.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: BuiltInRules.hs,v $
-- Revision 1.2  2003/12/18 18:27:46  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.1  2003/12/17 16:56:39  graham
-- Split content of BuiltInMap into separate modules, to avoid recursive
-- module dependency with RDFProofContext.
--
