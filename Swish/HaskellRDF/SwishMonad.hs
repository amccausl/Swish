{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
--------------------------------------------------------------------------------
--  $Id: SwishMonad.hs,v 1.12 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  SwishMonad
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  SwishMonad:  Composed state and IO monad for Swish
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.SwishMonad
    ( SwishStateIO, SwishState(..)
    , setFormat, setGraph
    , modGraphs, findGraph, findFormula
    , modRules, findRule
    , modRulesets, findRuleset
    , findOpenVarModify, findDatatype
    , setInfo, resetInfo, setError, resetError, setExitcode
    , emptyState
    , SwishFormat(..)
    , NamedGraph(..)
    , swishError
    , reportLines, reportLine
    )
where

import Swish.HaskellRDF.RDFGraph
    ( RDFGraph, emptyRDFGraph )

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFRuleMap, RDFRuleset, RDFRulesetMap )

import Swish.HaskellRDF.RDFDatatype
    ( RDFDatatype )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFOpenVarBindingModify
    )

import Swish.HaskellRDF.BuiltInMap
    ( findRDFOpenVarBindingModifier
    , findRDFDatatype
    , rdfRulesetMap
    )

import Swish.HaskellRDF.Ruleset
    ( getMaybeContextAxiom
    , getMaybeContextRule
    )

import Swish.HaskellRDF.Rule
    ( Formula(..)
    )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..) )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    , emptyLookupMap
    , mapFindMaybe
    , mapVals
    )

import Control.Monad.Trans
    ( MonadTrans(..) )

import Control.Monad.State
    ( modify, StateT(..))

import System.Exit
    ( ExitCode(ExitSuccess,ExitFailure) )

import System.IO
    ( hPutStrLn, stderr )

------------------------------------------------------------
--  State and state monad for Swish program
------------------------------------------------------------
--
--  Uses StateT Monad transformer:
--  See example by Mark Carroll at http://www.haskell.org/hawiki/MonadState

data SwishFormat = N3 | NT | RDF
    deriving (Eq, Show)

data SwishState = SwishState
    { format    :: SwishFormat
    , graph     :: RDFGraph         -- current graph
    , graphs    :: NamedGraphMap    -- script processor named graphs
    , rules     :: RDFRuleMap       -- script processor named rules
    , rulesets  :: RDFRulesetMap    -- script processor rulesets
    , infomsg   :: Maybe String     -- information message, or Nothing
    , errormsg  :: Maybe String     -- error message, or Nothing
    , exitcode  :: ExitCode
    }

type SwishStateIO a = StateT SwishState IO a

emptyState :: SwishState
emptyState = SwishState
    { format    = N3
    , graph     = emptyRDFGraph
    , graphs    = emptyLookupMap
    , rules     = emptyLookupMap
    , rulesets  = rdfRulesetMap
    , infomsg   = Nothing
    , errormsg  = Nothing
    , exitcode  = ExitSuccess
    }

setFormat :: SwishFormat -> SwishState -> SwishState
setFormat   fm state = state { format = fm }

setGraph :: RDFGraph -> SwishState -> SwishState
setGraph    gr state = state { graph = gr }

modGraphs ::
    ( NamedGraphMap -> NamedGraphMap ) -> SwishState -> SwishState
modGraphs grmod state = state { graphs = grmod (graphs state) }

findGraph :: ScopedName -> SwishState -> Maybe [RDFGraph]
findGraph nam state = mapFindMaybe nam (graphs state)

findFormula :: ScopedName -> SwishState -> Maybe RDFFormula
findFormula nam state = case findGraph nam state of
        Nothing  -> getMaybeContextAxiom nam (mapVals $ rulesets state)
        Just []  -> Just $ Formula nam emptyRDFGraph
        Just grs -> Just $ Formula nam (head grs)

modRules ::
    ( RDFRuleMap -> RDFRuleMap ) -> SwishState -> SwishState
modRules rlmod state = state { rules = rlmod (rules state) }

findRule :: ScopedName -> SwishState -> Maybe RDFRule
findRule nam state =
    let
        localrule   = mapFindMaybe nam (rules state)
        contextrule = getMaybeContextRule nam $ mapVals $ rulesets state
    in
        case localrule of
            Nothing -> contextrule
            justlr  -> justlr

modRulesets ::
    ( RDFRulesetMap -> RDFRulesetMap ) -> SwishState -> SwishState
modRulesets rsmod state = state { rulesets = rsmod (rulesets state) }

findRuleset ::
    ScopedName -> SwishState -> Maybe RDFRuleset
findRuleset nam state = mapFindMaybe (snScope nam) (rulesets state)

findOpenVarModify :: ScopedName -> SwishState -> Maybe RDFOpenVarBindingModify
findOpenVarModify nam _ = findRDFOpenVarBindingModifier nam

findDatatype :: ScopedName -> SwishState -> Maybe RDFDatatype
findDatatype nam _ = findRDFDatatype nam

setInfo :: String -> SwishState -> SwishState
setInfo msg state = state { infomsg = Just msg }

resetInfo :: SwishState -> SwishState
resetInfo state = state { infomsg = Nothing }

setError :: String -> SwishState -> SwishState
setError msg state = state { errormsg = Just msg }

resetError :: SwishState -> SwishState
resetError state = state { errormsg = Nothing }

setExitcode :: ExitCode -> SwishState -> SwishState
setExitcode ec state = state { exitcode = ec }


------------------------------------------------------------
--  Data types for Swish script dictionaries
------------------------------------------------------------
--
--  The graphs dictionary contains named graphs and/or lists
--  of graphs that are created and used by script statements.

data NamedGraph = NamedGraph
    { ngName    :: ScopedName
    , ngGraph   :: [RDFGraph]
    }

instance LookupEntryClass NamedGraph ScopedName [RDFGraph]
    where
        keyVal   (NamedGraph k v) = (k,v)
        newEntry (k,v)            = (NamedGraph k v)

type NamedGraphMap = LookupMap NamedGraph

------------------------------------------------------------
--  Report error and set exit status code
------------------------------------------------------------

swishError :: String -> Int -> SwishStateIO ()
swishError msg sts =
    do  { reportLine $ msg
        ; if sts == 4 then
            reportLine $ "Use 'Swish -?' for help"
          else
            return ()
        ; modify $ setExitcode (ExitFailure sts)
        }

------------------------------------------------------------
--  Output text to the standard error stream
------------------------------------------------------------
--
--  Each string in the supplied list is a line of text to
--  be displayed.

reportLines  :: [String] -> SwishStateIO ()
reportLines text =
    sequence_ (map reportLine text)

reportLine  :: String -> SwishStateIO ()
reportLine line =
    -- lift putStrLn line
    lift $ hPutStrLn stderr line

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
-- $Source: /file/cvsdev/HaskellRDF/SwishMonad.hs,v $
-- $Author: graham $
-- $Revision: 1.12 $
-- $Log: SwishMonad.hs,v $
-- Revision 1.12  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.11  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.10  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.9  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.8  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.7  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.6  2003/12/01 18:51:38  graham
-- Described syntax for Swish script.
-- Created Swish scripting test data.
-- Edited export/import lists in Swish main program modules.
--
-- Revision 1.5  2003/09/24 18:50:53  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.4  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.3  2003/05/29 12:39:49  graham
-- Improved error handling for stand-alone swish program
--
-- Revision 1.2  2003/05/21 13:34:13  graham
-- Various N3 parser bug fixes.
-- Need to fix handling of :name terms.
--
-- Revision 1.1  2003/05/20 23:36:30  graham
-- Add new Swish modules
--
