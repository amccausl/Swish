{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}

--------------------------------------------------------------------------------
--  $Id: GraphMem.hs,v 1.16 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphMem
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a simple memory-based graph instance.
--
--------------------------------------------------------------------------------

------------------------------------------------------------
-- Simple labelled directed graph value
------------------------------------------------------------

module Swish.HaskellRDF.GraphMem
    ( GraphMem(..)
    , setArcs, getArcs, add, delete, extract, labels
    , LabelMem(..)
    , labelIsVar, labelHash
      -- For debug/test:
    , matchGraphMem
    ) where

import Swish.HaskellUtils.LookupMap
import Swish.HaskellRDF.GraphClass
import Swish.HaskellRDF.GraphMatch
import Swish.HaskellUtils.MiscHelpers
    ( hash )
import Swish.HaskellUtils.FunctorM
    ( FunctorM(..) )
import Data.List
    ( nub, union, (\\), group, sort, sortBy, any )
import Data.Maybe
    ( isJust )

-----------------------------------------------------
--  Memory-based graph type and graph class functions
-----------------------------------------------------

data GraphMem lb = GraphMem { arcs :: [Arc lb] }

instance (Label lb) => LDGraph GraphMem lb where
    getArcs      = arcs
    setArcs as g = g { arcs=as }
    -- gmap f g = g { arcs = (map $ fmap f) (arcs g) }

instance (Label lb) => Eq (GraphMem lb) where
    (==) = graphEq

instance (Label lb) => Show (GraphMem lb) where
    show = graphShow

instance Functor GraphMem where
    fmap f g = GraphMem $ map (fmap f) (arcs g)

instance FunctorM GraphMem where
    fmapM f g =
        do  { arcs <- mapM (fmapM f) (arcs g)
            ; return $ GraphMem arcs
            }

graphShow   :: (Label lb) => GraphMem lb -> String
graphShow g = "Graph:"++(foldr (++) "" (map ("\n    "++) (map show (arcs g))))

toGraph :: (Label lb) => [Arc lb] -> GraphMem lb
toGraph as = GraphMem { arcs=(nub as) }

-----------
--  graphEq
-----------
--
--  Return Boolean graph equality

graphEq :: (Label lb) => GraphMem lb -> GraphMem lb -> Bool
graphEq g1 g2 = fst ( matchGraphMem g1 g2 )

-----------------
--  matchGraphMem
-----------------
--
--  GraphMem matching function accepting GraphMem value and returning
--  node map if successful
--
--  g1      is the first of two graphs to be compared
--  g2      is the second of two graphs to be compared
--
--  returns a label map that maps each label to an equivalence
--          class identifier, or Nothing if the graphs cannot be
--          matched.

matchGraphMem :: (Label lb) => GraphMem lb -> GraphMem lb
                            -> (Bool,LabelMap (ScopedLabel lb))
matchGraphMem g1 g2 =
    let
        gs1     = arcs g1
        gs2     = arcs g2
        matchable l1 l2
            | (labelIsVar l1) && (labelIsVar l2) = True
            | (labelIsVar l1) || (labelIsVar l2) = False
            | otherwise                          = l1 == l2
    in
        graphMatch matchable gs1 gs2

---------------
--  graphBiject
---------------
--
--  Return bijection between two graphs, or empty list
{-
graphBiject :: (Label lb) => GraphMem lb -> GraphMem lb -> [(lb,lb)]
graphBiject g1 g2 = if null lmap then [] else zip (sortedls g1) (sortedls g2)
    where
        lmap        = graphMatch g1 g2
        sortedls g  = map snd $
                      (sortBy indexComp) $
                      equivalenceClasses (graphLabels $ arcs g) lmap
        classComp ec1 ec2 = indexComp (classIndexVal ec1) (classIndexVal ec2)
        indexComp (g1,v1) (g2,v2)
            | g1 == g2  = compare v1 v2
            | otherwise = compare g1 g2
-}

------------------------------------------------------------
--  Minimal graph label value - for testing
------------------------------------------------------------

data LabelMem
    = LF String
    | LV String

instance Label LabelMem where
    labelIsVar (LV _)   = True
    labelIsVar _        = False
    getLocal   (LV loc) = loc
    getLocal   lab      = error "getLocal of non-variable label: "++(show lab)
    makeLabel  loc      = LV loc
    labelHash  seed lb  = hash seed (show lb)

instance Eq LabelMem where
    (LF l1) == (LF l2)  = l1 == l2
    (LV l1) == (LV l2)  = l1 == l2
    _ == _              = False

instance Show LabelMem where
    show (LF l1)        = "!"++l1
    show (LV l2)        = "?"++l2

instance Ord LabelMem where
    compare l1 l2 = compare (show l1) (show l2)

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
-- $Source: /file/cvsdev/HaskellRDF/GraphMem.hs,v $
-- $Author: graham $
-- $Revision: 1.16 $
-- $Log: GraphMem.hs,v $
-- Revision 1.16  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.15  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.14  2003/06/10 17:38:34  graham
-- Remove some unneeded calss constraints from data type declarations
-- Reworked NSGraph to be an instance of Functor, replacing function
-- gmap with fmap.  Graph formulae are still not handled well:  the data types
-- will need re-working so that a "Formula lb" type constructor can be
-- introduced having the correct (* -> *) kind to be a Functor.
--
-- Revision 1.13  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.12  2003/05/30 15:04:56  graham
-- Fix references to defunct GraphHelpers module
--
-- Revision 1.11  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.10  2003/05/23 16:29:20  graham
-- Partial code cleanup:
-- - Arc is an alebraic type
-- - Arc is an instance of Functor
-- - add gmap function to Graph interface
-- - remove some duplicate functions from GraphMatch
-- This in preparation for adding graph merge facility with
-- blank node renaming.
--
-- Revision 1.9  2003/05/14 02:01:59  graham
-- GraphMatch recoded and almost working, but
-- there are a couple of
-- obscure bugs that are proving rather stubborn to squash.
--
-- Revision 1.8  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.7  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.6  2003/04/11 18:04:49  graham
-- Rename GraphLookupMap to LookupMap:
-- GraphTest runs OK.
--
-- Revision 1.5  2003/04/10 13:41:22  graham
-- More graph code tidying
-- Graph test cases still run OK
--
-- Revision 1.4  2003/04/10 13:35:34  graham
-- Separated GraphMatch logic from GraphMem
--
-- Revision 1.3  2003/04/10 08:36:06  graham
-- Graph matching passes battery of new tests
-- Started work on RDF graph
--
-- Revision 1.2  2003/03/31 20:52:23  graham
-- Restructure graph matching to deal with same unbound node names in
-- different graphs.  It shows signs that it might be working now.
-- More testing is needed.
--
-- Revision 1.1  2003/03/28 21:50:22  graham
-- Graph equality coded and nearly working
--
