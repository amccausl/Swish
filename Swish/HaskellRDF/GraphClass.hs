{-# OPTIONS -XMultiParamTypeClasses #-}


--------------------------------------------------------------------------------
--  $Id: GraphClass.hs,v 1.16 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphClass
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a Labelled Directed Graph and Label classes,
--  and the Arc datatype.
--
--------------------------------------------------------------------------------

------------------------------------------------------------
-- Define LDGraph, arc and related classes and types
------------------------------------------------------------

module Swish.HaskellRDF.GraphClass
    ( LDGraph(..), replaceArcs
    , Label(..)
    , Arc(..), arcSubj, arcPred, arcObj, arc, arcToTriple, arcFromTriple
    , Selector
    , hasLabel, arcLabels
    )
where

import Swish.HaskellUtils.ListHelpers
    ( subset )

import Swish.HaskellUtils.FunctorM
    ( FunctorM(..) )

import Data.List
    ( nub, union, (\\) )

--------------------------------
--  Labelled Directed Graph class
--------------------------------
--
--  Minimum required implementation:  setArcs, getArcs
--
--  NOTE:  I wanted to declare this as a subclass of Functor, but
--  the constraint on the label type seems to prevent that.
--  So I've just declared specific instances to be Functors.
class (Eq (lg lb), Eq lb ) => LDGraph lg lb
    where
    --  empty graph
    --  emptyGr     :: lg lb    [[[TODO?]]]
    --  component-level operations
    setArcs     :: [Arc lb] -> lg lb -> lg lb       -- setarcs [arcs] in g2 -> g3
    getArcs     :: lg lb -> [Arc lb]                -- g1 -> [arcs]
    --  extract arcs from a graph
    extract     :: Selector lb -> lg lb -> lg lb    -- select f1 from g2 -> g3
    extract sel = update (filter sel)
    --  graph-level operations
    add         :: lg lb -> lg lb -> lg lb          -- g1 + g2 -> g3
    add    addg = update (union (getArcs addg))
    delete      :: lg lb -> lg lb -> lg lb          -- g2 - g1 -> g3
    delete delg = update (flip (\\) (getArcs delg))
    --  enumerate distinct labels contained in a graph
    labels      :: lg lb -> [lb]      -- g1 -> [labels]
    labels g    = foldl union [] (map arcLabels (getArcs g))
    --  enumerate distinct labels contained in a graph
    nodes       :: lg lb -> [lb]      -- g1 -> [labels]
    nodes g     = foldl union [] (map arcNodes (getArcs g))
    --  test for graph containment in another
    containedIn :: lg lb -> lg lb -> Bool           -- g1 <= g2?
    -- g1 update arcs in a graph using a supplied function:
    update      :: ( [Arc lb] -> [Arc lb] ) -> lg lb -> lg lb
    update f g  = setArcs ( f (getArcs g) ) g

-- |Function to replace arcs in a graph with a given list of arcs
replaceArcs :: (LDGraph lg lb) => lg lb -> [Arc lb] -> lg lb
replaceArcs gr as = update (const as) gr

---------------
--  Label class
---------------
--
--  A label may have a fixed binding, which means that the label identifies (is) a
--  particular graph node, and different such labels are always distinct nodes.
--  Alternatively, a label may be unbound (variable), which means that it is a
--  placeholder for an unknown node label.  Unbound node labels are used as
--  graph-local identifiers for indicating when the same node appears in
--  several arcs.
--
--  For the purposes of graph-isomorphism testing, fixed labels are matched when they
--  are the same.  Variable labels may be matched with any other variable label.
--  Our definition of isomorphism (for RDF graphs) does not match variable labels
--  with fixed labels.

class (Eq lb, Show lb, Ord lb) => Label lb where
    labelIsVar  :: lb -> Bool           -- does this node have a variable binding?
    labelHash   :: Int -> lb -> Int     -- calculate hash of label using supplied seed
    getLocal    :: lb -> String         -- extract local id from variable node
    makeLabel   :: String -> lb         -- make label value given local id
    -- compare     :: lb -> lb -> Ordering
    -- compare l1 l2 = compare (show l1) (show l2)

------------
--  Arc type
------------

data Arc lb = Arc { asubj, apred, aobj :: lb }
    deriving Eq

arcSubj :: Arc lb -> lb
arcSubj = asubj

arcPred :: Arc lb -> lb
arcPred = apred

arcObj :: Arc lb -> lb
arcObj = aobj

arc :: lb -> lb -> lb -> Arc lb
arc s p o = Arc s p o

arcToTriple :: Arc lb -> (lb,lb,lb)
arcToTriple a = (asubj a,apred a,aobj a)

arcFromTriple :: (lb,lb,lb) -> Arc lb
arcFromTriple (s,p,o) = Arc s p o

instance Ord lb => Ord (Arc lb) where
    compare (Arc s1 p1 o1) (Arc s2 p2 o2) =
        if cs /= EQ then cs else
        if cp /= EQ then cp else co
        where
            cs = compare s1 s2
            cp = compare p1 p2
            co = compare o1 o2
    (Arc s1 p1 o1) <= (Arc s2 p2 o2) =
        if (s1 /= s2) then (s1 <= s2) else
        if (p1 /= p2) then (p1 <= p2) else (o1 <= o2)

instance Functor Arc where
    -- fmap :: (lb -> l2) -> Arc lb -> Arc l2
    fmap f (Arc s p o) = Arc (f s) (f p) (f o)

instance FunctorM Arc where
    -- fmapM :: (lb -> m l2) -> Arc lb -> m (Arc l2)
    fmapM f (Arc s p o) =
        do  { s' <- f s
            ; p' <- f p
            ; o' <- f o
            ; return $ Arc s' p' o'
            }

instance (Show lb) => Show (Arc lb) where
    show (Arc lb1 lb2 lb3) =
        "("++(show lb1)++","++(show lb2)++","++(show lb3)++")"

type Selector lb = Arc lb -> Bool

hasLabel :: (Eq lb) => lb -> Arc lb -> Bool
hasLabel lbv (Arc lb1 lb2 lb3) = (lbv==lb1) || (lbv==lb2) || (lbv==lb3)

arcLabels :: Arc lb -> [lb]
arcLabels (Arc lb1 lb2 lb3) = [lb1,lb2,lb3]

arcNodes :: Arc lb -> [lb]
arcNodes (Arc lb1 _ lb3) = [lb1,lb3]

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
-- $Source: /file/cvsdev/HaskellRDF/GraphClass.hs,v $
-- $Author: graham $
-- $Revision: 1.16 $
-- $Log: GraphClass.hs,v $
-- Revision 1.16  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.15  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.14  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.13  2003/06/27 20:46:00  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.12  2003/06/10 17:38:34  graham
-- Remove some unneeded calss constraints from data type declarations
-- Reworked NSGraph to be an instance of Functor, replacing function
-- gmap with fmap.  Graph formulae are still not handled well:  the data types
-- will need re-working so that a "Formula lb" type constructor can be
-- introduced having the correct (* -> *) kind to be a Functor.
--
-- Revision 1.11  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.10  2003/05/30 15:04:56  graham
-- Fix references to defunct GraphHelpers module
--
-- Revision 1.9  2003/05/29 01:50:56  graham
-- More performance tuning, courtesy of GHC profiler.
-- All modules showing reasonable performance now.
--
-- Revision 1.8  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.7  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.6  2003/05/23 16:29:20  graham
-- Partial code cleanup:
-- - Arc is an alebraic type
-- - Arc is an instance of Functor
-- - add gmap function to Graph interface
-- - remove some duplicate functions from GraphMatch
-- This in preparation for adding graph merge facility with
-- blank node renaming.
--
-- Revision 1.5  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
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
