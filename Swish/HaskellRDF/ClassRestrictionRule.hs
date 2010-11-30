{-# OPTIONS -XMultiParamTypeClasses #-}
--------------------------------------------------------------------------------
--  $Id: ClassRestrictionRule.hs,v 1.15 2004/01/07 19:49:12 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ClassRestrictionRule
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module implements an inference rule based on a restruction on class
--  membership of one or more values.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.ClassRestrictionRule
    ( ClassRestriction(..), ClassRestrictionFn
    , makeDatatypeRestriction, makeDatatypeRestrictionFn
    , makeRDFClassRestrictionRules
    , makeRDFDatatypeRestrictionRules
    , falseGraph, falseGraphStr
    )
where

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..)
    , getScopedName
    , RDFGraph
    , getArcs
    , merge
    , toRDFGraph, emptyRDFGraph
    , Arc(..)
    , res_rdf_type
    , res_rdfd_maxCardinality
    )

import Swish.HaskellRDF.RDFRuleset
    ( RDFRule
    , makeRDFGraphFromN3String
    )

import Swish.HaskellRDF.RDFDatatype
    ( RDFDatatypeVal
    , fromRDFLabel, toRDFLabel
    )

import Swish.HaskellRDF.RDFQuery
    ( rdfQueryFind
    , rdfFindValSubj, rdfFindPredVal, rdfFindPredInt
    , rdfFindList
    )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding )

import Swish.HaskellRDF.Datatype
    ( DatatypeVal(..)
    , DatatypeRel(..), DatatypeRelFn
    )

import Swish.HaskellRDF.Rule
    ( Rule(..)
    , bwdCheckInference
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDFD
    )

import Swish.HaskellUtils.PartOrderedCollection
    ( minima, maxima
    , partCompareEq, partComparePair
    , partCompareListMaybe
    , partCompareListSubset
    )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    , mapFindMaybe
    )

import Swish.HaskellUtils.ListHelpers
    ( powerSet )

import Data.Maybe
    ( Maybe(..)
    , isJust, fromJust, fromMaybe, catMaybes )

import Data.List
    ( delete, nub, (\\) )

import Control.Monad
    ( liftM )

import Swish.HaskellUtils.TraceHelpers
    ( trace )

------------------------------------------------------------
--  Class restriction data type
------------------------------------------------------------

-- |Type of function that evaluates missing node values in a
--  restriction from those supplied.
type ClassRestrictionFn = [Maybe RDFLabel] -> Maybe [[RDFLabel]]

-- |Datatype for named class restriction
data ClassRestriction = ClassRestriction
    { crName    :: ScopedName
    , crFunc    :: ClassRestrictionFn
    }

instance Eq ClassRestriction where
    cr1 == cr2  =  crName cr1 == crName cr2

instance Show ClassRestriction where
    show cr = "ClassRestriction:"++(show $ crName cr)

instance LookupEntryClass ClassRestriction ScopedName ClassRestriction
    where
    newEntry (_,fn) = fn
    keyVal cr = (crName cr, cr)

------------------------------------------------------------
--  Instantiate a class restriction from a datatype relation
------------------------------------------------------------

-- |Make a class restriction from a datatype relation.
--
--  This "lifts" application of the datatype relation to operate
--  on RDFLabel values, which are presumed to contain appropriately
--  datatyped values.
--
makeDatatypeRestriction ::
    RDFDatatypeVal vt -> DatatypeRel vt -> ClassRestriction
makeDatatypeRestriction dtv dtrel = ClassRestriction
    { crName = dtRelName dtrel
    , crFunc = makeDatatypeRestrictionFn dtv (dtRelFunc dtrel)
    }

-- |Make a class restriction function from a datatype relation function.
--
--  The core logic is something like (map toLabels . dtrelfn . map frLabel)
--  but the extra lifting and catMaybes are needed to get the final result
--  type in the right form.
--
--  ClassRestrictionFn = [Maybe RDFLabel] -> Maybe [[RDFLabel]]
--
makeDatatypeRestrictionFn ::
    RDFDatatypeVal vt -> DatatypeRelFn vt -> ClassRestrictionFn
makeDatatypeRestrictionFn dtv dtrelfn =
    liftM (catMaybes . map toLabels) . dtrelfn . (map frLabel)
    where
        frLabel Nothing  = Nothing
        frLabel (Just l) = fromRDFLabel dtv l
        toLabels         = sequence . map toLabel   -- Maybe [RDFLabel]
        toLabel          = toRDFLabel dtv

------------------------------------------------------------
--  Make rules from supplied class restrictions and graph
------------------------------------------------------------

ruleQuery :: RDFGraph
ruleQuery = makeRDFGraphFromN3String $
    "@prefix rdfd: <" ++ nsURI namespaceRDFD ++ "> . \n" ++
    " ?c a rdfd:GeneralRestriction ; " ++
    "    rdfd:onProperties ?p ; "      ++
    "    rdfd:constraint   ?r . "

--  Placeholder false graph for now.
falseGraph :: RDFGraph
falseGraph = makeRDFGraphFromN3String $
    "@prefix rdfd: <" ++ nsURI namespaceRDFD ++ "> . \n" ++
    falseGraphStr

falseGraphStr :: String
falseGraphStr = "_:a rdfd:false _:b . "

-- |Make a list of class restriction rules given a list of class restriction
--  values and a graph containing one or more class restriction definitions.
--
makeRDFClassRestrictionRules :: [ClassRestriction] -> RDFGraph -> [RDFRule]
makeRDFClassRestrictionRules crs gr =
    catMaybes $ ( map constructRule . queryForRules ) gr
    where
        queryForRules = rdfQueryFind ruleQuery
        constructRule = makeRestrictionRule1 crs gr

makeRestrictionRule1 ::
    [ClassRestriction] -> RDFGraph -> RDFVarBinding -> Maybe RDFRule
makeRestrictionRule1 crs gr vb =
    {-
    trace "\nmakeRestrictionRule1:" $
    -- seq (traceShow "\ngr:" gr)
    seq (traceShow "\nvb:" vb) $
    seq (traceShow "\nc:" c) $
    seq (traceShow "\np:" p) $
    seq (traceShow "\nr:" r) $
    seq (traceShow "\nps:" ps) $
    -- seq (traceShow "\nrn:" rn) $
    -}
    makeRestrictionRule2 rn c ps cs
    where
        c  = fromMaybe NoNode $ vbMap vb (Var "c")
        p  = fromMaybe NoNode $ vbMap vb (Var "p")
        r  = fromMaybe NoNode $ vbMap vb (Var "r")
        cs = filter (>0) $ map fromInteger $
             rdfFindPredInt c res_rdfd_maxCardinality gr
        ps = rdfFindList gr p
        rn = mapFindMaybe (getScopedName r) (LookupMap crs)

makeRestrictionRule2 ::
    Maybe ClassRestriction -> RDFLabel -> [RDFLabel] -> [Int]
    -> Maybe RDFRule
makeRestrictionRule2 (Just restriction) cls@(Res cname) props cs =
    {-
    trace "\nmakeRestrictionRule2:" $
    seq (traceShow "\ncls:" cls)
    seq (traceShow "\nprops:" props) $
    -}
    Just restrictionRule
    where
        restrictionRule = Rule
            { ruleName = cname
              -- fwdApply :: [ex] -> [ex]
            , fwdApply = fwdApplyRestriction restriction cls props cs
              -- bwdApply :: ex -> [[ex]]
            , bwdApply = bwdApplyRestriction restriction cls props cs
            , checkInference = bwdCheckInference restrictionRule
            }
makeRestrictionRule2 _ _ _ _ =
    trace "\nmakeRestrictionRule: missing class restriction" $
    Nothing

--  Forward apply class restriction.
fwdApplyRestriction ::
    ClassRestriction -> RDFLabel -> [RDFLabel] -> [Int] -> [RDFGraph]
    -> [RDFGraph]
fwdApplyRestriction restriction cls props cs antgrs =
    if isJust newgrs then concat $ fromJust newgrs else [falseGraph]
    where
        -- Instances of the named class in the graph:
        ris = nub $ rdfFindValSubj res_rdf_type cls antgr
        --  Merge antecedent graphs into one (with bnode renaming):
        --  (Uses 'if' and 'foldl1' to avoid merging in the common case
        --  of just one graph supplied.)
        antgr = if null antgrs then emptyRDFGraph else foldl1 merge antgrs
        --  Apply class restriction to single instance of the restricted class
        newgr :: RDFLabel -> Maybe [RDFGraph]
        newgr ri = fwdApplyRestriction1 restriction ri props cs antgr
        newgrs :: Maybe [[RDFGraph]]
        newgrs = sequence $ map newgr ris

--  Forward apply class restriction to single class instance (ci).
--  Return single set of inferred results, for each combination of
--  property values, or an empty list, or Nothing if the supplied values
--  are inconsistent with the restriction.
fwdApplyRestriction1 ::
    ClassRestriction -> RDFLabel -> [RDFLabel] -> [Int] -> RDFGraph
    -> Maybe [RDFGraph]
fwdApplyRestriction1 restriction ci props cs antgr =
    {-
    trace "\nfwdApplyRestriction1:" $
    seq (traceShow "\nci:" ci)
    seq (traceShow "\nprops:" props)
    seq (traceShow "\nantgr:" antgr) $
    -}
    if grConsistent then Just newgrs else Nothing
    where
        --  Apply restriction to graph
        (grConsistent,_,_,sts) = applyRestriction restriction ci props cs antgr
        --  Select results, eliminate those with unknowns
        nts :: [[RDFLabel]]
        nts = catMaybes $ map sequence sts
        --  Make new graph from results, including only newly generated arcs
        newarcs = nub [Arc ci p v | vs <- nts, (p,v) <- zip props vs ]
                  \\ getArcs antgr
        newgrs  = if null newarcs then [] else [toRDFGraph newarcs]

--  Backward apply class restriction.
--
--  Returns a list of alternatives, any one of which is sufficient to
--  satisfy the given consequent.
--
bwdApplyRestriction ::
    ClassRestriction -> RDFLabel -> [RDFLabel] -> [Int] -> RDFGraph
    -> [[RDFGraph]]
bwdApplyRestriction restriction cls props cs congr =
    if isJust newgrs then fromJust newgrs else [[falseGraph]]
    where
        -- Instances of the named class in the graph:
        ris = rdfFindValSubj res_rdf_type cls congr
        --  Apply class restriction to single instance of the restricted class
        newgr :: RDFLabel -> Maybe [[RDFGraph]]
        newgr ri = bwdApplyRestriction1 restriction cls ri props cs congr
        --  'map newgr ris' is conjunction of disjunctions, where
        --  each disjunction is itself a conjunction of conjunctions.
        --  'sequence' distributes the conjunction over the disjunction,
        --  yielding an equivalent disjunction of conjunctions
        --  map concat flattens the conjunctions of conjuctions
        newgrs :: Maybe [[RDFGraph]]
        newgrs = liftM (map concat . sequence) $ sequence $ map newgr ris

--  Backward apply a class restriction to single class instance (ci).
--  Return one or more sets of antecedent results from which the consequence
--  can be derived in the defined relation, an empty list if the supplied
--  consequence cannot be inferred, or Nothing if the consequence is
--  inconsistent with the restriction.
bwdApplyRestriction1 ::
    ClassRestriction -> RDFLabel -> RDFLabel -> [RDFLabel] -> [Int] -> RDFGraph
    -> Maybe [[RDFGraph]]
bwdApplyRestriction1 restriction cls ci props cs congr =
    if grConsistent then Just grss else Nothing
    {-
    trace "\nfwdApplyRestriction1:" $
    seq (traceShow "\nci:" ci)
    seq (traceShow "\nprops:" props)
    seq (traceShow "\ncongr:" congr) $
    -}
    where
        --  Apply restriction to graph
        (grConsistent,pvs,cts,_) =
            applyRestriction restriction ci props cs congr
        --  Build list of all full tuples consistent with the values supplied
        fts :: [[RDFLabel]]
        fts = concatMap snd cts
        --  Construct partial tuples from members of fts from which at least
        --  one of the supplied values can be derived
        pts :: [([Maybe RDFLabel],[RDFLabel])]
        pts = concatMap (deriveTuple restriction) fts
        --  Select combinations of members of pts from which all the
        --  supplied values can be derived
        dtss :: [[[Maybe RDFLabel]]]
        dtss = coverSets pvs pts
        --  Filter members of dtss that fully cover the values
        --  obtained from the consequence graph.
        ftss :: [[[Maybe RDFLabel]]]
        ftss = filter (not . (\t -> coversVals deleteMaybe t pvs)) dtss
        --  Make new graphs for all alternatives
        grss :: [[RDFGraph]]
        grss = map ( makeGraphs . newArcs ) ftss
        --  Collect arcs for one alternative
        newArcs dts =
            [ Arc ci p v | mvs <- dts, (p,Just v) <- zip props mvs ]
        --  Make graphs for one alternative
        makeGraphs = map (toRDFGraph . (:[])) . ((Arc ci res_rdf_type cls):)

--  Helper function to select sub-tuples from which some of a set of
--  values can be derived using a class restriction.
--
--  restriction is the restriction being evaluated.
--  ft          is a full tuple of values known to be consistent with
--              the restriction
--
--  The result returned is a list of pairs, whose first member is a partial
--  tuples from which the full tuple supplied can be derived, and the second
--  is the supplied tuple calculated from that input.
--
deriveTuple ::
    ClassRestriction -> [RDFLabel]
    -> [([Maybe RDFLabel],[RDFLabel])]
deriveTuple restriction ft =
    map (tosnd ft) $ minima partCompareListMaybe $ filter derives partials
    where
        partials = sequence $ map (\x -> [Nothing,Just x]) ft
        derives  = ([ft]==) . fromJust . crFunc restriction
        tosnd    = flip (,)

--  Helper function to apply a restriction to selected information from
--  a supplied graph, and returns a tuple containing:
--  (a) an indication of whether the graph is consistent with the
--      restriction
--  (b) a list of values specified in the graph for each property
--  (c) a complete list of tuples that use combinations of values from
--      the graph and are consistent with the restriction.
--      Each member is a pair consisting of some combination of input
--      values, and a list of complete tuple values that can be
--      calculated from those inputs, or an empty list if there is
--      insufficient information.
--  (d) a set of tuples that are consistent with the restriction and use
--      as much information from the graph as possible.  This set is
--      minimal in the sense that they must all correspond to different
--      complete input tuples satisfying the restriction.
--
--  This function factors out logic that is common to forward and
--  backward chaining of a class restriction.
--
--  restriction is the class restriction being applied
--  ci          is the identifier of a graph node to be tested
--  props       is a list of properties of the graph noode whose values
--              are constrained by the class restriction.
--  cs          is a list of max cardinality constraints on the restriction,
--              the minimum of which is used as the cardinality constraint
--              on the restriction.  If the list is null, no cardinality
--              constraint is applied.
--  gr          is the graph from which property values are extracted.
--
applyRestriction ::
    ClassRestriction -> RDFLabel -> [RDFLabel] -> [Int] -> RDFGraph
    -> ( Bool
       , [[RDFLabel]]
       , [([Maybe RDFLabel],[[RDFLabel]])]
       , [[Maybe RDFLabel]]
       )
applyRestriction restriction ci props cs gr =
    ( (coversVals deleteMaybe sts pvs) && cardinalityOK, pvs, cts, sts )
    where
        --  Extract from the antecedent graph all specified values of the
        --  restricted properties (constructs inner list for each property)
        pvs :: [[RDFLabel]]
        pvs = [ rdfFindPredVal ci p gr | p <- props ]
        --  Convert tuple of alternatives to list of alternative tuples
        --  (Each tuple is an inner list)
        pts :: [[Maybe RDFLabel]]
        pts = sequence $ map allJustAndNothing pvs
        --  Try class restriction calculation for each tuple
        --  For each, result may be:
        --    Nothing  (inconsistent)
        --    Just []  (underspecified)
        --    Just [t] (single tuple of values derived from given values)
        --    Just ts  (alternative tuples derived from given values)
        rts :: [Maybe [[RDFLabel]]]
        rts = map (crFunc restriction) pts
        --  Extract list of consistent tuples of given values
        cts :: [([Maybe RDFLabel],[[RDFLabel]])]
        cts = map sndFromJust $ filter (isJust . snd) (zip pts rts)
        --  Build list of consistent tuples with maximum information
        --  based on that supplied and available
        -- mts = concatMap mostValues cts
        mts = map mostOneValue cts
        --  Eliminate consistent results subsumed by others.
        --  This results in a mimimal possible set of consistent inputs,
        --  because if any pair could be consistently unified then their
        --  common subsumer would still be in the list, and both would be
        --  thereby eliminated.
        sts :: [[Maybe RDFLabel]]
        sts = maxima partCompareListMaybe mts
        --  Check the cardinality constraint
        cardinalityOK = null cs || length sts <= minimum cs
        --  Remove Maybe wrapper from second component of a pair
        sndFromJust :: (a,Maybe b) -> (a,b)
        sndFromJust (a,Just b) = (a,b)

--  Map a non-empty list of values to a list of Just values,
--  preceding each with a Nothing element.
--
--  Nothing corresponds to an unknown value.  This logic is used
--  as part of constructing a list of alternative tuples of known
--  data values (either supplied or calculated from the class
--  restriction).
--
allJustAndNothing :: [a] -> [Maybe a]
allJustAndNothing as = Nothing:map Just as

--  Get maximum information about possible tuple values from a
--  given pair of input tuple, which is known to be consistent with
--  the restriction, and calculated result tuples.  Where the result
--  tuple is not exactly calculated, return the input tuple.
--
--  imvs    tuple of Maybe element values, with Nothing for
--          unspecified values
--  movss   Maybe list of possible fully-specified result tuples,
--          an empty list if no result tuples can be computed
--          based on the input tuple, or Nothing if the input
--          tuple is inconsistent.
--
mostValues :: ([Maybe a],[[a]]) -> [[Maybe a]]
mostValues (imvs,([])) = [imvs]
mostValues (_,movss) = map (map Just) movss

--  Get maximum information about possible tuple values from a
--  given pair of input and possible result tuples, which is
--  known to be consistent with the restriction.  If the result
--  tuple is not exactly calculated, return the input tuple.
--
--  This is a variant of mostValues that returns a single vector.
--  Multiple possible values are considered to be equivalent to
--  Just [], i.e. unknown result.
--
--  imvs    tuple of Maybe element values, with Nothing for
--          unspecified values
--  movss   Maybe list of possible fully-specified result tuples,
--          or an empty list if no result tuples can be computed
--          based on the input tuple.
--
mostOneValue :: ([Maybe a],[[a]]) -> [Maybe a]
mostOneValue (_,[movs]) = map Just movs
mostOneValue (imvs,_)   = imvs

--  Helper function that returns subsets of dts that "cover" the indicated
--  values;  i.e. from which all of the supplied values can be deduced
--  by the enumerated function results.  The minima of all such subsets is
--  returned, as each of these corresponds to some minimum information needed
--  to deduce all of the given values.
--
--  pvs     is a list of lists of values to be covered.  The inner list
--          contains multiple values for each member of a tuple.
--  dts     is an enumerated list of function values from some subset of
--          the tuple space to complete tuples.  Each member is a pair
--          containing the partial tuple (using Nothing for unspecified
--          values) and the full tuple calculated from it.
--
--  The return value is a disjunction of conjunctions of partial tuples
--  that cover the indicated parameter values.
--
--  NOTE:
--  The result minimization is not perfect (cf. test2 below), but I believe
--  it is adequate for the practical situations I envisage, and in any
--  case will not result in incorrect values.  It's significance is for
--  search-tree pruning.  A perfect minimization might be achieved by
--  using a more subtle partial ordering that takes account of both subsets
--  and the partial ordering of set members in place of 'partCompareListSubset'.
--
coverSets  :: (Eq a) => [[a]] -> [([Maybe a],[a])] -> [[[Maybe a]]]
coverSets pvs dts =
    minima partCompareListSubset $ map (map fst) ctss
    where
        ctss = filter (coverspvs) $ powerSet cts
        cts  = minima (partComparePair partCompareListMaybe partCompareEq) dts
        coverspvs cts = coversVals delete (map snd cts) pvs

--  Does a supplied list of tuples cover a list of possible alternative
--  values for each tuple member?
--
coversVals :: (a->[b]->[b]) -> [[a]] -> [[b]] -> Bool
coversVals dropVal ts vss =
    -- all null (foldr dropUsed vss ts)
    any (all null) (scanr dropUsed vss ts)
    where
        --  Remove single tuple values from the list of supplied values:
        dropUsed []       []     = []
        dropUsed (t:ts) (vs:vss) = dropVal t vs:dropUsed ts vss
        dropUsed _ _ = error "coversVals.dropUsed: list length mismatch"

{-
--  Does a supplied list of possible alternative values for each
--  element of a tuple cover every tuple in a supplied list?
--
--  (See module spike-coverVals.hs for test cases)
--
coversAll :: ([a]->b->Bool) -> [[a]] -> [[b]] -> Bool
coversAll matchElem vss ts = all (invss vss) ts
    where
        --  Test if a given tuple is covered by vss
        invss vss t = and $ zipWith matchElem vss t

--  Test if the value in a Maybe is contained in a list.
maybeElem :: (Eq a) => Maybe a -> [a] -> Bool
maybeElem Nothing  = const True
maybeElem (Just t) = elem t
-}

-- |Delete a Maybe value from a list
deleteMaybe :: (Eq a) => Maybe a -> [a] -> [a]
deleteMaybe Nothing  as = as
deleteMaybe (Just a) as = delete a as

------------------------------------------------------------
--  Make restriction rules from supplied datatype and graph
------------------------------------------------------------

makeRDFDatatypeRestrictionRules :: RDFDatatypeVal vt -> RDFGraph -> [RDFRule]
makeRDFDatatypeRestrictionRules dtval gr =
    makeRDFClassRestrictionRules dcrs gr
    where
        dcrs = map (makeDatatypeRestriction dtval) (tvalRel dtval)

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
-- $Source: /file/cvsdev/HaskellRDF/ClassRestrictionRule.hs,v $
-- $Author: graham $
-- $Revision: 1.15 $
-- $Log: ClassRestrictionRule.hs,v $
-- Revision 1.15  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.14  2003/12/20 12:53:39  graham
-- Fix up code to compile and test with GHC 5.04.3
--
-- Revision 1.13  2003/12/20 12:00:14  graham
-- Introduced new TraceHelpers module for Hugs-2003 compatibility.
--
-- Revision 1.12  2003/12/19 21:01:25  graham
-- Change Debug.Trace import (from Hugs.Trace)
--
-- Revision 1.11  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.10  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.9  2003/11/28 00:17:55  graham
-- Datatype constraint test cases all passed.
--
-- Revision 1.8  2003/11/27 11:35:49  graham
-- Variable modifier tests all run.
-- Initial class constraint reasoning tests pass.
-- Fixed bug in class constraint backward-chained reasoning that returned
-- multiple instances of some statements, and did not filter out all occurrences
-- of the original statements.
--
-- Revision 1.7  2003/11/24 22:13:09  graham
-- Working on reworking datatype variable modifiers to work with
-- revised datatype framework.
--
-- Revision 1.6  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.5  2003/11/20 17:58:09  graham
-- Class-constraint backward chaining: all test cases passed.
--
-- Revision 1.4  2003/11/19 22:13:03  graham
-- Some backward chaining tests passed
--
-- Revision 1.3  2003/11/17 21:53:30  graham
-- Datatype inference forward chaining updated to allow inconsistent
-- partial inputs to be detected.  All forward chaining test cases passed.
-- Need to develop backward chaining test cases.
--
-- Revision 1.2  2003/11/14 21:48:35  graham
-- First cut cardinality-checked datatype-constraint rules to pass test cases.
-- Backward chaining is still to do.
--
-- Revision 1.1  2003/11/13 01:15:23  graham
-- Working on ClassRestrictionRule.
-- Code almost complete, some test cases missing.
--
