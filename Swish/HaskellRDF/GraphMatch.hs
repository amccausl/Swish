{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}

--------------------------------------------------------------------------------
--  $Id: GraphMatch.hs,v 1.19 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphMatch
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains graph-matching logic.
--
--  The algorithm used is derived from a paper on RDF graph matching
--  by Jeremy Carroll [1].
--
--  [1] http://www.hpl.hp.com/techreports/2001/HPL-2001-293.html
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.GraphMatch
      ( graphMatch,
        -- The rest exported for testing only
        LabelMap, GenLabelMap(..), LabelEntry, GenLabelEntry(..),
        ScopedLabel(..), makeScopedLabel, makeScopedArc,
        LabelIndex, EquivalenceClass, nullLabelVal, emptyMap,
        labelIsVar, labelHash,
        mapLabelIndex, setLabelHash, newLabelMap,
        graphLabels, assignLabelMap, newGenerationMap,
        graphMatch1, graphMatch2, equivalenceClasses, reclassify
      ) where

import Swish.HaskellUtils.LookupMap
import Swish.HaskellUtils.ListHelpers
import Swish.HaskellUtils.MiscHelpers
import Swish.HaskellUtils.TraceHelpers( trace, traceShow )
import Swish.HaskellRDF.GraphClass
import Data.Maybe( isJust )
import Data.List( nub, sortBy, partition )
import qualified Data.List

--------------------------
--  Label index value type
--------------------------
--
--  LabelIndex is a unique value assigned to each label, such that
--  labels with different values are definitely different values
--  in the graph;  e.g. do not map to each other in the graph
--  bijection.  The first member is a generation counter that
--  ensures new values are distinct from earlier passes.

type LabelIndex = (Int,Int)

nullLabelVal :: LabelIndex
nullLabelVal = (0,0)

-----------------------
--  Label mapping types
-----------------------

data (Label lb) => GenLabelEntry lb lv = LabelEntry lb lv

type LabelEntry lb = GenLabelEntry lb LabelIndex

instance (Label lb, Eq lb, Show lb, Eq lv, Show lv)
    => LookupEntryClass (GenLabelEntry lb lv) lb lv where
    keyVal   (LabelEntry k v) = (k,v)
    newEntry (k,v)            = LabelEntry k v

instance (Label lb, Eq lb, Show lb, Eq lv, Show lv)
    => Show (GenLabelEntry lb lv) where
    show = entryShow

instance (Label lb, Eq lb, Show lb, Eq lv, Show lv)
    => Eq (GenLabelEntry lb lv) where
    (==) = entryEq

--  Type for label->index lookup table
data (Label lb, Eq lv, Show lv) => GenLabelMap lb lv =
    LabelMap Int (LookupMap (GenLabelEntry lb lv))

type LabelMap lb = GenLabelMap lb LabelIndex

instance (Label lb) => Show (LabelMap lb) where
    show = showLabelMap

instance (Label lb) => Eq (LabelMap lb) where
    LabelMap gen1 lmap1 == LabelMap gen2 lmap2 =
        (gen1 == gen2) && (es1 `equiv` es2)
        where
            es1 = listLookupMap lmap1
            es2 = listLookupMap lmap2

emptyMap :: (Label lb) => LabelMap lb
emptyMap = LabelMap 1 $ makeLookupMap []

--------------------------
--  Equivalence class type
--------------------------
--
--  Type for equivalence class description
--  (An equivalence class is a collection of labels with
--  the same LabelIndex value.)

type EquivalenceClass lb = (LabelIndex,[lb])

ecIndex :: EquivalenceClass lb -> LabelIndex
ecIndex = fst

ecLabels :: EquivalenceClass lb -> [lb]
ecLabels = snd

ecSize :: EquivalenceClass lb -> Int
ecSize (_,ls) = length ls

ecRemoveLabel :: (Label lb) => EquivalenceClass lb -> lb -> EquivalenceClass lb
ecRemoveLabel (lv,ls) l = (lv,Data.List.delete l ls)

------------------------------------------------------------
--  Augmented graph label value - for graph matching
------------------------------------------------------------
--
--  This instance of class label adds a graph identifier to
--  each variable label, so that variable labels from
--  different graphs are always seen as distinct values.
--
--  The essential logic added by this class instance is embodied
--  in the eq and hash functions.  Note that variable label hashes
--  depend only on the graph in which they appear, and non-variable
--  label hashes depend only on the variable.  Label hash values are
--  used when initializing a label equivalence-class map (and, for
--  non-variable labels, also for resolving hash collisions).

data (Label lb) => ScopedLabel lb = ScopedLabel Int lb

makeScopedLabel :: (Label lb) => Int -> lb -> ScopedLabel lb
makeScopedLabel scope lab = ScopedLabel scope lab

makeScopedArc :: (Label lb) => Int -> Arc lb -> Arc (ScopedLabel lb)
makeScopedArc scope a1 = arc (s arcSubj a1) (s arcPred a1) (s arcObj a1)
    where
        s f a = (ScopedLabel scope (f a))

instance (Label lb) => Label (ScopedLabel lb) where
    getLocal  lab    = error $ "getLocal for ScopedLabel: "++show lab
    makeLabel locnam = error $ "makeLabel for ScopedLabel: "++locnam
    labelIsVar (ScopedLabel _ lab)   = labelIsVar lab
    labelHash seed (ScopedLabel scope lab)
        | labelIsVar lab    = hash seed $ (show scope)++"???"
        | otherwise         = labelHash seed lab

instance (Label lb) => Eq (ScopedLabel lb) where
    (ScopedLabel s1 l1) == (ScopedLabel s2 l2)
        = ( l1 == l2 ) && (s1 == s2)

instance (Label lb) => Show (ScopedLabel lb) where
    show (ScopedLabel s1 l1) = (show s1) ++ ":" ++ (show l1)

instance (Label lb) => Ord (ScopedLabel lb) where
    compare (ScopedLabel s1 l1) (ScopedLabel s2 l2) =
        case (compare s1 s2) of
            LT -> LT
            EQ -> compare l1 l2
            GT -> GT

--------------
--  graphMatch
--------------
--
--  Graph matching function accepting two lists of arcs and
--  returning a node map if successful
--
--  matchable
--          is a function that tests for additional constraints
--          that may prevent the matching of a supplied pair
--          of nodes.  Returns True if the supplied nodes may be
--          matched.  (Used in RDF graph matching for checking
--          that formula assignments are compatible.)
--  gs1     is the first of two graphs to be compared,
--          supplied as a list of arcs.
--  gs2     is the second of two graphs to be compared,
--          supplied as a list of arcs.
--
--  returns a label map that maps each label to an equivalence
--          class identifier, or Nothing if the graphs cannot be
--          matched.

graphMatch :: (Label lb) =>
    (lb -> lb -> Bool) -> [Arc lb] -> [Arc lb]
    -> (Bool,LabelMap (ScopedLabel lb))
graphMatch matchable gs1 gs2 =
    let
        sgs1    = {- trace "sgs1 " $ -} map (makeScopedArc 1) gs1
        sgs2    = {- trace "sgs2 " $ -} map (makeScopedArc 2) gs2
        ls1     = {- traceShow "ls1 " $ -} graphLabels sgs1
        ls2     = {- traceShow "ls2 " $ -} graphLabels sgs2
        lmap    = {- traceShow "lmap " $ -}
                  newGenerationMap $
                  assignLabelMap ls1 $
                  assignLabelMap ls2 emptyMap
        ec1     = {- traceShow "ec1 " $ -} equivalenceClasses lmap ls1
        ec2     = {- traceShow "ec2 " $ -} equivalenceClasses lmap ls2
        ecpairs = zip (pairSort ec1) (pairSort ec2)
        matchableScoped (ScopedLabel _ l1) (ScopedLabel _ l2) = matchable l1 l2
        match   = graphMatch1 False matchableScoped sgs1 sgs2 lmap ecpairs
    in
        if (length ec1) /= (length ec2) then (False,emptyMap) else match

--  Recursive graph matching function
--  This function assumes that no variable label appears in both graphs.
--  (Function graphMatch, which calls this, ensures that all variable
--  labels are distinct.)
--
--  matchable
--          is a function that tests for additional constraints
--          that may prevent the matching of a supplied pair
--          of nodes.  Returns True if the supplied nodes may be
--          matched.
--  guessed is True if a guess has been used before trying this comparison,
--          False if nodes are being matched without any guesswork.
--  gs1     is the first of two lists of arcs (triples) to be compared
--  gs2     is the second of two lists of arcs (triples) to be compared
--  lmap    is the map so far used to map label values to equivalence
--          class values
--  ecpairs list of pairs of corresponding equivalence classes of nodes
--          from gs1 and gs2 that have not been confirmed in 1:1
--          correspondence with each other.
--          Each pair of equivalence classes contains nodes that must
--          be placed in 1:1 correspondence with each other.
--
--  returns a pair (match,map), where 'match' is Tue if the supplied
--          sets of arcs can be matched, in which case 'map' is a
--          corresponding map from labels to equivalence class identifiers.
--          When 'match' is False, 'map' is the most detailed equivalence
--          class map obtained before a mismatch was detected or a guess
--          was required -- this is intended to help identify where the
--          graph mismatch may be.
--
-- [[[TODO:  replace Equivalence class pair by (index,[lb],[lb]) ?]]]
-- [[[TODO:  possible optimization:  the graphMapEq test should be
--           needed only if graphMatch2 has been used to guess a
--           mapping;  either (a) supply flag saying guess has been
--           used, or (b) move test to graphMatch2 and use different
--           test to prevent rechecking for each guess used.]]]

graphMatch1 :: (Label lb) =>  Bool -> (lb -> lb -> Bool)
    -> [Arc lb] -> [Arc lb]
    -> LabelMap lb -> [(EquivalenceClass lb,EquivalenceClass lb)]
    -> (Bool,(LabelMap lb))
graphMatch1 guessed matchable gs1 gs2 lmap ecpairs =
    let
        (secs,mecs) = partition uniqueEc ecpairs
        uniqueEc ( (_,[_])  , (_,[_])  ) = True
        uniqueEc (  _       ,  _       ) = False
        doMatch  ( (_,[l1]) , (_,[l2]) ) = labelMatch matchable lmap l1 l2
        ecEqSize ( (_,ls1)  , (_,ls2)  ) = (length ls1) == (length ls2)
        ecSize   ( (_,ls1)  , _        ) = length ls1
        ecCompareSize ec1 ec2 = compare (ecSize ec1) (ecSize ec2)
        (lmap',mecs',newEc,matchEc) = reclassify gs1 gs2 lmap mecs
        match2 = graphMatch2 matchable gs1 gs2 lmap $ sortBy ecCompareSize mecs
    in
        -- trace ("graphMatch1\nsingle ECs:\n"++show secs++
        --                   "\nmultiple ECs:\n"++show mecs++
        --                   "\n\n") $
        --  if mismatch in singleton equivalence classes, fail
        if not $ all doMatch secs then (False,lmap)
        else
        --  if no multi-member equivalence classes,
        --  check and return label map supplied
        -- trace ("graphMatch1\ngraphMapEq: "++show (graphMapEq lmap gs1 gs2)) $
        if null mecs then (graphMapEq lmap gs1 gs2,lmap)
        else
        --  if size mismatch in equivalence classes, fail
        -- trace ("graphMatch1\nall ecEqSize mecs: "++show (all ecEqSize mecs)) $
        if not $ all ecEqSize mecs then (False,lmap)
        else
        --  invoke reclassification, and deal with result
        if not matchEc then (False,lmap)
        else
        if newEc then graphMatch1 guessed matchable gs1 gs2 lmap' mecs'
        else
        --  if guess does not result in a match, return supplied label map
        if fst match2 then match2 else (False,lmap)

--  Auxiliary graph matching function
--  This function is called when deterministic decomposition of node
--  mapping equivalence classes has run its course.
--
--  It picks a pair of equivalence classes in ecpairs, and arbitrarily matches
--  pairs of nodes in those equivalence classes, recursively calling the
--  graph matching function until a suitable node mapping is discovered
--  (success), or until all such pairs have been tried (failure).
--
--  This function represents a point to which arbitrary choices are backtracked.
--  The list comprehension 'glp' represents the alternative choices at the
--  point of backtracking
--
--  The selected pair of nodes are placed in a new equivalence class based on their
--  original equivalence class value, but with a new NodeVal generation number.

graphMatch2 :: (Label lb) => (lb -> lb -> Bool)
    -> [Arc lb] -> [Arc lb]
    -> LabelMap lb -> [(EquivalenceClass lb,EquivalenceClass lb)]
    -> (Bool,(LabelMap lb))
graphMatch2 matchable gs1 gs2 lmap ((ec1@(ev1,ls1),ec2@(ev2,ls2)):ecpairs) =
    let
        (_,v1) = ev1
        (_,v2) = ev2
        --  Return any equivalence-mapping obtained by matching a pair
        --  of labels in the supplied list, or Nothing.
        try []            = (False,lmap)
        try ((l1,l2):lps) = if equiv try1 l1 l2 then try1 else try lps
            where
                try1     = graphMatch1 True matchable gs1 gs2 lmap' ecpairs'
                lmap'    = newLabelMap lmap [(l1,v1),(l2,v1)]
                ecpairs' = ((ev',[l1]),(ev',[l2])):ec':ecpairs
                ev'      = mapLabelIndex lmap' l1
                ec'      = (ecRemoveLabel ec1 l1,ecRemoveLabel ec2 l2)
                -- [[[TODO: replace this: if isJust try ?]]]
                equiv (False,_)   _  _  = False
                equiv (True,lmap) l1 l2 =
                    (mapLabelIndex m1 l1) == (mapLabelIndex m2 l2)
                    where
                        m1 = remapLabels gs1 lmap [l1]
                        m2 = remapLabels gs2 lmap [l2]
        --  glp is a list of label-pair candidates for matching,
        --  selected from the first label-equivalence class.
        --  NOTE:  final test is call of external matchable function
        glp = [ (l1,l2) | l1 <- ls1 , l2 <- ls2 , matchable l1 l2 ]
    in
        assert (ev1==ev2) "GraphMatch2: Equivalence class value mismatch" $
        try glp

----------------------
--  LabelMap functions
----------------------

----------------
--  showLabelMap
----------------
--
--  Returns a string representation  of a LabelMap value

showLabelMap :: (Label lb) => LabelMap lb -> String
showLabelMap (LabelMap gn lmap) =
    "LabelMap gen="++(Prelude.show gn)++", map="++
    foldl (++) "" ((map ("\n    "++)) (map Prelude.show es ))
    where
        es = listLookupMap lmap

-----------------
--  mapLabelIndex
-----------------
--
--  Map a label to its corresponding label index value in the supplied LabelMap

mapLabelIndex :: (Label lb) => LabelMap lb -> lb -> LabelIndex
mapLabelIndex (LabelMap _ lxms) lb = mapFind nullLabelVal lb lxms

--------------
--  labelMatch
--------------
--
--  Confirm that a given pair of labels are matchable, and are
--  mapped to the same value by the supplied label map

labelMatch :: (Label lb)
    =>  (lb -> lb -> Bool) -> LabelMap lb -> lb -> lb -> Bool
labelMatch matchable lmap l1 l2 =
    (matchable l1 l2) && ((mapLabelIndex lmap l1) == (mapLabelIndex lmap l1))

---------------
--  newLabelMap
---------------
--
--  Replace selected values in a label map with new values from the supplied
--  list of labels and new label index values.  The generation number is
--  supplied from the current label map.  The generation number in the
--  resulting label map is incremented.

newLabelMap :: (Label lb) => LabelMap lb -> [(lb,Int)] -> LabelMap lb
newLabelMap (LabelMap g f) [] = (LabelMap (g+1) f) -- new generation
newLabelMap lmap (lv:lvs)     = setLabelHash (newLabelMap lmap lvs) lv

----------------
--  setLabelHash
----------------
--
--  setLabelHash replaces a label and its associated value in a label map
--  with a new value using the supplied hash value and the current
--  LabelMap generation number.  If the key is not found, then no change
--  is made to the label map.

setLabelHash :: (Label lb)
    => LabelMap lb -> (lb,Int) -> LabelMap lb
setLabelHash  (LabelMap g lmap) (lb,lh) =
    LabelMap g ( mapReplaceAll lmap $ newEntry (lb,(g,lh)) )

--------------------
--  newGenerationMap
--------------------
--
--  Increment generation of label map.
--  Returns a new label map identical to the supplied value
--  but with an incremented generation number.

newGenerationMap :: (Label lb) => LabelMap lb -> LabelMap lb
newGenerationMap (LabelMap g lvs) = (LabelMap (g+1) lvs)

------------------
--  assignLabelMap
------------------
--
--  Scan label list, assigning initial label map values,
--  adding new values to the label map supplied.
--
--  Label map values are assigned on the basis of the
--  label alone, without regard for it's connectivity in
--  the graph.  (cf. reClassify)
--
--  All variable node labels are assigned the same initial
--  value, as they may be matched with each other.

assignLabelMap :: (Label lb) => [lb] -> LabelMap lb -> LabelMap lb
assignLabelMap [] lmap      = lmap
assignLabelMap (n:ns) lmap  = assignLabelMap ns (assignLabelMap1 n lmap)

assignLabelMap1 :: (Label lb) => lb -> LabelMap lb -> LabelMap lb
assignLabelMap1 lab (LabelMap g lvs) = LabelMap g lvs'
    where
        lvs' = (mapAddIfNew lvs $ newEntry (lab,(g,initVal lab)))

--  Calculate initial value for a node

initVal :: (Label lb) => lb -> Int
initVal n = hashVal 0 n

hashVal :: (Label lb) => Int -> lb -> Int
hashVal seed lab =
    if (labelIsVar lab) then (hash seed "???") else (labelHash seed lab)

----------------------
--  equivalenceClasses
----------------------
--
--  lmap    label map
--  ls      list of nodes to be reclassified
--
--  return  list of equivalence classes of the supplied labels under
--          the supplied label map.

equivalenceClasses :: (Label lb) => LabelMap lb -> [lb] -> [EquivalenceClass lb]
equivalenceClasses lmap ls =
    pairGroup $ map labelPair ls
    where
        labelPair l = (mapLabelIndex lmap l,l)

--------------
--  reclassify
--------------
--
--  Reclassify labels
--
--  Examines the supplied label equivalence classes (based on the supplied
--  label map), and evaluates new equivalence subclasses based on node
--  values and adjacency (for variable nodes) and rehashing
--  (for non-variable nodes).
--
--  Note, assumes that all all equivalence classes supplied are
--  non-singletons;  i.e. contain more than one label.
--
--  gs1     is the first of two lists of arcs (triples) to perform a
--          basis for reclassifying the labels in the first equivalence
--          class in each pair of 'ecpairs'.
--  gs2     is the second of two lists of arcs (triples) to perform a
--          basis for reclassifying the labels in the second equivalence
--          class in each pair of 'ecpairs'.
--  lmap    is a label map used for classification of the labels in
--          the supplied equivalence classes.
--  ecpairs a list of pairs of corresponding equivalence classes of
--          nodes from gs1 and gs2 that have not been confirmed
--          in 1:1 correspondence with each other.
--
--  return  a quadruple of:
--          (a) a revised label map reflecting the reclassification,
--          (b) a new list of equivalence class pairs based on the
--          new node map, and
--          (c) if the reclassification partitions any of the
--          supplied equivalence classes then True, else False.
--          any of the supplied equivalence classes
--          (d) if reclassification results in each equivalence class
--          being split same-sized equivalence classes in the two graphs,
--          then True, otherwise False.

reclassify :: (Label lb) =>
    [Arc lb] -> [Arc lb]
    -> LabelMap lb -> [(EquivalenceClass lb,EquivalenceClass lb)]
    -> (LabelMap lb,[(EquivalenceClass lb,EquivalenceClass lb)],Bool,Bool)
reclassify gs1 gs2 lmap@(LabelMap _ lm) ecpairs =
    assert (gen1==gen2) "Label map generation mismatch" $
    (LabelMap gen1 lm',ecpairs',newPart,matchPart)
    where
        LabelMap gen1 lm1 =
            remapLabels gs1 lmap $ foldl1 (++) $ map (ecLabels . fst) ecpairs
        LabelMap gen2 lm2 =
            remapLabels gs2 lmap $ foldl1 (++) $ map (ecLabels . snd) ecpairs
        lm' = mapReplaceMap lm $ mapMerge lm1 lm2
        -- ecGroups :: [([EquivalenceClass lb],[EquivalenceClass lb])]
        ecGroups  = [ (remapEc ec1,remapEc ec2) | (ec1,ec2) <- ecpairs ]
        ecpairs'  = concat $ map (uncurry zip) ecGroups
        newPart   = or  $ map pairG1 lenGroups
        matchPart = and $ map pairEq lenGroups
        lenGroups = map subLength ecGroups
        pairEq (p1,p2) = p1 == p2
        pairG1 (p1,p2) = (p1 > 1) || (p2 > 1)
        subLength (ls1,ls2) = (length ls1,length ls2)
        remapEc ec = pairGroup $ map (newIndex lm') $ pairUngroup ec
        newIndex lm (_,lab) = (mapFind nullLabelVal lab lm,lab)

---------------
--  remapLabels
---------------
--
--  Calculate a new index value for a supplied list of labels based on the
--  supplied label map and adjacency calculations in the supplied graph
--
--  gs      is a list of Arcs used for adjacency calculations when remapping
--  lmap    is a label map used for obtaining current label index values
--  ls      is a list of graph labels for which new mappings are to be
--          created and returned.
--  return  a new label map containing recalculated label index values
--          for the labels in ls.  The label map generation number is
--          incremented by 1 from the supplied 'lmap' value.

remapLabels :: (Label lb) =>
    [Arc lb] -> LabelMap lb -> [lb] -> LabelMap lb
remapLabels gs lmap@(LabelMap gen _) ls =
    LabelMap gen' (LookupMap newEntries)
    where
        gen'                = gen+1
        newEntries          = [ newEntry (l, (gen',newIndex l)) | l <- ls ]
        newIndex l
            | labelIsVar l  = mapAdjacent l     -- adjacency classifies variable labels
            | otherwise     = hashVal gen l     -- otherwise rehash (to disentangle collisions)
        mapAdjacent l       = ( sum (sigsOver l) ) `rem` hashModulus
        sigsOver l          = select (hasLabel l) gs (arcSignatures lmap gs)

-----------------------------
--  Graph auxiliary functions
-----------------------------

---------------
--  graphLabels
---------------
--
--  Return list of distinct labels used in a graph

graphLabels :: (Label lb) => [Arc lb] -> [lb]
graphLabels gs = nub $ concat $ map arcLabels gs

{-  OLD CODE:
graphLabels gs = graphLabels1 gs []

graphLabels1 (t:gs) ls = graphLabels1 gs $
                         foldl (flip addSetElem) ls (arcLabels t)
graphLabels1 [] ls     = ls
-}

-- addSetElem ::  lb -> [lb] -> [lb]

-----------------
--  arcSignatures
-----------------
--
--  Calculate a signature value for each arc that can be used in constructing an
--  adjacency based value for a node.  The adjacancy value for a label is obtained
--  by summing the signatures of all statements containing that label.
--
--  lmap    is a label map used for obtaining current label index values
--  gs      is the list of arcs for which signaturews are calculated
--  return  a list of signature values in correspondence with gs

arcSignatures :: (Label lb) => LabelMap lb -> [Arc lb] -> [Int]
arcSignatures lmap gs =
    map (sigCalc . arcToTriple) gs
    where
        sigCalc (s,p,o)     =
            ( (labelVal2 s) +
              (labelVal2 p)*3 +
              (labelVal2 o)*5 ) `rem` hashModulus
        labelVal l          = mapLabelIndex lmap l
        labelVal2           = (\v -> (fst v) * (snd v) ) . labelVal

------------
--  graphMap
------------
--
--  Return new graph that is supplied graph with every node/arc
--  mapped to a new value according to the supplied function.
--
--  Used for testing for graph equivalence under a supplied
--  label mapping;  e.g.
--
--    if ( graphMap nodeMap gs1 ) `equiv` ( graphMap nodeMap gs2 ) then (same)

graphMap :: (Label lb) => LabelMap lb -> [Arc lb] -> [Arc LabelIndex]
graphMap lmap = map $ fmap (mapLabelIndex lmap) -- graphMapStmt

--------------
--  graphMapEq
--------------
--
--  Compare a pair of graphs for equivalence under a given mapping
--  function.
--
--  This is used to perform the ultimate test that two graphs are
--  indeed equivalent:  guesswork in graphMatch2 means that it is
--  occasionally possible to construct a node mapping that generates
--  the required singleton equivalence classes, but does not fully
--  reflect the topology of the graphs.

graphMapEq :: (Label lb) => LabelMap lb -> [Arc lb] -> [Arc lb] -> Bool
graphMapEq lmap gs1 gs2 = (graphMap lmap gs1) `equiv` (graphMap lmap gs2)

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
-- $Source: /file/cvsdev/HaskellRDF/GraphMatch.hs,v $
-- $Author: graham $
-- $Revision: 1.19 $
-- $Log: GraphMatch.hs,v $
-- Revision 1.19  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.18  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.17  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.16  2003/10/24 21:03:25  graham
-- Changed kind-structure of LookupMap type classes.
--
-- Revision 1.15  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.14  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.13  2003/05/29 01:50:56  graham
-- More performance tuning, courtesy of GHC profiler.
-- All modules showing reasonable performance now.
--
-- Revision 1.12  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.11  2003/05/23 16:29:20  graham
-- Partial code cleanup:
-- - Arc is an alebraic type
-- - Arc is an instance of Functor
-- - add gmap function to Graph interface
-- - remove some duplicate functions from GraphMatch
-- This in preparation for adding graph merge facility with
-- blank node renaming.
--
-- Revision 1.10  2003/05/14 11:13:15  graham
-- Fixed bug in graph matching.
-- (A graph-equivalence check is needed to weed out false matches
-- caused by the "guessing" stage.)
--
-- Revision 1.9  2003/05/14 02:01:59  graham
-- GraphMatch recoded and almost working, but
-- there are a couple of
-- obscure bugs that are proving rather stubborn to squash.
--
-- Revision 1.8  2003/05/09 00:29:14  graham
-- Started to restructure graph matching code
--
-- Revision 1.7  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.6  2003/05/01 23:15:44  graham
-- GraphTest passes all tests using refactored LookupMap
-- Extensive changes to GraphMatch were required.
--
-- Revision 1.5  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.4  2003/04/11 18:12:10  graham
-- Renamed GraphHelpers to ListHelpers
-- LookupMapTest, GraphTest, RDFGraphTest all run OK
--
-- Revision 1.3  2003/04/11 18:04:49  graham
-- Rename GraphLookupMap to LookupMap:
-- GraphTest runs OK.
--
-- Revision 1.2  2003/04/10 16:47:04  graham
-- Minor code cleanup
--
-- Revision 1.1  2003/04/10 13:35:34  graham
-- Separated GraphMatch logic from GraphMem
--
