--------------------------------------------------------------------------------
--  $Id: GraphPartition.hs,v 1.3 2004/02/11 14:19:36 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphPartition
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains functions for partitioning a graph into subgraphs
--  that rooted from different subject nodes.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.GraphPartition
    ( PartitionedGraph(..), getArcs, getPartitions
    , GraphPartition(..), node, toArcs
    , partitionGraph, comparePartitions
    , partitionShowP
    )
where

import Swish.HaskellRDF.GraphClass
    ( Label(..)
    , Arc(..), arcSubj, arcPred, arcObj, arc, arcToTriple, arcFromTriple
    -- , hasLabel, arcLabels
    )

import Data.List
    ( partition )

import Control.Monad.State
    ( MonadState(..), State(..), evalState )

import Data.Maybe
    ( isJust, fromJust, catMaybes, listToMaybe )


------------------------------------------------------------
--  Data type for a partitioned graph
------------------------------------------------------------

-- |Representation of a graph as a collection of (possibly nested)
--  partitions.  Each node in the graph appears at least once as the
--  root value of a GraphPartition value:
--
--  * Nodes that are the subject of at least one statement appear as
--    the first value of exactly one PartSub constructor, and may
--    also appear in any number of PartObj constructors.
--
--  * Nodes appearing only as objects of statements appear only in
--    PartObj constructors.

data PartitionedGraph lb = PartitionedGraph [GraphPartition lb]
    deriving (Eq,Show)

getArcs :: PartitionedGraph lb -> [Arc lb]
getArcs (PartitionedGraph ps) = concatMap toArcs ps

getPartitions :: PartitionedGraph lb -> [GraphPartition lb]
getPartitions (PartitionedGraph ps) = ps

data GraphPartition lb
    = PartObj lb
    | PartSub lb [(lb,GraphPartition lb)]

node :: GraphPartition lb -> lb
node (PartObj ob)   = ob
node (PartSub sb _) = sb

toArcs :: GraphPartition lb -> [Arc lb]
toArcs (PartObj _)      = []
toArcs (PartSub sb prs) = concat $ map toArcs1 prs
    where
        toArcs1 (pr,ob) = (Arc sb pr (node ob)):toArcs ob

instance (Label lb) => Eq (GraphPartition lb) where
    (==) = partitionEq

instance (Label lb) => Show (GraphPartition lb) where
    show = partitionShow

--  Equality is based on total structural equivalence.
--  This is not the same as graph equality.
partitionEq :: (Label lb) => (GraphPartition lb) -> (GraphPartition lb) -> Bool
partitionEq (PartObj o1)    (PartObj o2)    = o1 == o2
partitionEq (PartSub s1 p1) (PartSub s2 p2) = (s1 == s2) && (p1==p2)
partitionEq  _               _              = False

partitionShow :: (Label lb) => (GraphPartition lb) -> String
partitionShow (PartObj ob)          = show ob
partitionShow (PartSub sb (pr:prs)) =
    "("++ show sb ++ " " ++ showpr pr ++ concatMap ((" ; "++).showpr) prs ++ ")"
    where
        showpr (pr,ob) = show pr ++ " " ++ show ob

partitionShowP :: (Label lb) => String -> (GraphPartition lb) -> String
partitionShowP pref (PartObj ob)          = show ob
partitionShowP pref (PartSub sb (pr:prs)) =
    pref++"("++ show sb ++ " " ++ showpr pr ++ concatMap (((pref++"  ; ")++).showpr) prs ++ ")"
    where
        showpr (pr,ob) = show pr ++ " " ++ partitionShowP (pref++"  ") ob

------------------------------------------------------------
--  Creating partitioned graphs
------------------------------------------------------------
--
-- |Turning a partitioned graph into a flat graph is easy.
--  The interesting challenge is to turn a flat graph into a
--  partitioned graph that is more useful for certain purposes.
--  Currently, I'm interested in:
--  (a) isolating differences between graphs
--  (b) pretty-printing graphs
--
--  For (a), the goal is to separate subgraphs that are known
--  to be equivalent from subgraphs that are known to be different,
--  such that (i) different sub-graphs are minimized, (ii) different
--  sub-graphs are placed into 1:1 correspondence (possibly with null
--  subgraphs), and (iii) only deterministic matching decisions are made.
--
--  For (b), the goal is to decide when a subgraph is to be treated
--  as nested in another partition, or treated as a new top-level partition.
--  If a subgraph is referenced by exactly one graph partition, it should
--  be nested in that partition, otherwise it should be a new top-level
--  partition.
--
--  Strategy.  Examining just subject and object nodes:
--  1. all non-blank subject nodes are the root of a top-level partition
--  2. blank subject nodes that are not the object of exactly one statement
--     are the root of a top-level partition.
--  3. blank nodes referenced as the object of exactly 1 statement
--     of an existing partition are the root of a sub-partition of the
--     refering partition.
--  4. what remain are circular chains of blank nodes not referenced
--     elsewhere:  for each such chain, pick a root node arbitrarily.
--
partitionGraph :: (Label lb) => [Arc lb] -> PartitionedGraph lb
partitionGraph arcs =
    makePartitions fixs topv1 intv1
    where
        (fixs,vars)  = partition isNonVar $ collect arcSubj arcs
        vars1        = collectMore arcObj arcs vars
        (intv,topv)  = partition objOnce vars1
        intv1        = map stripObj intv
        topv1        = map stripObj topv
        isNonVar     = not . labelIsVar . fst
        objOnce      = isSingle . snd . snd
        isSingle [_] = True
        isSingle _   = False
        stripObj (k,(s,_)) = (k,s)

-- Local state type for partitioning function
type MakePartitionState lb = ([(lb,[Arc lb])],[(lb,[Arc lb])],[(lb,[Arc lb])])

makePartitions :: (Eq lb) =>
    [(lb,[Arc lb])] -> [(lb,[Arc lb])] -> [(lb,[Arc lb])] -> PartitionedGraph lb
makePartitions fixs topv intv =
    PartitionedGraph $ evalState (makePartitions1 []) (fixs,topv,intv)

-- Use a state monad to keep track of arcs that have been incorporated into
-- the resulting list of graph partitions.  The collections of arcs used to
-- generate the list of partitions are supplied as theinitial state of the
-- monad (see call of evalState above).
--
makePartitions1 :: (Eq lb) =>
    [(lb,[Arc lb])] -> State (MakePartitionState lb) [GraphPartition lb]
makePartitions1 [] =
    do  { s <- pickNextSubject
        ; if null s then return [] else makePartitions1 s
        }
makePartitions1 (sub:subs) =
    do  { ph <- makePartitions2 sub
        ; pt <- makePartitions1 subs
        ; return $ ph++pt
        }

makePartitions2 :: (Eq lb) =>
    (lb,[Arc lb]) -> State (MakePartitionState lb) [GraphPartition lb]
makePartitions2 subs =
    do  { (part,moresubs) <- makeStatements subs
        ; moreparts <- if (not $ null moresubs) then
            makePartitions1 moresubs
          else
            return []
        ; return $ part:moreparts
        }

makeStatements :: (Eq lb) =>
    (lb,[Arc lb])
    -> State (MakePartitionState lb) (GraphPartition lb,[(lb,[Arc lb])])
makeStatements (sub,stmts) =
    do  { propmore <- sequence (map makeStatement stmts)
        ; let (props,moresubs) = unzip propmore
        ; return (PartSub sub props,concat moresubs)
        }

makeStatement :: (Eq lb) =>
    Arc lb
    -> State (MakePartitionState lb) ((lb,GraphPartition lb),[(lb,[Arc lb])])
makeStatement (Arc sub prop obj) =
    do  { intobj <- pickIntSubject obj
        ; (gpobj,moresubs) <- if null intobj
          then
            do  { ms <- pickVarSubject obj
                ; return (PartObj obj,ms)
                }
          else
            makeStatements (head intobj)
        ; return ((prop,gpobj),moresubs)
        }

pickNextSubject :: State (MakePartitionState lb) [(lb,[Arc lb])]
pickNextSubject =
    do  { (s1,s2,s3) <- get
        ; let (s,st) = case (s1,s2,s3) of
                (s1h:s1t,s2,s3) -> ([s1h],(s1t,s2,s3))
                ([],s2h:s2t,s3) -> ([s2h],([],s2t,s3))
                ([],[],s3h:s3t) -> ([s3h],([],[],s3t))
                ([],[],[])      -> ([]   ,([],[],[] ))
        ; put st
        ; return s
        }

pickIntSubject :: (Eq lb) =>
    lb -> State (MakePartitionState lb) [(lb,[Arc lb])]
pickIntSubject sub =
    do  { (s1,s2,s3) <- get
        ; let varsub = removeBy (\x->(x==).fst) sub s3
        ; if (isJust varsub) then
            do  { let (vs,s3new) = fromJust varsub
                ; put (s1,s2,s3new)
                ; return [vs]
                }
          else
            return []
        }

pickVarSubject :: (Eq lb) =>
    lb -> State (MakePartitionState lb) [(lb,[Arc lb])]
pickVarSubject sub =
    do  { (s1,s2,s3) <- get
        ; let varsub = removeBy (\x->(x==).fst) sub s2
        ; if (isJust varsub) then
            do  { let (vs,s2new) = fromJust varsub
                ; put (s1,s2new,s3)
                ; return [vs]
                }
          else
            return []
        }

------------------------------------------------------------
--  Other useful functions
------------------------------------------------------------
--
--  Create a list of pairs of corresponding Partitions that
--  are unequal

comparePartitions :: (Label lb) =>
    PartitionedGraph lb -> PartitionedGraph lb
    -> [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
comparePartitions (PartitionedGraph gp1) (PartitionedGraph gp2) =
    comparePartitions1 (reverse gp1) (reverse gp2)

comparePartitions1 :: (Label lb) =>
    [GraphPartition lb] -> [GraphPartition lb]
    -> [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
comparePartitions1 pg1 pg2 =
        ds ++ [ (Just r1p,Nothing) | r1p<-r1 ]
           ++ [ (Nothing,Just r2p) | r2p<-r2 ]
    where
        (ds,r1,r2) = listDifferences comparePartitions2 pg1 pg2

--  Compare two graph partitions, with three possible outcomes:
--    Nothing    -> no match
--    Just []    -> total match
--    Just [...] -> partial match, with mismatched sub-partitions listed.
--
--  A partial match occurs when the leading nodes are non-variable and
--  equal, but something else in the partition does not match.
--
--  A complete match can be achieved with variable nodes that have
--  different labels
--
comparePartitions2 :: (Label lb) =>
    GraphPartition lb -> GraphPartition lb
    -> Maybe [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
comparePartitions2 (PartObj l1) (PartObj l2) =
    if matchNodes l1 l2 then Just [] else Nothing
comparePartitions2 pg1@(PartSub l1 p1s) pg2@(PartSub l2 p2s) =
    if match then comp1 else Nothing
    where
        comp1  = case comparePartitions3 l1 l2 p1s p2s of
                    Nothing -> if matchVar then Nothing
                                           else Just [(Just pg1,Just pg2)]
                    Just [] -> Just []
                    Just ps -> {- if matchVar then Nothing else -} Just ps
        matchVar = labelIsVar l1 && labelIsVar l2
        match    = matchVar || (l1 == l2)
comparePartitions2 pg1 pg2 =
    if not (labelIsVar l1) && (l1==l2)
        then Just [(Just pg1,Just pg2)]
        else Nothing
    where
        l1 = node pg1
        l2 = node pg2

comparePartitions3 :: (Label lb) =>
    lb -> lb -> [(lb,GraphPartition lb)] -> [(lb,GraphPartition lb)]
    -> Maybe [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
comparePartitions3 l1 l2 s1s s2s = Just $
        ds ++ [ (Just (PartSub l1 [r1p]),Nothing) | r1p<-r1 ]
           ++ [ (Nothing,Just (PartSub l2 [r2p])) | r2p<-r2 ]
    where
        (ds,r1,r2) = listDifferences (comparePartitions4 l1 l2) s1s s2s

comparePartitions4 :: (Label lb) =>
    lb -> lb -> (lb,GraphPartition lb) -> (lb,GraphPartition lb)
    -> Maybe [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
comparePartitions4 s1 s2 po1@(p1,o1) po2@(p2,o2) =
    if matchNodes p1 p2 then comp1 else Nothing
    where
        comp1   = case comparePartitions2 o1 o2 of
                    Nothing -> Just [((Just o1),(Just o2))]
                    ds      -> ds
        -- nomatch = (Just (PartSub s1 [po1]),Just (PartSub s2 [po2]))

matchNodes :: (Label lb) => lb -> lb -> Bool
matchNodes l1 l2
    | labelIsVar l1 = labelIsVar l2
    | otherwise     = l1 == l2


------------------------------------------------------------
--  Helpers
------------------------------------------------------------

-- |Collect a list of items by some comparison of a selected component
--  or other derived value.
--
--  cmp     a comparison function that determines if a pair of values
--          should be grouped together
--  sel     a function that selects a value from any item
--
--  Example:    collect fst [(1,'a'),(2,'b'),(1,'c')] =
--                  [(1,[(1,'a'),(1,'c')]),(2,[(2,'b')])]
--
collect :: (Eq b) => (a->b) -> [a] -> [(b,[a])]
collect = collectBy (==)

collectBy :: (b->b->Bool) -> (a->b) -> [a] -> [(b,[a])]
collectBy cmp sel = map reverseCollection . collectBy1 cmp sel []

collectBy1 :: (b->b->Bool) -> (a->b) -> [(b,[a])] -> [a] -> [(b,[a])]
collectBy1 cmp sel sofar []     = sofar
collectBy1 cmp sel sofar (a:as) =
    collectBy1 cmp sel (collectBy2 cmp sel a sofar) as

collectBy2 :: (b->b->Bool) -> (a->b) -> a -> [(b,[a])] -> [(b,[a])]
collectBy2 cmp sel a [] = [(sel a,[a])]
collectBy2 cmp sel a (col@(k,as):cols)
    | cmp ka k  = (k,a:as):cols
    | otherwise = col:collectBy2 cmp sel a cols
    where
        ka = sel a

reverseCollection :: (b,[a]) -> (b,[a])
reverseCollection (k,as) = (k,reverse as)

-- Example/test:
testCollect1 = collect fst [(1,'a'),(2,'b'),(1,'c'),(1,'d'),(2,'d'),(3,'d')]
testCollect2 = testCollect1
                == [ (1,[(1,'a'),(1,'c'),(1,'d')])
                   , (2,[(2,'b'),(2,'d')])
                   , (3,[(3,'d')])
                   ]

-- |Add new values to an existing list of collections.
--  The list of collections is not extended, but each collection is
--  augmented with a further list of values from the supplied list,
--  each of which are related to the existing collection in some way.
--
--  [[[NOTE: the basic pattern of collect and collectMore is similar,
--  and might be generalized into a common set of core functions.]]]
--
collectMore :: (Eq b) => (a->b) -> [a] -> [(b,c)] -> [(b,(c,[a]))]
collectMore = collectMoreBy (==)

collectMoreBy ::
    (b->b->Bool) -> (a->b) -> [a] -> [(b,c)] -> [(b,(c,[a]))]
collectMoreBy cmp sel as cols =
    map reverseMoreCollection $
    collectMoreBy1 cmp sel as (map (\ (b,cs) -> (b,(cs,[])) ) cols)

collectMoreBy1 ::
    (b->b->Bool) -> (a->b) -> [a] -> [(b,(c,[a]))] -> [(b,(c,[a]))]
collectMoreBy1 cmp sel []     cols = cols
collectMoreBy1 cmp sel (a:as) cols =
    collectMoreBy1 cmp sel as (collectMoreBy2 cmp sel a cols)

collectMoreBy2 ::
    (b->b->Bool) -> (a->b) -> a -> [(b,(c,[a]))] -> [(b,(c,[a]))]
collectMoreBy2 cmp sel a [] = []
collectMoreBy2 cmp sel a (col@(k,(b,as)):cols)
    | cmp (sel a) k = (k,(b,a:as)):cols
    | otherwise     = col:collectMoreBy2 cmp sel a cols

reverseMoreCollection :: (b,(c,[a])) -> (b,(c,[a]))
reverseMoreCollection (k,(c,as)) = (k,(c,reverse as))

-- Example/test:
testCollectMore1 =
    collectMore snd [(111,1),(112,1),(211,2),(311,3),(411,4)] testCollect1
testCollectMore2 = testCollectMore1
                == [ (1,([(1,'a'),(1,'c'),(1,'d')],[(111,1),(112,1)]))
                   , (2,([(2,'b'),(2,'d')],[(211,2)]))
                   , (3,([(3,'d')],[(311,3)]))
                   ]

-- |Remove supplied element from a list using the supplied test
--  function, and return Just the element remoived and the
--  remaining list, or Nothing if no element was matched for removal.
--
remove :: (Eq a) => a -> [a] -> Maybe (a,[a])
remove = removeBy (==)

removeBy :: (b->a->Bool) -> b -> [a] -> Maybe (a,[a])
removeBy cmp a0 as = removeBy1 cmp a0 as []

removeBy1 :: (b->a->Bool) -> b -> [a] -> [a] -> Maybe (a,[a])
removeBy1 _   _  []     _     = Nothing
removeBy1 cmp a0 (a:as) sofar
    | cmp a0 a  = Just (a,reverseTo sofar as)
    | otherwise = removeBy1 cmp a0 as (a:sofar)

testRemove1  = remove 3 [1,2,3,4,5]
testRemove2  = testRemove1 == Just (3,[1,2,4,5])
testRemove3  = remove 3 [1,2,4,5]
testRemove4  = testRemove3 == Nothing
testRemove5  = remove 5 [1,2,4,5]
testRemove6  = testRemove5 == Just (5,[1,2,4])
testRemove7  = remove 1 [1,2,4]
testRemove8  = testRemove7 == Just (1,[2,4])
testRemove9  = remove 2 [2]
testRemove10 = testRemove9 == Just (2,[])

-- |Reverse first argument, prepending the result to the second argument
--
reverseTo :: [a] -> [a] -> [a]
reverseTo []        back = back
reverseTo (a:front) back = reverseTo front (a:back)

-- |Remove each element from a list, returning a list of pairs,
--  each of which is the element removed and the list remaining.
--
removeEach :: [a] -> [(a,[a])]
removeEach [] = []
removeEach (a:as) = (a,as):[ (a1,a:a1s) | (a1,a1s) <- removeEach as ]

testRemoveEach1 = removeEach [1,2,3,4,5]
testRemoveEach2 = testRemoveEach1 ==
    [ (1,[2,3,4,5])
    , (2,[1,3,4,5])
    , (3,[1,2,4,5])
    , (4,[1,2,3,5])
    , (5,[1,2,3,4])
    ]

-- |List differences between the members of two lists, where corresponding
--  elements may appear at arbitrary locations in the corresponding lists.
--
--  Elements are compared using the function 'cmp', which returns:
--  * Nothing  if the elements are completely unrelated
--  * Just []  if the elements are identical
--  * Just ds  if the elements are related but not identical, in which case
--             ds is a list of values describing differences between them.
--
--  Returns (ds,u1,u2), where:
--  ds is null if the related elements from each list are identical,
--  otherwise is a list of differences between the related elements.
--  u1 is a list of elements in a1 not related to elements in a2.
--  u2 is a list of elements in a2 not related to elements in a1.
--
listDifferences :: (a->a->Maybe [d]) -> [a] -> [a] -> ([d],[a],[a])
listDifferences cmp []       a2s = ([],[],a2s)
listDifferences cmp (a1:a1t) a2s =
    case mcomp of
        Nothing       -> morediffs [] [a1] a1t a2s
        Just (ds,a2t) -> morediffs ds []   a1t a2t
    where
        -- mcomp finds identical match, if there is one, or
        -- the first element in a2s related to a1, or Nothing
        -- [choose was listToMaybe,
        --  but that didn't handle repeated properties well]
        mcomp = choose $ catMaybes $ map maybeResult comps
        comps = [ (cmp a1 a2,a2t) | (a2,a2t) <- removeEach a2s ]
        maybeResult (Nothing,_)   = Nothing
        maybeResult (Just ds,a2t) = Just (ds,a2t)
        morediffs ds a1h a1t a2t  = (ds++ds1,a1h++a1r,a2r)
            where
                (ds1,a1r,a2r) = listDifferences cmp a1t a2t
        choose  []       = Nothing
        choose  ds@(d:_) = choose1 d ds
        choose1 _ (d@([],dr):_) = Just d
        choose1 d []            = Just d
        choose1 d (_:ds)        = choose1 d ds

testcmp (l1,h1) (l2,h2)
    | (l1 >= h2) || (l2 >= h1) = Nothing
    | (l1 == l2) && (h1 == h2) = Just []
    | otherwise                = Just [((l1,h1),(l2,h2))]

testdiff1 = listDifferences testcmp
                [(12,15),(1,2),(3,4),(5,8),(10,11)]
                [(10,11),(0,1),(3,4),(6,9),(13,15)]
testdiff2 = testdiff1 == ([((12,15),(13,15)),((5,8),(6,9))],[(1,2)],[(0,1)])

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
-- $Source: /file/cvsdev/HaskellRDF/GraphPartition.hs,v $
-- $Author: graham $
-- $Revision: 1.3 $
-- $Log: GraphPartition.hs,v $
-- Revision 1.3  2004/02/11 14:19:36  graham
-- Add graph-difference option to Swish
--
-- Revision 1.2  2004/02/10 20:24:48  graham
-- Graph difference code now works.
--
-- Revision 1.1  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
