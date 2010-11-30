{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS  -XFunctionalDependencies #-}
{-# OPTIONS  -XFlexibleContexts #-}
{-# OPTIONS  -XFlexibleInstances #-}
{-# OPTIONS  -XTypeSynonymInstances  #-}
--------------------------------------------------------------------------------
--  $Id: LookupMap.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  LookupMap
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98, class dependencies
--
--  This module defines a lookup table format and associated functions
--  used by the graph matching code.
--
--------------------------------------------------------------------------------

------------------------------------------------------------
--  Generic list-of-pairs lookup functions
------------------------------------------------------------

module Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    , emptyLookupMap, makeLookupMap, listLookupMap
    , reverseLookupMap
    , keyOrder
    , mapFind, mapFindMaybe, mapContains
    , mapReplace, mapReplaceOrAdd, mapReplaceAll, mapReplaceMap
    , mapAdd, mapAddIfNew
    , mapDelete, mapDeleteAll
    , mapApplyToAll, mapTranslate
    , mapEq, mapKeys, mapVals
    , mapSelect, mapMerge
    , mapSortByKey, mapSortByVal
    , mapTranslateKeys, mapTranslateVals
    , mapTranslateEntries, mapTranslateEntriesM
    )
where

import Data.List( nub, sortBy )

import Swish.HaskellUtils.ListHelpers ( equiv )

------------------------------------------------------------
--  Class for lookup map entries
------------------------------------------------------------

-- |LookupEntryClass defines essential functions of any datatype
--  that can be used to make a LookupMap.
--
--  Minimal definition: newEntry and keyVal
--
class (Eq k, Show k) => LookupEntryClass a k v | a -> k, a -> v
    where
        newEntry    :: (k,v) -> a
        keyVal      :: a -> (k,v)
        entryKey    :: a -> k
        entryKey e = k where (k,_) = keyVal e
        entryVal    :: a -> v
        entryVal e = v where (_,v) = keyVal e
        entryEq     :: (Eq v) => a -> a -> Bool
        entryEq e1 e2 = (keyVal e1) == (keyVal e2)
        entryShow   :: (Show v) => a -> String
        entryShow e = (show k)++":"++(show v) where (k,v) = keyVal e
        kmap :: (LookupEntryClass a2 k2 v) => (k -> k2) -> a -> a2
        kmap f e    = newEntry (f $ entryKey e,entryVal e)
        vmap :: (LookupEntryClass a2 k v2) => (v -> v2) -> a -> a2
        vmap f e    = newEntry (entryKey e,f $ entryVal e)

-- |Predefine a pair of appropriate values as a valid lookup table entry
--  (i.e. an instance of LookupEntryClass).
--
instance (Eq k, Show k) => LookupEntryClass (k,v) k v where
    newEntry = id
    keyVal   = id

-- |Define a lookup map based on a list of values.
--
--  Note:  the class constraint that a is an instance of LookupEntryClass
--  is not defined here, for good reasons (which I forget right now, but
--  something to do with the method disctionary being superfluous on
--  an algebraic data type).
--
data LookupMap a = LookupMap [a]

-- |Define eqiality of LookupMap values based on equality of entries.
--
--  (This is possibly a poor definition, as it is dependent on ordering
--  of list members.  But it passes all current test cases, and is used
--  only for testing.)
--
--  See also mapEq
--  (why not just use that here?  I don't know:  it's probably historic.)
--
instance (Eq a) => Eq (LookupMap a) where
    LookupMap es1 == LookupMap es2 = es1 == es2

-- |Define Show instance for LookupMap based on Showing the
-- list of entries.
--
instance (Show a ) => Show (LookupMap a) where
    show (LookupMap es) = "LookupMap " ++ show es

-- |Empty lookup map of arbitrary (i.e. polymorphic) type.
--
emptyLookupMap :: (LookupEntryClass a k v) => LookupMap a
emptyLookupMap = LookupMap []

-- |Function to create a LookupMap from a list of entries.
--
--  Currently, this is trivial but future versions could be
--  more substantial.
--
makeLookupMap :: (LookupEntryClass a k v) => [a] -> LookupMap a
makeLookupMap es = LookupMap es

-- |Return list of lookup map entries.
--
--  Currently, this is trivial but future versions could be
--  more substantial.
--
listLookupMap :: (LookupEntryClass a k v) => LookupMap a -> [a]
listLookupMap (LookupMap es) = es

-- |Given a lookup map entry, return a new entry that can be used
--  in the reverse direction of lookup.  This is used to construct
--  a reverse LookupMap.
--
reverseEntry :: (LookupEntryClass a1 k v, LookupEntryClass a2 v k)
    => a1 -> a2
reverseEntry e = newEntry (v,k) where (k,v) = keyVal e

-- |Given a lookup map, return a new map that can be used
--  in the opposite direction of lookup.
--
reverseLookupMap :: (LookupEntryClass a1 b c, LookupEntryClass a2 c b)
    => LookupMap a1 -> LookupMap a2
reverseLookupMap (LookupMap es) = LookupMap (map reverseEntry es)

-- |Given a pair of lookup entry values, return the ordering of their
--  key values.
--
keyOrder :: (LookupEntryClass a k v, Ord k)
    =>  a -> a -> Ordering
keyOrder e1 e2 = compare k1 k2
    where
        (k1,_) = keyVal e1
        (k2,_) = keyVal e2

--  Local helper function to build a new LookupMap from
--  a new entry and an exiting map.
--
mapCons :: (LookupEntryClass a k v) =>
    a -> LookupMap a -> LookupMap a
mapCons e (LookupMap es) = LookupMap (e:es)

-- |Find key in lookup map and return corresponding value,
--  otherwise return default supplied.
--
mapFind :: (LookupEntryClass a k v) => v -> k -> LookupMap a -> v
mapFind def key (LookupMap es) = foldr match def es where
    match ent alt
        | key == (entryKey ent) = entryVal ent
        | otherwise             = alt

-- |Find key in lookup map and return Just the corresponding value,
--  otherwise return Nothing.
--
mapFindMaybe :: (LookupEntryClass a k v) => k -> LookupMap a -> Maybe v
mapFindMaybe key (LookupMap es) = foldr match Nothing es where
    match ent alt
        | key == (entryKey ent) = Just (entryVal ent)
        | otherwise             = alt

-- |Test to see if key is present in the supplied map
--
mapContains :: (LookupEntryClass a k v) =>
    LookupMap a -> k -> Bool
mapContains (LookupMap es) key  = or (map match es) where
    match ent = key == (entryKey ent)

-- |Replace an existing occurrence of a key a with a new key-value pair
--  The resulting lookup map has the same form as the original in all
--  other respects.  Assumes exactly one occurrence of the supplied key.
--
mapReplace :: (LookupEntryClass a k v) =>
    LookupMap a -> a -> LookupMap a
mapReplace (LookupMap (e:es)) newe
    | (entryKey e) == (entryKey newe)   = LookupMap (newe:es)
    | otherwise                         = mapAdd more e where
        more = mapReplace (LookupMap es) newe
mapReplace _ newe =
    error ("mapReplace: Key value not found in lookup table: "++
           (Prelude.show (entryKey newe)))

-- |Replace an existing occurrence of a key a with a new key-value pair,
--  or add a new key-value pair if the supplied key is not already present.
--
mapReplaceOrAdd :: (LookupEntryClass a k v) =>
    a -> LookupMap a -> LookupMap a
mapReplaceOrAdd newe (LookupMap (e:es))
    | (entryKey e) == (entryKey newe)   = LookupMap (newe:es)
    | otherwise                         = mapCons e more where
        more = mapReplaceOrAdd newe (LookupMap es)
mapReplaceOrAdd newe (LookupMap [])     = LookupMap [newe]

-- |Replace any occurrence of a key a with a new key-value pair
--  The resulting lookup map has the same form as the original in all
--  other respects.
--
mapReplaceAll :: (LookupEntryClass a k v) =>
    LookupMap a -> a -> LookupMap a
mapReplaceAll (LookupMap (e:es)) newe   = mapCons e' more where
    more = mapReplaceAll (LookupMap es) newe
    e'   = if (entryKey e) == (entryKey newe) then newe else e
mapReplaceAll (LookupMap []) _          = (LookupMap [])

-- |Replace any occurrence of a key in the first argument with a
--  corresponding key-value pair from the second argument, if present.
--
--  This could be implemented by multiple applications of mapReplaceAll,
--  but is arranged differently so that only one new LookupMap value is
--  created.
--
--  Note:  keys in the new map that are not present in the old map
--  are not included in the result map
--
mapReplaceMap :: (LookupEntryClass a k v) =>
    LookupMap a -> LookupMap a -> LookupMap a
mapReplaceMap (LookupMap (e:es)) newmap = mapCons e' more where
    more  = mapReplaceMap (LookupMap es) newmap
    e'    = newEntry (k,mapFind v k newmap)
    (k,v) = keyVal e
mapReplaceMap (LookupMap []) _ = (LookupMap [])

-- |Add supplied key-value pair to the lookup map.
--
--  This is effectively an optimized case of MapReplaceOrAdd or mapAddIfNew,
--  where the caller guarantees to avoid duplicate key values.
--
mapAdd :: (LookupEntryClass a k v) =>
    LookupMap a -> a -> LookupMap a
mapAdd emap e = mapCons e emap

-- |Add supplied key-value pair to the lookup map,
--  only if the key value is not already present.
--
mapAddIfNew :: (LookupEntryClass a k v) =>
    LookupMap a -> a -> LookupMap a
mapAddIfNew emap e = if mapContains emap (entryKey e)
                        then emap
                        else mapCons e emap

-- ADelete supplied key value from the lookup map.
--  This function assumes exactly one occurrence.
--
mapDelete :: (LookupEntryClass a k v) =>
    LookupMap a -> k -> LookupMap a
mapDelete (LookupMap (e:es)) k
    | k == (entryKey e) = LookupMap es
    | otherwise         = mapCons e more where
        more = mapDelete (LookupMap es) k
mapDelete _ k =
    error ("mapDelete: Key value not found in lookup table: "++(Prelude.show k))

-- |Delete any occurrence of a supplied key value from the lookup map.
--
mapDeleteAll :: (LookupEntryClass a k v) =>
    LookupMap a -> k -> LookupMap a
mapDeleteAll (LookupMap (e:es)) k =
    if (entryKey e) == k then more else mapCons e more where
        more = mapDeleteAll (LookupMap es) k
mapDeleteAll (LookupMap []) _ = (LookupMap [])

-- |Return a list of values obtained by applying a function to each key
--  in the map.  Creates an alternative set of values that can be
--  retrieved using mapTranslate.
--
mapApplyToAll :: (LookupEntryClass a k v) =>
    LookupMap a -> (k -> w) -> [w]
mapApplyToAll (LookupMap es) f = [ f (entryKey e) | e <- es ]

-- |Find a node in a lookup map list, and returns the
--  corresponding value from a supplied list.  The appropriate ordering
--  of the list is not specified here, but an appropriately ordered list
--  may be obtained by mapApplyToAll.
--
mapTranslate :: (LookupEntryClass a k v) =>
    LookupMap a -> [w] -> k -> w -> w
mapTranslate (LookupMap (e:es)) (w:ws) k def
    | k == (entryKey e) = w
    | otherwise         = mapTranslate (LookupMap es) ws k def
mapTranslate _ _ _ def = def

-- |Compare two lookup maps for equality.
--
--  Two maps are equal if they have the same set of keys, and if
--  each key maps to an equivalent value.
--
mapEq :: (LookupEntryClass a k v, Eq v) =>
    LookupMap a -> LookupMap a -> Bool
mapEq es1 es2 =
    ( ks1 `equiv` ks2 ) &&
    and [ (mapFindMaybe k es1) == (mapFindMaybe k es2) | k <- ks1 ]
    where
        ks1 = mapKeys es1
        ks2 = mapKeys es2

-- |Return the list of keys in a supplied LookupMap
--
mapKeys :: (LookupEntryClass a k v) =>
    LookupMap a -> [k]
mapKeys (LookupMap es) = nub $ map (fst . keyVal) es

-- |Return list of distinct values in a supplied LookupMap
--
mapVals :: (Eq v, LookupEntryClass a k v) =>
    LookupMap a -> [v]
mapVals (LookupMap es) = nub $ map (snd . keyVal) es

-- |Select portion of a lookup map that corresponds to
--  a supplied list of keys
--
mapSelect :: (LookupEntryClass a k v) =>
    LookupMap a -> [k] -> LookupMap a
mapSelect (LookupMap es) ks =
    LookupMap $ filter (keyIn ks) es
    where
        keyIn ks e = k `elem` ks where (k,_) = keyVal e

-- |Merge two lookup maps, ensuring that if the same key appears
--  in both maps it is associated with the same value.
--
mapMerge :: (LookupEntryClass a k v, Eq a, Show a, Ord k) =>
    LookupMap a -> LookupMap a -> LookupMap a
mapMerge (LookupMap es1) (LookupMap es2) =
    LookupMap $ merge (sortBy keyOrder es1) (sortBy keyOrder es2)
    where
        merge es1 [] = es1
        merge [] es2 = es2
        merge es1@(e1:et1) es2@(e2:et2) =
            case keyOrder e1 e2 of
                LT -> e1:(merge et1 es2)
                GT -> e2:(merge es1 et2)
                EQ -> if e1 /= e2
                        then error ("mapMerge key conflict: " ++ (show e1)
                                    ++ " with " ++ (show e2))
                        else e1:(merge et1 et2)

-- |Creates a new map that is the same as the supplied map, except
--  that its entries are sorted by key value.
--
--  (What's this used for?  It should be redundant.)
--
mapSortByKey :: (LookupEntryClass a k v, Ord k) =>
    LookupMap a -> LookupMap a
mapSortByKey (LookupMap es) =
    LookupMap $ sortBy keyCompare es
    where
        keyCompare e1 e2 = compare (entryKey e1) (entryKey e2)

-- |Creates a new map that is the same as the supplied map, except
--  that its entries are sorted by key value.
--
--  (What's this used for?  It should be redundant.)
--
mapSortByVal :: (LookupEntryClass a k v, Ord v) =>
    LookupMap a -> LookupMap a
mapSortByVal (LookupMap es) =
    LookupMap $ sortBy valCompare es
    where
        valCompare e1 e2 = compare (entryVal e1) (entryVal e2)

-- |An fmap-like function that returns a new lookup map that is a
--  copy of the supplied map with entry keys replaced according to
--  a supplied function.
--
mapTranslateKeys :: (LookupEntryClass a1 k1 v, LookupEntryClass a2 k2 v) =>
    (k1 -> k2) -> LookupMap a1 -> LookupMap a2
mapTranslateKeys f (LookupMap es) =
    LookupMap $ map (kmap f) es

-- |An fmap-like function that returns a new lookup map that is a
--  copy of the supplied map with entry values replaced according to
--  a supplied function.
--
mapTranslateVals :: (LookupEntryClass a1 k v1, LookupEntryClass a2 k v2) =>
    (v1 -> v2) -> LookupMap a1 -> LookupMap a2
mapTranslateVals f = mapTranslateEntries (vmap f)

-- |A function that returns a new lookup map that is a copy of the
--  supplied map with complete entries replaced according to
--  a supplied function.
--
mapTranslateEntries ::
    (a1 -> a2) -> LookupMap a1 -> LookupMap a2
mapTranslateEntries f (LookupMap es) =
    LookupMap $ map f es

-- |A monadic form of mapTranslateEntries
--
mapTranslateEntriesM :: (Monad m)
    => (a1 -> m (a2)) -> LookupMap a1 -> m (LookupMap a2)
mapTranslateEntriesM f (LookupMap es) =
    do  { m2 <- mapM f es
        ; return $ LookupMap m2
        }

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
-- $Source: /file/cvsdev/HaskellUtils/LookupMap.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: LookupMap.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.29  2003/12/07 19:10:35  graham
-- Cleaned up LookupMap code comments.
--
-- Revision 1.28  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.27  2003/12/03 22:04:00  graham
-- Re-ordered mapFind (again), to simplify currying of default value.
--
-- Revision 1.26  2003/12/03 22:02:09  graham
-- Re-ordered mapFind, to simplify currying of default value.
--
-- Revision 1.25  2003/11/24 15:46:03  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.24  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.23  2003/10/24 21:02:42  graham
-- Changed kind-structure of LookupMap type classes.
--
-- Revision 1.22  2003/10/23 18:54:00  graham
-- Moved context requirements for using LookupMap.
-- Some context requirements are now applied to individual
-- LoopkupMap routines that depend upon them.
--
-- Revision 1.21  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.20  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.19  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.18  2003/06/11 14:07:53  graham
-- Added mapTranslateEntriesM, which performs monadic translation of
-- LookupMap entries.  (Tested using Maybe monad.)
--
-- Revision 1.17  2003/06/10 17:38:34  graham
-- Remove some unneeded calss constraints from data type declarations
-- Reworked NSGraph to be an instance of Functor, replacing function
-- gmap with fmap.  Graph formulae are still not handled well:  the data types
-- will need re-working so that a "Formula lb" type constructor can be
-- introduced having the correct (* -> *) kind to be a Functor.
--
-- Revision 1.16  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.15  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.14  2003/05/23 19:33:36  graham
-- Added and tested RDF graph label translation functions
--
-- Revision 1.13  2003/05/14 19:38:32  graham
-- Simple formatter tests all working with reworked graph and lookup structures.
-- More complex formatter tests still to be coded.
--
-- Revision 1.12  2003/05/14 02:01:59  graham
-- GraphMatch recoded and almost working, but
-- there are a couple of
-- obscure bugs that are proving rather stubborn to squash.
--
-- Revision 1.11  2003/05/09 00:28:48  graham
-- Added partitionBy to ListHelpers (may want to remove since
-- it's also in the standard List module).
-- Added mapSelect and mapMerge to LookupMap, and test cases.
--
-- Revision 1.10  2003/05/07 23:58:09  graham
-- More restructuring.
-- RDFGraphTest runs OK.
-- N3ParserTest needs to be updated to use new structure for formulae.
--
-- Revision 1.9  2003/05/07 19:25:26  graham
-- Added mapFindMaybe to LookupMap export list
--
-- Revision 1.8  2003/05/07 18:50:38  graham
-- Add LookupMap functions: mapFindMaybe, mapKeys, mapEq
--
-- Revision 1.7  2003/05/01 23:15:44  graham
-- GraphTest passes all tests using refactored LookupMap
-- Extensive changes to GraphMatch were required.
--
-- Revision 1.6  2003/05/01 19:14:26  graham
-- LookupMap refactored to use class for entry, so that it can be
-- applied to a variety of different types with identifiable key and value
-- components.  All tests pass.
--
-- Revision 1.5  2003/05/01 00:21:41  graham
-- Started refactoring LookupMap.
-- Revised module compiles OK.
-- Working on test module.
--
-- Revision 1.4  2003/04/29 22:07:10  graham
-- Some refactoring of N3 formatter.
-- N3 formatter now handles trivial cases.
-- More complex formatter test cases still to be developed.
--
-- Revision 1.3  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.2  2003/04/11 18:04:49  graham
-- Rename GraphLookupMap to LookupMap:
-- GraphTest runs OK.
--
-- Revision 1.1  2003/04/11 17:38:33  graham
-- Rename GraphLookupMap to LookupMap
--
