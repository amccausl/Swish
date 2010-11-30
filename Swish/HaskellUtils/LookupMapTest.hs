{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}

--------------------------------------------------------------------------------
--  $Id: LookupMapTest.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  LookupMapTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
-- This Module defines test cases for module Parse parsing functions.
--
--------------------------------------------------------------------------------

--   WNH RIP OUT module Swish.HaskellUtils.LookupMapTest where

import Swish.HaskellUtils.LookupMap
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

import Swish.HaskellUtils.ListHelpers
    ( equiv )

import Data.List ( sort )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertEqual, runTestTT, runTestText, putTextToHandle )

------------------------------------------------------------
--  Declare lookup entry for testing
------------------------------------------------------------

data GenMapEntry a b = E a b

instance (Eq a, Show a, Eq b, Show b)
    => LookupEntryClass (GenMapEntry a b) a b
    where
        keyVal   (E k v) = (k,v)
        newEntry (k,v)   = (E k v)

instance (Eq a, Show a, Eq b, Show b) => Show (GenMapEntry a b) where
    show = entryShow

instance (Eq a, Show a, Eq b, Show b) => Eq (GenMapEntry a b) where
    (==) = entryEq

type TestEntry  = GenMapEntry Int String
type TestMap    = LookupMap (GenMapEntry Int String)
type RevTestMap = LookupMap (GenMapEntry String Int)
type MayTestMap = Maybe RevTestMap
type StrTestMap = LookupMap (GenMapEntry String String)

------------------------------------------------------------
--  Test class helper
------------------------------------------------------------

testeq :: (Show a, Eq a) => String -> a -> a -> Test
testeq lab req got =
    TestCase ( assertEqual ("test"++lab) req got )

testeqv :: (Show a, Eq a) => String -> [a] -> [a] -> Test
testeqv lab req got =
    TestCase ( assertEqual ("test"++lab) True (req `equiv` got) )

------------------------------------------------------------
--  LookupMap functions
------------------------------------------------------------

newMap :: [(Int,String)] -> TestMap
newMap es = makeLookupMap (map newEntry es)

testLookupMap :: String -> TestMap -> [(Int,String)] -> Test
testLookupMap lab m1 m2 = testeq ("LookupMap"++lab ) (newMap m2) m1

testLookupMapFind :: String -> TestMap -> Int -> String -> Test
testLookupMapFind lab lm k res =
    testeq ("LookupMapFind"++lab ) res (mapFind "" k lm)

lm00 = newMap []
testLookupMap00     = testLookupMap     "00" lm00 []
testLookupMapFind00 = testLookupMapFind "00" lm00 2 ""

lm01 = mapAdd lm00 $ newEntry (1,"aaa")
testLookupMap01     = testLookupMap     "01" lm01 [(1,"aaa")]
testLookupMapFind01 = testLookupMapFind "01" lm01 2 ""

lm02 = mapAdd lm01 $ newEntry (2,"bbb")
testLookupMap02     = testLookupMap     "02" lm02 [(2,"bbb"),(1,"aaa")]
testLookupMapFind02 = testLookupMapFind "02" lm02 2 "bbb"

lm03 = mapAdd lm02 $ newEntry (3,"ccc")
testLookupMap03     = testLookupMap     "03" lm03 [(3,"ccc"),(2,"bbb"),(1,"aaa")]
testLookupMapFind03 = testLookupMapFind "03" lm03 2 "bbb"

lm04 = mapAdd lm03 $ newEntry (2,"bbb")
testLookupMap04     = testLookupMap     "04" lm04 [(2,"bbb"),(3,"ccc"),(2,"bbb"),(1,"aaa")]
testLookupMapFind04 = testLookupMapFind "04" lm04 2 "bbb"

lm05 = mapReplaceAll lm04 $ newEntry (2,"bbb1")
testLookupMap05     = testLookupMap     "05" lm05 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa")]
testLookupMapFind05 = testLookupMapFind "05" lm05 2 "bbb1"

lm06 = mapReplaceAll lm05 $ newEntry (9,"zzzz")
testLookupMap06     = testLookupMap     "06" lm06 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa")]
testLookupMapFind06 = testLookupMapFind "06" lm06 2 "bbb1"

lm07 = mapReplace lm06 $ newEntry (2,"bbb")
testLookupMap07     = testLookupMap     "07" lm07 [(2,"bbb"),(3,"ccc"),(2,"bbb1"),(1,"aaa")]
testLookupMapFind07 = testLookupMapFind "07" lm07 2 "bbb"
testLookupMapFind0x = testLookupMapFind "0x" lm07 9 ""

lm08 = mapDelete lm07 3
testLookupMap08     = testLookupMap     "08" lm08 [(2,"bbb"),(2,"bbb1"),(1,"aaa")]
testLookupMapFind08 = testLookupMapFind "08" lm08 2 "bbb"

lm09 = mapDeleteAll lm08 2
testLookupMap09     = testLookupMap     "09" lm09 [(1,"aaa")]
testLookupMapFind09 = testLookupMapFind "09" lm09 2 ""

la10 = mapApplyToAll lm03 (flip replicate '*')
testLookupMapApp10  = testeq "LookupMapApplyToAll10" ["***","**","*"] la10

lt11 = mapTranslate lm03 la10 1 "****"
testLookupMapTran11  = testeq "LookupMapTranslate11" "*"   lt11

lt12 = mapTranslate lm03 la10 2 "****"
testLookupMapTran12  = testeq "LookupMapTranslate12" "**"  lt12

lt13 = mapTranslate lm03 la10 3 "****"
testLookupMapTran13  = testeq "LookupMapTranslate13" "***" lt13

lt14 = mapTranslate lm03 la10 4 "****"
testLookupMapTran14  = testeq "LookupMapTranslate14" "****" lt14

lm20 = mapReplaceMap lm05 $ newMap [(2,"bbb20"),(3,"ccc20")]
testLookupMap20     = testLookupMap     "20" lm20 [(2,"bbb20"),(3,"ccc20"),(2,"bbb20"),(1,"aaa")]
testLookupMapFind20 = testLookupMapFind "20" lm20 2 "bbb20"

lm21 = mapReplaceMap lm05 $ newMap []
testLookupMap21     = testLookupMap     "21" lm21 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa")]
testLookupMapFind21 = testLookupMapFind "21" lm21 2 "bbb1"

lm22 = mapReplaceMap lm05 $ newMap [(9,"zzz22"),(1,"aaa22")]
testLookupMap22     = testLookupMap     "22" lm22 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa22")]
testLookupMapFind22 = testLookupMapFind "22" lm22 1 "aaa22"

testLookupContains31 = testeq "LookupContains31" True  (mapContains lm22 2)
testLookupContains32 = testeq "LookupContains32" False (mapContains lm22 9)

lm33 = mapAddIfNew lm22 $ newEntry (1,"aaa33")
testLookupMap33      = testLookupMap      "33" lm33 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa22")]
testLookupMapFind33a = testLookupMapFind "33a" lm33 1 "aaa22"
testLookupMapFind33b = testLookupMapFind "33b" lm33 4 ""

lm34 = mapAddIfNew lm22 $ newEntry (4,"ddd34")
testLookupMap34      = testLookupMap      "34" lm34 [(4,"ddd34"),(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa22")]
testLookupMapFind34a = testLookupMapFind "34a" lm34 1 "aaa22"
testLookupMapFind34b = testLookupMapFind "34b" lm34 4 "ddd34"

lm35 = mapReplaceOrAdd (newEntry (1,"aaa35")) lm22
testLookupMap35      = testLookupMap      "35" lm35 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa35")]
testLookupMapFind35a = testLookupMapFind "35a" lm35 1 "aaa35"
testLookupMapFind35b = testLookupMapFind "35b" lm35 4 ""

lm36 = mapReplaceOrAdd (newEntry (4,"ddd36")) lm22
testLookupMap36      = testLookupMap      "36" lm36 [(2,"bbb1"),(3,"ccc"),(2,"bbb1"),(1,"aaa22"),(4,"ddd36")]
testLookupMapFind36a = testLookupMapFind "36a" lm36 1 "aaa22"
testLookupMapFind36b = testLookupMapFind "36b" lm36 4 "ddd36"

testLookupMapSuite = TestList
    [
    testLookupMap01, testLookupMapFind01,
    testLookupMap02, testLookupMapFind02,
    testLookupMap03, testLookupMapFind03,
    testLookupMap04, testLookupMapFind04,
    testLookupMap05, testLookupMapFind05,
    testLookupMap06, testLookupMapFind06,
    testLookupMap07, testLookupMapFind07, testLookupMapFind0x,
    testLookupMap08, testLookupMapFind08,
    testLookupMap09, testLookupMapFind09,
    testLookupMapApp10,
    testLookupMapTran11, testLookupMapTran12,
    testLookupMapTran13, testLookupMapTran14,
    testLookupMap20, testLookupMapFind20,
    testLookupMap21, testLookupMapFind21,
    testLookupMap22, testLookupMapFind22,
    testLookupContains31,
    testLookupContains32,
    testLookupMap33, testLookupMapFind33a, testLookupMapFind33b,
    testLookupMap34, testLookupMapFind34a, testLookupMapFind34b,
    testLookupMap35, testLookupMapFind35a, testLookupMapFind35b,
    testLookupMap36, testLookupMapFind36a, testLookupMapFind36b
    ]

------------------------------------------------------------
--  Reverse lookup map test tests
------------------------------------------------------------

revdef = -1 :: Int

newRevMap :: [(String,Int)] -> RevTestMap
newRevMap es = makeLookupMap (map newEntry es)

testRevLookupMap :: String -> RevTestMap -> [(String,Int)] -> Test
testRevLookupMap lab m1 m2 =
    testeq ("RevLookupMap"++lab) (newRevMap m2) m1

testRevLookupMapFind :: String -> RevTestMap -> String -> Int -> Test
testRevLookupMapFind lab lm k res =
    testeq ("RevLookupMapFind"++lab) res (mapFind revdef k lm)

rlm00 :: RevTestMap
rlm00 = reverseLookupMap lm00
testRevLookupMap00     = testRevLookupMap     "00" rlm00 []
testRevLookupMapFind00 = testRevLookupMapFind "00" rlm00 "" revdef

rlm01 :: RevTestMap
rlm01 = reverseLookupMap lm01
testRevLookupMap01     = testRevLookupMap     "01" rlm01 [("aaa",1)]
testRevLookupMapFind01 = testRevLookupMapFind "01" rlm01 "bbb" revdef

rlm02 :: RevTestMap
rlm02 = reverseLookupMap lm02
testRevLookupMap02     = testRevLookupMap     "02" rlm02 [("bbb",2),("aaa",1)]
testRevLookupMapFind02 = testRevLookupMapFind "02" rlm02 "bbb" 2

rlm03 :: RevTestMap
rlm03 = reverseLookupMap lm03
testRevLookupMap03     = testRevLookupMap     "03" rlm03 [("ccc",3),("bbb",2),("aaa",1)]
testRevLookupMapFind03 = testRevLookupMapFind "03" rlm03 "bbb" 2

rlm04 :: RevTestMap
rlm04 = reverseLookupMap lm04
testRevLookupMap04     = testRevLookupMap     "04" rlm04 [("bbb",2),("ccc",3),("bbb",2),("aaa",1)]
testRevLookupMapFind04 = testRevLookupMapFind "04" rlm04 "bbb" 2

rlm05 :: RevTestMap
rlm05 = reverseLookupMap lm05
testRevLookupMap05     = testRevLookupMap     "05" rlm05 [("bbb1",2),("ccc",3),("bbb1",2),("aaa",1)]
testRevLookupMapFind05 = testRevLookupMapFind "05" rlm05 "bbb1" 2

rlm06 :: RevTestMap
rlm06 = reverseLookupMap lm06
testRevLookupMap06     = testRevLookupMap     "06" rlm06 [("bbb1",2),("ccc",3),("bbb1",2),("aaa",1)]
testRevLookupMapFind06 = testRevLookupMapFind "06" rlm06 "bbb1" 2

rlm07 :: RevTestMap
rlm07 = reverseLookupMap lm07
testRevLookupMap07     = testRevLookupMap     "07" rlm07 [("bbb",2),("ccc",3),("bbb1",2),("aaa",1)]
testRevLookupMapFind07 = testRevLookupMapFind "07" rlm07 "bbb" 2
testRevLookupMapFind0w = testRevLookupMapFind "07" rlm07 "bbb1" 2
testRevLookupMapFind0x = testRevLookupMapFind "0x" rlm07 "*" revdef

rlm08 :: RevTestMap
rlm08 = reverseLookupMap lm08
testRevLookupMap08     = testRevLookupMap     "08" rlm08 [("bbb",2),("bbb1",2),("aaa",1)]
testRevLookupMapFind08 = testRevLookupMapFind "08" rlm08 "bbb" 2

rlm09 :: RevTestMap
rlm09 = reverseLookupMap lm09
testRevLookupMap09     = testRevLookupMap     "09" rlm09 [("aaa",1)]
testRevLookupMapFind09 = testRevLookupMapFind "09" rlm09 "" revdef

testRevLookupMapSuite = TestList
    [
    testRevLookupMap01, testRevLookupMapFind01,
    testRevLookupMap02, testRevLookupMapFind02,
    testRevLookupMap03, testRevLookupMapFind03,
    testRevLookupMap04, testRevLookupMapFind04,
    testRevLookupMap05, testRevLookupMapFind05,
    testRevLookupMap06, testRevLookupMapFind06,
    testRevLookupMap07, testRevLookupMapFind07,
                        testRevLookupMapFind0w,
                        testRevLookupMapFind0x,
    testRevLookupMap08, testRevLookupMapFind08,
    testRevLookupMap09, testRevLookupMapFind09
    ]

------------------------------------------------------------
--  mapKeys
------------------------------------------------------------

testMapKeys :: String -> TestMap -> [Int] -> Test
testMapKeys lab m1 mk =
    testeq ("testMapKeys:"++lab) mk (sort $ mapKeys m1)

testMapKeys00 = testMapKeys "00" lm00 []
testMapKeys01 = testMapKeys "01" lm01 [1]
testMapKeys02 = testMapKeys "02" lm02 [1,2]
testMapKeys03 = testMapKeys "03" lm03 [1,2,3]
testMapKeys04 = testMapKeys "04" lm04 [1,2,3]
testMapKeys05 = testMapKeys "05" lm05 [1,2,3]
testMapKeys06 = testMapKeys "06" lm06 [1,2,3]
testMapKeys07 = testMapKeys "07" lm07 [1,2,3]
testMapKeys08 = testMapKeys "08" lm08 [1,2]
testMapKeys09 = testMapKeys "09" lm09 [1]

testMapKeysSuite = TestList
    [ testMapKeys00
    , testMapKeys01
    , testMapKeys02
    , testMapKeys03
    , testMapKeys04
    , testMapKeys05
    , testMapKeys06
    , testMapKeys07
    , testMapKeys08
    , testMapKeys09
    ]

------------------------------------------------------------
--  mapVals
------------------------------------------------------------

testMapVals :: String -> TestMap -> [String] -> Test
testMapVals lab m1 mv =
    testeq ("MapVals:"++lab) mv (sort $ mapVals m1)

testMapVals00 = testMapVals "00" lm00 []
testMapVals01 = testMapVals "01" lm01 ["aaa"]
testMapVals02 = testMapVals "02" lm02 ["aaa","bbb"]
testMapVals03 = testMapVals "03" lm03 ["aaa","bbb","ccc"]
testMapVals04 = testMapVals "04" lm04 ["aaa","bbb","ccc"]
testMapVals05 = testMapVals "05" lm05 ["aaa","bbb1","ccc"]
testMapVals06 = testMapVals "06" lm06 ["aaa","bbb1","ccc"]
testMapVals07 = testMapVals "07" lm07 ["aaa","bbb","bbb1","ccc"]
testMapVals08 = testMapVals "08" lm08 ["aaa","bbb","bbb1"]
testMapVals09 = testMapVals "09" lm09 ["aaa"]

testMapValsSuite = TestList
    [ testMapVals00
    , testMapVals01
    , testMapVals02
    , testMapVals03
    , testMapVals04
    , testMapVals05
    , testMapVals06
    , testMapVals07
    , testMapVals08
    , testMapVals09
    ]

------------------------------------------------------------
--  mapEq
------------------------------------------------------------

maplist =
  [ ("lm00",lm00)
  , ("lm01",lm01)
  , ("lm02",lm02)
  , ("lm03",lm03)
  , ("lm04",lm04)
  , ("lm05",lm05)
  , ("lm06",lm06)
  , ("lm07",lm07)
  , ("lm08",lm08)
  , ("lm09",lm09)
  ]

mapeqlist =
  [ ("lm01","lm09")
  , ("lm02","lm08")
  , ("lm03","lm04")
  , ("lm03","lm07")
  , ("lm04","lm07")
  , ("lm05","lm06")
  ]

testMapEq :: String -> Bool -> TestMap -> TestMap -> Test
testMapEq lab eq m1 m2 =
    testeq ("testMapEq:"++lab) eq (mapEq m1 m2)

testMapEqSuite = TestList
  [ testMapEq (testLab l1 l2) (testEq l1 l2) m1 m2
      | (l1,m1) <- maplist , (l2,m2) <- maplist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)       ||
            (l1,l2) `elem` mapeqlist ||
            (l2,l1) `elem` mapeqlist

------------------------------------------------------------
--  mapSelect and mapMerge
------------------------------------------------------------

lm101 = mapAdd lm03 $ newEntry (4,"ddd")
testLookupMap101 = testLookupMap "101" lm101 [(4,"ddd"),(3,"ccc"),(2,"bbb"),(1,"aaa")]

lm102 = mapSelect lm101 [1,3]
testLookupMap102 = testLookupMap "102" lm102 [(3,"ccc"),(1,"aaa")]

lm103 = mapSelect lm101 [2,4]
testLookupMap103 = testLookupMap "103" lm103 [(4,"ddd"),(2,"bbb")]

lm104 = mapSelect lm101 [2,3]
testLookupMap104 = testLookupMap "104" lm104 [(3,"ccc"),(2,"bbb")]

mapSelectSuite = TestList
    [ testLookupMap101
    , testLookupMap102
    , testLookupMap103
    , testLookupMap104
    ]

lm105 = mapMerge lm102 lm103
testLookupMap105 = testLookupMap "105" lm105 [(1,"aaa"),(2,"bbb"),(3,"ccc"),(4,"ddd")]

lm106 = mapMerge lm102 lm104
testLookupMap106 = testLookupMap "106" lm106 [(1,"aaa"),(2,"bbb"),(3,"ccc")]

lm107 = mapMerge lm103 lm104
testLookupMap107 = testLookupMap "107" lm107 [(2,"bbb"),(3,"ccc"),(4,"ddd")]

lm108 = mapMerge lm101 lm102
testLookupMap108 = testLookupMap "108" lm108 [(1,"aaa"),(2,"bbb"),(3,"ccc"),(4,"ddd")]

mapMergeSuite = TestList
    [ testLookupMap105
    , testLookupMap106
    , testLookupMap107
    , testLookupMap108
    ]

------------------------------------------------------------
--  Tranlation tests
------------------------------------------------------------

-- Rather late in the day, generic versions of the testing functions used earlier
type TestMapG a b = LookupMap (GenMapEntry a b)
newMapG :: (Eq a, Show a, Eq b, Show b) => [(a,b)] -> (TestMapG a b)
newMapG es = makeLookupMap (map newEntry es)
testLookupMapG :: (Eq a, Show a, Eq b, Show b) => String -> (TestMapG a b) -> [(a,b)] -> Test
testLookupMapG lab m1 m2 = testeq ("LookupMapG"++lab ) (newMapG m2) m1
testLookupMapM ::
    (Eq a, Show a, Eq b, Show b, Monad m,
     Eq (m (TestMapG a b)), Show (m (TestMapG a b)))
    => String -> m (TestMapG a b) -> m (TestMapG a b) -> Test
testLookupMapM lab m1 m2 = testeq ("LookupMapM"++lab ) m2 m1

tm101               = newMap [(1,"a"),(2,"bb"),(3,"ccc"),(4,"dddd")]
testTranslateMap101 = testLookupMapG "tm101" tm101 [(1,"a"),(2,"bb"),(3,"ccc"),(4,"dddd")]

tf102 = (flip replicate '*') :: Int -> String
tm102 :: StrTestMap
tm102 = mapTranslateKeys tf102 tm101
testTranslateMap102 = testLookupMapG "tm102" tm102 [("*","a"),("**","bb"),("***","ccc"),("****","dddd")]

tf103 = length
tm103 :: RevTestMap
tm103 = mapTranslateVals tf103 tm102
testTranslateMap103 = testLookupMapG "tm103" tm103 [("*",1),("**",2),("***",3),("****",4)]

tf104 e = newEntry ( (flip replicate '#') k, 5-(length v) ) where (k,v) = keyVal e
tm104 :: RevTestMap
tm104 = mapTranslateEntries tf104 tm101
testTranslateMap104 = testLookupMapG "tm104" tm104 [("#",4),("##",3),("###",2),("####",1)]

-- Test monadic translation, using Maybe monad
-- (Note that if Nothing is generated at any step,
-- it propagates to the result)
tf105 e = Just $ tf104 e
tm105 :: MayTestMap
tm105 = mapTranslateEntriesM tf105 tm101
testTranslateMap105 = testLookupMapM "tm105" tm105 (Just tm104)

tf106 e = if k == 2 then Nothing else tf105 e where (k,_) = keyVal e
tm106 :: MayTestMap
tm106 = mapTranslateEntriesM tf106 tm101
testTranslateMap106 = testLookupMapM "tm106" tm106 Nothing

mapTranslateSuite = TestList
    [ testTranslateMap101
    , testTranslateMap102
    , testTranslateMap103
    , testTranslateMap104
    , testTranslateMap105
    , testTranslateMap106
    ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ testLookupMapSuite
  , testRevLookupMapSuite
  , testMapKeysSuite
  , testMapValsSuite
  , testMapEqSuite
  , mapSelectSuite
  , mapMergeSuite
  , mapTranslateSuite
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

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
-- $Source: /file/cvsdev/HaskellUtils/LookupMapTest.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: LookupMapTest.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.20  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.19  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.18  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.17  2003/12/03 22:04:00  graham
-- Re-ordered mapFind (again), to simplify currying of default value.
--
-- Revision 1.16  2003/12/03 22:02:09  graham
-- Re-ordered mapFind, to simplify currying of default value.
--
-- Revision 1.15  2003/10/24 21:02:42  graham
-- Changed kind-structure of LookupMap type classes.
--
-- Revision 1.14  2003/10/14 20:31:21  graham
-- Add separate module for generic variable binding functions.
--
-- Revision 1.13  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.12  2003/06/11 14:07:53  graham
-- Added mapTranslateEntriesM, which performs monadic translation of
-- LookupMap entries.  (Tested using Maybe monad.)
--
-- Revision 1.11  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.10  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.9  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.8  2003/05/23 19:33:36  graham
-- Added and tested RDF graph label translation functions
--
-- Revision 1.7  2003/05/09 00:28:48  graham
-- Added partitionBy to ListHelpers (may want to remove since
-- it's also in the standard List module).
-- Added mapSelect and mapMerge to LookupMap, and test cases.
--
-- Revision 1.6  2003/05/07 18:50:38  graham
-- Add LookupMap functions: mapFindMaybe, mapKeys, mapEq
--
-- Revision 1.5  2003/05/01 23:15:44  graham
-- GraphTest passes all tests using refactored LookupMap
-- Extensive changes to GraphMatch were required.
--
-- Revision 1.4  2003/05/01 19:14:26  graham
-- LookupMap refactored to use class for entry, so that it can be
-- applied to a variety of different types with identifiable key and value
-- components.  All tests pass.
--
-- Revision 1.3  2003/05/01 00:21:41  graham
-- Started refactoring LookupMap.
-- Revised module compiles OK.
-- Working on test module.
--
-- Revision 1.2  2003/04/11 18:12:10  graham
-- Renamed GraphHelpers to ListHelpers
-- LookupMapTest, GraphTest, RDFGraphTest all run OK
--
-- Revision 1.1  2003/04/11 18:05:57  graham
-- Add separate LookupMap test harness
-- Added mapReplaceOrAdd function
-- LookupMapTest runs OK
--
-- Revision 1.7  2003/04/10 13:41:22  graham
-- More graph code tidying
-- Graph test cases still run OK
--
-- Revision 1.6  2003/04/10 13:35:34  graham
-- Separated GraphMatch logic from GraphMem
--
-- Revision 1.5  2003/04/10 08:36:06  graham
-- Graph matching passes battery of new tests
-- Started work on RDF graph
--
-- Revision 1.4  2003/03/31 22:18:08  graham
-- Simple graph equality tests all pass
--
-- Revision 1.3  2003/03/31 20:52:23  graham
-- Restructure graph matching to deal with same unbound node names in
-- different graphs.  It shows signs that it might be working now.
-- More testing is needed.
--
-- Revision 1.2  2003/03/28 21:50:22  graham
-- Graph equality coded and nearly working
--
-- Revision 1.1  2003/03/12 23:00:43  graham
-- Graph model coded and working, except for graph isomorphism test.
--
