--------------------------------------------------------------------------------
--  $Id: GraphTest.hs,v 1.24 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + multi-parameter classes
--
--  This module defines test cases for module Graph.
--
--------------------------------------------------------------------------------


-- WNH module Swish.HaskellRDF.GraphTest where

import System.IO
      ( Handle, IOMode(WriteMode),
        openFile, hClose, hPutStr, hPutStrLn )
import Test.HUnit
      ( Test(TestCase,TestList,TestLabel),
        assertEqual, runTestTT, runTestText, putTextToHandle )
import Data.List( elemIndex )
import Data.Maybe( fromJust )

import Swish.HaskellUtils.ListHelpers
import Swish.HaskellUtils.MiscHelpers
import Swish.HaskellRDF.GraphClass (Arc(..),Label(..),arcFromTriple,arcToTriple)
import Swish.HaskellRDF.GraphMem
import Swish.HaskellRDF.GraphMatch
      ( graphMatch,
        -- The rest exported for testing only
        LabelMap(..), GenLabelMap(..), LabelEntry(..), GenLabelEntry(..),
        ScopedLabel(..), makeScopedLabel, makeScopedArc,
        LabelIndex, EquivalenceClass, nullLabelVal, emptyMap,
        labelIsVar, labelHash,
        mapLabelIndex, {-mapLabelList,-} setLabelHash, newLabelMap,
        graphLabels, assignLabelMap, newGenerationMap,
        graphMatch1, graphMatch2, equivalenceClasses, reclassify
      )
import Swish.HaskellUtils.LookupMap
      ( LookupEntryClass(..), LookupMap(..), makeLookupMap
      , mapSortByKey, mapSortByVal
      )

default ( Int )

------------------------------------------------------------
-- Define some common values
------------------------------------------------------------

base1 = "http://id.ninebynine.org/wip/2003/test/graph1/node#"
base2 = "http://id.ninebynine.org/wip/2003/test/graph2/node/"
base3 = "http://id.ninebynine.org/wip/2003/test/graph3/node"
base4 = "http://id.ninebynine.org/wip/2003/test/graph3/nodebase"

------------------------------------------------------------
--  Set, get graph arcs as lists of triples
------------------------------------------------------------

setArcsT a = setArcs $ map arcFromTriple a
getArcsT g = map arcToTriple $ getArcs g

toStatement s p o = Arc s p o

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
--  Label map and entry creation helpers
------------------------------------------------------------

tstLabelMap :: (Label lb) => Int -> [(lb,LabelIndex)] -> LabelMap lb
tstLabelMap gen lvs = LabelMap gen (makeLookupMap $ makeEntries lvs)

makeEntries :: (Label lb) => [(lb,LabelIndex)] -> [LabelEntry lb]
makeEntries lvs = map newEntry lvs

labelMapSortByVal :: (Label lb) => LabelMap lb -> LabelMap lb
labelMapSortByVal (LabelMap gen lmap) = LabelMap gen (mapSortByVal lmap)

------------------------------------------------------------
--  Graph helper function tests
------------------------------------------------------------

-- select

testSelect :: String -> [Char] -> [Char] -> Test
testSelect lab l1 l2 = testeq ("Select"++lab ) l1 l2

testSelect01 = testSelect "01"
                (select (1==) [0,1,2,0,1,2] ['a','b','c','a','b','c'])
                ['b','b']
testSelect02 = testSelect "02"
                (select (1==) [1,1,1,1,1,1] ['a','b','c','a','b','c'])
                ['a','b','c','a','b','c']
testSelect03 = testSelect "03"
                (select (1==) [0,0,0,0,0,0] ['a','b','c','a','b','c'])
                []
testSelect04 = testSelect "04"
                (select (1==) []            []                       )
                []

testSelectSuite = TestList
    [
    testSelect01, testSelect02, testSelect03, testSelect04
    ]

-- mapset

mf   :: Int -> Char
mf n = "_abcde" !! n

testMapset :: String -> [Int] -> [Char] -> Test
testMapset lab l1 l2 = testeq ("Mapset"++lab ) l2 (mapset mf l1)

testMapset01 = testMapset "01" [0,1,2,3,4,5] ['_','a','b','c','d','e']
testMapset02 = testMapset "02" [1,1,3,3,5,5] ['a','c','e']
testMapset03 = testMapset "03" [5,4,3,2,1,0] ['e','d','c','b','a','_']
testMapset04 = testMapset "04" []            []
testMapset05 = testMapset "05" [1,2,3,4,5,0] ['a','b','c','d','e','_']

testMapsetSuite = TestList
    [
    testMapset01, testMapset02, testMapset03, testMapset04,
    testMapset05
    ]

-- subset

testSubset :: String -> Bool -> [Int] -> [Int] -> Test
testSubset lab res l1 l2 = testeq ("Mapset"++lab ) res (l1 `subset` l2)

testSubset01 = testSubset "01" True  [1,2,3]       [0,1,2,3,4,5]
testSubset02 = testSubset "02" True  [5,3,1]       [0,1,2,3,4,5]
testSubset03 = testSubset "03" True  [5,4,3,2,1,0] [0,1,2,3,4,5]
testSubset04 = testSubset "04" True  []            []
testSubset05 = testSubset "05" False [0,1,2,3,4,5] [1,2,3]
testSubset06 = testSubset "06" False [0,1,2,3,4,5] [5,3,1]
testSubset07 = testSubset "07" True  []            [1,2,3]
testSubset08 = testSubset "08" False [1,2,3]       []

testSubsetSuite = TestList
    [
    testSubset01, testSubset02, testSubset03, testSubset04,
    testSubset05, testSubset06, testSubset07, testSubset08
    ]

-- hash

testHash :: String -> Bool -> Int -> Int -> Test
testHash lab eq h1 h2 = testeq ("Hash"++lab ) eq (h1 == h2)
testHashEq lab h1 h2  = testeq ("Hash"++lab ) h1 h2

testHash01 = testHash "01" True  (hash 0 base1) (hash 0 base1)
testHash02 = testHash "02" True  (hash 2 "")    (hash 2 "")
testHash03 = testHash "03" False (hash 3 base1) (hash 3 base2)
testHash04 = testHash "04" False (hash 4 base1) (hash 5 base1)
testHash05 = testHash "05" False (hash 2 "")    (hash 3 "")
testHash06 = testHashEq "06"     1424775        (hash 3 base1)
testHash07 = testHashEq "07"     11801303       (hash 3 base2)

testHashSuite = TestList
    [
    testHash01, testHash02, testHash03, testHash04,
    testHash05, testHash06, testHash07
    ]

------------------------------------------------------------
--  Simple graph label tests
------------------------------------------------------------

testLab01 = testeq "Lab01" False (labelIsVar lab1f)
testLab02 = testeq "Lab02" True  (labelIsVar lab1v)
testLab03 = testeq "Lab03" False (labelIsVar lab2f)
testLab04 = testeq "Lab04" True  (labelIsVar lab2v)

testLab05 = testeq "Lab05"  3436883 (labelHash 1 lab1f)
testLab06 = testeq "Lab06" 10955600 (labelHash 1 lab1v)
testLab07 = testeq "Lab07"  3436884 (labelHash 1 lab2f)
testLab08 = testeq "Lab08" 10955601 (labelHash 1 lab2v)

testLab09 = testeq "Lab09" "!lab1" (show lab1f)
testLab10 = testeq "Lab10" "?lab1" (show lab1v)
testLab11 = testeq "Lab11" "!lab2" (show lab2f)
testLab12 = testeq "Lab12" "?lab2" (show lab2v)

testLab13 = testeq "Lab13" "lab1" (getLocal lab1v)
testLab14 = testeq "Lab14" "lab2" (getLocal lab2v)
testLab15 = testeq "Lab15" lab1v  (makeLabel "lab1")
testLab16 = testeq "Lab16" lab2v  (makeLabel "lab2")

testLabSuite = TestList
    [
    testLab01, testLab02, testLab03, testLab04,
    testLab05, testLab06, testLab07, testLab08,
    testLab09, testLab10, testLab11, testLab12,
    testLab13, testLab14, testLab15, testLab16
    ]

------------------------------------------------------------
--  Simple graph tests
------------------------------------------------------------

lab1f = LF "lab1"
lab1v = LV "lab1"
lab2f = LF "lab2"
lab2v = LV "lab2"

gr1 = GraphMem { arcs=[]::[Arc LabelMem] }
ga1 =
    [
    (lab1f,lab1f,lab1f),
    (lab1v,lab1v,lab1v),
    (lab2f,lab2f,lab2f),
    (lab2v,lab2v,lab2v),
    (lab1f,lab1f,lab1v),
    (lab1f,lab1f,lab2f),
    (lab1f,lab1f,lab2v),
    (lab1v,lab1v,lab1f),
    (lab1v,lab1v,lab2f),
    (lab1v,lab1v,lab2v),
    (lab1f,lab1v,lab2f),
    (lab1f,lab1v,lab2v),
    (lab1v,lab2f,lab2v)
    ]

gs4 (Arc _ _ (LV "lab2")) = True
gs4 (Arc _ _  _         ) = False
ga4 =
    [
    (lab2v,lab2v,lab2v),
    (lab1f,lab1f,lab2v),
    (lab1v,lab1v,lab2v),
    (lab1f,lab1v,lab2v),
    (lab1v,lab2f,lab2v)
    ]

gr2 = GraphMem { arcs=[]::[Arc LabelMem] }
ga2 =
    [
    (lab1f,lab1f,lab1f),
    (lab1v,lab1v,lab1v),
    (lab2f,lab2f,lab2f),
    (lab2v,lab2v,lab2v)
    ]

gr3 = GraphMem { arcs=[]::[Arc LabelMem] }
ga3 =
    [
    (lab1f,lab1f,lab1v),
    (lab1f,lab1f,lab2f),
    (lab1f,lab1f,lab2v),
    (lab1v,lab1v,lab1f),
    (lab1v,lab1v,lab2f),
    (lab1v,lab1v,lab2v),
    (lab1f,lab1v,lab2f),
    (lab1f,lab1v,lab2v),
    (lab1v,lab2f,lab2v)
    ]

gl4 = [lab1f,lab1v,lab2f,lab2v]


gr1a = setArcsT ga1 gr1
testGraph01 = testeq "Graph01" ga1 (getArcsT gr1a)

gr2a = setArcsT ga2 gr2
testGraph02 = testeq "Graph01" ga2 (getArcsT gr2a)

gr3a = setArcsT ga3 gr3
testGraph03 = testeq "Graph03" ga3 (getArcsT gr3a)

gr4a = add gr2a gr3a
testGraph04 = testeqv "Graph04" ga1 (getArcsT gr4a)

gr4b = add gr3a gr2a
testGraph05 = testeqv "Graph05" ga1 (getArcsT gr4b)

gr4c = delete gr2a gr4a
testGraph06 = testeqv "Graph06" ga3 (getArcsT gr4c)

gr4d = delete gr3a gr4a
testGraph07 = testeqv "Graph07" ga2 (getArcsT gr4d)

gr4e = extract gs4 gr4a
testGraph08 = testeqv "Graph08" ga4 (getArcsT gr4e)
gr4ee = map gs4 (getArcs gr4a)

gl4f = labels gr4a
testGraph09 = testeqv "Graph09" gl4 gl4f

gr4g = add gr2a gr4a
testGraph10 = testeq "Graph10" ga1 (getArcsT gr4g)

testGraphSuite = TestList
    [
    testGraph01, testGraph02, testGraph03, testGraph04,
    testGraph05, testGraph06, testGraph07, testGraph08,
    testGraph09, testGraph10
    ]

------------------------------------------------------------
--
------------------------------------------------------------

------------------------------------------------------------
-- Define some common values
------------------------------------------------------------

s1 = LF "s1"
s2 = LF "s2"
s3 = LF "s3"
s4 = LF ""
s5 = LV "s5"
s6 = LF "basemore"
s7 = LF ("base"++"more")
s8 = LV "s8"

b1 = LV "b1"
b2 = LV "b2"
b3 = LV "b3"
b4 = LV "b4"

p1 = LF "p1"
p2 = LF "p2"
p3 = LF "p3"
p4 = LF "p4"

o1 = LF "o1"
o2 = LF "o2"
o3 = LF "o3"
o4 = LF ""
o5 = LV "o5"
o6 = LV "s5"

l1  = LF "l1"
l2  = LF "l2-en"
l3  = LF "l2-fr"
l4  = LF "l4-type1"
l5  = LF "l4-type1"
l6  = LF "l4-type1"
l7  = LF "l4-type2"
l8  = LF "l4-type2"
l9  = LF "l4-type2"
l10 = LF "l10-xml"
l11 = LF "l10-xml-en"
l12 = LF "l10-xml-fr"

v1  = LV "v1"
v2  = LV "v2"
v3  = LV "v3"
v4  = LV "v4"

------------------------------------------------------------
--  Label construction and equality tests
------------------------------------------------------------

testLabelEq :: String -> Bool -> LabelMem -> LabelMem -> Test
testLabelEq lab eq n1 n2 =
    TestCase ( assertEqual ("testLabelEq:"++lab) eq (n1==n2) )

nodelist =
  [ ("s1",s1), ("s2",s2), ("s3",s3), ("s4",s4), ("s5",s5),
    ("s6",s6), ("s7",s7), ("s8",s8),
    ("o5",o5),
    ("p1",p1), ("p2",p2), ("p3",p3), ("p4",p4),
    ("o1",o1), ("o2",o2), ("o3",o3), ("o4",o4),
    ("l1",l1), ("l2",l2), ("l3",l3), ("l4",l4), ("l5",l5),
    ("l6",l6), ("l7",l7), ("l8",l8), ("l9",l9),
    ("l10",l10), ("l11",l11), ("l12",l12),
    ("v1",v1), ("v2",v2)
  ]

nodeeqlist =
  [
    ("s4","o4"),
    ("s5","o6"),
    ("s6","s7"),
    ("l4","l5"),
    ("l4","l6"),
    ("l5","l6"),
    ("l7","l8"),
    ("l7","l9"),
    ("l8","l9")
  ]

testLabelEqSuite = TestList
  [ testLabelEq (testLab l1 l2) (testEq  l1 l2) n1 n2
      | (l1,n1) <- nodelist , (l2,n2) <- nodelist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` nodeeqlist ||
            (l2,l1) `elem` nodeeqlist


------------------------------------------------------------
--  Label ordering tests
------------------------------------------------------------

testLabelOrd :: String -> Ordering -> LabelMem -> LabelMem -> Test
testLabelOrd lab order n1 n2 =
    TestCase ( assertEqual ("testLabelOrd:"++lab) order (compare n1 n2) )

nodeorder =
  [
    "o4",
    "s4", "s6", "s7",
    "l1", "l10", "l11", "l12", "l2", "l3", "l4", "l5", "l6", "l7", "l8", "l9",
    "o1", "o2", "o3",
    "p1", "p2", "p3", "p4",
    "s1", "s2", "s3",
    "b1", "b2", "b3", "b4",
    "o5",
    "s5", "s8",
    "v1", "v2"
  ]

testLabelOrdSuite = TestList
  [ testLabelOrd (testLab l1 l2) (testOrd l1 l2) n1 n2
      | (l1,n1) <- nodelist , (l2,n2) <- nodelist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testOrd l1 l2
      | testEq l1 l2  = EQ
      | otherwise     = compare (fromJust $ elemIndex l1 nodeorder)
                                (fromJust $ elemIndex l2 nodeorder)
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` nodeeqlist ||
            (l2,l1) `elem` nodeeqlist


------------------------------------------------------------
-- Statement construction and equality tests
------------------------------------------------------------

type Statement = Arc LabelMem

testStmtEq :: String -> Bool -> Statement -> Statement -> Test
testStmtEq lab eq t1 t2 =
    TestCase ( assertEqual ("testStmtEq:"++lab) eq (t1==t2) )

slist =
  [
    ("s1",s1), ("s4",s4), ("s5",s5), ("s6",s6), ("s7",s7)
  ]

plist =
  [
    ("p1",p1)
  ]

olist =
  [ ("o1",o1), ("o4",o4), ("o5",o5),
    ("l1",l1), ("l4",l4), ("l7",l7), ("l8",l8), ("l10",l10)
  ]

tlist =
  [ (lab s p o,trp s p o) | s <- slist, p <- plist, o <- olist ]
    where
    lab (s,_) (p,_) (o,_) = s++"."++p++"."++o
    trp (_,s) (_,p) (_,o) = Arc s p o

stmteqlist =
  [
    ("s6.p1.l1", "s7.p1.l1"),
    ("s6.p1.l4", "s7.p1.l4"),
    ("s6.p1.l7", "s7.p1.l7"),
    ("s6.p1.l7", "s7.p1.l8"),
    ("s6.p1.l8", "s7.p1.l7"),
    ("s6.p1.l8", "s7.p1.l8"),
    ("s6.p1.l10","s7.p1.l10"),
    ("s6.p1.o1", "s7.p1.o1"),
    ("s6.p1.o4", "s7.p1.o4"),
    ("s6.p1.o5", "s7.p1.o5"),
    ("s1.p1.l7", "s1.p1.l8"),
    ("s4.p1.l7", "s4.p1.l8"),
    ("s5.p1.l7", "s5.p1.l8"),
    ("s6.p1.l7", "s6.p1.l8"),
    ("s7.p1.l7", "s7.p1.l8")
  ]

testStmtEqSuite = TestList
  [ testStmtEq (testLab l1 l2) (testEq  l1 l2) t1 t2
      | (l1,t1) <- tlist , (l2,t2) <- tlist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` stmteqlist ||
            (l2,l1) `elem` stmteqlist

------------------------------------------------------------
--  Graph element handling support routines
------------------------------------------------------------

lmap = tstLabelMap 5 [(s1,(1,1)),(s2,(2,2)),(s3,(3,3)),(s4,(4,4)),
                      (o1,(1,1)),(o2,(2,2)),(o3,(3,3))]
llst = ["s1","s2","s3","s4","o1","o2","o3"]

-- showLabelMap :: (Label lb) => LabelMap lb -> String
testShowLabelMap = testeq "showLabelMap" showMap (show lmap)
    where
        showMap = "LabelMap gen=5, map=\n"++
                  "    !s1:(1,1)\n"++
                  "    !s2:(2,2)\n"++
                  "    !s3:(3,3)\n"++
                  "    !:(4,4)\n"++
                  "    !o1:(1,1)\n"++
                  "    !o2:(2,2)\n"++
                  "    !o3:(3,3)"

-- mapLabelIndex :: (Label lb) => LabelMap lb -> lb -> LabelIndex
testMapLabelIndex01 = testeq "testMapLabelIndex01" (1,1) (mapLabelIndex lmap s1 )
testMapLabelIndex02 = testeq "testMapLabelIndex02" (2,2) (mapLabelIndex lmap s2 )
testMapLabelIndex03 = testeq "testMapLabelIndex03" (3,3) (mapLabelIndex lmap s3 )
testMapLabelIndex04 = testeq "testMapLabelIndex04" (4,4) (mapLabelIndex lmap s4 )
testMapLabelIndex05 = testeq "testMapLabelIndex05" (1,1) (mapLabelIndex lmap o1 )
testMapLabelIndex06 = testeq "testMapLabelIndex06" (4,4) (mapLabelIndex lmap o4 )
testMapLabelIndex07 = testeq "testMapLabelIndex07" nullLabelVal (mapLabelIndex lmap o5 )
testMapLabelIndex08 = testeq "testMapLabelIndex08" nullLabelVal (mapLabelIndex lmap o6 )

-- setLabelHash :: (Label lb) => LabelMap lb -> (lb,Int) -> LabelMap lb
lmap1 = setLabelHash lmap (s2,22)

testMapLabelHash00 = testeq "mapLabelHash00" showMap (show lmap1)
    where
        showMap = "LabelMap gen=5, map=\n"++
                  "    !s1:(1,1)\n"++
                  "    !s2:(5,22)\n"++
                  "    !s3:(3,3)\n"++
                  "    !:(4,4)\n"++
                  "    !o1:(1,1)\n"++
                  "    !o2:(2,2)\n"++
                  "    !o3:(3,3)"

testMapLabelHash01 = testeq "MapLabelHash01" (1,1)  (mapLabelIndex lmap1 s1 )
testMapLabelHash02 = testeq "MapLabelHash02" (5,22) (mapLabelIndex lmap1 s2 )
testMapLabelHash03 = testeq "MapLabelHash03" (3,3)  (mapLabelIndex lmap1 s3 )
testMapLabelHash04 = testeq "MapLabelHash04" (4,4)  (mapLabelIndex lmap1 s4 )
testMapLabelHash05 = testeq "MapLabelHash05" (1,1)  (mapLabelIndex lmap1 o1 )
testMapLabelHash06 = testeq "MapLabelHash06" (4,4)  (mapLabelIndex lmap1 o4 )
testMapLabelHash07 = testeq "MapLabelHash07" nullLabelVal (mapLabelIndex lmap1 o5 )
testMapLabelHash08 = testeq "MapLabelHash08" nullLabelVal (mapLabelIndex lmap1 o6 )

lmap2a = setLabelHash lmap1  (o1,66)
lmap2b = setLabelHash lmap2a (o5,67)
testMapLabelHash11 = testeq "MapLabelHash11" (1,1)  (mapLabelIndex lmap2b s1 )
testMapLabelHash12 = testeq "MapLabelHash12" (5,22) (mapLabelIndex lmap2b s2 )
testMapLabelHash13 = testeq "MapLabelHash13" (3,3)  (mapLabelIndex lmap2b s3 )
testMapLabelHash14 = testeq "MapLabelHash14" (4,4)  (mapLabelIndex lmap2b s4 )
testMapLabelHash15 = testeq "MapLabelHash15" (5,66) (mapLabelIndex lmap2b o1 )
testMapLabelHash16 = testeq "MapLabelHash16" (2,2)  (mapLabelIndex lmap2b o2 )
testMapLabelHash17 = testeq "MapLabelHash17" (4,4)  (mapLabelIndex lmap2b o4 )
testMapLabelHash18 = testeq "MapLabelHash18" nullLabelVal (mapLabelIndex lmap1 o5 )

-- newLabelMap :: (Label lb) => LabelMap lb -> [(lb,Int)] -> LabelMap lb
lmap3 = newLabelMap lmap [(s1,61),(s3,63),(o2,66)]
testLabelMap01 = testeq "LabelMap01" (6,61) (mapLabelIndex lmap3 s1 )
testLabelMap02 = testeq "LabelMap02" (2,2)  (mapLabelIndex lmap3 s2 )
testLabelMap03 = testeq "LabelMap03" (6,63) (mapLabelIndex lmap3 s3 )
testLabelMap04 = testeq "LabelMap04" (4,4)  (mapLabelIndex lmap3 s4 )
testLabelMap05 = testeq "LabelMap05" (1,1)  (mapLabelIndex lmap3 o1 )
testLabelMap06 = testeq "LabelMap06" (6,66) (mapLabelIndex lmap3 o2 )

testLabelMapSuite = TestList
  [ testShowLabelMap
  , testMapLabelIndex01
  , testMapLabelIndex02
  , testMapLabelIndex03
  , testMapLabelIndex04
  , testMapLabelIndex05
  , testMapLabelIndex06
  , testMapLabelIndex07
  , testMapLabelIndex08
  , testMapLabelHash00
  , testMapLabelHash01
  , testMapLabelHash02
  , testMapLabelHash03
  , testMapLabelHash04
  , testMapLabelHash05
  , testMapLabelHash06
  , testMapLabelHash07
  , testMapLabelHash08
  , testMapLabelHash11
  , testMapLabelHash12
  , testMapLabelHash13
  , testMapLabelHash14
  , testMapLabelHash15
  , testMapLabelHash16
  , testMapLabelHash17
  , testMapLabelHash18
  , testLabelMap01
  , testLabelMap02
  , testLabelMap03
  , testLabelMap04
  , testLabelMap05
  ]

------------------------------------------------------------
--  Graph matching support
------------------------------------------------------------

t01 = toStatement s1 p1 o1
t02 = toStatement s2 p1 o2
t03 = toStatement s3 p1 o3
t04 = toStatement s1 p1 l1
t05 = toStatement s2 p1 l4
t06 = toStatement s3 p1 l10

t10 = toStatement s1 p1 b1
t11 = toStatement b1 p2 b2
t12 = toStatement b2 p3 o1

t20 = toStatement s1 p1 b3
t21 = toStatement b3 p2 b4
t22 = toStatement b4 p3 o1

as1 = [t01]

as2 = [t01,t02,t03,t04,t05,t06]

as4 = [t01,t02,t03,t04,t05,t06,t10,t11,t12]

as5 = [t01,t02,t03,t04,t05,t06,t20,t21,t22]

as6 = [t01,t02,t03,t04,t05,t06,t10,t11,t12,t20,t21,t22]


-- graphLabels :: (Label lb) => [Arc lb] -> [lb]
ls4 = [s1,s2,s3,p1,p2,p3,o1,o2,o3,l1,l4,l10,b1,b2]
testGraphLabels04 = testeqv "GraphLabels04" ls4 (graphLabels as4)
testGraphLabels14 = testeq  "GraphLabels14" str (show (graphLabels as4))
    where
        str = "[!s1,!p1,!o1,!s2,!o2,!s3,!o3,!l1,!l4-type1,!l10-xml,?b1,!p2,?b2,!p3]"
        -- str = "[!p3,?b2,!p2,?b1,!l10-xml,!l4-type1,!l1,!o3,!s3,!o2,!s2,!o1,!p1,!s1]"

ls5 = [s1,s2,s3,p1,p2,p3,o1,o2,o3,l1,l4,l10,b3,b4]
testGraphLabels05 = testeqv "GraphLabels05" ls5 (graphLabels as5)
testGraphLabels15 = testeq  "GraphLabels15" str (show (graphLabels as5))
    where
        str = "[!s1,!p1,!o1,!s2,!o2,!s3,!o3,!l1,!l4-type1,!l10-xml,?b3,!p2,?b4,!p3]"
        -- str = "[!p3,?b4,!p2,?b3,!l10-xml,!l4-type1,!l1,!o3,!s3,!o2,!s2,!o1,!p1,!s1]"

ls6 = [s1,s2,s3,p1,p2,p3,o1,o2,o3,l1,l4,l10,b1,b2,b3,b4]
testGraphLabels06 = testeqv "GraphLabels05" ls6 (graphLabels as6)
testGraphLabels16 = testeq  "GraphLabels16" str (show (graphLabels as6))
    where
        str = "[!s1,!p1,!o1,!s2,!o2,!s3,!o3"++
              ",!l1,!l4-type1,!l10-xml,?b1,!p2,?b2,!p3,?b3,?b4]"
        -- str = "[?b4,?b3,!p3,?b2,!p2,?b1,!l10-xml,!l4-type1,!l1"++
        --       ",!o3,!s3,!o2,!s2,!o1,!p1,!s1]"

-- assignLabels :: (Label lb) => [lb] -> LabelMap lb -> LabelMap lb

lmap5 = tstLabelMap 2 [(s1,(1,142577)),(s2,(1,142578)),(s3,(1,142579)),
                       (p1,(1,142385)),(p2,(1,142386)),(p3,(1,142387)),
                       (o1,(1,142321)),(o2,(1,142322)),(o3,(1,142323)),
                       (l1,(1,142129)),(l4,(1,1709580)),(l10,(1,3766582)),
                       (b3,(1,262143)),(b4,(1,262143))]
testAssignLabelMap05 = testeq "AssignLabels05" lmap5
                        (newGenerationMap $ assignLabelMap ls5 emptyMap)

lmap6 = tstLabelMap 2 [(s1,(1,142577)),(s2,(1,142578)),(s3,(1,142579)),
                       (p1,(1,142385)),(p2,(1,142386)),(p3,(1,142387)),
                       (o1,(1,142321)),(o2,(1,142322)),(o3,(1,142323)),
                       (l1,(1,142129)),(l4,(1,1709580)),(l10,(1,3766582)),
                       (b1,(2,262143)),(b2,(2,262143)),(b3,(1,262143)),(b4,(1,262143))]
testAssignLabelMap06 = testeq "AssignLabels06" lmap6 (assignLabelMap ls6 lmap5)


lmapc = tstLabelMap 1 [(s1,(1,11)),(s2,(1,12)),(s3,(1,13)),
                       (p1,(1,21)),(p2,(1,22)),(p3,(1,13)),
                       (o1,(1,31)),(o2,(1,32)),(o3,(1,13)),
                       (l1,(1,41)),(l4,(1,42)),(l10,(1,43)),
                       (b1,(1,51)),(b2,(1,51)),(b3,(1,51)),(b4,(1,51))]

-- [[[TODO: test hash value collision on non-variable label]]]

testGraphMatchSupportSuite = TestList
  [ testGraphLabels04
  , testGraphLabels14
  , testGraphLabels05
  , testGraphLabels15
  , testGraphLabels06
  , testGraphLabels16
  , testAssignLabelMap05
  , testAssignLabelMap06
  ]

------------------------------------------------------------
--  Test steps in graph equality test
------------------------------------------------------------

matchable l1 l2 = True

s1_1 = makeScopedLabel 1 s1
s2_1 = makeScopedLabel 1 s2
s3_1 = makeScopedLabel 1 s3
p1_1 = makeScopedLabel 1 p1
p2_1 = makeScopedLabel 1 p2
p3_1 = makeScopedLabel 1 p3
o1_1 = makeScopedLabel 1 o1
o2_1 = makeScopedLabel 1 o2
o3_1 = makeScopedLabel 1 o3
l1_1 = makeScopedLabel 1 l1
l4_1 = makeScopedLabel 1 l4
l10_1 = makeScopedLabel 1 l10
b1_1 = makeScopedLabel 1 b1
b2_1 = makeScopedLabel 1 b2
b3_1 = makeScopedLabel 1 b3
b4_1 = makeScopedLabel 1 b4

s1_2 = makeScopedLabel 2 s1
s2_2 = makeScopedLabel 2 s2
s3_2 = makeScopedLabel 2 s3
p1_2 = makeScopedLabel 2 p1
p2_2 = makeScopedLabel 2 p2
p3_2 = makeScopedLabel 2 p3
o1_2 = makeScopedLabel 2 o1
o2_2 = makeScopedLabel 2 o2
o3_2 = makeScopedLabel 2 o3
l1_2 = makeScopedLabel 2 l1
l4_2 = makeScopedLabel 2 l4
l10_2 = makeScopedLabel 2 l10
b1_2 = makeScopedLabel 2 b1
b2_2 = makeScopedLabel 2 b2
b3_2 = makeScopedLabel 2 b3
b4_2 = makeScopedLabel 2 b4

t01_1 = makeScopedArc 1 t01

t01_2 = makeScopedArc 2 t01
t02_2 = makeScopedArc 2 t02
t03_2 = makeScopedArc 2 t03
t04_2 = makeScopedArc 2 t04
t05_2 = makeScopedArc 2 t05
t06_2 = makeScopedArc 2 t06

t10_1 = makeScopedArc 1 t10
t11_1 = makeScopedArc 1 t11
t12_1 = makeScopedArc 1 t12
t20_1 = makeScopedArc 1 t20
t21_1 = makeScopedArc 1 t21
t22_1 = makeScopedArc 1 t22

t10_2 = makeScopedArc 2 t10
t11_2 = makeScopedArc 2 t11
t12_2 = makeScopedArc 2 t12
t20_2 = makeScopedArc 2 t20
t21_2 = makeScopedArc 2 t21
t22_2 = makeScopedArc 2 t22

-- Compare graph as6 with self, in steps

as61 = map (makeScopedArc 1) as6
as62 = map (makeScopedArc 2) as6

eq1lmap     = newGenerationMap $
              assignLabelMap (graphLabels as62) $
              assignLabelMap (graphLabels as61) emptyMap
eq1ltst     = tstLabelMap 2 [
                             (s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                             (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                             (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                             (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                             (b1_1,(1,262143)),(b2_1,(1,262143)),(b3_1,(1,262143)),(b4_1,(1,262143)),
                             (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                             (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                             (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                             (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                             (b1_2,(1,262143)),(b2_2,(1,262143)),(b3_2,(1,262143)),(b4_2,(1,262143))
                            ]
testEqAssignMap01 = testeq "EqAssignMap01" eq1ltst eq1lmap

eq1hs1      = [t10_1,t11_1,t12_1,t20_1,t21_1,t22_1]
eq1hs2      = [t10_2,t11_2,t12_2,t20_2,t21_2,t22_2]

eq1lmap'    = tstLabelMap 2 [(s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                             (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                             (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                             (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                             (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                             (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                             (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                             (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                             (b1_1,(2,3880463)),(b2_1,(2,3400925)),
                                                (b3_1,(2,3880463)),
                                                (b4_1,(2,3400925)),
                             (b1_2,(2,3880463)),(b2_2,(2,3400925)),
                                                (b3_2,(2,3880463)),
                                                (b4_2,(2,3400925))]

eq1lmap''   = newLabelMap eq1lmap'
                [
                (b1_1,2576315),(b2_1,3400925),(b3_1,1571691),
                (b1_2,2576315),(b2_2,3400925),(b3_2,1571691)
                ]
eq1ltst''   = tstLabelMap 3 [
                            (s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                            (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                            (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                            (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                            (b1_1,(3,2576315)),
                            (b2_1,(3,3400925)),
                            (b3_1,(3,1571691)),
                            (b4_1,(2,3400925)),
                            (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                            (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                            (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                            (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                            (b1_2,(3,2576315)),
                            (b2_2,(3,3400925)),
                            (b3_2,(3,1571691)),
                            (b4_2,(2,3400925))
                            ]
testEqNewLabelMap07 = testeq "EqNewLabelMap07" eq1ltst'' eq1lmap''

-- Repeat same tests for as4...

as41 = map (makeScopedArc 1) as4
as42 = map (makeScopedArc 2) as4

eq2lmap     = newGenerationMap $
              assignLabelMap (graphLabels as42) $
              assignLabelMap (graphLabels as41) emptyMap
eq2ltst     = tstLabelMap 2 [(s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                             (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                             (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                             (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                             (b1_1,(1,262143)),(b2_1,(1,262143)),
                             (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                             (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                             (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                             (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                             (b1_2,(1,262143)),(b2_2,(1,262143))]
testEqAssignMap21 = testeq "EqAssignMap21" eq2ltst eq2lmap

eq2hs1      = [t10_1,t11_1,t12_1]
eq2hs2      = [t10_2,t11_2,t12_2]

eq2lmap'    = tstLabelMap 2 [
                             (s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                             (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                             (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                             (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                             (b1_1,(2,3880463)),(b2_1,(2,3400925)),
                             (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                             (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                             (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                             (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                             (b1_2,(2,3880463)),(b2_2,(2,3400925))
                            ]

eq2lmap''   = newLabelMap eq2lmap'
                [
                (b2_1,3400925),
                (b2_2,3400925)
                ]
eq2ltst''   = tstLabelMap 3 [
                            (s1_1,(1,142577)),(s2_1,(1,142578)),(s3_1,(1,142579)),
                            (p1_1,(1,142385)),(p2_1,(1,142386)),(p3_1,(1,142387)),
                            (o1_1,(1,142321)),(o2_1,(1,142322)),(o3_1,(1,142323)),
                            (l1_1,(1,142129)),(l4_1,(1,1709580)),(l10_1,(1,3766582)),
                            (b1_1,(2,3880463)),
                            (b2_1,(3,3400925)),
                            (s1_2,(1,142577)),(s2_2,(1,142578)),(s3_2,(1,142579)),
                            (p1_2,(1,142385)),(p2_2,(1,142386)),(p3_2,(1,142387)),
                            (o1_2,(1,142321)),(o2_2,(1,142322)),(o3_2,(1,142323)),
                            (l1_2,(1,142129)),(l4_2,(1,1709580)),(l10_2,(1,3766582)),
                            (b1_2,(2,3880463)),
                            (b2_2,(3,3400925))
                            ]
testEqNewLabelMap27 = testeq "EqNewLabelMap27" eq2ltst'' eq2lmap''

-- Compare as1 with as2, in steps

as11 = map (makeScopedArc 1) as1
as22 = map (makeScopedArc 2) as2

eq3hs1   = [t01_1]
eq3hs2   = [t01_2,t02_2,t03_2,t04_2,t05_2,t06_2]

testEqGraphMap31_1 = testeq "testEqGraphMap31_1" eq3hs1 as11
testEqGraphMap31_2 = testeq "testEqGraphMap31_2" eq3hs2 as22

eq3lmap     = newGenerationMap $
              assignLabelMap (graphLabels as11) $
              assignLabelMap (graphLabels as22) emptyMap
eq3ltst     = tstLabelMap 2
    [ (s1_1,(1,142577))
    , (p1_1,(1,142385))
    , (o1_1,(1,142321))
    , (s1_2,(1,142577)), (s2_2,(1,142578)), (s3_2,(1,142579))
    , (p1_2,(1,142385))
    , (o1_2,(1,142321)), (o2_2,(1,142322)), (o3_2,(1,142323))
    , (l1_2,(1,142129)), (l4_2,(1,1709580)), (l10_2,(1,3766582))
    ]
testEqAssignMap32 = testeq "EqAssignMap32" eq3ltst eq3lmap

ec31     = equivalenceClasses eq3lmap (graphLabels as11)
ec31test =
    [ ((1,142321),[o1_1])
    , ((1,142385),[p1_1])
    , ((1,142577),[s1_1])
    ]

ec32 = equivalenceClasses eq3lmap (graphLabels as22)
ec32test =
    [ ((1,142129),[l1_2])
    , ((1,142321),[o1_2])
    , ((1,142322),[o2_2])
    , ((1,142323),[o3_2])
    , ((1,142385),[p1_2])
    , ((1,142577),[s1_2])
    , ((1,142578),[s2_2])
    , ((1,142579),[s3_2])
    , ((1,1709580),[l4_2])
    , ((1,3766582),[l10_2])
    ]

testEquivClass33_1 = testeq "EquivClass33_1" ec31test ec31
testEquivClass33_2 = testeq "EquivClass33_2" ec32test ec32

-- This value is nonsense for this test,
-- but a parameter is needed for graphMatch1 (below)
ec3pairs = zip (pairSort ec31) (pairSort ec32)
ec3test  =
    [ ( ((1,142321),[o1_1]), ((1,142321),[o1_2]) )
    , ( ((1,142385),[p1_1]), ((1,142385),[p1_2]) )
    , ( ((1,142577),[s1_1]), ((1,142577),[s1_2]) )
    ]

{-  This is a pointless test in this case
testEquivClass33_3 = testeq "EquivClass33_3" ec3test ec3pairs
-}

eq3lmap1 = graphMatch1 False matchable eq3hs1 eq3hs2 eq3lmap ec3pairs
eq3ltst1 = tstLabelMap 2
    [ (o1_1,(1,142321))
    , (p1_1,(1,142385))
    , (s1_1,(1,142577))
    , (l10_2,(1,3766582))
    , (l4_2,(1,1709580))
    , (l1_2,(1,142129))
    , (o3_2,(1,142323))
    , (s3_2,(1,142579))
    , (o2_2,(1,142322))
    , (s2_2,(1,142578))
    , (o1_2,(1,142321))
    , (p1_2,(1,142385))
    , (s1_2,(1,142577))
    ]
-- testEqAssignMap34 = testeq "EqAssignMap34" (Just eq3ltst1) eq3lmap1
-- testEqAssignMap34 = testeq "EqAssignMap34" Nothing eq3lmap1
testEqAssignMap34 = testeq "EqAssignMap34" False (fst eq3lmap1)

{-
eq3rc1      = reclassify eq3hs1 eq3lmap
eq3rctst1   = []
testEqReclassify35_1 = testeqv "EqReclassify35_1" (makeEntries eq3rctst1) eq3rc1
eq3rc2      = reclassify eq3hs2 eq3lmap
eq3rctst2   = []
testEqReclassify35_2 = testeqv "EqReclassify35_2" (makeEntries eq3rctst2) eq3rc2
-}


-- Test suite

testGraphMatchStepSuite = TestList
  [ testEqAssignMap01
  -- , testEqReclassify03_1, testEqReclassify03_2
  , testEqNewLabelMap07
  -- , testEqGraphMatch08
  , testEqAssignMap21
  -- , testEqReclassify23_1, testEqReclassify23_2
  , testEqNewLabelMap27
  -- , testEqGraphMatch28
  , testEqGraphMap31_1, testEqGraphMap31_2
  , testEqAssignMap32
  , testEquivClass33_1, testEquivClass33_2 -- , testEquivClass33_3
  , testEqAssignMap34
  -- , testEqReclassify35_1, testEqReclassify35_2
  ]

------------------------------------------------------------
--  Graph equality tests
------------------------------------------------------------

testGraphEq :: ( Label lb ) => String -> Bool -> GraphMem lb -> GraphMem lb -> Test
testGraphEq lab eq g1 g2 =
    TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )

g1 = GraphMem { arcs = [t01] }

g2 = GraphMem { arcs = [t01,t02,t03,t04,t05,t06] }

g3 = GraphMem { arcs = [t06,t05,t04,t03,t02,t01] }

g4 = GraphMem { arcs = [t01,t02,t03,t04,t05,t06,t10,t11,t12] }

g5 = GraphMem { arcs = [t01,t02,t03,t04,t05,t06,t20,t21,t22] }

g6 = GraphMem { arcs = [t01,t02,t03,t04,t05,t06,t10,t11,t12,t20,t21,t22] }

g7 = GraphMem { arcs = [t01,t02] }

g8 = GraphMem { arcs = [t02,t01] }

glist =
  [ ("g1",g1), ("g2",g2), ("g3",g3), ("g4",g4), ("g5",g5), ("g6",g6) ]

grapheqlist =
  [ ("g2","g3")
  , ("g4","g5")
  ]

testGraphEqSuitePart = TestLabel "testGraphEqSuitePart" $ TestList
  [ testGraphEq "g1-g2" False g1 g2
  , testGraphEq "g2-g1" False g2 g1
  , testGraphEq "g2-g2" True  g2 g2
  , testGraphEq "g2-g3" True  g2 g3
  , testGraphEq "g1-g4" False g1 g4
  , testGraphEq "g2-g4" False g2 g4
  , testGraphEq "g3-g4" False g3 g4
  , testGraphEq "g4-g3" False g4 g3
  , testGraphEq "g4-g4" True  g4 g4
  , testGraphEq "g4-g5" True  g4 g5
  , testGraphEq "g4-g6" False g4 g6
  , testGraphEq "g6-g6" True  g6 g6
  , testGraphEq "g7-g7" True  g7 g7
  , testGraphEq "g7-g8" True  g7 g8
  , testGraphEq "g8-g7" True  g8 g7
  ]

testGraphEqSuite = TestLabel "testGraphEqSuite" $ TestList
  [ testGraphEq (testLab l1 l2) (testEq l1 l2) g1 g2
      | (l1,g1) <- glist , (l2,g2) <- glist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` grapheqlist ||
            (l2,l1) `elem` grapheqlist

-- Selected tests for debugging
geq12 = testGraphEq "g1-g2" False g1 g2
geq21 = testGraphEq "g2-g1" False g2 g1
geq22 = testGraphEq "g2-g2" True  g2 g2
geq23 = testGraphEq "g2-g3" True  g2 g3
geq14 = testGraphEq "g1-g4" False g1 g4
geq24 = testGraphEq "g2-g4" False g2 g4
geq77 = testGraphEq "g7-g7" True  g7 g7
geq78 = testGraphEq "g7-g8" True  g7 g8
geq87 = testGraphEq "g8-g7" True  g8 g7


------------------------------------------------------------
--  More graph equality tests
------------------------------------------------------------
--
--  These tests are based on the 10-node, triply connected
--  graph examples in Jeremy Carroll's paper on matching RDF
--  graphs.

--  Graph pattern 1:
--  pentangle-in-pentangle, corresponding vertices linked upward

v101  = LV "v101"
v102  = LV "v102"
v103  = LV "v103"
v104  = LV "v104"
v105  = LV "v105"
v106  = LV "v106"
v107  = LV "v107"
v108  = LV "v108"
v109  = LV "v109"
v110  = LV "v110"

p101  = LV "p101"
p102  = LV "p102"
p103  = LV "p103"
p104  = LV "p104"
p105  = LV "p105"
p106  = LV "p106"
p107  = LV "p107"
p108  = LV "p108"
p109  = LV "p109"
p110  = LV "p110"
p111  = LV "p111"
p112  = LV "p112"
p113  = LV "p113"
p114  = LV "p114"
p115  = LV "p115"

t10102 = toStatement v101 p101 v102
t10203 = toStatement v102 p102 v103
t10304 = toStatement v103 p103 v104
t10405 = toStatement v104 p104 v105
t10501 = toStatement v105 p105 v101
t10106 = toStatement v101 p106 v106
t10207 = toStatement v102 p107 v107
t10308 = toStatement v103 p108 v108
t10409 = toStatement v104 p109 v109
t10510 = toStatement v105 p110 v110
t10607 = toStatement v106 p111 v107
t10708 = toStatement v107 p112 v108
t10809 = toStatement v108 p113 v109
t10910 = toStatement v109 p114 v110
t11006 = toStatement v110 p115 v106

--  Graph pattern 2:
--  pentangle-in-pentangle, corresponding vertices linked downward

v201  = LV "v201"
v202  = LV "v202"
v203  = LV "v203"
v204  = LV "v204"
v205  = LV "v205"
v206  = LV "v206"
v207  = LV "v207"
v208  = LV "v208"
v209  = LV "v209"
v210  = LV "v210"

p201  = LV "p201"
p202  = LV "p202"
p203  = LV "p203"
p204  = LV "p204"
p205  = LV "p205"
p206  = LV "p206"
p207  = LV "p207"
p208  = LV "p208"
p209  = LV "p209"
p210  = LV "p210"
p211  = LV "p211"
p212  = LV "p212"
p213  = LV "p213"
p214  = LV "p214"
p215  = LV "p215"

t20102 = toStatement v201 p201 v202
t20203 = toStatement v202 p202 v203
t20304 = toStatement v203 p203 v204
t20405 = toStatement v204 p204 v205
t20501 = toStatement v205 p205 v201
t20601 = toStatement v206 p206 v201
t20702 = toStatement v207 p207 v202
t20803 = toStatement v208 p208 v203
t20904 = toStatement v209 p209 v204
t21005 = toStatement v210 p210 v205
t20607 = toStatement v206 p211 v207
t20708 = toStatement v207 p212 v208
t20809 = toStatement v208 p213 v209
t20910 = toStatement v209 p214 v210
t21006 = toStatement v210 p215 v206

--  Graph pattern 3:
--  star-in-pentangle, corresponding vertices linked toward star
--  Although this graph is similarly linked to patterns 1 and 2,
--  it is topologically different as it contains circuits only of
--  length 5, where the others have circuits of length 4 and 5
--  (ignoring direction of arcs)

v301  = LV "v301"
v302  = LV "v302"
v303  = LV "v303"
v304  = LV "v304"
v305  = LV "v305"
v306  = LV "v306"
v307  = LV "v307"
v308  = LV "v308"
v309  = LV "v309"
v310  = LV "v310"

p301  = LV "p301"
p302  = LV "p302"
p303  = LV "p303"
p304  = LV "p304"
p305  = LV "p305"
p306  = LV "p306"
p307  = LV "p307"
p308  = LV "p308"
p309  = LV "p309"
p310  = LV "p310"
p311  = LV "p311"
p312  = LV "p312"
p313  = LV "p313"
p314  = LV "p314"
p315  = LV "p315"

t30102 = toStatement v301 p301 v302
t30203 = toStatement v302 p302 v303
t30304 = toStatement v303 p303 v304
t30405 = toStatement v304 p304 v305
t30501 = toStatement v305 p305 v301
t30106 = toStatement v301 p306 v306
t30207 = toStatement v302 p307 v307
t30308 = toStatement v303 p308 v308
t30409 = toStatement v304 p309 v309
t30510 = toStatement v305 p310 v310
t30608 = toStatement v306 p311 v308
t30709 = toStatement v307 p312 v309
t30810 = toStatement v308 p313 v310
t30906 = toStatement v309 p314 v306
t31007 = toStatement v310 p315 v307

--  Graph pattern 4:
--  pentangle-in-pentangle, corresponding vertices linked upward
--  The vertices 6-10 are linked in reverse order to the
--  corresponding vertices 1-5.

v401  = LV "v401"
v402  = LV "v402"
v403  = LV "v403"
v404  = LV "v404"
v405  = LV "v405"
v406  = LV "v406"
v407  = LV "v407"
v408  = LV "v408"
v409  = LV "v409"
v410  = LV "v410"

p401  = LV "p401"
p402  = LV "p402"
p403  = LV "p403"
p404  = LV "p404"
p405  = LV "p405"
p406  = LV "p406"
p407  = LV "p407"
p408  = LV "p408"
p409  = LV "p409"
p410  = LV "p410"
p411  = LV "p411"
p412  = LV "p412"
p413  = LV "p413"
p414  = LV "p414"
p415  = LV "p415"

t40102 = toStatement v401 p401 v402
t40203 = toStatement v402 p402 v403
t40304 = toStatement v403 p403 v404
t40405 = toStatement v404 p404 v405
t40501 = toStatement v405 p405 v401
t40106 = toStatement v401 p406 v406
t40207 = toStatement v402 p407 v407
t40308 = toStatement v403 p408 v408
t40409 = toStatement v404 p409 v409
t40510 = toStatement v405 p410 v410
t41009 = toStatement v410 p411 v409
t40908 = toStatement v409 p412 v408
t40807 = toStatement v408 p413 v407
t40706 = toStatement v407 p414 v406
t40610 = toStatement v406 p415 v410

--  Graph pattern 5:
--  Same as pattern 1, except same fixed property in all cases.

p5    = LF "p5"

t50102 = toStatement v101 p5 v102
t50203 = toStatement v102 p5 v103
t50304 = toStatement v103 p5 v104
t50405 = toStatement v104 p5 v105
t50501 = toStatement v105 p5 v101
t50106 = toStatement v101 p5 v106
t50207 = toStatement v102 p5 v107
t50308 = toStatement v103 p5 v108
t50409 = toStatement v104 p5 v109
t50510 = toStatement v105 p5 v110
t50607 = toStatement v106 p5 v107
t50708 = toStatement v107 p5 v108
t50809 = toStatement v108 p5 v109
t50910 = toStatement v109 p5 v110
t51006 = toStatement v110 p5 v106

--  Graph pattern 6:
--  Same as pattern 5, with different variables

t60102 = toStatement v201 p5 v202
t60203 = toStatement v202 p5 v203
t60304 = toStatement v203 p5 v204
t60405 = toStatement v204 p5 v205
t60501 = toStatement v205 p5 v201
t60106 = toStatement v201 p5 v206
t60207 = toStatement v202 p5 v207
t60308 = toStatement v203 p5 v208
t60409 = toStatement v204 p5 v209
t60510 = toStatement v205 p5 v210
t60607 = toStatement v206 p5 v207
t60708 = toStatement v207 p5 v208
t60809 = toStatement v208 p5 v209
t60910 = toStatement v209 p5 v210
t61006 = toStatement v210 p5 v206

--

arcsToGraph as = GraphMem { arcs = as }

-- Very simple case

g100 = arcsToGraph
       [ t10102, t10203, t10304, t10405, t10501,
         t10607, t10708, t10809, t10910, t11006
       ]

g200 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20607, t20708, t20809, t20910, t21006
       ]

-- 10/3 node graph comparisons

g101 = arcsToGraph
       [ t10102, t10203, t10304, t10405, t10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g201 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803, t20904, t21005,
         t20607, t20708, t20809, t20910, t21006 ]

g301 = arcsToGraph
       [ t30102, t30203, t30304, t30405, t30501,
         t30106, t30207, t30308, t30409, t30510,
         t30608, t30709, t30810, t30906, t31007 ]

g401 = arcsToGraph
       [ t40102, t40203, t40304, t40405, t40501,
         t40106, t40207, t40308, t40409, t40510,
         t40610, t40706, t40807, t40908, t41009 ]

g501 = arcsToGraph
       [ t50102, t50203, t50304, t50405, t50501,
         t50106, t50207, t50308, t50409, t50510,
         t50607, t50708, t50809, t50910, t51006 ]

g601 = arcsToGraph
       [ t60102, t60203, t60304, t60405, t60501,
         t60106, t60207, t60308, t60409, t60510,
         t60607, t60708, t60809, t60910, t61006 ]

-- Remove one arc from each

g102 = arcsToGraph
       [ t10102, t10203, t10304, t10405,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g202 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803, t20904, t21005,
                 t20708, t20809, t20910, t21006 ]

g302 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803, t20904,
         t20607, t20708, t20809, t20910, t21006 ]

-- Remove two adjacent arcs from each

g103 = arcsToGraph
       [ t10102, t10203, t10304,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g203 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803, t20904, t21005,
         t20607, t20708,                 t21006 ]

g303 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803, t20904,
         t20607, t20708, t20809,         t21006 ]

-- Remove two adjacent arcs from one, non-adjacent from another

g104 = arcsToGraph
       [ t10102, t10203, t10304,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g204 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20601, t20702, t20803,
         t20607, t20708, t20809, t20910, t21006 ]

-- Compare two rings of 5 with one ring of 10
-- (each node double-connected, but different overall topology)

t10901 = toStatement v109 p109 v101

g105 = arcsToGraph
       [ t10102, t10203, t10304, t10405,
                                 t10901, t10510,
         t10607, t10708, t10809,         t11006 ]

g205 = arcsToGraph
       [ t20102, t20203, t20304, t20405, t20501,
         t20607, t20708, t20809, t20910, t21006 ]

-- Reverse one arc from test 01
-- (also, rearrange arcs to catch ordering artefacts)

t20201 = toStatement v202 p201 v201

g106 = arcsToGraph
       [ t10102, t10203, t10304, t10405, t10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g206 = arcsToGraph
       [ t20607, t20708, t20809, t20910, t21006,
         t20601, t20702, t20803, t20904, t21005,
         t20102, t20203, t20304, t20405, t20501 ]

g306 = arcsToGraph
       [ t20607, t20708, t20809, t20910, t21006,
         t20601, t20702, t20803, t20904, t21005,
         t20201, t20203, t20304, t20405, t20501 ]

-- Similar tests to 02,03,04,
-- but add identified property rather than removing arcs

f01  = LF "f01"
f02  = LF "f02"

-- Fix one arc from each

f10102 = toStatement v101 f01 v102
f10501 = toStatement v105 f01 v101
f21006 = toStatement v210 f01 v206
f20510 = toStatement v205 f01 v210

g107 = arcsToGraph
       [ f10102, t10203, t10304, t10405, t10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g207 = arcsToGraph
       [ t10102, t10203, t10304, t10405, f10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g307 = arcsToGraph
       [ t20607, t20708, t20809, t20910, f21006,
         t20601, t20702, t20803, t20904, t21005,
         t20102, t20203, t20304, t20405, t20501 ]

g407 = arcsToGraph
       [ t20607, t20708, t20809, t20910, t21006,
         t20601, t20702, t20803, t20904, t21005,
         t20102, t20203, t20304, t20405, t20501 ]

-- Fix two adjacent arcs from each

f10203 = toStatement v102 f01 v103
f10405 = toStatement v104 f01 v105
f20910 = toStatement v209 f01 v210
f20601 = toStatement v206 f01 v201

g108 = arcsToGraph
       [ f10102, f10203, t10304, t10405, t10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g208 = arcsToGraph
       [ t10102, t10203, t10304, f10405, f10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g308 = arcsToGraph
       [ t20607, t20708, t20809, f20910, f21006,
         t20601, t20702, t20803, t20904, t21005,
         t20102, t20203, t20304, t20405, t20501 ]

g408 = arcsToGraph
       [ t20607, t20708, t20809, t20910, f21006,
         f20601, t20702, t20803, t20904, t21005,
         t20102, t20203, t20304, t20405, t20501 ]

-- Fix two adjacent arcs with different properties

g10203 = toStatement v102 f02 v103
g10102 = toStatement v101 f02 v102
g10405 = toStatement v104 f02 v105

g109 = arcsToGraph
       [ f10102, g10203, t10304, t10405, t10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g209 = arcsToGraph
       [ g10102, t10203, t10304, t10405, f10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]

g309 = arcsToGraph
       [ t10102, t10203, t10304, g10405, f10501,
         t10106, t10207, t10308, t10409, t10510,
         t10607, t10708, t10809, t10910, t11006 ]


mgeq00 = testGraphEq "g100-g200" True  g100 g200

mgeq0112 = testGraphEq "g101-g201" True  g101 g201
mgeq0113 = testGraphEq "g101-g301" False g101 g301
mgeq0114 = testGraphEq "g101-g401" False g101 g401
mgeq0115 = testGraphEq "g101-g501" False g101 g501
mgeq0116 = testGraphEq "g101-g601" False g101 g601
mgeq0156 = testGraphEq "g501-g601" True  g501 g601

mgeq0212 = testGraphEq "g102-g202" True  g102 g202
mgeq0213 = testGraphEq "g102-g302" False g102 g302

mgeq0312 = testGraphEq "g103-g203" True  g103 g203
mgeq0313 = testGraphEq "g103-g303" False g103 g303

mgeq04 = testGraphEq "g104-g204" False g104 g204
mgeq05 = testGraphEq "g105-g205" False g105 g205

mgeq0612 = testGraphEq "g106-g206" True  g106 g206
mgeq0613 = testGraphEq "g106-g306" False g106 g306

mgeq0712 = testGraphEq "g107-g207" True  g107 g207
mgeq0713 = testGraphEq "g107-g307" True  g107 g307
mgeq0714 = testGraphEq "g107-g407" False g107 g407

mgeq0812 = testGraphEq "g108-g208" True  g108 g208
mgeq0813 = testGraphEq "g108-g308" True  g108 g308
mgeq0814 = testGraphEq "g108-g408" False g108 g408

mgeq0912 = testGraphEq "g109-g209" True  g109 g209
mgeq0913 = testGraphEq "g109-g309" False g109 g309

testGraphEqSuiteMore = TestList
  [ mgeq00
  , mgeq0112, mgeq0113, mgeq0114, mgeq0115, mgeq0116, mgeq0156
  , mgeq0212, mgeq0213
  , mgeq0312, mgeq0313
  , mgeq04
  , mgeq05
  , mgeq0612, mgeq0613
  , mgeq0712, mgeq0713, mgeq0714
  , mgeq0812, mgeq0813, mgeq0814
  , mgeq0912, mgeq0913
  ]

------------------------------------------------------------
-- All tests
------------------------------------------------------------

allTests = TestList
  [ testSelectSuite
  , testMapsetSuite
  , testSubsetSuite
  , testHashSuite
  , testLabSuite
  , testGraphSuite
  , testLabelEqSuite
  , testLabelOrdSuite
  , testStmtEqSuite
  , testLabelMapSuite
  , testGraphMatchSupportSuite
  , testGraphMatchStepSuite
  , testGraphEqSuitePart
  , testGraphEqSuite
  , testGraphEqSuiteMore
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

geq    = testGraphEqSuite
geq1   = testGraphEqSuiteMore
ttmore = tt testGraphEqSuiteMore    -- this test may take a long time
tfmore = tf testGraphEqSuiteMore
ttstep = tt testGraphMatchStepSuite
tfstep = tf testGraphMatchStepSuite

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
-- $Source: /file/cvsdev/HaskellRDF/GraphTest.hs,v $
-- $Author: graham $
-- $Revision: 1.24 $
-- $Log: GraphTest.hs,v $
-- Revision 1.24  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.23  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.22  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.21  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.20  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.19  2003/05/29 01:50:56  graham
-- More performance tuning, courtesy of GHC profiler.
-- All modules showing reasonable performance now.
--
-- Revision 1.18  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.17  2003/05/23 16:29:20  graham
-- Partial code cleanup:
-- - Arc is an alebraic type
-- - Arc is an instance of Functor
-- - add gmap function to Graph interface
-- - remove some duplicate functions from GraphMatch
-- This in preparation for adding graph merge facility with
-- blank node renaming.
--
-- Revision 1.16  2003/05/20 23:35:28  graham
-- Modified code to compile with GHC hierarchical libraries
--
-- Revision 1.15  2003/05/14 11:13:15  graham
-- Fixed bug in graph matching.
-- (A graph-equivalence check is needed to weed out false matches
-- caused by the "guessing" stage.)
--
-- Revision 1.14  2003/05/14 02:01:59  graham
-- GraphMatch recoded and almost working, but
-- there are a couple of
-- obscure bugs that are proving rather stubborn to squash.
--
-- Revision 1.13  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.12  2003/05/07 19:26:32  graham
-- Sync
--
-- Revision 1.11  2003/05/01 23:15:44  graham
-- GraphTest passes all tests using refactored LookupMap
-- Extensive changes to GraphMatch were required.
--
-- Revision 1.10  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.9  2003/04/11 18:12:10  graham
-- Renamed GraphHelpers to ListHelpers
-- LookupMapTest, GraphTest, RDFGraphTest all run OK
--
-- Revision 1.8  2003/04/11 18:04:49  graham
-- Rename GraphLookupMap to LookupMap:
-- GraphTest runs OK.
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
