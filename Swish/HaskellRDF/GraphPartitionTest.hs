--------------------------------------------------------------------------------
--  $Id: GraphPartitionTest.hs,v 1.2 2004/02/10 20:24:48 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  GraphPartitionTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains test cases for graph partitioning logic.
--
--------------------------------------------------------------------------------

--module Swish.HaskellRDF.GraphPartitionTest where
-- module Main(main) where -- WNH


import Swish.HaskellRDF.GraphPartition
    ( PartitionedGraph(..), getArcs
    , GraphPartition(..), node, toArcs
    , partitionGraph, comparePartitions
    )

import Swish.HaskellRDF.GraphClass
    ( Label(..)
    , Arc(..), arcSubj, arcPred, arcObj, arc, arcToTriple, arcFromTriple
    -- , hasLabel, arcLabels
    )

import Swish.HaskellRDF.GraphMem
    -- ( GraphMem(..)
    -- , setArcs, getArcs, add, delete, extract, labels
    ( LabelMem(..)
    , labelIsVar, labelHash
    )

import Swish.HaskellUtils.TestHelpers
    ( test, testEq, 
    --     WNH FIX testNe, 
    testLe, testGe, testElem
    , testJust, testNothing
    , testEqv, 
    --   WNH FIXtestNotEqv, 
    testEqv2, testHasEqv, testMaybeEqv
    )

import Swish.HaskellUtils.ListHelpers
    ( equiv )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , Assertion
    , assertBool, assertEqual, assertString, assertFailure
    , runTestTT, runTestText, putTextToHandle
    )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn
    )

import Control.Monad
    ( unless )

import Data.List
    ( sort, union, intersect )

import Data.Maybe
    ( isJust, fromJust, fromMaybe )

------------------------------------------------------------
--  Basic GraphPartition tests
------------------------------------------------------------

gp1 = PartitionedGraph [ p11 ]
gp2 = PartitionedGraph [ p11, p12 ]
gp3 = PartitionedGraph [ p11, p13 ]
gp4 = PartitionedGraph [ p11, p14 ]
gp5 = PartitionedGraph [ p11, p12, p15 ]

p11 = PartSub (LF "s1") [ (LF "p11",PartObj (LF "o11")) ]
p12 = PartSub (LF "s2") [ (LF "p21",PartObj (LF "o21"))
                        , (LF "p22",PartObj (LF "o22"))
                        ]
p13 = PartSub (LF "s3") [ (LF "p31",PartObj (LF "o31"))
                        , (LF "p32",p12)
                        , (LF "p33",PartObj (LF "s3"))
                        ]
p14 = PartSub (LF "s3") [ (LF "p31",PartObj (LF "o31"))
                        , (LF "p33",PartObj (LF "s3"))
                        , (LF "p32",p12)
                        ]
p15 = PartSub (LF "s3") [ (LF "p31",PartObj (LF "o31"))
                        , (LF "p32",PartObj (LF "s2"))
                        , (LF "p33",PartObj (LF "s3"))
                        ]

ga1 =
    [ Arc (LF "s1") (LF "p11") (LF "o11")
    ]

ga2 =
    [ Arc (LF "s1") (LF "p11") (LF "o11")
    , Arc (LF "s2") (LF "p21") (LF "o21")
    , Arc (LF "s2") (LF "p22") (LF "o22")
    ]

ga3 =
    [ Arc (LF "s1") (LF "p11") (LF "o11")
    , Arc (LF "s3") (LF "p31") (LF "o31")
    , Arc (LF "s3") (LF "p32") (LF "s2")
    , Arc (LF "s2") (LF "p21") (LF "o21")
    , Arc (LF "s2") (LF "p22") (LF "o22")
    , Arc (LF "s3") (LF "p33") (LF "s3")
    ]
ga4 =
    [ Arc (LF "s1") (LF "p11") (LF "o11")
    , Arc (LF "s3") (LF "p31") (LF "o31")
    , Arc (LF "s3") (LF "p33") (LF "s3")
    , Arc (LF "s3") (LF "p32") (LF "s2")
    , Arc (LF "s2") (LF "p21") (LF "o21")
    , Arc (LF "s2") (LF "p22") (LF "o22")
    ]
ga5 =
    [ Arc (LF "s1") (LF "p11") (LF "o11")
    , Arc (LF "s2") (LF "p21") (LF "o21")
    , Arc (LF "s2") (LF "p22") (LF "o22")
    , Arc (LF "s3") (LF "p31") (LF "o31")
    , Arc (LF "s3") (LF "p32") (LF "s2")
    , Arc (LF "s3") (LF "p33") (LF "s3")
    ]

testBasic01 = testEq "testBasic01" gp1 gp1
testBasic02 = testEq "testBasic02" gp2 gp2
testBasic03 = testEq "testBasic03" gp3 gp3
testBasic04 = testEq "testBasic04" gp4 gp4
testBasic05 = testEq "testBasic05" gp5 gp5
{-     WNH FIX 
testBasic06 = testNe "testBasic06" gp2 gp3
testBasic07 = testNe "testBasic07" gp3 gp4
-}

testBasic11 = testEq "testBasic11"
        "PartitionedGraph [(!s1 !p11 !o11)]"
        (show gp1)
testBasic12 = testEq "testBasic12"
        ( "PartitionedGraph "++
          "[(!s1 !p11 !o11)"++
          ",(!s2 !p21 !o21 ; !p22 !o22)"++
          "]"
        )
        (show gp2)
testBasic13 = testEq "testBasic13"
        ( "PartitionedGraph "++
          "[(!s1 !p11 !o11)"++
          ",(!s3 !p31 !o31 ; !p32 (!s2 !p21 !o21 ; !p22 !o22) ; !p33 !s3)"++
          "]"
        )
        (show gp3)
testBasic14 = testEq "testBasic14"
        ( "PartitionedGraph "++
          "[(!s1 !p11 !o11)"++
          ",(!s3 !p31 !o31 ; !p33 !s3 ; !p32 (!s2 !p21 !o21 ; !p22 !o22))"++
          "]"
        )
        (show gp4)
testBasic15 = testEq "testBasic15"
        ( "PartitionedGraph "++
          "[(!s1 !p11 !o11)"++
          ",(!s2 !p21 !o21 ; !p22 !o22)"++
          ",(!s3 !p31 !o31 ; !p32 !s2 ; !p33 !s3)"++
          "]"
        )
        (show gp5)

testBasic21 = testEq "testBasic21" (LF "s1") (node p11)
testBasic22 = testEq "testBasic22" (LF "s2") (node p12)
testBasic23 = testEq "testBasic23" (LF "s3") (node p13)
testBasic24 = testEq "testBasic24" (LF "s3") (node p14)
testBasic25 = testEq "testBasic25" (LF "s3") (node p15)

testBasic31 = testEq "testBasic31" ga1 (getArcs gp1)
testBasic32 = testEq "testBasic32" ga2 (getArcs gp2)
testBasic33 = testEq "testBasic33" ga3 (getArcs gp3)
testBasic34 = testEq "testBasic34" ga4 (getArcs gp4)
testBasic35 = testEq "testBasic35" ga5 (getArcs gp5)
--     WNH FIX testBasic36 = testNotEqv "testBasic36" (getArcs gp2) (getArcs gp3)
testBasic37 = testEqv    "testBasic37" (getArcs gp3) (getArcs gp4)
testBasic38 = testEqv    "testBasic38" (getArcs gp3) (getArcs gp5)

testBasicSuite = TestList
    [ testBasic01
    , testBasic02
    , testBasic03
    , testBasic04
    , testBasic05
    --   WNH FIX, testBasic06
    --   WNH FIX, testBasic07
    , testBasic11
    , testBasic12
    , testBasic13
    , testBasic14
    , testBasic15
    , testBasic21
    , testBasic22
    , testBasic23
    , testBasic24
    , testBasic25
    , testBasic31
    , testBasic32
    , testBasic33
    , testBasic34
    , testBasic35
    -- WNH FIX, testBasic36
    , testBasic37
    , testBasic38
    ]

------------------------------------------------------------
--  Creating GraphPartition tests
------------------------------------------------------------

pa1 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    ]

pa2 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    , Arc (LF "s2") (LF "p1") (LF "o21")
    , Arc (LF "s2") (LF "p2") (LF "o22")
    ]

pa3 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    , Arc (LF "s2") (LF "p1") (LF "o21")
    , Arc (LF "s2") (LF "p2") (LF "o22")
    , Arc (LV "b3") (LF "p") (LF "o31")
    , Arc (LV "b3") (LF "p") (LF "s2")
    , Arc (LV "b3") (LF "p") (LV "b3")
    ]

pa4 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    , Arc (LF "s2") (LF "p1") (LF "o21")
    , Arc (LF "s2") (LF "p2") (LF "o22")
    , Arc (LV "b3") (LF "p") (LF "o31")
    , Arc (LV "b3") (LF "p") (LF "s2")
    , Arc (LV "b3") (LF "p") (LV "b3")
    , Arc (LV "b3") (LF "p") (LV "b4")
    , Arc (LV "b4") (LF "p") (LF "s2")
    , Arc (LV "b4") (LF "p") (LV "b3")
    ]

pa5 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    , Arc (LF "s2") (LF "p1") (LF "o21")
    , Arc (LF "s2") (LF "p2") (LF "o22")
    , Arc (LV "b3") (LF "p") (LF "o31")
    , Arc (LV "b3") (LF "p") (LF "s2")
    , Arc (LV "b3") (LF "p") (LV "b3")
    , Arc (LV "b3") (LF "p") (LV "b4")
    , Arc (LV "b4") (LF "p") (LF "s2")
    , Arc (LV "b4") (LF "p") (LV "b3")
    , Arc (LV "b5a") (LF "p") (LV "b5b")
    , Arc (LV "b5b") (LF "p") (LV "b5c")
    , Arc (LV "b5c") (LF "p") (LV "b5a")
    ]

pa6 =
    [ Arc (LF "s1") (LF "p") (LF "o11")
    , Arc (LF "s2") (LF "p1") (LF "o21")
    , Arc (LF "s2") (LF "p2") (LF "o22")
    , Arc (LV "b3") (LF "p") (LF "o31")
    , Arc (LV "b3") (LF "p") (LF "s2")
    , Arc (LV "b3") (LF "p") (LV "b3")
    , Arc (LV "b3") (LF "p") (LV "b4")
    , Arc (LV "b4") (LF "p") (LF "s2")
    , Arc (LV "b4") (LF "p") (LV "b3")
    , Arc (LV "b4") (LF "p") (LV "b5b")
    , Arc (LV "b5a") (LF "p") (LV "b5b")
    , Arc (LV "b5b") (LF "p") (LV "b5c")
    , Arc (LV "b5c") (LF "p") (LV "b5a")
    ]

pp1  = PartitionedGraph [ ps1 ]
pp2f = PartitionedGraph [ ps1,  ps2f ]
pp2r = PartitionedGraph [ ps2r, ps1 ]
pp3f = PartitionedGraph [ ps1,  ps2f, pb3f ]
pp3r = PartitionedGraph [ ps2r, ps1,  pb3r ]
pp4f = PartitionedGraph [ ps1,  ps2f, pb3af ]
pp4r = PartitionedGraph [ ps2r, ps1,  pb3ar ]
pp5f = PartitionedGraph [ ps1,  ps2f, pb3af, pb5a1 ]
pp5r = PartitionedGraph [ ps2r, ps1,  pb3ar, pb5c3 ]
pp6f = PartitionedGraph [ ps1,  ps2f, pb3bf, pb5b2 ]
pp6r = PartitionedGraph [ ps2r, ps1,  pb5b2, pb3br ]

ps1  = PartSub (LF "s1") [ (LF "p",PartObj (LF "o11")) ]
ps2f = PartSub (LF "s2") [ (LF "p1",PartObj (LF "o21"))
                         , (LF "p2",PartObj (LF "o22"))
                         ]
ps2r = PartSub (LF "s2") [ (LF "p2",PartObj (LF "o22"))
                         , (LF "p1",PartObj (LF "o21"))
                         ]
pb3f = PartSub (LV "b3") [ (LF "p",PartObj (LF "o31"))
                         , (LF "p",PartObj (LF "s2"))
                         , (LF "p",PartObj (LV "b3"))
                         ]
pb3r = PartSub (LV "b3") [ (LF "p",PartObj (LV "b3"))
                         , (LF "p",PartObj (LF "s2"))
                         , (LF "p",PartObj (LF "o31"))
                         ]

pb3af = PartSub (LV "b3") [ (LF "p",PartObj (LF "o31"))
                          , (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",pb4af)
                          ]
pb3ar = PartSub (LV "b3") [ (LF "p",pb4ar)
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LF "o31"))
                          ]
pb4af = PartSub (LV "b4") [ (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LV "b3"))
                          ]
pb4ar = PartSub (LV "b4") [ (LF "p",PartObj (LV "b3"))
                          , (LF "p",PartObj (LF "s2"))
                          ]
pb5a1 = PartSub (LV "b5a") [ (LF "p",pb5b1) ]
pb5b1 = PartSub (LV "b5b") [ (LF "p",pb5c1) ]
pb5c1 = PartSub (LV "b5c") [ (LF "p",PartObj (LV "b5a")) ]

pb3bf = PartSub (LV "b3") [ (LF "p",PartObj (LF "o31"))
                          , (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",pb4bf)
                          ]
pb3br = PartSub (LV "b3") [ (LF "p",pb4br)
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LF "o31"))
                          ]
pb4bf = PartSub (LV "b4") [ (LF "p",PartObj (LF "s2"))
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",PartObj (LV "b5b"))
                          ]
pb4br = PartSub (LV "b4") [ (LF "p",PartObj (LV "b5b"))
                          , (LF "p",PartObj (LV "b3"))
                          , (LF "p",PartObj (LF "s2"))
                          ]
pb5a2 = PartSub (LV "b5a") [ (LF "p",PartObj (LV "b5b")) ]
pb5b2 = PartSub (LV "b5b") [ (LF "p",pb5c2) ]
pb5c2 = PartSub (LV "b5c") [ (LF "p",pb5a2) ]

pb5a3 = PartSub (LV "b5a") [ (LF "p",pb5b3) ]
pb5b3 = PartSub (LV "b5b") [ (LF "p",PartObj (LV "b5c")) ]
pb5c3 = PartSub (LV "b5c") [ (LF "p",pb5a3) ]

testPartition11 = testEq "testPartition11" pp1  (partitionGraph pa1)
testPartition12 = testEq "testPartition12" pp2f (partitionGraph pa2)
testPartition13 = testEq "testPartition13" pp3f (partitionGraph pa3)
testPartition14 = testEq "testPartition15" pp4f (partitionGraph pa4)
testPartition15 = testEq "testPartition14" pp5f (partitionGraph pa5)
testPartition16 = testEq "testPartition16" pp6f (partitionGraph pa6)

testPartition21 = testEq "testPartition21" pp1  (partitionGraph $ reverse pa1)
testPartition22 = testEq "testPartition22" pp2r (partitionGraph $ reverse pa2)
testPartition23 = testEq "testPartition23" pp3r (partitionGraph $ reverse pa3)
testPartition24 = testEq "testPartition24" pp4r (partitionGraph $ reverse pa4)
testPartition25 = testEq "testPartition25" pp5r (partitionGraph $ reverse pa5)
testPartition26 = testEq "testPartition26" pp6r (partitionGraph $ reverse pa6)

testPartition31 = testEqv "testPartition31" pa1  (getArcs pp1)
testPartition32 = testEqv "testPartition32" pa2  (getArcs pp2f)
testPartition33 = testEqv "testPartition33" pa3  (getArcs pp3f)
testPartition34 = testEqv "testPartition35" pa4  (getArcs pp4f)
testPartition35 = testEqv "testPartition34" pa5  (getArcs pp5f)
testPartition36 = testEqv "testPartition36" pa6  (getArcs pp6f)

testPartition41 = testEqv "testPartition41" pa1  (getArcs pp1 )
testPartition42 = testEqv "testPartition42" pa2  (getArcs pp2r)
testPartition43 = testEqv "testPartition43" pa3  (getArcs pp3r)
testPartition44 = testEqv "testPartition44" pa4  (getArcs pp4r)
testPartition45 = testEqv "testPartition45" pa5  (getArcs pp5r)
testPartition46 = testEqv "testPartition46" pa6  (getArcs pp6r)

testPartition51 = testEqv "testPartition51" []   (comparePartitions pp1  pp1)
testPartition52 = testEqv "testPartition52" []   (comparePartitions pp2f pp2r)
testPartition53 = testEqv "testPartition53" []   (comparePartitions pp3f pp3r)
testPartition54 = testEqv "testPartition54" []   (comparePartitions pp4f pp4r)
testPartition55 = testEqv "testPartition55" []   (comparePartitions pp5f pp5r)
testPartition56 = testEqv "testPartition56" []   (comparePartitions pp6f pp6r)
testPartition57 = testEqv "testPartition57"
        [(Nothing,Just $ PartSub (LV "b3") [(LF "p",pb4af)])]
        (comparePartitions pp3f pp4f)
testPartition58 = testEqv "testPartition58"
        [(Nothing,Just pb5a1)]
        (comparePartitions pp4f pp5f)
testPartition59 = testEqv "testPartition59"
        [(Nothing,Just $ PartSub (LV "b4") [(LF "p",PartObj (LV "b5b"))])]
        (comparePartitions pp5f pp6f)

testPartitionSuite = TestList
    [ testPartition11
    , testPartition12
    , testPartition13
    , testPartition14
    , testPartition15
    , testPartition16
    , testPartition21
    , testPartition22
    , testPartition23
    , testPartition24
    , testPartition25
    , testPartition26
    , testPartition31
    , testPartition32
    , testPartition33
    , testPartition34
    , testPartition35
    , testPartition36
    , testPartition41
    , testPartition42
    , testPartition43
    , testPartition44
    , testPartition45
    , testPartition46
    , testPartition51
    , testPartition52
    , testPartition53
    , testPartition54
    , testPartition55
    , testPartition56
    , testPartition57
    , testPartition58
    , testPartition59
    ]


------------------------------------------------------------
--  GraphPartition compare test with partial matching
------------------------------------------------------------

pgc1a = PartitionedGraph [ c11, c12a ]
pgc1b = PartitionedGraph [ c11, c12b ]

c11  = PartSub (LF "s1") [ (LF "p11",PartObj (LF "o11")) ]
c12a = PartSub (LF "s2") [ (LF "p21",c13a)
                         , (LF "p22",PartObj (LF "o22"))
                         ]
c12b = PartSub (LF "s2") [ (LF "p22",PartObj (LF "o22"))
                         , (LF "p21",c13b)
                         ]
c13a = PartSub (LV "b3") [ (LF "p31",PartObj (LF "o31"))
                         , (LF "p33",PartObj (LF "o33a"))
                         ]
c13b = PartSub (LV "b3") [ (LF "p31",PartObj (LF "o31"))
                         , (LF "p33",PartObj (LF "o33b"))
                         ]
testCompare01 = testEqv "testCompare01"
        [(Just (PartObj (LF "o33a")),Just (PartObj (LF "o33b")))]
        (comparePartitions pgc1a pgc1b)


testCompareSuite = TestList
    [ testCompare01
    ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
    [ testBasicSuite
    , testPartitionSuite
    , testCompareSuite
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
-- $Source: /file/cvsdev/HaskellRDF/GraphPartitionTest.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: GraphPartitionTest.hs,v $
-- Revision 1.2  2004/02/10 20:24:48  graham
-- Graph difference code now works.
--
-- Revision 1.1  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
