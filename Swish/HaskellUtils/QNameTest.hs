--------------------------------------------------------------------------------
--  $Id: QNameTest.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  QNameTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines test cases for QName data
--
--------------------------------------------------------------------------------

-- WNH module Swish.HaskellUtils.QNameTest where

-- module Main where

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn
    )

import Data.Maybe
    ( fromJust )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    , newQName, qnameFromPair, qnameFromURI
    , getNamespace, getLocalName, getQNameURI
    , splitURI
    )




------------------------------------------------------------
--  Define some common values
------------------------------------------------------------

base1  = "http://id.ninebynine.org/wip/2003/test/graph1/node#"
base2  = "http://id.ninebynine.org/wip/2003/test/graph2/node/"
base3  = "http://id.ninebynine.org/wip/2003/test/graph3/node"
base4  = "http://id.ninebynine.org/wip/2003/test/graph3/nodebase"
base5  = "http://id.ninebynine.org/wip/2003/test/graph5/"

qb1s1  = QName base1 "s1"
qb2s2  = QName base2 "s2"
qb3s3  = QName base3 "s3"
qb3    = QName base3 ""
qb3bm  = QName base3 "basemore"
qb4m   = QName base4 "more"

qb5    = QName base5 ""
qb5s5  = QName base5 "s5"

qb1st1 = QName base1 "st1"
qb2st2 = QName base2 "st2"
qb3st3 = QName base3 "st3"


------------------------------------------------------------
--  QName equality tests
------------------------------------------------------------

testQNameEq :: String -> Bool -> QName -> QName -> Test
testQNameEq lab eq n1 n2 =
    TestCase ( assertEqual ("testQNameEq:"++lab) eq (n1==n2) )

qnlist =
  [ ("qb1s1", qb1s1)
  , ("qb2s2", qb2s2)
  , ("qb3s3", qb3s3)
  , ("qb3",   qb3)
  , ("qb3bm", qb3bm)
  , ("qb4m",  qb4m)
  , ("qb5",   qb5)
  , ("qb5s5", qb5s5)
  , ("qb1st1",qb1st1)
  , ("qb2st2",qb2st2)
  , ("qb3st3",qb3st3)
  ]

qneqlist =
  [ ("qb3bm","qb4m")
  ]

testQNameEqSuite = TestList
  [ testQNameEq (testLab l1 l2) (testEq  l1 l2) n1 n2
      | (l1,n1) <- qnlist , (l2,n2) <- qnlist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` qneqlist ||
            (l2,l1) `elem` qneqlist

------------------------------------------------------------
--  Alternative constructors
------------------------------------------------------------

nq1 = newQName base1 "s1"
nq2 = newQName base1 "s2"

testnq01 = testQNameEq "testnq01" True  nq1 qb1s1
testnq02 = testQNameEq "testnq02" False nq2 qb1s1

qp1 = qnameFromPair (base1,"s1")
qp2 = qnameFromPair (base1,"s2")

testqp01 = testQNameEq "testqp01" True  qp1 qb1s1
testqp02 = testQNameEq "testqp02" False qp2 qb1s1

qu1 = qnameFromURI "http://id.ninebynine.org/wip/2003/test/graph1/node#s1"
qu2 = qnameFromURI "http://id.ninebynine.org/wip/2003/test/graph2/node/s2"
qu3 = qnameFromURI "http://id.ninebynine.org/wip/2003/test/graph3/node"
qu4 = qnameFromURI "http://id.ninebynine.org/wip/2003/test/graph5/"
qu5 = qnameFromURI "http://id.ninebynine.org/wip/2003/test/graph5/s5"

testqu01 = testQNameEq "testqu01" True qb1s1 qu1
testqu02 = testQNameEq "testqu02" True qb2s2 qu2
testqu03 = testQNameEq "testqu03" True qb3   qu3
testqu04 = testQNameEq "testqu04" True qb5   qu4
testqu05 = testQNameEq "testqu05" True qb5s5 qu5

testMakeQNameSuite = TestList
  [ testnq01, testnq02
  , testqp01, testqp02
  , testqu01, testqu02, testqu03, testqu04, testqu05
  ]


------------------------------------------------------------
--  Extract components
------------------------------------------------------------

testStringEq :: String -> String -> String -> Test
testStringEq lab s1 s2 =
    TestCase ( assertEqual ("testStringEq:"++lab) s1 s2 )

testGetNamespace01 = testStringEq "testGetNamespace01"
    "http://id.ninebynine.org/wip/2003/test/graph1/node#"
    (getNamespace qb1s1)

testGetNamespace02 = testStringEq "testGetNamespace02"
    "http://id.ninebynine.org/wip/2003/test/graph2/node/"
    (getNamespace qb2s2)

testGetNamespace03 = testStringEq "testGetNamespace03"
    "http://id.ninebynine.org/wip/2003/test/graph3/node"
    (getNamespace qb3s3)

testGetNamespace04 = testStringEq "testGetNamespace04"
    "http://id.ninebynine.org/wip/2003/test/graph3/node"
    (getNamespace qb3)

testGetLocalName01 = testStringEq "testGetLocalName01"
    "s1"
    (getLocalName qb1s1)

testGetLocalName02 = testStringEq "testGetLocalName02"
    "s2"
    (getLocalName qb2s2)

testGetLocalName03 = testStringEq "testGetLocalName03"
    "s3"
    (getLocalName qb3s3)

testGetLocalName04 = testStringEq "testGetLocalName04"
    ""
    (getLocalName qb3)

testGetQNameURI01 = testStringEq "testGetQNameURI01"
    "http://id.ninebynine.org/wip/2003/test/graph1/node#s1"
    (getQNameURI qb1s1)

testGetQNameURI02 = testStringEq "testGetQNameURI02"
    "http://id.ninebynine.org/wip/2003/test/graph2/node/s2"
    (getQNameURI qb2s2)

testGetQNameURI03 = testStringEq "testGetQNameURI03"
    "http://id.ninebynine.org/wip/2003/test/graph3/nodes3"
    (getQNameURI qb3s3)

testGetQNameURI04 = testStringEq "testGetQNameURI04"
    "http://id.ninebynine.org/wip/2003/test/graph3/node"
    (getQNameURI qb3)


testPartQNameSuite = TestList
  [ testGetNamespace01, testGetNamespace02, testGetNamespace03
  , testGetNamespace04
  , testGetLocalName01, testGetLocalName02, testGetLocalName03
  , testGetLocalName04
  , testGetQNameURI01,  testGetQNameURI02,  testGetQNameURI03
  , testGetQNameURI04
  ]

------------------------------------------------------------
--  Maybe Qname comparison
------------------------------------------------------------

testMaybeQNameEq :: String -> Bool -> (Maybe QName) -> (Maybe QName) -> Test
testMaybeQNameEq lab eq n1 n2 =
    TestCase ( assertEqual ("testMaybeQNameEq:"++lab) eq (n1==n2) )

testMaybeQNameEq01 = testMaybeQNameEq "testMaybeQNameEq01" True
    (Just qb1s1) (Just qb1s1)
testMaybeQNameEq02 = testMaybeQNameEq "testMaybeQNameEq02" False
    (Just qb1s1) (Just qb2s2)
testMaybeQNameEq03 = testMaybeQNameEq "testMaybeQNameEq03" False
    (Just qb1s1) Nothing
testMaybeQNameEq04 = testMaybeQNameEq "testMaybeQNameEq04" False
    Nothing (Just qb1s1)
testMaybeQNameEq05 = testMaybeQNameEq "testMaybeQNameEq05" True
    Nothing Nothing

testMaybeQNameEqSuite = TestList
  [ testMaybeQNameEq01
  , testMaybeQNameEq02
  , testMaybeQNameEq03
  , testMaybeQNameEq04
  , testMaybeQNameEq05
  ]

------------------------------------------------------------
--  QName ordering
------------------------------------------------------------

testQNameLe :: String -> Bool -> QName -> QName -> Test
testQNameLe lab le n1 n2 =
    TestCase ( assertEqual ("testQNameLe:"++lab) le (n1<=n2) )

testQNameLe01 = testQNameLe "testQNameLe01" True  qb3bm qb4m
testQNameLe02 = testQNameLe "testQNameLe02" True  qb4m  qb3bm
testQNameLe03 = testQNameLe "testQNameLe03" True  qb1s1 qb2s2
testQNameLe04 = testQNameLe "testQNameLe04" False qb2s2 qb1s1

testQNameLeSuite = TestList
  [ testQNameLe01
  , testQNameLe02
  , testQNameLe03
  , testQNameLe04
  ]

------------------------------------------------------------
--  Show QName
------------------------------------------------------------

testShowQName01 = testStringEq "testShowQName01"
    "<http://id.ninebynine.org/wip/2003/test/graph1/node#s1>"
    (show qb1s1)

testShowQName02 = testStringEq "testShowQName02"
    "<http://id.ninebynine.org/wip/2003/test/graph2/node/s2>"
    (show qb2s2)

testShowQName03 = testStringEq "testShowQName03"
    "<http://id.ninebynine.org/wip/2003/test/graph3/node>"
    (show qb3)

testShowQName04 = testStringEq "testShowQName04"
    "<http://id.ninebynine.org/wip/2003/test/graph5/>"
    (show qb5)

testShowQNameSuite = TestList
  [ testShowQName01
  , testShowQName02
  , testShowQName03
  , testShowQName04
  ]


------------------------------------------------------------
--  Split URI string into QName parts
------------------------------------------------------------

-- splitURI :: String -> ( String, String )
    -- splitURI "http://example.org/aaa#bbb" = ("http://example.org/aaa#","bbb")
    -- splitURI "http://example.org/aaa/bbb" = ("http://example.org/aaa/","bbb")
    -- splitURI "http://example.org/aaa/"    = ("http://example.org/aaa/","")

testSplitURI :: String -> String -> ( String, String ) -> Test
testSplitURI label input ( main, local ) =
    TestCase ( assertEqual label ( main, local ) ( splitURI input ) )

testSplitURI01 = testSplitURI "testSplitURI01"
                    "http://example.org/aaa#bbb"
                    ( "http://example.org/aaa#", "bbb" )
testSplitURI02 = testSplitURI "testSplitURI02"
                    "http://example.org/aaa/bbb"
                    ( "http://example.org/aaa/", "bbb" )
testSplitURI03 = testSplitURI "testSplitURI03"
                    "http://example.org/aaa#"
                    ( "http://example.org/aaa#", "" )
testSplitURI04 = testSplitURI "testSplitURI04"
                    "http://example.org/aaa/"
                    ( "http://example.org/aaa/", "" )
testSplitURI05 = testSplitURI "testSplitURI05"
                    "//example.org/aaa#bbb"
                    ( "//example.org/aaa#", "bbb" )
testSplitURI06 = testSplitURI "testSplitURI06"
                    "aaa/bbb"
                    ( "aaa/", "bbb" )
testSplitURI07 = testSplitURI "testSplitURI07"
                    "aaa/bbb/"
                    ( "aaa/bbb/", "" )
-- Thanks to Ian Dickinson of the HP Jena team for spotting this one:
-- So what *is* the correct split here?
testSplitURI08 = testSplitURI "testSplitURI08"
                    "mortal"
                    ( "", "mortal" )

testSplitURISuite = TestList
  [
    testSplitURI01, testSplitURI02, testSplitURI03, testSplitURI04,
    testSplitURI05, testSplitURI06, testSplitURI07, testSplitURI08
  ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ testQNameEqSuite
  , testMakeQNameSuite
  , testPartQNameSuite
  , testMaybeQNameEqSuite
  , testQNameLeSuite
  , testShowQNameSuite
  , testSplitURISuite
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
-- $Source: /file/cvsdev/HaskellUtils/QNameTest.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: QNameTest.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.5  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.4  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.3  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.2  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.1  2003/09/24 12:51:00  graham
-- Add separate QName module and test suite
--
