--------------------------------------------------------------------------------
--  $Id: TestHelpers.hs,v 1.2 2004/01/13 12:18:34 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  TestHelpers
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains test case helper functions, providing a range of
--  commonly-used test cases.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.TestHelpers
    ( test, testEq, testLe, testGe, testElem
    , testJust, testNothing
    , testEqv, testEqv2, testHasEqv, testMaybeEqv
    )
where

import Swish.HaskellUtils.ListHelpers
    ( equiv )

import Test.HUnit
    ( Test(TestCase,TestList)
    , Assertion
    , assertBool, assertEqual, assertFailure
    , runTestTT
    )

import Control.Monad
    ( unless )

import Data.Maybe
    ( isJust )


------------------------------------------------------------
--  Test case helpers
------------------------------------------------------------

assertMember :: (Eq a, Show a) => String -> a -> [a] -> Assertion
assertMember preface item list =
  unless (item `elem` list) (assertFailure msg)
  where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show item ++ "\nin list: " ++ show list

test :: String -> Bool -> Test
test lab bv =
    TestCase ( assertBool ("test:"++lab) bv )

testEq :: (Eq a, Show a) => String -> a -> a -> Test
testEq lab a1 a2 =
    TestCase ( assertEqual ("testEq:"++lab) a1 a2 )

testLe :: (Ord a, Show a) => String -> a -> a -> Test
testLe lab a1 a2 =
    TestCase ( assertBool ("testLe:"++lab++vals) (a1<=a2) )
    where
        vals = ", fail: "++show a1++" <= "++show a2

testGe :: (Ord a, Show a) => String -> a -> a -> Test
testGe lab a1 a2 =
    TestCase ( assertBool ("testGe:"++lab++vals) (a1>=a2) )
    where
        vals = ", fail: "++show a1++" >= "++show a2

-- Test for Just x or Nothing

testJust :: String -> Maybe a -> Test
testJust lab av =
    TestCase ( assertBool ("testJust:"++lab) (isJust av) )

testNothing :: String -> Maybe a -> Test
testNothing lab av =
    TestCase ( assertBool ("testJust:"++lab) (not $ isJust av) )

-- Test for list membership

testElem :: (Eq a, Show a) => String -> a -> [a] -> Test
testElem lab a1 as =
    TestCase ( assertMember ("testElem:"++lab) a1 as )

-- Compare lists and lists of lists and Maybe lists for set equivalence:

data ListTest a = ListTest [a]

instance (Eq a) => Eq (ListTest a) where
    (ListTest a1) == (ListTest a2) = a1 `equiv` a2

instance (Show a) => Show (ListTest a) where
    show (ListTest a) = show a

data MaybeListTest a = MaybeListTest (Maybe [a])

instance (Eq a) => Eq (MaybeListTest a) where
    MaybeListTest (Just a1) == MaybeListTest (Just a2) = a1 `equiv` a2
    MaybeListTest Nothing   == MaybeListTest Nothing   = True
    _                       == _                       = False

instance (Show a) => Show (MaybeListTest a) where
    show (MaybeListTest a) = show a

testEqv :: (Eq a, Show a) => String -> [a] -> [a] -> Test
testEqv lab a1 a2 =
    TestCase ( assertEqual ("testEqv:"++lab) (ListTest a1) (ListTest a2) )

testEqv2 :: (Eq a, Show a) => String -> [[a]] -> [[a]] -> Test
testEqv2 lab a1 a2 =
    TestCase ( assertEqual ("testEqv2:"++lab) ma1 ma2 )
    where
        ma1 = ListTest $ map ListTest a1
        ma2 = ListTest $ map ListTest a2

testHasEqv :: (Eq a, Show a) => String -> [a] -> [[a]] -> Test
testHasEqv lab a1 a2 =
    TestCase ( assertMember ("testHasEqv:"++lab) ma1 ma2 )
    where
        ma1 = ListTest a1
        ma2 = map ListTest a2

testMaybeEqv :: (Eq a, Show a) => String -> Maybe [a] -> Maybe [a] -> Test
testMaybeEqv lab a1 a2 =
    TestCase ( assertEqual ("testMaybeEqv:"++lab) ma1 ma2 )
    where
        ma1 = (MaybeListTest a1)
        ma2 = (MaybeListTest a2)

------------------------------------------------------------
--  Test suites for the above
------------------------------------------------------------

testSuccessSuite = TestList
    [ test          "01" True
    , testEq        "02" 2 2
    , testLe        "03" 1 2
    , testLe        "04" 2 2
    , testGe        "05" 3 2
    , testGe        "07" 2 2
    , testJust      "08" (Just "08")
    , testNothing   "09" (Nothing :: Maybe String)
    , testElem      "10" 'b' "abc"
    , testEqv       "11" "abc" "bca"
    , testEqv       "12" "abc" "bbccaa"
    , testEqv2      "13" ["abc","def","ghi"] ["fed","ghi","bca"]
    , testHasEqv    "14" "abc"               ["fed","ghi","bca"]
    , testHasEqv    "15" "ghi"               ["fed","ghi","bca"]
    , testHasEqv    "16" "def"               ["fed","ghi","bca"]
    , testMaybeEqv  "17" (Just "abc") (Just "bca")
    , testMaybeEqv  "18" Nothing      (Nothing :: Maybe String)
    ]

-- All of these tests should be failures:
-- Look for number of failures == total number of tests
testFailureSuite = TestList
    [ test          "01" False
    , testEq        "02" 2 22
    , testLe        "03" 2 1
    , testGe        "04" 2 3
    , testJust      "05" (Nothing :: Maybe String)
    , testNothing   "06" (Just "09")
    , testElem      "07" 'd' "abc"
    , testEqv       "08" "abd" "bca"
    , testEqv2      "09" ["abd","def","ghi"] ["fed","ghi","bca"]
    , testHasEqv    "10" "abd"               ["fed","ghi","bca"]
    , testMaybeEqv  "11" (Just "abc") (Just "bda")
    , testMaybeEqv  "12" Nothing      (Just "bda")
    ]


------------------------------------------------------------
--  All tests
------------------------------------------------------------

allSuccessTests = TestList
    [ testSuccessSuite
    ]

allFailureTests = TestList
    [ testFailureSuite
    ]

mainS = runTestTT allSuccessTests
mainF = runTestTT allFailureTests

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
-- $Source: /file/cvsdev/HaskellUtils/TestHelpers.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: TestHelpers.hs,v $
-- Revision 1.2  2004/01/13 12:18:34  graham
-- Clean up test case helpers module.
--
-- Revision 1.1.1.1  2004/01/13 12:15:56  graham
-- Fix up name of HaskellUtils project
