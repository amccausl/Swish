--------------------------------------------------------------------------------
--  $Id: VarBindingTest.hs,v 1.6 2004/01/06 13:53:10 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  VarBindingTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains test cases for variable binding values and
--  variable binding modifier values.
--
--------------------------------------------------------------------------------

-- WNH RIP OUT module Swish.HaskellRDF.VarBindingTest where

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    , subBinding, nullVarBinding, makeVarBinding
    , boundVars, subBinding, makeVarBinding
    , applyVarBinding, joinVarBindings
    , VarBindingModify(..)
    , vbmCompatibility, vbmCompose
    , findCompositions, findComposition
    , makeVarFilterModify
    , makeVarTestFilter, makeVarCompareFilter
    , varBindingId, varFilterDisjunction, varFilterConjunction
    , varFilterEQ, varFilterNE
    )

import Swish.HaskellRDF.Vocabulary
    ( swishName )

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

import Control.Monad ( unless )

import Data.List
    ( sort, union, intersect )

import Data.Maybe
    ( isJust, fromJust )


------------------------------------------------------------
--  Test case helpers
------------------------------------------------------------

assertMember :: (Eq a, Show a) => String -> a -> [a] -> Assertion
assertMember preface expected actual =
  unless (expected `elem` actual ) (assertFailure msg)
  where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show expected ++ "\nbut got: " ++ show actual

test :: String -> Bool -> Test
test lab bv =
    TestCase ( assertBool ("test:"++lab) bv )

testEq :: (Eq a, Show a) => String -> a -> a -> Test
testEq lab a1 a2 =
    TestCase ( assertEqual ("testEq:"++lab) a1 a2 )

testLe :: (Ord a, Show a) => String -> Bool -> a -> a -> Test
testLe lab eq a1 a2 =
    TestCase ( assertEqual ("testLe:"++lab) eq (a1<=a2) )

-- Test for Just x or Nothing

testJust :: String -> Maybe a -> Test
testJust lab av =
    TestCase ( assertBool ("testJust:"++lab) (isJust av) )

testNothing :: String -> Maybe a -> Test
testNothing lab av =
    TestCase ( assertBool ("testJust:"++lab) (not $ isJust av) )

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

testEqvEqv :: (Eq a, Show a) => String -> [[a]] -> [[a]] -> Test
testEqvEqv lab a1 a2 =
    TestCase ( assertEqual ("testEqvEqv:"++lab) ma1 ma2 )
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
--  Define and variable bindings
------------------------------------------------------------

vb1 :: VarBinding Int String
vb1    = makeVarBinding [(1,"a"),(2,"b"),(3,"c")]
vb1str = "[(1,\"a\"),(2,\"b\"),(3,\"c\")]"

vb2 :: VarBinding Int String
vb2    = makeVarBinding [(3,"c"),(2,"b"),(1,"a")]
vb2str = "[(3,\"c\"),(2,\"b\"),(1,\"a\")]"

vb3 :: VarBinding Int String
vb3    = makeVarBinding [(1,"a"),(2,"b"),(3,"c"),(4,"d"),(5,"e")]
vb3str = "[(1,\"a\"),(2,\"b\"),(3,\"c\"),(4,\"d\"),(5,\"e\")]"

vb4 :: VarBinding Int String
vb4 = nullVarBinding
vb4str = "[]"

testVarBinding01 = test   "testVarBinding01" $ (vb1==vb2)
testVarBinding02 = test   "testVarBinding02" $ (vb1/=vb3)
testVarBinding03 = test   "testVarBinding03" $ (vb1/=vb4)
testVarBinding04 = testEq "testVarBinding04" vb1str  $ show vb1
testVarBinding05 = testEq "testVarBinding05" vb2str  $ show vb2
testVarBinding06 = testEq "testVarBinding06" vb4str  $ show vb4

testVarBinding10 = testEq "testVarBinding10" [1,2,3] $ boundVars vb1
testVarBinding11 = testEq "testVarBinding11" [3,2,1] $ boundVars vb2
testVarBinding12 = testEq "testVarBinding12" []      $ boundVars vb4

testVarBinding20 = test   "testVarBinding20" $ (subBinding vb1 vb2)
testVarBinding21 = test   "testVarBinding21" $ (subBinding vb1 vb3)
testVarBinding22 = test   "testVarBinding22" $ not (subBinding vb1 vb4)
testVarBinding23 = test   "testVarBinding23" $ (subBinding vb2 vb1)
testVarBinding24 = test   "testVarBinding24" $ not (subBinding vb3 vb1)
testVarBinding25 = test   "testVarBinding25" $ (subBinding vb4 vb1)
testVarBinding26 = test   "testVarBinding26" $ (subBinding vb4 vb4)

vb5 :: VarBinding Int Int
vb5 = makeVarBinding [(1,11),(2,22),(3,33)]

testVarBinding30 = testEq "testVarBinding30"  0 $ applyVarBinding vb5 0
testVarBinding31 = testEq "testVarBinding31" 11 $ applyVarBinding vb5 1
testVarBinding32 = testEq "testVarBinding32" 22 $ applyVarBinding vb5 2
testVarBinding33 = testEq "testVarBinding33" 33 $ applyVarBinding vb5 3
testVarBinding34 = testEq "testVarBinding34"  4 $ applyVarBinding vb5 4
testVarBinding35 = testEq "testVarBinding35" 11 $ applyVarBinding vb5 11

vb6 :: VarBinding Int String
vb6 = makeVarBinding [(3,"cc"),(4,"dd"),(5,"ee")]

vb12 = joinVarBindings vb1 vb2
vb13 = joinVarBindings vb1 vb3
vb14 = joinVarBindings vb1 vb4
vb16 = joinVarBindings vb1 vb6
vb21 = joinVarBindings vb2 vb1
vb44 = joinVarBindings vb4 vb4

vb12str = vb1str
vb13str = vb3str
vb14str = vb1str
vb16str = "[(1,\"a\"),(2,\"b\"),(3,\"c\"),(4,\"dd\"),(5,\"ee\")]"
vb21str = vb2str
vb44str = vb4str

testVarBinding40 = test   "testVarBinding40" $ not (vbNull vb12)
testVarBinding41 = test   "testVarBinding41" $ not (vbNull vb13)
testVarBinding42 = test   "testVarBinding42" $ not (vbNull vb14)
testVarBinding43 = test   "testVarBinding43" $ not (vbNull vb16)
testVarBinding44 = test   "testVarBinding44" $ not (vbNull vb21)
testVarBinding45 = test   "testVarBinding45" $ (vbNull vb44)

testVarBinding50 = test   "testVarBinding50" $ (subBinding vb12 vb13)
testVarBinding51 = test   "testVarBinding51" $ (subBinding vb12 vb14)
testVarBinding52 = test   "testVarBinding52" $ (subBinding vb12 vb16)
testVarBinding53 = test   "testVarBinding53" $ (subBinding vb12 vb21)
testVarBinding54 = test   "testVarBinding54" $ not (subBinding vb12 vb44)
testVarBinding55 = test   "testVarBinding55" $ not (subBinding vb13 vb12)
testVarBinding56 = test   "testVarBinding56" $ (subBinding vb14 vb12)
testVarBinding57 = test   "testVarBinding57" $ (subBinding vb44 vb12)
testVarBinding58 = test   "testVarBinding58" $ not (subBinding vb16 vb12)

testVarBinding60 = testEq "testVarBinding60" vb12str $ show vb12
testVarBinding61 = testEq "testVarBinding61" vb13str $ show vb13
testVarBinding62 = testEq "testVarBinding62" vb14str $ show vb14
testVarBinding63 = testEq "testVarBinding63" vb16str $ show vb16
testVarBinding64 = testEq "testVarBinding64" vb21str $ show vb21
testVarBinding65 = testEq "testVarBinding65" vb44str $ show vb44

testVarBinding70 = testEq "testVarBinding70" (Just "a")  $ vbMap vb16 1
testVarBinding71 = testEq "testVarBinding71" (Just "c")  $ vbMap vb16 3
testVarBinding72 = testEq "testVarBinding72" (Just "ee") $ vbMap vb16 5
testVarBinding73 = testEq "testVarBinding73" Nothing     $ vbMap vb16 7

testVarBindingSuite = TestList
    [ testVarBinding01, testVarBinding02, testVarBinding03, testVarBinding04
    , testVarBinding05, testVarBinding06
    , testVarBinding10, testVarBinding11, testVarBinding12
    , testVarBinding20, testVarBinding21, testVarBinding22, testVarBinding23
    , testVarBinding24, testVarBinding25, testVarBinding26
    , testVarBinding30, testVarBinding31, testVarBinding32, testVarBinding33
    , testVarBinding34, testVarBinding35
    , testVarBinding40, testVarBinding41, testVarBinding42, testVarBinding43
    , testVarBinding44, testVarBinding45
    , testVarBinding50, testVarBinding51, testVarBinding52, testVarBinding53
    , testVarBinding54, testVarBinding55, testVarBinding56, testVarBinding57
    , testVarBinding58
    , testVarBinding60, testVarBinding61, testVarBinding62, testVarBinding63
    , testVarBinding64, testVarBinding65
    , testVarBinding70, testVarBinding71, testVarBinding72, testVarBinding73
    ]

------------------------------------------------------------
--  Variable binding modifier tests
------------------------------------------------------------

vb1m :: VarBinding String Int
vb1m    = makeVarBinding [("a",1)]

vb2m :: VarBinding String Int
vb2m    = makeVarBinding [("a",1),("b",2)]

vb3m :: VarBinding String Int
vb3m    = makeVarBinding [("a",1),("c",3)]

vb4m :: VarBinding String Int
vb4m    = makeVarBinding [("b",2),("c",3)]

vb5m :: VarBinding String Int
vb5m    = makeVarBinding [("a",1),("b",2),("c",3)]

vb6m :: VarBinding String Int
vb6m    = makeVarBinding [("a",1),("b",2),("c",4)]

vb9m :: VarBinding String Int
vb9m    = makeVarBinding [("i",9)]

-- Add new bindings per vb9m
vbm1 :: VarBindingModify String Int
vbm1 = VarBindingModify
    { vbmName  = swishName "vbm1"
    , vbmApply = map (\vb -> joinVarBindings vb vb9m)
    , vbmVocab = boundVars vb9m
    , vbmUsage = [boundVars vb9m]
    }

[vb1m1] = vbmApply vbm1 [vb1m]
[vb2m1] = vbmApply vbm1 [vb2m]

testVarModifyName01 = testEq "testVarModifyName01"
                        (swishName "vbm1") $
                        vbmName vbm1

testVarModify01 = testEq "testVarModify01" (Just 1) $ vbMap vb1m1 "a"
testVarModify02 = testEq "testVarModify02" Nothing  $ vbMap vb1m1 "b"
testVarModify03 = testEq "testVarModify03" Nothing  $ vbMap vb2m1 "c"
testVarModify04 = testEq "testVarModify04" (Just 9) $ vbMap vb1m1 "i"
testVarModify05 = testEq "testVarModify05" (Just 1) $ vbMap vb2m1 "a"
testVarModify06 = testEq "testVarModify06" (Just 2) $ vbMap vb2m1 "b"
testVarModify07 = testEq "testVarModify07" Nothing  $ vbMap vb2m1 "c"
testVarModify08 = testEq "testVarModify08" (Just 9) $ vbMap vb2m1 "i"

testVarModify10 = testEq "testVarModify10" (Just ["i"]) $
                    vbmCompatibility vbm1 ["a","b"]
testVarModify11 = testEq "testVarModify11" Nothing $
                    vbmCompatibility vbm1 ["a","b","i"]

-- Filter for bindings that define a
vbm2 :: VarBindingModify String Int
vbm2 = VarBindingModify
    { vbmName  = swishName "vbm2"
    , vbmApply = filter (\vb -> isJust $ vbMap vb "a")
    , vbmVocab = ["a"]
    , vbmUsage = [[]]
    }

vb12m2 = vbmApply vbm2 [vb1m,vb2m,vb9m]

testVarModifyName02 = testEq "testVarModifyName02"
                        (swishName "vbm2") $
                        vbmName vbm2

testVarModify20 = testEq "testVarModify20" 2 $ length vb12m2
testVarModify21 = testEq "testVarModify21" vb1m $ vb12m2!!0
testVarModify22 = testEq "testVarModify22" vb2m $ vb12m2!!1
testVarModify23 = testEq "testVarModify23" (Just []) $
                    vbmCompatibility vbm2 ["a","b"]
testVarModify24 = testEq "testVarModify24" (Just []) $
                    vbmCompatibility vbm2 ["a","b"]
testVarModify25 = testEq "testVarModify25" (Just []) $
                    vbmCompatibility vbm2 ["a","b","i"]
testVarModify26 = testEq "testVarModify26" Nothing $
                    vbmCompatibility vbm2 ["i"]

-- Filter or add bindings so that a+b=c
vbm3 :: VarBindingModify String Int
vbm3 = VarBindingModify
    { vbmName  = swishName "vbm3"
    , vbmApply = sumBinding "a" "b" "c"
    , vbmVocab = ["a","b","c"]
    , vbmUsage = [[],["a"],["b"],["c"]]
    }

sumBinding :: String -> String -> String -> [VarBinding String Int]
    -> [VarBinding String Int]
sumBinding va vb vc vbinds = concatMap abSumc vbinds
    where
        abSumc :: VarBinding String Int -> [VarBinding String Int]
        abSumc vbind =
            abSumc1 (vbMap vbind va) (vbMap vbind vb) (vbMap vbind vc) vbind
        abSumc1 (Just a) (Just b) (Just c) vbind
            | (a+b) == c = [vbind]
            | otherwise  = []
        abSumc1 (Just a) (Just b) Nothing vbind  =
            [ joinVarBindings vbind  $ makeVarBinding [(vc,a+b)] ]
        abSumc1 (Just a) Nothing (Just c) vbind  =
            [ joinVarBindings vbind  $ makeVarBinding [(vb,c-a)] ]
        abSumc1 Nothing (Just b) (Just c) vbind  =
            [ joinVarBindings vbind  $ makeVarBinding [(va,c-b)] ]
        abSumc1 _ _ _ _ = []

vb16m3 = vbmApply vbm3 [vb1m,vb2m,vb3m,vb4m,vb5m,vb6m]

testVarModifyName03 = testEq "testVarModifyName03"
                        (swishName "vbm3") $
                        vbmName vbm3

testVarModify30 = testEq "testVarModify30" 4 $ length vb16m3
testVarModify31 = testEq "testVarModify31" vb5m $ (vb16m3!!0)
testVarModify32 = testEq "testVarModify32" vb5m $ (vb16m3!!1)
testVarModify33 = testEq "testVarModify33" vb5m $ (vb16m3!!2)
testVarModify34 = testEq "testVarModify34" vb5m $ (vb16m3!!3)
testVarModify35 = testEq "testVarModify35" (Just ["c"]) $
                    vbmCompatibility vbm3 ["a","b"]
testVarModify36 = testEq "testVarModify36" (Just ["b"]) $
                    vbmCompatibility vbm3 ["a","c"]
testVarModify37 = testEq "testVarModify37" (Just ["a"]) $
                    vbmCompatibility vbm3 ["b","c","i"]
testVarModify38 = testEq "testVarModify38" (Just []) $
                    vbmCompatibility vbm3 ["i","c","a","b"]
testVarModify39 = testEq "testVarModify39" Nothing $
                    vbmCompatibility vbm3 ["i","a"]
testVarModify40 = testEq "testVarModify40" Nothing $
                    vbmCompatibility vbm3 ["i","b"]
testVarModify41 = testEq "testVarModify41" Nothing $
                    vbmCompatibility vbm3 ["i","c"]
testVarModify42 = testEq "testVarModify42" Nothing $
                    vbmCompatibility vbm3 ["i","d"]

testVarModifySuite = TestList
    [ testVarModifyName01, testVarModifyName02, testVarModifyName03
    , testVarModify01, testVarModify02, testVarModify03
    , testVarModify04, testVarModify05, testVarModify06
    , testVarModify07, testVarModify08
    , testVarModify10, testVarModify11
    , testVarModify20, testVarModify21, testVarModify22
    , testVarModify23, testVarModify24, testVarModify25
    , testVarModify26
    , testVarModify30, testVarModify31, testVarModify32
    , testVarModify33, testVarModify34, testVarModify35
    , testVarModify36, testVarModify37, testVarModify38
    , testVarModify39, testVarModify40, testVarModify41
    , testVarModify42
    ]

------------------------------------------------------------
--  Variable binding modifier composition tests
------------------------------------------------------------

--  Given (1) a+b=c and (2) a+c=d, then:
--    a=1 b=2   =>   c=3 d=4   by (1) then (2)
--    a=1 c=3   =>   b=2 d=4   by (1) then (2) or (2) then (1)
--    a=1 d=4   =>   b=2 c=3   by (2) then (1)
--    b=2 c=3   =>   a=1 d=4   by (1) then (2)
--    b=2 d=4   =>   insufficient data
--    c=3 d=4   =>   a=1 b=2   by (2) then (1)


-- Filter or add bindings so that a+b=c
vbm4 :: VarBindingModify String Int
vbm4 = VarBindingModify
    { vbmName  = swishName "vbm4"
    , vbmApply = sumBinding "a" "c" "d"
    , vbmVocab = ["a","c","d"]
    , vbmUsage = [[],["a"],["c"],["d"]]
    }

Just vbm34 = vbmCompose vbm3 vbm4
vbm34vocab = [ "a", "b", "c", "d"]
vbm34usage = [ ["a","d"], ["b","d"], ["c","d"]
             , ["a"], ["b"], ["c"], ["d"], []
             ]

Just vbm43 = vbmCompose vbm4 vbm3
vbm43vocab = [ "a", "b", "c", "d"]
vbm43usage = [ ["a","b"], ["b","c"], ["b","d"]
             , ["a"], ["b"], ["c"], ["d"], []
             ]

vbab :: VarBinding String Int
vbab    = makeVarBinding [("a",1),("b",2)]

vbac :: VarBinding String Int
vbac    = makeVarBinding [("a",1),("c",3)]

vbad :: VarBinding String Int
vbad    = makeVarBinding [("a",1),("d",4)]

vbbc :: VarBinding String Int
vbbc    = makeVarBinding [("b",2),("c",3)]

vbbd :: VarBinding String Int
vbbd    = makeVarBinding [("b",2),("d",4)]

vbcd :: VarBinding String Int
vbcd    = makeVarBinding [("c",3),("d",4)]

vbabcd :: VarBinding String Int
vbabcd    = makeVarBinding [("a",1),("b",2),("c",3),("d",4)]


testVarModifyName04 = testEq "testVarModifyName04"
                        (swishName "vbm4") $
                        vbmName vbm4

testVarModifyName05 = testEq "testVarModifyName05"
                        (swishName "_vbm4_vbm3_") $
                        vbmName vbm43

testVarModifyName06 = testEq "testVarModifyName06"
                        (swishName "_vbm3_vbm4_") $
                        vbmName vbm34

testVarCompose01 = testEqv "testVarCompose01" vbm34vocab $
                   vbmVocab vbm34
testVarCompose02 = testEqvEqv "testVarCompose02" vbm34usage $
                   vbmUsage vbm34
testVarCompose03 = testMaybeEqv "testVarCompose03" (Just ["c","d"]) $
                    vbmCompatibility vbm34 ["a","b"]
testVarCompose04 = testMaybeEqv "testVarCompose04" (Just ["b","d"]) $
                    vbmCompatibility vbm34 ["a","c"]
testVarCompose05 = testMaybeEqv "testVarCompose05" Nothing $
                    vbmCompatibility vbm34 ["a","d"]
testVarCompose06 = testMaybeEqv "testVarCompose06" (Just ["a","d"]) $
                    vbmCompatibility vbm34 ["b","c"]
testVarCompose07 = testMaybeEqv "testVarCompose07" Nothing $
                    vbmCompatibility vbm34 ["b","d"]
testVarCompose08 = testMaybeEqv "testVarCompose08" Nothing $
                    vbmCompatibility vbm34 ["c","d"]
testVarCompose09 = testMaybeEqv "testVarCompose09" (Just ["a"]) $
                    vbmCompatibility vbm34 ["b","c","d"]
testVarCompose10 = testMaybeEqv "testVarCompose10" (Just ["b"]) $
                    vbmCompatibility vbm34 ["a","c","d"]
testVarCompose11 = testMaybeEqv "testVarCompose11" (Just ["c"]) $
                    vbmCompatibility vbm34 ["a","b","d"]
testVarCompose12 = testMaybeEqv "testVarCompose12" (Just ["d"]) $
                    vbmCompatibility vbm34 ["a","b","c"]
testVarCompose13 = testMaybeEqv "testVarCompose13" (Just []) $
                    vbmCompatibility vbm34 ["a","b","c","d"]
testVarCompose14 = testEqv "testVarCompose14" [vbabcd,vbabcd,vbabcd] $
                    vbmApply vbm34 [vbab,vbac,vbbc]
testVarCompose15 = testEqv "testVarCompose15" [] $
                    vbmApply vbm34 [vbad,vbbd,vbcd]

testVarCompose21 = testEqv "testVarCompose21" vbm43vocab $
                   vbmVocab vbm43
testVarCompose22 = testEqvEqv "testVarCompose22" vbm43usage $
                   vbmUsage vbm43
testVarCompose23 = testMaybeEqv "testVarCompose23" Nothing $
                    vbmCompatibility vbm43 ["a","b"]
testVarCompose24 = testMaybeEqv "testVarCompose24" (Just ["b","d"]) $
                    vbmCompatibility vbm43 ["a","c"]
testVarCompose25 = testMaybeEqv "testVarCompose25" (Just ["b","c"]) $
                    vbmCompatibility vbm43 ["a","d"]
testVarCompose26 = testMaybeEqv "testVarCompose26" Nothing $
                    vbmCompatibility vbm43 ["b","c"]
testVarCompose27 = testMaybeEqv "testVarCompose27" Nothing $
                    vbmCompatibility vbm43 ["b","d"]
testVarCompose28 = testMaybeEqv "testVarCompose28" (Just ["a","b"]) $
                    vbmCompatibility vbm43 ["c","d"]
testVarCompose29 = testMaybeEqv "testVarCompose29" (Just ["a"]) $
                    vbmCompatibility vbm43 ["b","c","d"]
testVarCompose30 = testMaybeEqv "testVarCompose30" (Just ["b"]) $
                    vbmCompatibility vbm43 ["a","c","d"]
testVarCompose31 = testMaybeEqv "testVarCompose31" (Just ["c"]) $
                    vbmCompatibility vbm43 ["a","b","d"]
testVarCompose32 = testMaybeEqv "testVarCompose32" (Just ["d"]) $
                    vbmCompatibility vbm43 ["a","b","c"]
testVarCompose33 = testMaybeEqv "testVarCompose33" (Just []) $
                    vbmCompatibility vbm43 ["a","b","c","d"]
testVarCompose34 = testEqv "testVarCompose34" [] $
                    vbmApply vbm43 [vbab,vbbc,vbbd]
testVarCompose35 = testEqv "testVarCompose35" [vbabcd,vbabcd,vbabcd] $
                    vbmApply vbm43 [vbac,vbad,vbcd]

-- [[[need test for incompatible composition]]] --
--  Three ways to be incompatible:
--  (a) both modifers define same new output
--  (b) output from second modifier is input to first modifier

vbm5 :: VarBindingModify String Int
vbm5 = VarBindingModify
    { vbmName  = swishName "vbm5"
    , vbmApply = id                 -- incorrect: dummy for testing only
    , vbmVocab = ["a","b","c"]
    , vbmUsage = [["a"],["b"]]
    }

vbm6 :: VarBindingModify String Int
vbm6 = VarBindingModify
    { vbmName  = swishName "vbm6"
    , vbmApply = id                 -- incorrect: dummy for testing only
    , vbmVocab = ["a","b","c"]
    , vbmUsage = [["a","b"],["b","c"],["a","c"]]
    }

vbm7 :: VarBindingModify String Int
vbm7 = VarBindingModify
    { vbmName  = swishName "vbm7"
    , vbmApply = id                 -- incorrect: dummy for testing only
    , vbmVocab = ["a","b","c"]
    , vbmUsage = [["a"]]
    }

vbm8 :: VarBindingModify String Int
vbm8 = VarBindingModify
    { vbmName  = swishName "vbm8"
    , vbmApply = id                 -- incorrect: dummy for testing only
    , vbmVocab = ["b","c","d"]
    , vbmUsage = [["b"],["c"],["b","c"]]
    }

vbm56 = vbmCompose vbm5 vbm6
vbm65 = vbmCompose vbm6 vbm5
vbm78 = vbmCompose vbm7 vbm8
vbm87 = vbmCompose vbm8 vbm7
vbm87usage = [["a","b"],["a","c"],["a","b","c"]]

testVarCompose41 = test   "testVarCompose41" $ not (isJust vbm56)
testVarCompose42 = test   "testVarCompose42" $ not (isJust vbm65)
testVarCompose43 = test   "testVarCompose43" $ not (isJust vbm78)
testVarCompose44 = test   "testVarCompose44" $     (isJust vbm87)
testVarCompose45 = testEqvEqv "testVarCompose45" vbm87usage $
                    vbmUsage (fromJust vbm87)

jvbm1id    = vbmCompose vbm1 varBindingId
jvbmid1    = vbmCompose varBindingId vbm1

testVarCompose51 = test   "testVarCompose51" $ isJust jvbm1id
testVarCompose52 = test   "testVarCompose52" $ isJust jvbmid1

[vb1m1id] = vbmApply (fromJust jvbm1id) [vb1m]
[vb2m1id] = vbmApply (fromJust jvbm1id) [vb2m]

testVarModifyName07 = testEq "testVarModifyName07"
                        (swishName "_vbm1_varBindingId_") $
                        vbmName (fromJust jvbm1id)

testVarModifyName08 = testEq "testVarModifyName08"
                        (swishName "_varBindingId_vbm1_") $
                        vbmName (fromJust jvbmid1)

testVarCompose61 = testEq "testVarCompose61" (Just 1) $ vbMap vb1m1id "a"
testVarCompose62 = testEq "testVarCompose62" Nothing  $ vbMap vb1m1id "b"
testVarCompose63 = testEq "testVarCompose63" Nothing  $ vbMap vb2m1id "c"
testVarCompose64 = testEq "testVarCompose64" (Just 9) $ vbMap vb1m1id "i"
testVarCompose65 = testEq "testVarCompose65" (Just 1) $ vbMap vb2m1id "a"
testVarCompose66 = testEq "testVarCompose66" (Just 2) $ vbMap vb2m1id "b"
testVarCompose67 = testEq "testVarCompose67" Nothing  $ vbMap vb2m1id "c"
testVarCompose68 = testEq "testVarCompose68" (Just 9) $ vbMap vb2m1id "i"

[vb1mid1] = vbmApply (fromJust jvbmid1) [vb1m]
[vb2mid1] = vbmApply (fromJust jvbmid1) [vb2m]

testVarCompose71 = testEq "testVarCompose71" (Just 1) $ vbMap vb1mid1 "a"
testVarCompose72 = testEq "testVarCompose72" Nothing  $ vbMap vb1mid1 "b"
testVarCompose73 = testEq "testVarCompose73" Nothing  $ vbMap vb2mid1 "c"
testVarCompose74 = testEq "testVarCompose74" (Just 9) $ vbMap vb1mid1 "i"
testVarCompose75 = testEq "testVarCompose75" (Just 1) $ vbMap vb2mid1 "a"
testVarCompose76 = testEq "testVarCompose76" (Just 2) $ vbMap vb2mid1 "b"
testVarCompose77 = testEq "testVarCompose77" Nothing  $ vbMap vb2mid1 "c"
testVarCompose78 = testEq "testVarCompose78" (Just 9) $ vbMap vb2mid1 "i"

testVarComposeSuite = TestList
    [ testVarModifyName04, testVarModifyName05, testVarModifyName06
    , testVarModifyName07, testVarModifyName08
    , testVarCompose01, testVarCompose02, testVarCompose03, testVarCompose04
    , testVarCompose05, testVarCompose06, testVarCompose07, testVarCompose08
    , testVarCompose09, testVarCompose10, testVarCompose11, testVarCompose12
    , testVarCompose13, testVarCompose14, testVarCompose15
    , testVarCompose21, testVarCompose22, testVarCompose23, testVarCompose24
    , testVarCompose25, testVarCompose26, testVarCompose27, testVarCompose28
    , testVarCompose29, testVarCompose30, testVarCompose31, testVarCompose32
    , testVarCompose33, testVarCompose34, testVarCompose35
    , testVarCompose41, testVarCompose42, testVarCompose43, testVarCompose44
    , testVarCompose45
    , testVarCompose51, testVarCompose52
    , testVarCompose61, testVarCompose62, testVarCompose63, testVarCompose64
    , testVarCompose65, testVarCompose66, testVarCompose67, testVarCompose68
    , testVarCompose71, testVarCompose72, testVarCompose73, testVarCompose74
    , testVarCompose75, testVarCompose76, testVarCompose77, testVarCompose78
    ]

------------------------------------------------------------
--  Modifier composition discovery tests
------------------------------------------------------------

--  vbm3: a+b=c (1)
--  vbm4: a+c=d (2)
--  vbm9: c+d=e (3)
--
--  a,b -> c,d,e  by (1,2,3)
--  a,c -> b,d,e  by (1,2,3)
--         d,b,e  by (2,1,3)
--         d,e,b  by (2,3,1)
--  a,d -> c,b,e  by (2,1,3)
--         c,e,b  by (2,3,1)
--  a,e -> None
--  b,c -> a,d,e  by (1,2,3)
--  b,d -> None
--  b,e -> None
--  c,d -> a,b,e  by (2,1,3)
--      -> a,e,a  by (2,3,1)
--      -> e,a,b  by (3,2,1)
--  c,e -> d,a,b  by (3,2,1)
--  d,e -> c,a,b  by (3,2,1)

vbm9 :: VarBindingModify String Int
vbm9 = VarBindingModify
    { vbmName  = swishName "vbm9"
    , vbmApply = sumBinding "c" "d" "e"
    , vbmVocab = ["c","d","e"]
    , vbmUsage = [[],["c"],["d"],["e"]]
    }

compab = findCompositions [vbm3,vbm4,vbm9] ["a","b"]    -- 1
compac = findCompositions [vbm3,vbm4,vbm9] ["a","c"]    -- 3
compad = findCompositions [vbm3,vbm4,vbm9] ["a","d"]    -- 2
compae = findCompositions [vbm3,vbm4,vbm9] ["a","e"]    -- 0
compba = findCompositions [vbm3,vbm4,vbm9] ["b","a"]    -- 1
compbc = findCompositions [vbm3,vbm4,vbm9] ["b","c"]    -- 1
compbd = findCompositions [vbm3,vbm4,vbm9] ["b","d"]    -- 0
compbe = findCompositions [vbm3,vbm4,vbm9] ["b","e"]    -- 0
compca = findCompositions [vbm3,vbm4,vbm9] ["c","a"]    -- 3
compcd = findCompositions [vbm3,vbm4,vbm9] ["c","d"]    -- 3
compce = findCompositions [vbm3,vbm4,vbm9] ["c","e"]    -- 1
compde = findCompositions [vbm3,vbm4,vbm9] ["d","e"]    -- 1

testVarModifyName09 = testEq "testVarModifyName08"
                        (swishName "__vbm4_vbm3__vbm9_") $
                        vbmName (compad!!0)

testVarModifyName10 = testEq "testVarModifyName08"
                        (swishName "__vbm4_vbm9__vbm3_") $
                        vbmName (compad!!1)

testFindComp01 = testEq "testFindComp01" 1 $ (length compab)
testFindComp02 = testEq "testFindComp02" 3 $ (length compac)
testFindComp03 = testEq "testFindComp03" 2 $ (length compad)
testFindComp04 = testEq "testFindComp04" 0 $ (length compae)
testFindComp05 = testEq "testFindComp05" 1 $ (length compba)
testFindComp06 = testEq "testFindComp06" 1 $ (length compbc)
testFindComp07 = testEq "testFindComp07" 0 $ (length compbd)
testFindComp08 = testEq "testFindComp08" 0 $ (length compbe)
testFindComp09 = testEq "testFindComp09" 3 $ (length compca)
testFindComp10 = testEq "testFindComp10" 3 $ (length compcd)
testFindComp11 = testEq "testFindComp11" 1 $ (length compce)
testFindComp12 = testEq "testFindComp12" 1 $ (length compde)

compvocab = ["a","b","c","d","e"]

testFindComp21 = testEqv "testFindComp21" compvocab $ vbmVocab (head compab)
testFindComp22 = testEqv "testFindComp22" compvocab $ vbmVocab (head compac)
testFindComp23 = testEqv "testFindComp23" compvocab $ vbmVocab (head compad)
testFindComp24 = testEqv "testFindComp24" compvocab $ vbmVocab (head compba)
testFindComp25 = testEqv "testFindComp25" compvocab $ vbmVocab (head compbc)
testFindComp26 = testEqv "testFindComp26" compvocab $ vbmVocab (head compca)
testFindComp27 = testEqv "testFindComp27" compvocab $ vbmVocab (head compcd)
testFindComp28 = testEqv "testFindComp28" compvocab $ vbmVocab (head compce)
testFindComp29 = testEqv "testFindComp29" compvocab $ vbmVocab (head compde)

testFindComp31 = testHasEqv "testFindComp31" ["c","d","e"] $ vbmUsage (head compab)
testFindComp32 = testHasEqv "testFindComp32" ["b","d","e"] $ vbmUsage (head compac)
testFindComp33 = testHasEqv "testFindComp33" ["b","c","e"] $ vbmUsage (head compad)
testFindComp34 = testHasEqv "testFindComp34" ["c","d","e"] $ vbmUsage (head compba)
testFindComp35 = testHasEqv "testFindComp35" ["a","d","e"] $ vbmUsage (head compbc)
testFindComp36 = testHasEqv "testFindComp36" ["b","d","e"] $ vbmUsage (head compca)
testFindComp37 = testHasEqv "testFindComp37" ["a","b","e"] $ vbmUsage (head compcd)
testFindComp38 = testHasEqv "testFindComp38" ["a","b","d"] $ vbmUsage (head compce)
testFindComp39 = testHasEqv "testFindComp39" ["a","b","c"] $ vbmUsage (head compde)

compBindings :: [VarBinding String Int]
compBindings = map makeVarBinding
    [ [ ("a",1), ("b",2) ]
    , [ ("a",1), ("c",3) ]
    , [ ("a",1), ("d",4) ]
    , [ ("a",1), ("e",7) ]
    , [ ("b",2), ("c",3) ]
    , [ ("b",2), ("d",4) ]
    , [ ("b",2), ("e",7) ]
    , [ ("c",3), ("d",4) ]
    , [ ("c",3), ("e",7) ]
    , [ ("d",4), ("e",7) ]
    ]

compResult :: [VarBinding String Int]
compResult = map makeVarBinding
    [ [ ("a",1), ("b",2), ("c",3), ("d",4), ("e",7) ] ]

compApply :: [VarBindingModify String Int] -> [VarBinding String Int]
compApply vbms = (vbmApply (head vbms)) compBindings

testFindComp41 = testEqv "testFindComp41" compResult $ (compApply compab)
testFindComp42 = testEqv "testFindComp42" compResult $ (compApply compac)
testFindComp43 = testEqv "testFindComp43" compResult $ (compApply compad)
testFindComp44 = testEqv "testFindComp44" compResult $ (compApply compba)
testFindComp45 = testEqv "testFindComp45" compResult $ (compApply compbc)
testFindComp46 = testEqv "testFindComp46" compResult $ (compApply compca)
testFindComp47 = testEqv "testFindComp47" compResult $ (compApply compcd)
testFindComp48 = testEqv "testFindComp48" compResult $ (compApply compce)
testFindComp49 = testEqv "testFindComp49" compResult $ (compApply compde)

jcompab = findComposition [vbm3,vbm4,vbm9] ["a","b"]    -- 1
jcompac = findComposition [vbm3,vbm4,vbm9] ["a","c"]    -- 3
jcompad = findComposition [vbm3,vbm4,vbm9] ["a","d"]    -- 1
jcompae = findComposition [vbm3,vbm4,vbm9] ["a","e"]    -- 0
jcompba = findComposition [vbm3,vbm4,vbm9] ["b","a"]    -- 1
jcompbc = findComposition [vbm3,vbm4,vbm9] ["b","c"]    -- 1
jcompbd = findComposition [vbm3,vbm4,vbm9] ["b","d"]    -- 0
jcompbe = findComposition [vbm3,vbm4,vbm9] ["b","e"]    -- 0
jcompca = findComposition [vbm3,vbm4,vbm9] ["c","a"]    -- 3
jcompcd = findComposition [vbm3,vbm4,vbm9] ["c","d"]    -- 3
jcompce = findComposition [vbm3,vbm4,vbm9] ["c","e"]    -- 1
jcompde = findComposition [vbm3,vbm4,vbm9] ["d","e"]    -- 1

testFindComp51 = testJust    "testFindComp51" jcompab
testFindComp52 = testJust    "testFindComp52" jcompac
testFindComp53 = testJust    "testFindComp53" jcompad
testFindComp54 = testNothing "testFindComp54" jcompae
testFindComp55 = testJust    "testFindComp55" jcompba
testFindComp56 = testJust    "testFindComp56" jcompbc
testFindComp57 = testNothing "testFindComp57" jcompbd
testFindComp58 = testNothing "testFindComp58" jcompbe
testFindComp59 = testJust    "testFindComp59" jcompca
testFindComp60 = testJust    "testFindComp60" jcompcd
testFindComp61 = testJust    "testFindComp61" jcompce
testFindComp62 = testJust    "testFindComp62" jcompde

testFindCompSuite = TestList
    [ testVarModifyName09, testVarModifyName10
    , testFindComp01, testFindComp02, testFindComp03, testFindComp04
    , testFindComp05, testFindComp06, testFindComp07, testFindComp08
    , testFindComp09, testFindComp10, testFindComp11, testFindComp12
    , testFindComp21, testFindComp22, testFindComp23, testFindComp24
    , testFindComp25, testFindComp26, testFindComp27, testFindComp28
    , testFindComp29
    , testFindComp31, testFindComp32, testFindComp33, testFindComp34
    , testFindComp35, testFindComp36, testFindComp37, testFindComp38
    , testFindComp39
    , testFindComp41, testFindComp42, testFindComp43, testFindComp44
    , testFindComp45, testFindComp46, testFindComp47, testFindComp48
    , testFindComp49
    ]

------------------------------------------------------------
--  Variable binding filters
------------------------------------------------------------

testFilterBindings :: [VarBinding String Int]
testFilterBindings = map makeVarBinding
    [ [ ("a",0), ("b",2), ("c",2) ]
    , [ ("a",0), ("b",2), ("c",3) ]
    , [ ("a",1), ("b",2), ("c",2) ]
    , [ ("a",1), ("b",2), ("c",3) ]
    , [ ("a",1), ("b",2), ("c",0) ]
    , [ ("a",0), ("b",2), ("c",0) ]
    , [ ("a",4), ("b",2), ("c",4) ]
    , [ ("x",4), ("y",2), ("z",4) ]
    ]

filtertesta0 :: VarBindingModify String Int
filtertesta0 = makeVarFilterModify $
        makeVarTestFilter (swishName "filtertesta0") (==0) "a"
vba0 :: [VarBinding String Int]
vba0 = map makeVarBinding
    [ [ ("a",0), ("b",2), ("c",2) ]
    , [ ("a",0), ("b",2), ("c",3) ]
    , [ ("a",0), ("b",2), ("c",0) ]
    ]

filtertestc0 :: VarBindingModify String Int
filtertestc0 = makeVarFilterModify $
        makeVarTestFilter (swishName "filtertestc0") (==0) "c"
vbc0 :: [VarBinding String Int]
vbc0 = map makeVarBinding
    [ [ ("a",1), ("b",2), ("c",0) ]
    , [ ("a",0), ("b",2), ("c",0) ]
    ]

filtercompabeq :: VarBindingModify String Int
filtercompabeq = makeVarFilterModify $ varFilterEQ "a" "b"
vbabeq :: [VarBinding String Int]
vbabeq = map makeVarBinding
    [ ]

filtercompaceq :: VarBindingModify String Int
filtercompaceq = makeVarFilterModify $ varFilterEQ "a" "c"
vbaceq :: [VarBinding String Int]
vbaceq = map makeVarBinding
    [ [ ("a",0), ("b",2), ("c",0) ]
    , [ ("a",4), ("b",2), ("c",4) ]
    ]

filtercompbceq :: VarBindingModify String Int
filtercompbceq = makeVarFilterModify $ varFilterEQ "b" "c"
vbbceq :: [VarBinding String Int]
vbbceq = map makeVarBinding
    [ [ ("a",0), ("b",2), ("c",2) ]
    , [ ("a",1), ("b",2), ("c",2) ]
    ]

filtercompbcne :: VarBindingModify String Int
filtercompbcne = makeVarFilterModify $ varFilterNE "b" "c"
vbbcne :: [VarBinding String Int]
vbbcne = map makeVarBinding
    [ [ ("a",0), ("b",2), ("c",3) ]
    , [ ("a",1), ("b",2), ("c",3) ]
    , [ ("a",1), ("b",2), ("c",0) ]
    , [ ("a",0), ("b",2), ("c",0) ]
    , [ ("a",4), ("b",2), ("c",4) ]
    ]

filterdisjunct :: VarBindingModify String Int
filterdisjunct = makeVarFilterModify $
                 varFilterDisjunction
                    [ makeVarTestFilter (swishName "isZero") (==0) "a"
                    , varFilterEQ "a" "c"]
vbdisj = vbaceq `union` vba0

filterconjunct :: VarBindingModify String Int
filterconjunct = makeVarFilterModify $
                 varFilterConjunction
                    [ makeVarTestFilter (swishName "isZero") (==0) "a"
                    , varFilterEQ "a" "c"]
vbconj = vbaceq `intersect` vba0

testFilterName01 = testEq "testFilterName01" (swishName "filtertesta0") $
                    vbmName filtertesta0
testFilterName02 = testEq "testFilterName02" (swishName "filtertestc0") $
                    vbmName filtertestc0
testFilterName03 = testEq "testFilterName03" (swishName "varFilterEQ") $
                    vbmName filtercompabeq
testFilterName04 = testEq "testFilterName04" (swishName "varFilterNE") $
                    vbmName filtercompbcne
testFilterName05 = testEq "testFilterName05" (swishName "varFilterDisjunction") $
                    vbmName filterdisjunct
testFilterName06 = testEq "testFilterName06" (swishName "varFilterConjunction") $
                    vbmName filterconjunct

testFilter01 = testEqv "testFilter01" vba0   $ vbmApply filtertesta0   testFilterBindings
testFilter02 = testEqv "testFilter02" vbc0   $ vbmApply filtertestc0   testFilterBindings
testFilter03 = testEqv "testFilter03" vbabeq $ vbmApply filtercompabeq testFilterBindings
testFilter04 = testEqv "testFilter04" vbaceq $ vbmApply filtercompaceq testFilterBindings
testFilter05 = testEqv "testFilter05" vbbceq $ vbmApply filtercompbceq testFilterBindings
testFilter06 = testEqv "testFilter06" vbbcne $ vbmApply filtercompbcne testFilterBindings
testFilter07 = testEqv "testFilter07" vbdisj $ vbmApply filterdisjunct testFilterBindings
testFilter08 = testEqv "testFilter08" vbconj $ vbmApply filterconjunct testFilterBindings

testFilter10 = testEqv "testFilter10" testFilterBindings $
                vbmApply varBindingId testFilterBindings

testFilterSuite = TestList
    [ testFilterName01, testFilterName02, testFilterName03
    , testFilterName04, testFilterName05, testFilterName06
    , testFilter01, testFilter02, testFilter03, testFilter04
    , testFilter05, testFilter06, testFilter07, testFilter08
    , testFilter10
    ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
    [ testVarBindingSuite
    , testVarModifySuite
    , testVarComposeSuite
    , testFindCompSuite
    , testFilterSuite
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
-- $Source: /file/cvsdev/HaskellRDF/VarBindingTest.hs,v $
-- $Author: graham $
-- $Revision: 1.6 $
-- $Log: VarBindingTest.hs,v $
-- Revision 1.6  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.5  2003/12/08 16:58:27  graham
-- Add name to variable binding modifiers and filters.
-- Add namespace for Swish-defined names.
--
-- Revision 1.4  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.3  2003/10/15 16:40:52  graham
-- Reworked RDFQuery to use new query binding framework.
-- (Note: still uses VarBindingFilter rather than VarBindingModify.
-- The intent is to incorproate the VarBindingModify logic into RDFProof,
-- displaying the existing use of BindingFilter.)
--
-- Revision 1.2  2003/10/15 00:07:01  graham
-- Added variable binding filter structures, and some common filters
--
-- Revision 1.1  2003/10/14 20:30:58  graham
-- Add separate module for generic variable binding functions.
--
