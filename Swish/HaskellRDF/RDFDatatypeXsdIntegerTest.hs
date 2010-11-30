--------------------------------------------------------------------------------
--  $Id: RDFDatatypeXsdIntegerTest.hs,v 1.13 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFDatatypeXsdIntegerTest
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

-- WNH RIP OUT module Swish.HaskellRDF.RDFDatatypeXsdIntegerTest where

import Swish.HaskellRDF.RDFDatatypeXsdInteger
    ( rdfDatatypeXsdInteger
    , rdfDatatypeValXsdInteger
    , typeNameXsdInteger, namespaceXsdInteger
    , axiomsXsdInteger, rulesXsdInteger
    , prefixXsdInteger
    )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding )

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFClosure, RDFRuleset
    , makeRDFGraphFromN3String
    , makeRDFFormula
    )

import Swish.HaskellRDF.RDFDatatype
    ( RDFDatatype
    , RDFDatatypeVal
    , RDFDatatypeMod
    , applyRDFDatatypeMod
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..), RDFGraph
    )

import Swish.HaskellRDF.ClassRestrictionRule
    ( ClassRestriction(..), ClassRestrictionFn
    , makeDatatypeRestriction, makeDatatypeRestrictionFn
    , makeRDFClassRestrictionRules
    , makeRDFDatatypeRestrictionRules
    , falseGraph, falseGraphStr
    )

import Swish.HaskellRDF.Datatype
    ( Datatype(..)
    , typeName, typeRules, typeMkRules
    , getTypeAxiom, getTypeRule
    , DatatypeVal(..)
    , getDTMod
    , DatatypeMap(..)
    , DatatypeMod(..)
    , nullDatatypeMod
    )

import Swish.HaskellRDF.Ruleset
    ( Ruleset(..)
    , getRulesetAxiom, getRulesetRule
    )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..)
    , nullScope, nullFormula, nullRule
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    , makeVarBinding
    , VarBindingModify(..)
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI
    , makeScopedName
    , matchName
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceNull
    , namespaceRDF
    , namespaceRDFS
    , namespaceXSD
    , namespaceMATH
    , namespaceXsdType
    , namespaceDefault
    , scopeRDF
    , scopeRDFS
    , scopeRDFD
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..), LookupMap(..)
    , mapFind, mapFindMaybe
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

import Control.Monad ( unless )

import Data.List
    ( sort, union, intersect )

import Data.Maybe
    ( isJust, fromJust, fromMaybe )


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

testElem :: (Eq a, Show a) => String -> a -> [a] -> Test
testElem lab a1 as =
    TestCase ( assertMember ("testElem:"++lab) a1 as )

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
--  Misc values
------------------------------------------------------------

xsd_int_name nam  = (ScopedName namespaceXsdInteger nam)

axiomXsdIntegerDT       = xsd_int_name "dt"

ruleXsdIntegerAbs       = xsd_int_name "Abs"
ruleXsdIntegerNeg       = xsd_int_name "Neg"
ruleXsdIntegerSum       = xsd_int_name "Sum"
ruleXsdIntegerDiff      = xsd_int_name "Diff"
ruleXsdIntegerProd      = xsd_int_name "Prod"
ruleXsdIntegerDivMod    = xsd_int_name "DivMod"
ruleXsdIntegerPower     = xsd_int_name "Power"
ruleXsdIntegerEq        = xsd_int_name "Eq"
ruleXsdIntegerNe        = xsd_int_name "Ne"
ruleXsdIntegerLt        = xsd_int_name "Lt"
ruleXsdIntegerLe        = xsd_int_name "Le"
ruleXsdIntegerGt        = xsd_int_name "Gt"
ruleXsdIntegerGe        = xsd_int_name "Ge"

------------------------------------------------------------
--  Basic rdfDatatypeXsdInteger tests
------------------------------------------------------------

getXsdIntegerAxiom scopnam =
    fromMaybe nullFormula $ getTypeAxiom scopnam rdfDatatypeXsdInteger

getXsdIntegerRule scopnam =
    fromMaybe nullRule $ getTypeRule scopnam rdfDatatypeXsdInteger

getXsdIntegerDTmod scopnam =
    fromMaybe nullDatatypeMod $ getDTMod scopnam rdfDatatypeValXsdInteger

testDatatype01 = testEq  "testDatatype01" typeNameXsdInteger $
                    typeName rdfDatatypeXsdInteger
testDatatype02 = testEq  "testDatatype02" namespaceXsdInteger $
                    rsNamespace (typeRules rdfDatatypeXsdInteger)
testDatatype03 = testEqv "testDatatype03" axiomsXsdInteger $
                    rsAxioms (typeRules rdfDatatypeXsdInteger)
testDatatype04 = testEqv "testDatatype04" rulesXsdInteger $
                    rsRules (typeRules rdfDatatypeXsdInteger)
testDatatype05 = testEq "testDatatype05" axiomXsdIntegerDT $
                    formName (getXsdIntegerAxiom axiomXsdIntegerDT)
testDatatype06 = testEq "testDatatype06" ruleXsdIntegerAbs $
                    ruleName (getXsdIntegerRule ruleXsdIntegerAbs)

testDatatypeSuite = TestList
    [ testDatatype01, testDatatype02, testDatatype03, testDatatype04
    , testDatatype05, testDatatype06
    ]

------------------------------------------------------------
--  Basic rdfDatatypeValXsdInteger tests
------------------------------------------------------------

testDatatypeVal01 = testEq  "testDatatypeVal01" (Just 123) $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "123"
testDatatypeVal02 = testEq  "testDatatypeVal02" (Just 0) $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "0"
testDatatypeVal03 = testEq  "testDatatypeVal03" (Just 456) $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "+000456"
testDatatypeVal04 = testEq  "testDatatypeVal04" (Just (-987)) $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "-0987"
testDatatypeVal05 = testEq  "testDatatypeVal05" Nothing $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "11x2"
testDatatypeVal06 = testEq  "testDatatypeVal06" Nothing $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) " 321"
testDatatypeVal07 = testEq  "testDatatypeVal07" Nothing $
                        mapL2V (tvalMap rdfDatatypeValXsdInteger) "321 "

testDatatypeVal11 = testEq  "testDatatypeVal11" (Just "123") $
                        mapV2L (tvalMap rdfDatatypeValXsdInteger) 123
testDatatypeVal12 = testEq  "testDatatypeVal12" (Just "-987") $
                        mapV2L (tvalMap rdfDatatypeValXsdInteger) (-987)

testDatatypeVal21 = testElem "testDatatypeVal21" dmodXsdIntegerAbs $
                    map dmName (tvalMod rdfDatatypeValXsdInteger)
testDatatypeVal22 = testEq "testDatatypeVal22" dmodXsdIntegerAbs $
                    dmName (getXsdIntegerDTmod dmodXsdIntegerAbs)

testDatatypeValSuite = TestList
    [ testDatatypeVal01, testDatatypeVal02, testDatatypeVal03, testDatatypeVal04
    , testDatatypeVal05, testDatatypeVal06, testDatatypeVal07
    , testDatatypeVal11, testDatatypeVal12
    , testDatatypeVal21, testDatatypeVal22
    ]

------------------------------------------------------------
--  Variable binding modifier tests
------------------------------------------------------------

dmodXsdIntegerAbs    = xsd_int_name "abs"
dmodXsdIntegerNeg    = xsd_int_name "neg"
dmodXsdIntegerSum    = xsd_int_name "sum"
dmodXsdIntegerDiff   = xsd_int_name "diff"
dmodXsdIntegerProd   = xsd_int_name "prod"
dmodXsdIntegerDivMod = xsd_int_name "divmod"
dmodXsdIntegerPower  = xsd_int_name "power"
dmodXsdIntegerEq     = xsd_int_name "eq"
dmodXsdIntegerNe     = xsd_int_name "ne"
dmodXsdIntegerLt     = xsd_int_name "lt"
dmodXsdIntegerLe     = xsd_int_name "le"
dmodXsdIntegerGt     = xsd_int_name "gt"
dmodXsdIntegerGe     = xsd_int_name "ge"

testVmod2 = testVmodN [(Var "a"),(Var "b")]

testVmod3 = testVmodN [(Var "a"),(Var "b"),(Var "c")]

testVmod4 = testVmodN [(Var "a"),(Var "b"),(Var "c"),(Var "d")]

testVmodN :: [RDFLabel]
    -> String -> Maybe (RDFDatatypeMod Integer)
    -> [RDFVarBinding] -> [RDFVarBinding]
    -> Test
testVmodN vars lab (Just dmod) ibinds obinds =
    testEqv lab obinds $
        applyRDFDatatypeMod rdfDatatypeValXsdInteger dmod vars ibinds
testVmodN vars lab Nothing ibinds obinds = TestCase $
    assertFailure $ "testVmodN:"++lab++", null variable binding modifier"

--  make various kinds of RDF variable bindings
rdfVR (v,u) = (Var v,Res u)                     -- (Variable,Resource)
rdfVB (v,b) = (Var v,Blank b)                   -- (Variable,Blank)
rdfVL (v,l) = (Var v,Lit l Nothing)             -- (Variable,Untyped literal)
rdfVI (v,l) = (Var v,Lit l (Just typeNameXsdInteger))
                                                -- (Variable,Integer literal)

makeBVR :: [(String,ScopedName)] -> RDFVarBinding
makeBVR nls = makeVarBinding $ map rdfVR nls

makeBVB :: [(String,String)] -> RDFVarBinding
makeBVB nls = makeVarBinding $ map rdfVB nls

makeBVI :: [(String,String)] -> RDFVarBinding
makeBVI nls = makeVarBinding $ map rdfVI nls

makeBVL :: [(String,String)] -> RDFVarBinding
makeBVL nls = makeVarBinding $ map rdfVL nls

--  Test null modifier

testVarModify00 = testVmod2  "testVarModify00"
                    (Just nullDatatypeMod)
                    [makeBVI [("a","123")]]
                    [makeBVI [("a","123")]]

--  Tests for xsd_integer:abs

testVarModifyAbs01 = testVmod2  "testVarModifyAbs01"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("b","123")]]
                    [makeBVI [("a","123"),("b","123")]]

testVarModifyAbs02 = testVmod2  "testVarModifyAbs02"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("b","-123")]]
                    [makeBVI [("a","123"),("b","-123")]]

testVarModifyAbs03 = testVmod2  "testVarModifyAbs03"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("a","123"),("b","123")]]
                    [makeBVI [("a","123"),("b","123")]]

testVarModifyAbs04 = testVmod2  "testVarModifyAbs04"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("a","123"),("b","-123")]]
                    [makeBVI [("a","123"),("b","-123")]]

testVarModifyAbs05 = testVmod2  "testVarModifyAbs05"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-123"),("b","123")]]
                    []

testVarModifyAbs06 = testVmod2  "testVarModifyAbs06"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("a","123"),("b","456")]]
                    []

testVarModifyAbs07 = testVmod2  "testVarModifyAbs07"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVI [("c","123")]]
                    []

testVarModifyAbs08 = testVmod2  "testVarModifyAbs08"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVL [("b","123")]]
                    []

testVarModifyAbs09 = testVmod2  "testVarModifyAbs09"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVR [("b",makeScopedName "" "http://ex.org/" "123")]]
                    []

testVarModifyAbs10 = testVmod2  "testVarModifyAbs10"
                    (getDTMod dmodXsdIntegerAbs rdfDatatypeValXsdInteger)
                    [makeBVB [("b","123")]]
                    []

--  Tests for xsd_integer:neg

testVarModifyNeg01 = testVmod2  "testVarModifyNeg01"
                    (getDTMod dmodXsdIntegerNeg rdfDatatypeValXsdInteger)
                    [makeBVI [("a","123"),("b","-123")]]
                    [makeBVI [("a","123"),("b","-123")]]

testVarModifyNeg02 = testVmod2  "testVarModifyNeg02"
                    (getDTMod dmodXsdIntegerNeg rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-123"),("b","123")]]
                    [makeBVI [("a","-123"),("b","123")]]

testVarModifyNeg03 = testVmod2  "testVarModifyNeg03"
                    (getDTMod dmodXsdIntegerNeg rdfDatatypeValXsdInteger)
                    [makeBVI [("a","123"),("b","123")]]
                    []

testVarModifyNeg04 = testVmod2  "testVarModifyNeg04"
                    (getDTMod dmodXsdIntegerNeg rdfDatatypeValXsdInteger)
                    [makeBVI [("b","123")]]
                    [makeBVI [("a","-123"),("b","123")]]

testVarModifyNeg05 = testVmod2  "testVarModifyNeg05"
                    (getDTMod dmodXsdIntegerNeg rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-123")]]
                    [makeBVI [("a","-123"),("b","123")]]

--  Tests for xsd_integer:sum

testVarModifySum01 = testVmod3  "testVarModifySum01"
                    (getDTMod dmodXsdIntegerSum rdfDatatypeValXsdInteger)
                    [makeBVI [("a","33"),("b","22"),("c","11")]]
                    [makeBVI [("a","33"),("b","22"),("c","11")]]

testVarModifySum02 = testVmod3  "testVarModifySum02"
                    (getDTMod dmodXsdIntegerSum rdfDatatypeValXsdInteger)
                    [makeBVI [("b","22"),("c","11")]]
                    [makeBVI [("a","33"),("b","22"),("c","11")]]

testVarModifySum03 = testVmod3  "testVarModifySum03"
                    (getDTMod dmodXsdIntegerSum rdfDatatypeValXsdInteger)
                    [makeBVI [("a","33"),("c","11")]]
                    [makeBVI [("a","33"),("b","22"),("c","11")]]

testVarModifySum04 = testVmod3  "testVarModifySum04"
                    (getDTMod dmodXsdIntegerSum rdfDatatypeValXsdInteger)
                    [makeBVI [("a","33"),("b","22")]]
                    [makeBVI [("a","33"),("b","22"),("c","11")]]

testVarModifySum05 = testVmod3  "testVarModifySum05"
                    (getDTMod dmodXsdIntegerSum rdfDatatypeValXsdInteger)
                    [makeBVI [("a","44"),("b","22"),("c","11")]]
                    []

--  Tests for xsd_integer:diff

testVarModifyDiff01 = testVmod3  "testVarModifyDiff01"
                    (getDTMod dmodXsdIntegerDiff rdfDatatypeValXsdInteger)
                    [makeBVI [("a","11"),("b","33"),("c","22")]]
                    [makeBVI [("a","11"),("b","33"),("c","22")]]

testVarModifyDiff02 = testVmod3  "testVarModifyDiff02"
                    (getDTMod dmodXsdIntegerDiff rdfDatatypeValXsdInteger)
                    [makeBVI [("b","33"),("c","22")]]
                    [makeBVI [("a","11"),("b","33"),("c","22")]]

testVarModifyDiff03 = testVmod3  "testVarModifyDiff03"
                    (getDTMod dmodXsdIntegerDiff rdfDatatypeValXsdInteger)
                    [makeBVI [("a","11"),("c","22")]]
                    [makeBVI [("a","11"),("b","33"),("c","22")]]

testVarModifyDiff04 = testVmod3  "testVarModifyDiff04"
                    (getDTMod dmodXsdIntegerDiff rdfDatatypeValXsdInteger)
                    [makeBVI [("a","11"),("b","33")]]
                    [makeBVI [("a","11"),("b","33"),("c","22")]]

testVarModifyDiff05 = testVmod3  "testVarModifyDiff05"
                    (getDTMod dmodXsdIntegerDiff rdfDatatypeValXsdInteger)
                    [makeBVI [("a","11"),("b","44"),("c","22")]]
                    []

--  Tests for xsd_integer:prod
--
--  Note:   product can also be used to test if a value is
--          an exact multiple of some other.

testVarModifyProd01 = testVmod3  "testVarModifyProd01"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("a","6"),("b","2"),("c","3")]]
                    [makeBVI [("a","6"),("b","2"),("c","3")]]

testVarModifyProd02 = testVmod3  "testVarModifyProd02"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("b","2"),("c","3")]]
                    [makeBVI [("a","6"),("b","2"),("c","3")]]

testVarModifyProd03 = testVmod3  "testVarModifyProd03"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("a","6"),("c","3")]]
                    [makeBVI [("a","6"),("b","2"),("c","3")]]

testVarModifyProd04 = testVmod3  "testVarModifyProd04"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("a","6"),("c","3")]]
                    [makeBVI [("a","6"),("b","2"),("c","3")]]

testVarModifyProd05 = testVmod3  "testVarModifyProd05"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("a","7"),("b","2"),("c","3")]]
                    []

testVarModifyProd06 = testVmod3  "testVarModifyProd06"
                    (getDTMod dmodXsdIntegerProd rdfDatatypeValXsdInteger)
                    [makeBVI [("a","7"),("b","2")]]
                    []

--  Tests for xsd_integer:divmod
--
--  Note:   truncates downwards, so remainder is same sign as divisor
--          cf. Haskell divMod function.

testVarModifyDivMod01 = testVmod4  "testVarModifyDivMod01"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("a","2"),("b","1"),("c","7"),("d","3")]]
                    [makeBVI [("a","2"),("b","1"),("c","7"),("d","3")]]

testVarModifyDivMod02 = testVmod4  "testVarModifyDivMod02"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("c","7"),("d","3")]]
                    [makeBVI [("a","2"),("b","1"),("c","7"),("d","3")]]

testVarModifyDivMod03 = testVmod4  "testVarModifyDivMod03"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("c","-7"),("d","3")]]
                    [makeBVI [("a","-3"),("b","2"),("c","-7"),("d","3")]]

testVarModifyDivMod04 = testVmod4  "testVarModifyDivMod04"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("c","7"),("d","-3")]]
                    [makeBVI [("a","-3"),("b","-2"),("c","7"),("d","-3")]]

testVarModifyDivMod05 = testVmod4  "testVarModifyDivMod05"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("c","-7"),("d","-3")]]
                    [makeBVI [("a","2"),("b","-1"),("c","-7"),("d","-3")]]

testVarModifyDivMod06 = testVmod4  "testVarModifyDivMod06"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("a","2"),("b","5"),("c","7"),("d","3")]]
                    []

testVarModifyDivMod07 = testVmod4  "testVarModifyDivMod07"
                    (getDTMod dmodXsdIntegerDivMod rdfDatatypeValXsdInteger)
                    [makeBVI [("a","2"),("b","1"),("d","3")]]
                    []

--  Tests for xsd_integer:power

testVarModifyPower01 = testVmod3  "testVarModifyPower01"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("a","8"),("b","2"),("c","3")]]
                    [makeBVI [("a","8"),("b","2"),("c","3")]]

testVarModifyPower02 = testVmod3  "testVarModifyPower02"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("b","2"),("c","3")]]
                    [makeBVI [("a","8"),("b","2"),("c","3")]]

testVarModifyPower03 = testVmod3  "testVarModifyPower03"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("a","8"),("c","3")]]
                    []

testVarModifyPower04 = testVmod3  "testVarModifyPower04"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("a","8"),("b","2")]]
                    []

testVarModifyPower05 = testVmod3  "testVarModifyPower05"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("a","8"),("b","3"),("c","2")]]
                    []

testVarModifyPower06 = testVmod3  "testVarModifyPower06"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("b","55"),("c","0")]]
                    [makeBVI [("a","1"),("b","55"),("c","0")]]

testVarModifyPower07 = testVmod3  "testVarModifyPower07"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("b","-2"),("c","3")]]
                    [makeBVI [("a","-8"),("b","-2"),("c","3")]]

testVarModifyPower08 = testVmod3  "testVarModifyPower08"
                    (getDTMod dmodXsdIntegerPower rdfDatatypeValXsdInteger)
                    [makeBVI [("b","55"),("c","-2")]]
                    []

--  Tests for xsd_integer:eq

testVarModifyEq01 = testVmod2  "testVarModifyEq01"
                    (getDTMod dmodXsdIntegerEq rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    [makeBVI [("a","100"),("b","100")]]

testVarModifyEq02 = testVmod2  "testVarModifyEq02"
                    (getDTMod dmodXsdIntegerEq rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    []

testVarModifyEq03 = testVmod2  "testVarModifyEq03"
                    (getDTMod dmodXsdIntegerEq rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    []

testVarModifyEq04 = testVmod2  "testVarModifyEq04"
                    (getDTMod dmodXsdIntegerEq rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyEq05 = testVmod2  "testVarModifyEq05"
                    (getDTMod dmodXsdIntegerEq rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Tests for xsd_integer:ne

testVarModifyNe01 = testVmod2  "testVarModifyNe01"
                    (getDTMod dmodXsdIntegerNe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    []

testVarModifyNe02 = testVmod2  "testVarModifyNe02"
                    (getDTMod dmodXsdIntegerNe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    [makeBVI [("a","99"),("b","100")]]

testVarModifyNe03 = testVmod2  "testVarModifyNe03"
                    (getDTMod dmodXsdIntegerNe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    [makeBVI [("a","-99"),("b","-100")]]

testVarModifyNe04 = testVmod2  "testVarModifyNe04"
                    (getDTMod dmodXsdIntegerNe rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyNe05 = testVmod2  "testVarModifyNe05"
                    (getDTMod dmodXsdIntegerNe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Tests for xsd_integer:lt

testVarModifyLt01 = testVmod2  "testVarModifyLt01"
                    (getDTMod dmodXsdIntegerLt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    []

testVarModifyLt02 = testVmod2  "testVarModifyLt02"
                    (getDTMod dmodXsdIntegerLt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    [makeBVI [("a","99"),("b","100")]]

testVarModifyLt03 = testVmod2  "testVarModifyLt03"
                    (getDTMod dmodXsdIntegerLt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    []

testVarModifyLt04 = testVmod2  "testVarModifyLt04"
                    (getDTMod dmodXsdIntegerLt rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyLt05 = testVmod2  "testVarModifyLt05"
                    (getDTMod dmodXsdIntegerLt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Tests for xsd_integer:le

testVarModifyLe01 = testVmod2  "testVarModifyLe01"
                    (getDTMod dmodXsdIntegerLe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    [makeBVI [("a","100"),("b","100")]]

testVarModifyLe02 = testVmod2  "testVarModifyLe02"
                    (getDTMod dmodXsdIntegerLe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    [makeBVI [("a","99"),("b","100")]]

testVarModifyLe03 = testVmod2  "testVarModifyLe03"
                    (getDTMod dmodXsdIntegerLe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    []

testVarModifyLe04 = testVmod2  "testVarModifyLe04"
                    (getDTMod dmodXsdIntegerLe rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyLe05 = testVmod2  "testVarModifyLe05"
                    (getDTMod dmodXsdIntegerLe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Tests for xsd_integer:gt

testVarModifyGt01 = testVmod2  "testVarModifyGt01"
                    (getDTMod dmodXsdIntegerGt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    []

testVarModifyGt02 = testVmod2  "testVarModifyGt02"
                    (getDTMod dmodXsdIntegerGt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    []

testVarModifyGt03 = testVmod2  "testVarModifyGt03"
                    (getDTMod dmodXsdIntegerGt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    [makeBVI [("a","-99"),("b","-100")]]

testVarModifyGt04 = testVmod2  "testVarModifyGt04"
                    (getDTMod dmodXsdIntegerGt rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyGt05 = testVmod2  "testVarModifyGt05"
                    (getDTMod dmodXsdIntegerGt rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Tests for xsd_integer:ge

testVarModifyGe01 = testVmod2  "testVarModifyGe01"
                    (getDTMod dmodXsdIntegerGe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100"),("b","100")]]
                    [makeBVI [("a","100"),("b","100")]]

testVarModifyGe02 = testVmod2  "testVarModifyGe02"
                    (getDTMod dmodXsdIntegerGe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","99"),("b","100")]]
                    []

testVarModifyGe03 = testVmod2  "testVarModifyGe03"
                    (getDTMod dmodXsdIntegerGe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","-99"),("b","-100")]]
                    [makeBVI [("a","-99"),("b","-100")]]

testVarModifyGe04 = testVmod2  "testVarModifyGe04"
                    (getDTMod dmodXsdIntegerGe rdfDatatypeValXsdInteger)
                    [makeBVI [("b","100")]]
                    []

testVarModifyGe05 = testVmod2  "testVarModifyGe05"
                    (getDTMod dmodXsdIntegerGe rdfDatatypeValXsdInteger)
                    [makeBVI [("a","100")]]
                    []

--  Full suite for variable binding modifier tests

testVarModifySuite = TestList
    [ testVarModify00
    , testVarModifyAbs01,    testVarModifyAbs02,    testVarModifyAbs03
    , testVarModifyAbs04,    testVarModifyAbs05,    testVarModifyAbs06
    , testVarModifyAbs07,    testVarModifyAbs08,    testVarModifyAbs09
    , testVarModifyAbs10
    , testVarModifyNeg01,    testVarModifyNeg02,    testVarModifyNeg03
    , testVarModifyNeg04,    testVarModifyNeg05
    , testVarModifySum01,    testVarModifySum02,    testVarModifySum03
    , testVarModifySum04,    testVarModifySum05
    , testVarModifyDiff01,   testVarModifyDiff02,   testVarModifyDiff03
    , testVarModifyDiff04,   testVarModifyDiff05
    , testVarModifyProd01,   testVarModifyProd02,   testVarModifyProd03
    , testVarModifyProd04,   testVarModifyProd05,   testVarModifyProd06
    , testVarModifyDivMod01, testVarModifyDivMod02, testVarModifyDivMod03
    , testVarModifyDivMod04, testVarModifyDivMod05, testVarModifyDivMod06
    , testVarModifyDivMod07
    , testVarModifyPower01,  testVarModifyPower02,  testVarModifyPower03
    , testVarModifyPower04,  testVarModifyPower05,  testVarModifyPower06
    , testVarModifyPower07,  testVarModifyPower08
    , testVarModifyEq01,     testVarModifyEq02,     testVarModifyEq03
    , testVarModifyEq04,     testVarModifyEq05
    , testVarModifyNe01,     testVarModifyNe02,     testVarModifyNe03
    , testVarModifyNe04,     testVarModifyNe05
    , testVarModifyLt01,     testVarModifyLt02,     testVarModifyLt03
    , testVarModifyLt04,     testVarModifyLt05
    , testVarModifyLe01,     testVarModifyLe02,     testVarModifyLe03
    , testVarModifyLe04,     testVarModifyLe05
    , testVarModifyGt01,     testVarModifyGt02,     testVarModifyGt03
    , testVarModifyGt04,     testVarModifyGt05
    , testVarModifyGe01,     testVarModifyGe02,     testVarModifyGe03
    , testVarModifyGe04,     testVarModifyGe05
    ]

------------------------------------------------------------
--  Test rules defined for datatype
------------------------------------------------------------

mkGraph grstr = makeRDFGraphFromN3String (prefixXsdInteger++base++grstr)
    where
        base = "@prefix : <"++nsURI namespaceDefault++"> . \n"

testRuleFwd lab (Just rule) antstr constrs =
    let
        antgr  = mkGraph antstr
        congrs = map mkGraph constrs
    in
        testEqv lab congrs $ fwdApply rule [antgr]
testRuleFwd lab Nothing _ _ = TestCase $
    assertFailure $ "testRuleFwd:"++lab++", null rule supplied"

testRuleBwd lab (Just rule) antstr prestrss =
    let
        antgr   = mkGraph antstr
        pregrss = map (map mkGraph) prestrss
    in
        testEqvEqv lab pregrss $ bwdApply rule antgr
testRuleBwd lab Nothing _ _ = TestCase $
    assertFailure $ "testRuleBwd:"++lab++", null rule supplied"

testRuleChk lab (Just rule) antstr constr =
    let
        antgr = mkGraph antstr
        congr = mkGraph constr
    in
        test lab $ checkInference rule [antgr] congr
testRuleChk lab Nothing _ _ = TestCase $
    assertFailure $ "testRuleChk:"++lab++", null rule supplied"

xsdIntRules = (typeRules rdfDatatypeXsdInteger)

axdt        = getRulesetAxiom axiomXsdIntegerDT      xsdIntRules

ruleabs     = getRulesetRule  ruleXsdIntegerAbs      xsdIntRules
ruleneg     = getRulesetRule  ruleXsdIntegerNeg      xsdIntRules
rulesum     = getRulesetRule  ruleXsdIntegerSum      xsdIntRules
rulediff    = getRulesetRule  ruleXsdIntegerDiff     xsdIntRules
ruleprod    = getRulesetRule  ruleXsdIntegerProd     xsdIntRules
ruledivmod  = getRulesetRule  ruleXsdIntegerDivMod   xsdIntRules
rulepower   = getRulesetRule  ruleXsdIntegerPower    xsdIntRules
ruleeq      = getRulesetRule  ruleXsdIntegerEq       xsdIntRules
rulene      = getRulesetRule  ruleXsdIntegerNe       xsdIntRules
rulelt      = getRulesetRule  ruleXsdIntegerLt       xsdIntRules
rulele      = getRulesetRule  ruleXsdIntegerLe       xsdIntRules
rulegt      = getRulesetRule  ruleXsdIntegerGt       xsdIntRules
rulege      = getRulesetRule  ruleXsdIntegerGe       xsdIntRules

-- Test cases for the arithmetic functions

-- abs

abs01inp =
        "_:a a xsd_integer:Abs ; "
    +++ "  rdf:_2 \"1\"^^xsd:integer . "
abs01fwd =
    [ "_:a rdf:_1 \"1\"^^xsd:integer . " ]
abs01bwd = []
testRuleFwdAbs01 = testRuleFwd "testRuleFwdAbs01" ruleabs abs01inp abs01fwd
testRuleBwdAbs01 = testRuleBwd "testRuleBwdAbs01" ruleabs abs01inp abs01bwd

abs02inp =
        "_:a a xsd_integer:Abs ; "
    +++ "  rdf:_2 \"-1\"^^xsd:integer . "
abs02fwd =
    [ "_:a rdf:_1 \"1\"^^xsd:integer . " ]
abs02bwd =
    []
testRuleFwdAbs02 = testRuleFwd "testRuleFwdAbs02" ruleabs abs02inp abs02fwd
testRuleBwdAbs02 = testRuleBwd "testRuleBwdAbs02" ruleabs abs02inp abs02bwd

abs03inp =
        "_:a a xsd_integer:Abs ; "
    +++ "  rdf:_1 \"1\"^^xsd:integer . "
abs03fwd = []
abs03bwd =
    [ [ "_:a a xsd_integer:Abs . "
      , "_:a rdf:_2 \"1\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Abs . "
      , "_:a rdf:_2 \"-1\"^^xsd:integer . "
      ]
    ]
testRuleFwdAbs03 = testRuleFwd "testRuleFwdAbs03" ruleabs abs03inp abs03fwd
testRuleBwdAbs03 = testRuleBwd "testRuleBwdAbs03" ruleabs abs03inp abs03bwd

abs04inp =
        "_:a a xsd_integer:Abs ; "
    +++ "  rdf:_1 \"-1\"^^xsd:integer . "
abs04fwd =
    [ falseGraphStr
    ]
abs04bwd =
    [ [ falseGraphStr
      ]
    ]
testRuleFwdAbs04 = testRuleFwd "testRuleFwdAbs04" ruleabs abs04inp abs04fwd
testRuleBwdAbs04 = testRuleBwd "testRuleBwdAbs04" ruleabs abs04inp abs04bwd

-- neg

neg01inp =
        "_:a a xsd_integer:Neg ; "
    +++ "  rdf:_2 \"1\"^^xsd:integer . "
neg01fwd =
    [ "_:a rdf:_1 \"-1\"^^xsd:integer . " ]
neg01bwd =
    [ [ "_:a a xsd_integer:Neg . "
      , "_:a rdf:_1 \"-1\"^^xsd:integer . "
      ]
    ]
testRuleFwdNeg01 = testRuleFwd "testRuleFwdNeg01" ruleneg neg01inp neg01fwd
testRuleBwdNeg01 = testRuleBwd "testRuleBwdNeg01" ruleneg neg01inp neg01bwd

neg02inp =
        "_:a a xsd_integer:Neg ; "
    +++ "  rdf:_2 \"-2\"^^xsd:integer . "
neg02fwd =
    [ "_:a rdf:_1 \"2\"^^xsd:integer . " ]
neg02bwd =
    [ [ "_:a a xsd_integer:Neg . "
      , "_:a rdf:_1 \"2\"^^xsd:integer . "
      ]
    ]
testRuleFwdNeg02 = testRuleFwd "testRuleFwdNeg02" ruleneg neg02inp neg02fwd
testRuleBwdNeg02 = testRuleBwd "testRuleBwdNeg02" ruleneg neg02inp neg02bwd

-- sum

sum01inp =
        "_:a a xsd_integer:Sum ; "
    +++ "  rdf:_2 \"31\"^^xsd:integer ; "
    +++ "  rdf:_3 \"20\"^^xsd:integer . "
sum01fwd =
    [ "_:a rdf:_1 \"51\"^^xsd:integer . " ]
sum01bwd =
    [ [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_1 \"51\"^^xsd:integer . "
      , "_:a rdf:_2 \"31\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_1 \"51\"^^xsd:integer . "
      , "_:a rdf:_3 \"20\"^^xsd:integer . "
      ]
    ]
testRuleFwdSum01 = testRuleFwd "testRuleFwdSum01" rulesum sum01inp sum01fwd
testRuleBwdSum01 = testRuleBwd "testRuleBwdSum01" rulesum sum01inp sum01bwd

sum02inp =
        "_:a a xsd_integer:Sum ; "
    +++ "  rdf:_1 \"52\"^^xsd:integer ; "
    +++ "  rdf:_3 \"21\"^^xsd:integer . "
sum02fwd =
    [ "_:a rdf:_2 \"31\"^^xsd:integer . " ]
sum02bwd =
    [ [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_1 \"52\"^^xsd:integer . "
      , "_:a rdf:_2 \"31\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_2 \"31\"^^xsd:integer . "
      , "_:a rdf:_3 \"21\"^^xsd:integer . "
      ]
    ]
testRuleFwdSum02 = testRuleFwd "testRuleFwdSum02" rulesum sum02inp sum02fwd
testRuleBwdSum02 = testRuleBwd "testRuleBwdSum02" rulesum sum02inp sum02bwd

sum03inp =
        "_:a a xsd_integer:Sum ; "
    +++ "  rdf:_1 \"53\"^^xsd:integer ; "
    +++ "  rdf:_2 \"32\"^^xsd:integer . "
sum03fwd =
    [ "_:a rdf:_3 \"21\"^^xsd:integer . " ]
sum03bwd =
    [ [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_1 \"53\"^^xsd:integer . "
      , "_:a rdf:_3 \"21\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Sum . "
      , "_:a rdf:_2 \"32\"^^xsd:integer . "
      , "_:a rdf:_3 \"21\"^^xsd:integer . "
      ]
    ]
testRuleFwdSum03 = testRuleFwd "testRuleFwdSum03" rulesum sum03inp sum03fwd
testRuleBwdSum03 = testRuleBwd "testRuleBwdSum03" rulesum sum03inp sum03bwd

-- diff

diff01inp =
        "_:a a xsd_integer:Diff ; "
    +++ "  rdf:_2 \"222\"^^xsd:integer ; "
    +++ "  rdf:_3 \"333\"^^xsd:integer . "
diff01fwd =
    [ "_:a rdf:_1 \"-111\"^^xsd:integer . " ]
diff01bwd =
    [ [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_1 \"-111\"^^xsd:integer . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_1 \"-111\"^^xsd:integer . "
      , "_:a rdf:_3 \"333\"^^xsd:integer . "
      ]
    ]
testRuleFwdDiff01 = testRuleFwd "testRuleFwdDiff01" rulediff diff01inp diff01fwd
testRuleBwdDiff01 = testRuleBwd "testRuleBwdDiff01" rulediff diff01inp diff01bwd

diff02inp =
        "_:a a xsd_integer:Diff ; "
    +++ "  rdf:_1 \"-111\"^^xsd:integer ; "
    +++ "  rdf:_3 \"333\"^^xsd:integer . "
diff02fwd =
    [ "_:a rdf:_2 \"222\"^^xsd:integer . " ]
diff02bwd =
    [ [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_1 \"-111\"^^xsd:integer . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      , "_:a rdf:_3 \"333\"^^xsd:integer . "
      ]
    ]
testRuleFwdDiff02 = testRuleFwd "testRuleFwdDiff02" rulediff diff02inp diff02fwd
testRuleBwdDiff02 = testRuleBwd "testRuleBwdDiff02" rulediff diff02inp diff02bwd

diff03inp =
        "_:a a xsd_integer:Diff ; "
    +++ "  rdf:_1 \"-111\"^^xsd:integer ; "
    +++ "  rdf:_2 \"222\"^^xsd:integer . "
diff03fwd =
    [ "_:a rdf:_3 \"333\"^^xsd:integer . " ]
diff03bwd =
    [ [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_1 \"-111\"^^xsd:integer . "
      , "_:a rdf:_3 \"333\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Diff . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      , "_:a rdf:_3 \"333\"^^xsd:integer . "
      ]
    ]
testRuleFwdDiff03 = testRuleFwd "testRuleFwdDiff03" rulediff diff03inp diff03fwd
testRuleBwdDiff03 = testRuleBwd "testRuleBwdDiff03" rulediff diff03inp diff03bwd

-- prod

prod01inp =
        "_:a a xsd_integer:Prod ; "
    +++ "  rdf:_2 \"222\"^^xsd:integer ; "
    +++ "  rdf:_3 \"3\"^^xsd:integer . "
prod01fwd =
    [ "_:a rdf:_1 \"666\"^^xsd:integer . " ]
prod01bwd =
    [ [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_1 \"666\"^^xsd:integer . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_1 \"666\"^^xsd:integer . "
      , "_:a rdf:_3 \"3\"^^xsd:integer . "
      ]
    ]
testRuleFwdProd01 = testRuleFwd "testRuleFwdProd01" ruleprod prod01inp prod01fwd
testRuleBwdProd01 = testRuleBwd "testRuleBwdProd01" ruleprod prod01inp prod01bwd

prod02inp =
        "_:a a xsd_integer:Prod ; "
    +++ "  rdf:_1 \"666\"^^xsd:integer ; "
    +++ "  rdf:_3 \"3\"^^xsd:integer . "
prod02fwd =
    [ "_:a rdf:_2 \"222\"^^xsd:integer . " ]
prod02bwd =
    [ [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_1 \"666\"^^xsd:integer . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      , "_:a rdf:_3 \"3\"^^xsd:integer . "
      ]
    ]
testRuleFwdProd02 = testRuleFwd "testRuleFwdProd02" ruleprod prod02inp prod02fwd
testRuleBwdProd02 = testRuleBwd "testRuleBwdProd02" ruleprod prod02inp prod02bwd

prod03inp =
        "_:a a xsd_integer:Prod ; "
    +++ "  rdf:_1 \"666\"^^xsd:integer ; "
    +++ "  rdf:_2 \"222\"^^xsd:integer . "
prod03fwd =
    [ "_:a rdf:_3 \"3\"^^xsd:integer . " ]
prod03bwd =
    [ [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_1 \"666\"^^xsd:integer . "
      , "_:a rdf:_3 \"3\"^^xsd:integer . "
      ]
    , [ "_:a a xsd_integer:Prod . "
      , "_:a rdf:_2 \"222\"^^xsd:integer . "
      , "_:a rdf:_3 \"3\"^^xsd:integer . "
      ]
    ]
testRuleFwdProd03 = testRuleFwd "testRuleFwdProd03" ruleprod prod03inp prod03fwd
testRuleBwdProd03 = testRuleBwd "testRuleBwdProd03" ruleprod prod03inp prod03bwd

-- divmod

divmod01inp =
        "_:a a xsd_integer:DivMod ; "
    +++ "  rdf:_3 \"33\"^^xsd:integer ; "
    +++ "  rdf:_4 \"5\"^^xsd:integer . "
divmod01fwd =
    [     "_:a rdf:_1 \"6\"^^xsd:integer . "
      +++ "_:a rdf:_2 \"3\"^^xsd:integer . "
    ]
divmod01bwd =
    [ {- "_:a a xsd_integer:DivMod . "
      , "_:a rdf:_1 \"6\"^^xsd:integer . "
      , "_:a rdf:_2 \"3\"^^xsd:integer . "
      , "_:a rdf:_4 \"5\"^^xsd:integer . "
      -}
    ]
testRuleFwdDivMod01 = testRuleFwd "testRuleFwdDivMod01" ruledivmod divmod01inp divmod01fwd
testRuleBwdDivMod01 = testRuleBwd "testRuleBwdDivMod01" ruledivmod divmod01inp divmod01bwd

divmod02inp =
        "_:a a xsd_integer:DivMod ; "
    +++ "  rdf:_1 \"6\"^^xsd:integer ; "
    +++ "  rdf:_2 \"3\"^^xsd:integer ; "
    +++ "  rdf:_4 \"5\"^^xsd:integer . "
divmod02fwd =
    [ ]
divmod02bwd =
    [ {- "_:a a xsd_integer:DivMod . "
      , "_:a rdf:_3 \"33\"^^xsd:integer . "
      , "_:a rdf:_4 \"5\"^^xsd:integer . "
      -}
    ]
testRuleFwdDivMod02 = testRuleFwd "testRuleFwdDivMod02" ruledivmod divmod02inp divmod02fwd
testRuleBwdDivMod02 = testRuleBwd "testRuleBwdDivMod02" ruledivmod divmod02inp divmod02bwd

divmod03inp =
        "_:a a xsd_integer:DivMod ; "
    +++ "  rdf:_3 \"-33\"^^xsd:integer ; "
    +++ "  rdf:_4 \"5\"^^xsd:integer . "
divmod03fwd =
    [     "_:a rdf:_1 \"-7\"^^xsd:integer . "
      +++ "_:a rdf:_2 \"2\"^^xsd:integer . "
    ]
divmod03bwd =
    [ ]
testRuleFwdDivMod03 = testRuleFwd "testRuleFwdDivMod03" ruledivmod divmod03inp divmod03fwd
testRuleBwdDivMod03 = testRuleBwd "testRuleBwdDivMod03" ruledivmod divmod03inp divmod03bwd

-- power

power01inp =
        "_:a a xsd_integer:Power ; "
    +++ "  rdf:_2 \"2\"^^xsd:integer ; "
    +++ "  rdf:_3 \"5\"^^xsd:integer . "
power01fwd =
    [ "_:a rdf:_1 \"32\"^^xsd:integer . " ]
power01bwd =
    [ ]
testRuleFwdPower01 = testRuleFwd "testRuleFwdPower01" rulepower power01inp power01fwd
testRuleBwdPower01 = testRuleBwd "testRuleBwdPower01" rulepower power01inp power01bwd

power02inp =
        "_:a a xsd_integer:Power ; "
    +++ "  rdf:_2 \"111\"^^xsd:integer ; "
    +++ "  rdf:_3 \"0\"^^xsd:integer . "
power02fwd =
    [ "_:a rdf:_1 \"1\"^^xsd:integer . " ]
power02bwd =
    [ ]
testRuleFwdPower02 = testRuleFwd "testRuleFwdPower02" rulepower power02inp power02fwd
testRuleBwdPower02 = testRuleBwd "testRuleBwdPower02" rulepower power02inp power02bwd

power03inp =
        "_:a a xsd_integer:Power ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer ; "
    +++ "  rdf:_3 \"-33\"^^xsd:integer . "
power03fwd =
    [ falseGraphStr ]
power03bwd =
    [ [ falseGraphStr ]
    ]
testRuleFwdPower03 = testRuleFwd "testRuleFwdPower03" rulepower power03inp power03fwd
testRuleBwdPower03 = testRuleBwd "testRuleBwdPower03" rulepower power03inp power03bwd

-- eq

eq01inp =
        "_:a a xsd_integer:Eq ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
eq01fwd = [ ]
eq01bwd = [ ]
testRuleFwdEq01 = testRuleFwd "testRuleFwdEq01" ruleeq eq01inp eq01fwd
testRuleBwdEq01 = testRuleBwd "testRuleBwdEq01" ruleeq eq01inp eq01bwd

eq02inp =
        "_:a a xsd_integer:Eq ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
eq02fwd = [ falseGraphStr ]
eq02bwd = [ [falseGraphStr] ]
testRuleFwdEq02 = testRuleFwd "testRuleFwdEq02" ruleeq eq02inp eq02fwd
testRuleBwdEq02 = testRuleBwd "testRuleBwdEq02" ruleeq eq02inp eq02bwd

eq03inp =
        "_:a a xsd_integer:Eq ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
eq03fwd = [ falseGraphStr ]
eq03bwd = [ [falseGraphStr] ]
testRuleFwdEq03 = testRuleFwd "testRuleFwdEq03" ruleeq eq03inp eq03fwd
testRuleBwdEq03 = testRuleBwd "testRuleBwdEq03" ruleeq eq03inp eq03bwd

-- ne

ne01inp =
        "_:a a xsd_integer:Ne ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
ne01fwd = [ falseGraphStr ]
ne01bwd = [ [falseGraphStr] ]
testRuleFwdNe01 = testRuleFwd "testRuleFwdNe01" rulene ne01inp ne01fwd
testRuleBwdNe01 = testRuleBwd "testRuleBwdNe01" rulene ne01inp ne01bwd

ne02inp =
        "_:a a xsd_integer:Ne ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
ne02fwd = [ ]
ne02bwd = [ ]
testRuleFwdNe02 = testRuleFwd "testRuleFwdNe02" rulene ne02inp ne02fwd
testRuleBwdNe02 = testRuleBwd "testRuleBwdNe02" rulene ne02inp ne02bwd

ne03inp =
        "_:a a xsd_integer:Ne ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
ne03fwd = [ ]
ne03bwd = [ ]
testRuleFwdNe03 = testRuleFwd "testRuleFwdNe03" rulene ne03inp ne03fwd
testRuleBwdNe03 = testRuleBwd "testRuleBwdNe03" rulene ne03inp ne03bwd

-- lt

lt01inp =
        "_:a a xsd_integer:Lt ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
lt01fwd = [ falseGraphStr ]
lt01bwd = [ [falseGraphStr] ]
testRuleFwdLt01 = testRuleFwd "testRuleFwdLt01" rulelt lt01inp lt01fwd
testRuleBwdLt01 = testRuleBwd "testRuleBwdLt01" rulelt lt01inp lt01bwd

lt02inp =
        "_:a a xsd_integer:Lt ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
lt02fwd = [ ]
lt02bwd = [ ]
testRuleFwdLt02 = testRuleFwd "testRuleFwdLt02" rulelt lt02inp lt02fwd
testRuleBwdLt02 = testRuleBwd "testRuleBwdLt02" rulelt lt02inp lt02bwd

lt03inp =
        "_:a a xsd_integer:Lt ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
lt03fwd = [ falseGraphStr ]
lt03bwd = [ [falseGraphStr] ]
testRuleFwdLt03 = testRuleFwd "testRuleFwdLt03" rulelt lt03inp lt03fwd
testRuleBwdLt03 = testRuleBwd "testRuleBwdLt03" rulelt lt03inp lt03bwd

-- le

le01inp =
        "_:a a xsd_integer:Le ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
le01fwd = [ ]
le01bwd = [ ]
testRuleFwdLe01 = testRuleFwd "testRuleFwdLe01" rulele le01inp le01fwd
testRuleBwdLe01 = testRuleBwd "testRuleBwdLe01" rulele le01inp le01bwd

le02inp =
        "_:a a xsd_integer:Le ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
le02fwd = [ ]
le02bwd = [ ]
testRuleFwdLe02 = testRuleFwd "testRuleFwdLe02" rulele le02inp le02fwd
testRuleBwdLe02 = testRuleBwd "testRuleBwdLe02" rulele le02inp le02bwd

le03inp =
        "_:a a xsd_integer:Le ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
le03fwd = [ falseGraphStr ]
le03bwd = [ [falseGraphStr] ]
testRuleFwdLe03 = testRuleFwd "testRuleFwdLe03" rulele le03inp le03fwd
testRuleBwdLe03 = testRuleBwd "testRuleBwdLe03" rulele le03inp le03bwd

-- gt

gt01inp =
        "_:a a xsd_integer:Gt ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
gt01fwd = [ falseGraphStr ]
gt01bwd = [ [falseGraphStr] ]
testRuleFwdGt01 = testRuleFwd "testRuleFwdGt01" rulegt gt01inp gt01fwd
testRuleBwdGt01 = testRuleBwd "testRuleBwdGt01" rulegt gt01inp gt01bwd

gt02inp =
        "_:a a xsd_integer:Gt ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
gt02fwd = [ falseGraphStr ]
gt02bwd = [ [falseGraphStr] ]
testRuleFwdGt02 = testRuleFwd "testRuleFwdGt02" rulegt gt02inp gt02fwd
testRuleBwdGt02 = testRuleBwd "testRuleBwdGt02" rulegt gt02inp gt02bwd

gt03inp =
        "_:a a xsd_integer:Gt ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
gt03fwd = [ ]
gt03bwd = [ ]
testRuleFwdGt03 = testRuleFwd "testRuleFwdGt03" rulegt gt03inp gt03fwd
testRuleBwdGt03 = testRuleBwd "testRuleBwdGt03" rulegt gt03inp gt03bwd

-- ge

ge01inp =
        "_:a a xsd_integer:Ge ; "
    +++ "  rdf:_1 \"11\"^^xsd:integer ; "
    +++ "  rdf:_2 \"11\"^^xsd:integer . "
ge01fwd = [ ]
ge01bwd = [ ]
testRuleFwdGe01 = testRuleFwd "testRuleFwdGe01" rulege ge01inp ge01fwd
testRuleBwdGe01 = testRuleBwd "testRuleBwdGe01" rulege ge01inp ge01bwd

ge02inp =
        "_:a a xsd_integer:Ge ; "
    +++ "  rdf:_1 \"21\"^^xsd:integer ; "
    +++ "  rdf:_2 \"22\"^^xsd:integer . "
ge02fwd = [ falseGraphStr ]
ge02bwd = [ [falseGraphStr] ]
testRuleFwdGe02 = testRuleFwd "testRuleFwdGe02" rulege ge02inp ge02fwd
testRuleBwdGe02 = testRuleBwd "testRuleBwdGe02" rulege ge02inp ge02bwd

ge03inp =
        "_:a a xsd_integer:Ge ; "
    +++ "  rdf:_1 \"31\"^^xsd:integer ; "
    +++ "  rdf:_2 \"-32\"^^xsd:integer . "
ge03fwd = [ ]
ge03bwd = [ ]
testRuleFwdGe03 = testRuleFwd "testRuleFwdGe03" rulege ge03inp ge03fwd
testRuleBwdGe03 = testRuleBwd "testRuleBwdGe03" rulege ge03inp ge03bwd

-- Test cases from design notes

infixr 5 +++
(+++) :: String -> ShowS
(+++) str = ((str++"\n")++)

-- Make a vector of rules using the graph string below

pvRules :: [RDFRule]
-- pvRules = makeRDFDatatypeRestrictionRules rdfDatatypeValXsdInteger gr
pvRules = typeMkRules rdfDatatypeXsdInteger gr
    where
        gr = (mkGraph pvRulesStr)

pvRulesStr =
        ":PassengerVehicle a rdfd:GeneralRestriction ; "
    +++ "  rdfd:onProperties (:totalCapacity :seatedCapacity :standingCapacity) ; "
    +++ "  rdfd:constraint xsd_integer:sum . "
    +++ ":PassengerVehicle1 a rdfd:GeneralRestriction ; "
    +++ "  rdfd:onProperties (:totalCapacity :seatedCapacity :standingCapacity) ; "
    +++ "  rdfd:constraint xsd_integer:sum ; "
    +++ "  rdfd:maxCardinality \"1\"^^xsd:nonNegativeInteger . "

--  Now the test cases that use the rules created above.

pvRule0 = mapFindMaybe
            (ScopedName namespaceDefault "PassengerVehicle")
            (LookupMap pvRules)
pvRule1 = mapFindMaybe
            (ScopedName namespaceDefault "PassengerVehicle1")
            (LookupMap pvRules)

pv01inp =
        "_:a a :PassengerVehicle ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :standingCapacity \"20\"^^xsd:integer . "
pv01fwd =
    [ "_:a :totalCapacity \"50\"^^xsd:integer . " ]
pv01bwd =
    [ [ "_:a a :PassengerVehicle . "
      , "_:a :totalCapacity \"50\"^^xsd:integer . "
      , "_:a :seatedCapacity \"30\"^^xsd:integer . "
      ]
    , [ "_:a a :PassengerVehicle . "
      , "_:a :totalCapacity \"50\"^^xsd:integer . "
      , "_:a :standingCapacity \"20\"^^xsd:integer . "
      ]
    ]
testRuleFwdPv01 = testRuleFwd "testRuleFwdPv01" pvRule0 pv01inp pv01fwd
testRuleBwdPv01 = testRuleBwd "testRuleBwdPv01" pvRule0 pv01inp pv01bwd

pv02inp =
        "_:a a :PassengerVehicle ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :totalCapacity \"51\"^^xsd:integer . "
    +++ "_:b a :PassengerVehicle ; "
    +++ "  :standingCapacity \"20\"^^xsd:integer ; "
    +++ "  :totalCapacity \"52\"^^xsd:integer . "
pv02fwd =
    [ "_:a :standingCapacity \"21\"^^xsd:integer . "
    , "_:b :seatedCapacity \"32\"^^xsd:integer . "
    ]
pv02bwd =
    [ [ "_:a a :PassengerVehicle . "
      , "_:a :standingCapacity \"21\"^^xsd:integer . "
      , "_:a :totalCapacity \"51\"^^xsd:integer . "
      , "_:b a :PassengerVehicle . "
      , "_:b :seatedCapacity \"32\"^^xsd:integer . "
      , "_:b :totalCapacity \"52\"^^xsd:integer . "
      ]
    , [ "_:a a :PassengerVehicle . "
      , "_:a :seatedCapacity \"30\"^^xsd:integer . "
      , "_:a :standingCapacity \"21\"^^xsd:integer . "
      , "_:b a :PassengerVehicle . "
      , "_:b :seatedCapacity \"32\"^^xsd:integer . "
      , "_:b :totalCapacity \"52\"^^xsd:integer . "
      ]
    , [ "_:a a :PassengerVehicle . "
      , "_:a :standingCapacity \"21\"^^xsd:integer . "
      , "_:a :totalCapacity \"51\"^^xsd:integer . "
      , "_:b a :PassengerVehicle . "
      , "_:b :seatedCapacity \"32\"^^xsd:integer . "
      , "_:b :standingCapacity \"20\"^^xsd:integer . "
      ]
    , [ "_:a a :PassengerVehicle . "
      , "_:a :seatedCapacity \"30\"^^xsd:integer . "
      , "_:a :standingCapacity \"21\"^^xsd:integer . "
      , "_:b a :PassengerVehicle . "
      , "_:b :seatedCapacity \"32\"^^xsd:integer . "
      , "_:b :standingCapacity \"20\"^^xsd:integer . "
      ]
    ]
testRuleFwdPv02 = testRuleFwd "testRuleFwdPv02" pvRule0 pv02inp pv02fwd
testRuleBwdPv02 = testRuleBwd "testRuleBwdPv02" pvRule0 pv02inp pv02bwd

pv03inp =
        "_:a a :PassengerVehicle ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :standingCapacity \"23\"^^xsd:integer ; "
    +++ "  :totalCapacity \"53\"^^xsd:integer . "
pv03fwd = []
testRuleFwdPv03 = testRuleFwd "testRuleFwdPv03" pvRule0 pv03inp pv03fwd

pv04inp =
        "_:a a :PassengerVehicle ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :standingCapacity \"20\"^^xsd:integer ; "
    +++ "  :totalCapacity \"54\"^^xsd:integer . "
pv04fwd =
    [     "_:a :standingCapacity \"24\"^^xsd:integer . "
      +++ "_:a :seatedCapacity \"34\"^^xsd:integer . "
      +++ "_:a :totalCapacity \"50\"^^xsd:integer . "
    ]
testRuleFwdPv04 = testRuleFwd "testRuleFwdPv04" pvRule0 pv04inp pv04fwd

pv05inp =
        "_:a a :PassengerVehicle1 ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :standingCapacity \"25\"^^xsd:integer ; "
    +++ "  :totalCapacity \"55\"^^xsd:integer . "
pv05fwd = []
testRuleFwdPv05 = testRuleFwd "testRuleFwdPv05" pvRule1 pv05inp pv05fwd

pv06inp =
        "_:a a :PassengerVehicle1 ; "
    +++ "  :seatedCapacity \"30\"^^xsd:integer ; "
    +++ "  :standingCapacity \"20\"^^xsd:integer ; "
    +++ "  :totalCapacity \"56\"^^xsd:integer . "
pv06fwd =
    [ falseGraphStr
    ]
pv06bwd =
    [ [ falseGraphStr
      ]
    ]
testRuleFwdPv06 = testRuleFwd "testRuleFwdPv06" pvRule1 pv06inp pv06fwd
testRuleBwdPv06 = testRuleBwd "testRuleBwdPv06" pvRule1 pv06inp pv06bwd

pv07inp =
        "_:a a :PassengerVehicle ; "
    +++ "  :totalCapacity \"57\"^^xsd:integer . "
pv07fwd = []
pv07bwd = []
testRuleFwdPv07 = testRuleFwd "testRuleFwdPv07" pvRule0 pv07inp pv07fwd
testRuleBwdPv07 = testRuleFwd "testRuleBwdPv07" pvRule0 pv07inp pv07bwd

--  Full suite for datatype rule tests

testDatatypeRuleSuite = TestList
    [ testRuleFwdAbs01, testRuleFwdAbs02, testRuleFwdAbs03, testRuleFwdAbs04
    , testRuleFwdNeg01, testRuleFwdNeg02
    , testRuleFwdSum01, testRuleFwdSum02, testRuleFwdSum03
    , testRuleFwdDiff01, testRuleFwdDiff02, testRuleFwdDiff03
    , testRuleFwdProd01, testRuleFwdProd02, testRuleFwdProd03
    , testRuleFwdDivMod01, testRuleFwdDivMod02, testRuleFwdDivMod03
    , testRuleFwdPower01, testRuleFwdPower02, testRuleFwdPower03
    , testRuleFwdEq01, testRuleFwdEq02, testRuleFwdEq03
    , testRuleFwdNe01, testRuleFwdNe02, testRuleFwdNe03
    , testRuleFwdLt01, testRuleFwdLt02, testRuleFwdLt03
    , testRuleFwdLe01, testRuleFwdLe02, testRuleFwdLe03
    , testRuleFwdGt01, testRuleFwdGt02, testRuleFwdGt03
    , testRuleFwdGe01, testRuleFwdGe02, testRuleFwdGe03
    -- backard chaining tests
    , testRuleBwdAbs01, testRuleBwdAbs02, testRuleBwdAbs03, testRuleBwdAbs04
    , testRuleBwdNeg01, testRuleBwdNeg02
    , testRuleBwdSum01, testRuleBwdSum02, testRuleBwdSum03
    , testRuleBwdDiff01, testRuleBwdDiff02, testRuleBwdDiff03
    , testRuleBwdProd01, testRuleBwdProd02, testRuleBwdProd03
    , testRuleBwdDivMod01, testRuleBwdDivMod02, testRuleBwdDivMod03
    , testRuleBwdPower01, testRuleBwdPower02, testRuleBwdPower03
    , testRuleBwdEq01, testRuleBwdEq02, testRuleBwdEq03
    , testRuleBwdNe01, testRuleBwdNe02, testRuleBwdNe03
    , testRuleBwdLt01, testRuleBwdLt02, testRuleBwdLt03
    , testRuleBwdLe01, testRuleBwdLe02, testRuleBwdLe03
    , testRuleBwdGt01, testRuleBwdGt02, testRuleBwdGt03
    , testRuleBwdGe01, testRuleBwdGe02, testRuleBwdGe03
    -- test cases from design notes
    , testRuleFwdPv01, testRuleFwdPv02, testRuleFwdPv03, testRuleFwdPv04
    , testRuleFwdPv05, testRuleFwdPv06, testRuleFwdPv07
    , testRuleBwdPv01, testRuleBwdPv02, testRuleBwdPv06, testRuleBwdPv07
    ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
    [ testDatatypeSuite
    , testDatatypeValSuite
    , testVarModifySuite
    , testDatatypeRuleSuite
    ]

main = runTestTT allTests
trules = runTestTT testDatatypeRuleSuite

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
-- $Source: /file/cvsdev/HaskellRDF/RDFDatatypeXsdIntegerTest.hs,v $
-- $Author: graham $
-- $Revision: 1.13 $
-- $Log: RDFDatatypeXsdIntegerTest.hs,v $
-- Revision 1.13  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.12  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.11  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.10  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.9  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.8  2003/11/28 00:17:55  graham
-- Datatype constraint test cases all passed.
--
-- Revision 1.7  2003/11/27 11:35:49  graham
-- Variable modifier tests all run.
-- Initial class constraint reasoning tests pass.
-- Fixed bug in class constraint backward-chained reasoning that returned
-- multiple instances of some statements, and did not filter out all occurrences
-- of the original statements.
--
-- Revision 1.6  2003/11/25 23:02:17  graham
-- Reworked datatype variable modifier logic.
-- Limited range of test cases so far all pass.
--
-- Revision 1.5  2003/11/24 22:13:09  graham
-- Working on reworking datatype variable modifiers to work with
-- revised datatype framework.
--
-- Revision 1.4  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.3  2003/11/11 21:02:55  graham
-- Working on datatype class-constraint inference rule.  Incomplete.
--
-- Revision 1.2  2003/11/07 21:45:47  graham
-- Started rework of datatype to use new DatatypeRel structure.
--
-- Revision 1.1  2003/10/24 21:05:09  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
