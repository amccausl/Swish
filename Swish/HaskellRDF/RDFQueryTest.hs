--------------------------------------------------------------------------------
--  $Id: RDFQueryTest.hs,v 1.23 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFQueryTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + multi-parameter classes
--
--  This module defines test cases for querying an RDF graph to obtain
--  a set of variable substitutions, and to apply a set of variable
--  substitutions to a query pattern to obtain a new graph.
--
--  It also tests some primitive graph access functions.
--
--------------------------------------------------------------------------------

--  WNH RIP OUT module Swish.HaskellRDF.RDFQueryTest where

import Swish.HaskellRDF.RDFQuery
    ( rdfQueryFind, rdfQueryFilter
    , rdfQueryBack, rdfQueryBackFilter, rdfQueryBackModify
    , rdfQueryInstance
    , rdfQuerySubs, rdfQueryBackSubs
    , rdfQuerySubsAll
    , rdfQuerySubsBlank, rdfQueryBackSubsBlank
    , rdfFindArcs, rdfSubjEq, rdfPredEq, rdfObjEq, rdfFindPredVal
    , rdfFindValSubj, rdfFindPredVal, rdfFindPredInt, rdfFindList
    -- debug
    , rdfQuerySubs2
    )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding, nullRDFVarBinding
    , RDFVarBindingModify, RDFVarBindingFilter
    , rdfVarBindingUriRef, rdfVarBindingBlank
    , rdfVarBindingLiteral
    , rdfVarBindingUntypedLiteral, rdfVarBindingTypedLiteral
    , rdfVarBindingXMLLiteral, rdfVarBindingDatatyped
    , rdfVarBindingMemberProp
    )

import Swish.HaskellRDF.RDFGraph
    ( Arc(..), arcSubj
    , RDFGraph, RDFLabel(..)
    , isLiteral, isBlank, isQueryVar, makeBlank
    , setArcs, getArcs, addArc, add, delete, extract, labels, merge
    , allLabels, remapLabels
    , mapnode, maplist
    , res_rdf_type, res_rdf_first, res_rdf_rest, res_rdf_nil
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..), nullVarBinding
    , boundVars, subBinding, makeVarBinding
    , applyVarBinding, joinVarBindings
    , VarBindingModify(..)
    , vbmCompatibility, vbmCompose
    , findCompositions, findComposition
    , VarBindingFilter(..)
    , makeVarFilterModify
    , makeVarTestFilter, makeVarCompareFilter
    , varBindingId, varFilterDisjunction, varFilterConjunction
    , varFilterEQ, varFilterNE
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , makeNamespaceQName
    , ScopedName(..)
    , getQName
    , makeScopedName
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceXSD
    , namespaceLang, langName
    , swishName
    , rdf_type, rdf_XMLLiteral
    , xsd_boolean, xsd_integer
    )

import Swish.HaskellRDF.N3Parser
    ( ParseResult(..), parseN3fromString )

import Swish.HaskellUtils.QName
    ( QName(..) )

import Swish.HaskellUtils.ListHelpers
    ( equiv )

import Swish.HaskellUtils.ErrorM
    ( ErrorM(Error,Result) )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

import Data.Maybe
    ( isJust, fromJust )

------------------------------------------------------------
--  misc helpers
------------------------------------------------------------

newtype Set a = Set [a] deriving Show
instance (Eq a) => Eq (Set a) where
    Set v1 == Set v2 = v1 `equiv` v2

test :: String -> Bool -> Test
test lab tst = TestCase $ assertBool lab tst

testEq :: (Eq a, Show a) => String -> a -> a -> Test
testEq lab e a = TestCase $ assertEqual lab e a

testLs :: (Eq a, Show a) => String -> [a] -> [a] -> Test
testLs lab e a = TestCase $ assertEqual lab (Set e) (Set a)

testGr :: String -> String -> [RDFGraph] -> Test
testGr lab e a = TestCase $ assertBool lab (eg `elem` a)
    where eg = graphFromString e

graphFromString :: String -> RDFGraph
graphFromString str = case parseN3fromString str of
    Result gr -> gr
    Error msg -> error msg

-- Compare lists for set equivalence:

data ListTest a = ListTest [a]

instance (Eq a) => Eq (ListTest a) where
    (ListTest a1) == (ListTest a2) = a1 `equiv` a2

instance (Show a) => Show (ListTest a) where
    show (ListTest a) = show a

testEqv :: (Eq a, Show a) => String -> [a] -> [a] -> Test
testEqv lab a1 a2 =
    TestCase ( assertEqual ("testEqv:"++lab) (ListTest a1) (ListTest a2) )

------------------------------------------------------------
--  test1:  simple query qith URI, literal and blank nodes.
------------------------------------------------------------

prefix1 =
    "@prefix ex: <http://example.org/> . \n" ++
    " \n"

graph1    = graphFromString graph1str
graph1str = prefix1 ++
    "ex:s1  ex:p  ex:o1 . \n"  ++
    "ex:s2  ex:p  \"lit1\" . \n" ++
    "[ ex:p ex:o3 ] . \n"

query11    = graphFromString query11str
query11str = prefix1 ++
    "?s  ex:p  ?o . \n"

result11    = graphFromString result11str
result11str = prefix1 ++
    "?s  ex:r  ?o . \n"

result11a = prefix1 ++
    "ex:s1  ex:r  ex:o1 . \n"

result11b = prefix1 ++
    "ex:s2  ex:r  \"lit1\" . \n"

result11c = prefix1 ++
    "[ ex:r ex:o3 ] . \n"

var11         = rdfQueryFind query11 graph1
testQuery11   = test "testQuery11" (not $ null var11)
res11         = rdfQuerySubs var11 result11
testResult11  = testEq "testResult11" 3 (length res11)
testResult11a = testGr "testResult11a" result11a res11
testResult11b = testGr "testResult11b" result11b res11
testResult11c = testGr "testResult11c" result11c res11

test1 = TestList
    [ testQuery11,   testResult11
    , testResult11a, testResult11b, testResult11c
    ]

------------------------------------------------------------
--  test2:  a range of more complex queries based on a
--  single relationship graph.
------------------------------------------------------------

prefix2 =
    "@prefix pers: <urn:pers:> . \n"      ++
    "@prefix rel:  <urn:rel:> . \n"       ++
    " \n"

graph2    = graphFromString graph2str
graph2str = prefix2 ++
    "pers:St1 rel:wife     pers:Do1 ; \n" ++
    "         rel:daughter pers:Ma2 ; \n" ++
    "         rel:daughter pers:An2 . \n" ++
    "pers:Pa2 rel:wife     pers:Ma2 ; \n" ++
    "         rel:son      pers:Gr3 ; \n" ++
    "         rel:son      pers:La3 ; \n" ++
    "         rel:son      pers:Si3 ; \n" ++
    "         rel:son      pers:Al3 . \n" ++
    "pers:Br2 rel:wife     pers:Ri2 ; \n" ++
    "         rel:daughter pers:Ma3 ; \n" ++
    "         rel:son      pers:Wi3 . \n" ++
    "pers:Gr3 rel:wife     pers:Ma3 ; \n" ++
    "         rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter pers:Rh4 . \n" ++
    "pers:Si3 rel:wife     pers:Jo3 ; \n" ++
    "         rel:son      pers:Ol4 ; \n" ++
    "         rel:son      pers:Lo4 . \n" ++
    "pers:Al3 rel:wife     pers:Su3 ; \n" ++
    "         rel:son      pers:Ha4 ; \n" ++
    "         rel:son      pers:El4 . \n"

query21    = graphFromString query21str
query21str = prefix2 ++
    "?a rel:wife ?b . \n"

result21    = graphFromString result21str
result21str = prefix2 ++
    "?b rel:husband ?a . \n"

result21a = prefix2 ++
    "pers:Do1 rel:husband pers:St1 . \n"

result21b = prefix2 ++
    "pers:Ma2 rel:husband pers:Pa2 . \n"

result21c = prefix2 ++
    "pers:Ri2 rel:husband pers:Br2 . \n"

result21d = prefix2 ++
    "pers:Ma3 rel:husband pers:Gr3 . \n"

result21e = prefix2 ++
    "pers:Jo3 rel:husband pers:Si3 . \n"

result21f = prefix2 ++
    "pers:Su3 rel:husband pers:Al3 . \n"

var21         = rdfQueryFind query21 graph2
testQuery21   = test "testQuery21" (not $ null var21)
res21         = rdfQuerySubs var21 result21
testResult21  = testEq "testResult21" 6 (length res21)
testResult21a = testGr "testResult21a" result21a res21
testResult21b = testGr "testResult21b" result21b res21
testResult21c = testGr "testResult21c" result21c res21
testResult21d = testGr "testResult21d" result21d res21
testResult21e = testGr "testResult21e" result21e res21
testResult21f = testGr "testResult21f" result21f res21

query22    = graphFromString query22str
query22str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?b rel:son ?c . \n"

result22    = graphFromString result22str
result22str = prefix2 ++
    "?a rel:grandparent ?c . \n"

result22a = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ro4 . \n"

result22b = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ol4 . \n"

result22c = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Lo4 . \n"

result22d = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ha4 . \n"

result22e = prefix2 ++
    "pers:Pa2 rel:grandparent pers:El4 . \n"

var22         = rdfQueryFind query22 graph2
testQuery22   = test "testQuery22" (not $ null var22)
res22         = rdfQuerySubs var22 result22
testResult22  = testEq "testResult22" 5 (length res22)
testResult22a = testGr "testResult22a" result22a res22
testResult22b = testGr "testResult22b" result22b res22
testResult22c = testGr "testResult22c" result22c res22
testResult22d = testGr "testResult22d" result22d res22
testResult22e = testGr "testResult22e" result22e res22

query23    = graphFromString query23str
query23str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result23    = graphFromString result23str
result23str = prefix2 ++
    "?b rel:brother ?c . \n"

result23a = prefix2 ++
    "pers:Gr3 rel:brother pers:Gr3 . \n"

result23b = prefix2 ++
    "pers:Gr3 rel:brother pers:La3 . \n"

result23c = prefix2 ++
    "pers:Gr3 rel:brother pers:Si3 . \n"

result23d = prefix2 ++
    "pers:Gr3 rel:brother pers:Al3 . \n"

result23e = prefix2 ++
    "pers:La3 rel:brother pers:Gr3 . \n"

result23f = prefix2 ++
    "pers:La3 rel:brother pers:La3 . \n"

result23g = prefix2 ++
    "pers:La3 rel:brother pers:Si3 . \n"

result23h = prefix2 ++
    "pers:La3 rel:brother pers:Al3 . \n"

result23i = prefix2 ++
    "pers:Si3 rel:brother pers:Gr3 . \n"

result23j = prefix2 ++
    "pers:Si3 rel:brother pers:La3 . \n"

result23k = prefix2 ++
    "pers:Si3 rel:brother pers:Si3 . \n"

result23l = prefix2 ++
    "pers:Si3 rel:brother pers:Al3 . \n"

result23m = prefix2 ++
    "pers:Al3 rel:brother pers:Gr3 . \n"

result23n = prefix2 ++
    "pers:Al3 rel:brother pers:La3 . \n"

result23o = prefix2 ++
    "pers:Al3 rel:brother pers:Si3 . \n"

result23p = prefix2 ++
    "pers:Al3 rel:brother pers:Al3 . \n"

result23q = prefix2 ++
    "pers:Wi3 rel:brother pers:Wi3 . \n"

result23r = prefix2 ++
    "pers:Ro4 rel:brother pers:Ro4 . \n"

result23s = prefix2 ++
    "pers:Ol4 rel:brother pers:Lo4 . \n"

result23t = prefix2 ++
    "pers:Ol4 rel:brother pers:Ol4 . \n"

result23u = prefix2 ++
    "pers:Lo4 rel:brother pers:Lo4 . \n"

result23v = prefix2 ++
    "pers:Lo4 rel:brother pers:Ol4 . \n"

result23w = prefix2 ++
    "pers:Ha4 rel:brother pers:El4 . \n"

result23x = prefix2 ++
    "pers:Ha4 rel:brother pers:Ha4 . \n"

result23y = prefix2 ++
    "pers:El4 rel:brother pers:El4 . \n"

result23z = prefix2 ++
    "pers:El4 rel:brother pers:Ha4 . \n"

var23         = rdfQueryFind query23 graph2
testQuery23   = test "testQuery23" (not $ null var23)
res23         = rdfQuerySubs var23 result23
testResult23  = testEq "testResult23" 26 (length res23)
testResult23a = testGr "testResult23a" result23a res23
testResult23b = testGr "testResult23b" result23b res23
testResult23c = testGr "testResult23c" result23c res23
testResult23d = testGr "testResult23d" result23d res23
testResult23e = testGr "testResult23e" result23e res23
testResult23f = testGr "testResult23f" result23f res23
testResult23g = testGr "testResult23g" result23g res23
testResult23h = testGr "testResult23h" result23h res23
testResult23i = testGr "testResult23i" result23i res23
testResult23j = testGr "testResult23j" result23j res23
testResult23k = testGr "testResult23k" result23k res23
testResult23l = testGr "testResult23l" result23l res23
testResult23m = testGr "testResult23m" result23m res23
testResult23n = testGr "testResult23n" result23n res23
testResult23o = testGr "testResult23o" result23o res23
testResult23p = testGr "testResult23p" result23p res23
testResult23q = testGr "testResult23q" result23q res23
testResult23r = testGr "testResult23r" result23r res23
testResult23s = testGr "testResult23s" result23s res23
testResult23t = testGr "testResult23t" result23t res23
testResult23u = testGr "testResult23u" result23u res23
testResult23v = testGr "testResult23v" result23v res23
testResult23w = testGr "testResult23w" result23w res23
testResult23x = testGr "testResult23x" result23x res23
testResult23y = testGr "testResult23y" result23y res23
testResult23z = testGr "testResult23z" result23z res23

-- apply filtering to result:
filter23 = varFilterNE (Var "b") (Var "c") :: RDFVarBindingFilter
var23F   = rdfQueryFilter filter23 var23
res23F   = rdfQuerySubs var23F result23
testResult23F  = testEq "testResult23" 16 (length res23F)
testResult23bF = testGr "testResult23b" result23b res23F
testResult23cF = testGr "testResult23c" result23c res23F
testResult23dF = testGr "testResult23d" result23d res23F
testResult23eF = testGr "testResult23e" result23e res23F
testResult23gF = testGr "testResult23g" result23g res23F
testResult23hF = testGr "testResult23h" result23h res23F
testResult23iF = testGr "testResult23i" result23i res23F
testResult23jF = testGr "testResult23j" result23j res23F
testResult23lF = testGr "testResult23l" result23l res23F
testResult23mF = testGr "testResult23m" result23m res23F
testResult23nF = testGr "testResult23n" result23n res23F
testResult23oF = testGr "testResult23o" result23o res23F
testResult23sF = testGr "testResult23s" result23s res23F
testResult23vF = testGr "testResult23v" result23v res23F
testResult23wF = testGr "testResult23w" result23w res23F
testResult23zF = testGr "testResult23z" result23z res23F


query24    = graphFromString query24str
query24str = prefix2 ++
    "?a rel:daughter ?b . \n" ++
    "?a rel:daughter ?c . \n"

result24    = graphFromString result24str
result24str = prefix2 ++
    "?b rel:sister ?c . \n"

result24a = prefix2 ++
    "pers:Ma2 rel:sister pers:Ma2 . \n"

result24b = prefix2 ++
    "pers:Ma2 rel:sister pers:An2 . \n"

result24c = prefix2 ++
    "pers:An2 rel:sister pers:Ma2 . \n"

result24d = prefix2 ++
    "pers:An2 rel:sister pers:An2 . \n"

result24e = prefix2 ++
    "pers:Ma3 rel:sister pers:Ma3 . \n"

result24f = prefix2 ++
    "pers:Rh4 rel:sister pers:Rh4 . \n"

var24         = rdfQueryFind query24 graph2
testQuery24   = test "testQuery24" (not $ null var24)
res24         = rdfQuerySubs var24 result24
testResult24  = testEq "testResult24" 6 (length res24)
testResult24a = testGr "testResult24a" result24a res24
testResult24b = testGr "testResult24b" result24b res24
testResult24c = testGr "testResult24c" result24c res24
testResult24d = testGr "testResult24d" result24d res24
testResult24e = testGr "testResult24e" result24e res24
testResult24f = testGr "testResult24f" result24f res24


query25    = graphFromString query25str
query25str = prefix2 ++
    "?a rel:son      ?b . \n" ++
    "?a rel:daughter ?c . \n"

result25    = graphFromString result25str
result25str = prefix2 ++
    "?b rel:sister  ?c . \n" ++
    "?c rel:brother ?b . \n"

result25a = prefix2 ++
    "pers:Wi3 rel:sister  pers:Ma3 . \n" ++
    "pers:Ma3 rel:brother pers:Wi3 . \n"

result25b = prefix2 ++
    "pers:Ro4 rel:sister  pers:Rh4 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n"

var25         = rdfQueryFind query25 graph2
testQuery25   = test "testQuery25" (not $ null var25)
res25         = rdfQuerySubs var25 result25
testResult25  = testEq "testResult25" 2 (length res25)
testResult25a = testGr "testResult25a" result25a res25
testResult25b = testGr "testResult25b" result25b res25

test2 = TestList
    [ testQuery21,   testResult21
    , testResult21a, testResult21b, testResult21c
    , testResult21d, testResult21e, testResult21f
    , testQuery22,   testResult22
    , testResult22a, testResult22b, testResult22c
    , testResult22d, testResult22e
    , testQuery23,   testResult23
    , testResult23a, testResult23b, testResult23c
    , testResult23d, testResult23e, testResult23f
    , testResult23g, testResult23h, testResult23i
    , testResult23j, testResult23k, testResult23l
    , testResult23m, testResult23n, testResult23o
    , testResult23p, testResult23q, testResult23r
    , testResult23s, testResult23t, testResult23u
    , testResult23v, testResult23w, testResult23x
    , testResult23y, testResult23z
    , testResult23F
    , testResult23bF, testResult23cF
    , testResult23dF, testResult23eF
    , testResult23gF, testResult23hF, testResult23iF
    , testResult23jF, testResult23lF
    , testResult23mF, testResult23nF, testResult23oF
    , testResult23sF
    , testResult23vF, testResult23wF
    , testResult23zF
    , testQuery24,   testResult24
    , testResult24a, testResult24b, testResult24c
    , testResult24d, testResult24e, testResult24f
    ]

------------------------------------------------------------
--  test handling of unsubstituted variables, and
--  rdfQuerySubsAll, rdfQuerySubsBlank
------------------------------------------------------------

graph3    = graphFromString graph3str
graph3str = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ro4 . \n" ++
    "pers:Pa2 rel:grandparent pers:Ol4 . \n"

query31    = graphFromString query31str
query31str = prefix2 ++
    "?a rel:grandparent ?c . \n"

result31    = graphFromString result31str
result31str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?b rel:son ?c . \n"

result31a = prefix2 ++
    "pers:Pa2 rel:son ?b . \n" ++
    "?b rel:son pers:Ro4 . \n"

result31b = prefix2 ++
    "pers:Pa2 rel:son ?b . \n" ++
    "?b rel:son pers:Ol4 . \n"

var31          = rdfQueryFind query31 graph3
testQuery31    = test "testQuery31" (not $ null var31)
res31pairs     = rdfQuerySubsAll var31 result31
(res31,res31v) = unzip res31pairs
testUnsubs31   = testEq "testUnsubs31" 2 (length res31v)
testUnsubs31a  = testEq "testUnsubs31a" [(Var "b")] (head res31v)
testUnsubs31b  = testEq "testUnsubs31a" [(Var "b")] (head . tail $ res31v)
testResult31   = testEq "testResult31" 2 (length res31)
testResult31a  = testGr "testResult31a" result31a res31
testResult31b  = testGr "testResult31b" result31b res31

query32    = graphFromString query32str
query32str = prefix2 ++
    "?a rel:grandparent ?c . \n"

result32    = graphFromString result32str
result32str = prefix2 ++
    "?a rel:wife _:b  . \n" ++
    "?d rel:any  _:b0 . \n" ++
    "?a rel:son ?b . \n"    ++
    "?b rel:son ?c . \n"

result32a = prefix2 ++
    "pers:Pa2 rel:wife _:b      . \n" ++
    "_:d0     rel:any  _:b0     . \n" ++
    "pers:Pa2 rel:son  _:b1     . \n" ++
    "_:b1     rel:son  pers:Ro4 . \n"

result32b = prefix2 ++
    "pers:Pa2 rel:wife _:b      . \n" ++
    "_:d0     rel:any  _:b0     . \n" ++
    "pers:Pa2 rel:son  _:b1     . \n" ++
    "_:b1     rel:son  pers:Ol4 . \n"

res32          = rdfQuerySubsBlank var31 result32
testResult32   = testEq "testResult32" 2 (length res32)
testResult32a  = testGr "testResult32a" result32a res32
testResult32b  = testGr "testResult32b" result32b res32

res33          = rdfQuerySubs var31 result32
testResult33   = testEq "testResult33" 0 (length res33)

test3 = TestList
    [ testQuery31
    , testUnsubs31, testUnsubs31a, testUnsubs31b
    , testResult31, testResult31a, testResult31b
    , testResult32, testResult32a, testResult32b
    , testResult33
    ]

--  Debug sequence for rdfQuerySubsBlank
--  (using internals of rdfQuerySubsBlank implementation)
--  res32 = rdfQuerySubsBlank (fromJust var31) result32
d1 = result32
d2 = rdfQuerySubs2 (head $ var31) d1
d3 = allLabels isBlank (fst d2)
d4 = remapLabels (snd d2) d3 makeBlank (fst d2)

------------------------------------------------------------
--  test4:  test of backward-chaining query
------------------------------------------------------------

prefix4 =
    "@prefix pers: <urn:pers:> . \n"      ++
    "@prefix rel:  <urn:rel:> . \n"       ++
    " \n"

graph41    = graphFromString graph41str
graph41str = prefix4 ++
    "pers:St1 rel:wife     pers:Do1 . \n"

query41    = graphFromString query41str
query41str = prefix4 ++
    "?a rel:wife ?b . \n"

result41    = graphFromString result41str
result41str = prefix4 ++
    "?b rel:husband ?a . \n"

result41a = prefix4 ++
    "pers:Do1 rel:husband pers:St1 . \n"

var41          = rdfQueryBack query41 graph41
testQuery41    = test "testQuery41" (not $ null var41)
testQuery41a   = testEq "testQuery41a" 1 (length var41)
res41          = rdfQueryBackSubs var41 result41
testResult41   = testEq "testResult41" 1 (length res41)
testResult41a  = testGr "testResult41a" result41a (fst $ unzip $ head res41)
testUnbound41a = testLs "testUnbound41a" [] (snd $ head $ head res41)

graph42    = graphFromString graph42str
graph42str = prefix4 ++
    "pers:Pa2 rel:grandparent pers:Ro4 . \n"

query42    = graphFromString query42str
query42str = prefix4 ++
    "?a rel:grandparent ?c . \n"

result42    = graphFromString result42str
result42str = prefix4 ++
    "?a rel:son ?b . \n" ++
    "?b rel:son ?c . \n"

result42a = prefix4 ++
    "pers:Pa2 rel:son ?b       . \n" ++
    "?b       rel:son pers:Ro4 . \n"

var42          = rdfQueryBack query42 graph42
testQuery42    = test "testQuery42" (not $ null var42)
testQuery42a   = testEq "testQuery42a" 1 (length var42)
res42          = rdfQueryBackSubs var42 result42
testResult42   = testEq "testResult42" 1 (length res42)
testResult42a  = testGr "testResult42a" result42a (fst $ unzip $ head res42)
testUnbound42a = testLs "testUnbound42a" [(Var "b")] (snd $ head $ head res42)


graph43    = graphFromString graph43str
graph43str = prefix4 ++
    "pers:Gr3 rel:brother pers:La3 . \n"

query43    = graphFromString query43str
query43str = prefix4 ++
    "?b rel:brother ?c . \n"

result43    = graphFromString result43str
result43str = prefix4 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result43a = prefix4 ++
    "?a rel:son pers:Gr3 . \n" ++
    "?a rel:son pers:La3 . \n"

var43          = rdfQueryBack query43 graph43
testQuery43    = test "testQuery43" (not $ null var43)
testQuery43a   = testEq "testQuery43a" 1 (length var43)
res43          = rdfQueryBackSubs var43 result43
testResult43   = testEq "testResult43" 1 (length res43)
testResult43a  = testGr "testResult43a" result43a (fst $ unzip $ head res43)
testUnbound43a = testLs "testUnbound43a" [(Var "a")] (snd $ head $ head res43)


graph44    = graphFromString graph44str
graph44str = prefix4 ++
    "pers:Pa2 rel:grandson pers:Ro4 . \n"

query44    = graphFromString query44str
query44str = prefix4 ++
    "?a rel:grandson ?b . \n" ++
    "?c rel:grandson ?d . \n"

result44    = graphFromString result44str
result44str = prefix4 ++
    "?a rel:son      ?m . \n" ++
    "?m rel:son      ?b . \n" ++
    "?c rel:daughter ?n . \n" ++
    "?n rel:son      ?d . \n"

result44a = prefix4 ++
    "pers:Pa2 rel:son ?m       . \n" ++
    "?m       rel:son pers:Ro4 . \n" ++
    "?c rel:daughter ?n . \n" ++
    "?n rel:son      ?d . \n"
unbound44a = [(Var "m"),(Var "c"),(Var "n"),(Var "d")]

result44b = prefix4 ++
    "?a rel:son      ?m . \n" ++
    "?m rel:son      ?b . \n" ++
    "pers:Pa2 rel:daughter ?n .       \n" ++
    "?n       rel:son      pers:Ro4 . \n"
unbound44b = [(Var "a"),(Var "m"),(Var "b"),(Var "n")]

var44          = rdfQueryBack query44 graph44
testQuery44    = test "testQuery44" (not $ null var44)
testQuery44a   = testEq "testQuery44a"   2 (length var44)
res44          = rdfQueryBackSubs var44 result44
testResult44   = testEq "testResult44"   2 (length res44)
[res44_1,res44_2] = res44
testResult44a  = testGr "testResult44a"  result44a  (fst $ unzip res44_2)
testUnbound44a = testLs "testUnbound44a" unbound44a (snd $ head res44_2)
testResult44b  = testGr "testResult44b"  result44b  (fst $ unzip res44_1)
testUnbound44b = testLs "testUnbound44b" unbound44b (snd $ head res44_1)

--  test45:  multiple substitutions used together
--
--  (?a daughter ?b, ?a son ?c) => ?b brother ?c
--
--  (b1 brother c1, b2 brother c2) if
--      (?a daughter b1, ?a son c1) && (?a daughter b2, ?a son c2)

graph45    = graphFromString graph45str
graph45str = prefix4 ++
    "pers:Rh4 rel:brother pers:Ro4 . \n" ++
    "pers:Ma3 rel:brother pers:Wi3 . \n"

query45    = graphFromString query45str
query45str = prefix4 ++
    "?b rel:brother ?c . \n"

result45    = graphFromString result45str
result45str = prefix4 ++
    "?a rel:daughter ?b . \n" ++
    "?a rel:son      ?c . \n"

result45a1 = prefix4 ++
    "?a rel:daughter pers:Rh4 . \n" ++
    "?a rel:son      pers:Ro4 . \n"
unbound45a1 = [(Var "a")]

result45a2 = prefix4 ++
    "?a rel:daughter pers:Ma3 . \n" ++
    "?a rel:son      pers:Wi3 . \n"
unbound45a2 = [(Var "a")]

var45          = rdfQueryBack query45 graph45
testQuery45    = test "testQuery45" (not $ null var45)
testQuery45a   = testEq "testQuery45a"   1 (length var45)
res45          = rdfQueryBackSubs var45 result45
testResult45   = testEq "testResult45"   1 (length res45)
[res45_1] = res45
testResult45_1 = testEq "testResult45_1" 2 (length res45_1)
[res45_11,res45_12] = res45_1
testResult45a1  = testGr "testResult45a1"  result45a1  [fst res45_11]
testUnbound45a1 = testLs "testUnbound45a1" unbound45a1 (snd res45_11)
testResult45a2  = testGr "testResult45a2"  result45a2  [fst res45_12]
testUnbound45a2 = testLs "testUnbound45a2" unbound45a2 (snd res45_12)

--  test46:  multiple ways to get solution
--
--  (?c son ?a, ?c stepSon b) => (?a stepBrother ?b, ?b stepBrother ?a)
--
--  a stepBrother b if
--      (_:c1 son a, _:c1 stepSon b) || (_:c2 stepSon a, _:c2 son b)

graph46    = graphFromString graph46str
graph46str = prefix4 ++
    "pers:Gr3 rel:stepbrother pers:St3 . \n"

query46    = graphFromString query46str
query46str = prefix4 ++
    "?b rel:stepbrother ?c . \n" ++
    "?c rel:stepbrother ?b . \n"

result46    = graphFromString result46str
result46str = prefix4 ++
    "?a rel:son     ?b . \n" ++
    "?a rel:stepson ?c . \n"

result46a = prefix4 ++
    "?a rel:son     pers:St3 . \n" ++
    "?a rel:stepson pers:Gr3 . \n"
unbound46a = [(Var "a")]

result46b = prefix4 ++
    "?a rel:son     pers:Gr3 . \n" ++
    "?a rel:stepson pers:St3 . \n"
unbound46b = [(Var "a")]

var46          = rdfQueryBack query46 graph46
testQuery46    = test "testQuery46" (not $ null var46)
testQuery46a   = testEq "testQuery46a"   2 (length var46)
res46          = rdfQueryBackSubs var46 result46
testResult46   = testEq "testResult46"   2 (length res46)
[res46_1,res46_2] = res46
testResult46_1 = testEq "testResult46_1" 1 (length res46_1)
testResult46_2 = testEq "testResult46_2" 1 (length res46_2)
[res46_11] = res46_1
[res46_21] = res46_2
testResult46a  = testGr "testResult46a"  result46a  [fst res46_11]
testUnbound46a = testLs "testUnbound46a" unbound46a (snd res46_11)
testResult46b  = testGr "testResult46b"  result46b  [fst res46_21]
testUnbound46b = testLs "testUnbound46b" unbound46b (snd res46_21)


--  test47:  multiple ways to multiple solutions
--
--  (?c son ?a, ?c stepSon b) => (?a stepBrother ?b, ?b stepBrother ?a)
--
--  (a stepBrother b, c stepBrother d) if
--      ((_:e son a, _:e stepSon b) && (_:f son a, _:f stepSon b)) ||
--      ((_:e son a, _:e stepSon b) && (_:f stepSon a, _:f son b)) ||
--      ((_:e stepSon a, _:e son b) && (_:f son a, _:f stepSon b)) ||
--      ((_:e stepSon a, _:e son b) && (_:f stepSon a, _:f son b))

graph47    = graphFromString graph47str
graph47str = prefix4 ++
    "pers:Gr3 rel:stepbrother pers:St3 . \n" ++
    "pers:St3 rel:stepbrother pers:Gr3 . \n"

query47    = graphFromString query47str
query47str = prefix4 ++
    "?b rel:stepbrother ?c . \n" ++
    "?c rel:stepbrother ?b . \n"

result47    = graphFromString result47str
result47str = prefix4 ++
    "?a rel:son     ?b . \n" ++
    "?a rel:stepson ?c . \n"

result47a1 = prefix4 ++
    "?a rel:son     pers:St3 . \n" ++
    "?a rel:stepson pers:Gr3 . \n"
unbound47a1 = [(Var "a")]

result47a2 = prefix4 ++
    "?a rel:son     pers:Gr3 . \n" ++
    "?a rel:stepson pers:St3 . \n"
unbound47a2 = [(Var "a")]

result47b1 = prefix4 ++
    "?a rel:stepson pers:St3 . \n" ++
    "?a rel:son     pers:Gr3 . \n"
unbound47b1 = [(Var "a")]

result47b2 = prefix4 ++
    "?a rel:stepson pers:St3 . \n" ++
    "?a rel:son     pers:Gr3 . \n"
unbound47b2 = [(Var "a")]

result47c1 = prefix4 ++
    "?a rel:son     pers:St3 . \n" ++
    "?a rel:stepson pers:Gr3 . \n"
unbound47c1 = [(Var "a")]

result47c2 = prefix4 ++
    "?a rel:son     pers:St3 . \n" ++
    "?a rel:stepson pers:Gr3 . \n"
unbound47c2 = [(Var "a")]

result47d1 = prefix4 ++
    "?a rel:stepson pers:St3 . \n" ++
    "?a rel:son     pers:Gr3 . \n"
unbound47d1 = [(Var "a")]

result47d2 = prefix4 ++
    "?a rel:son     pers:St3 . \n" ++
    "?a rel:stepson pers:Gr3 . \n"
unbound47d2 = [(Var "a")]

var47          = rdfQueryBack query47 graph47
testQuery47    = test "testQuery47" (not $ null var47)
testQuery47a   = testEq "testQuery47a"   4 (length var47)
res47          = rdfQueryBackSubs var47 result47
testResult47   = testEq "testResult47"   4 (length res47)
[res47_1,res47_2,res47_3,res47_4] = res47
testResult47_1 = testEq "testResult47_1" 2 (length res47_1)
testResult47_2 = testEq "testResult47_2" 2 (length res47_2)
testResult47_3 = testEq "testResult47_3" 2 (length res47_3)
testResult47_4 = testEq "testResult47_4" 2 (length res47_4)
[res47_11,res47_12] = res47_1
[res47_21,res47_22] = res47_2
[res47_31,res47_32] = res47_3
[res47_41,res47_42] = res47_4
testResult47a1  = testGr "testResult47a1"  result47a1  [fst res47_11]
testUnbound47a1 = testLs "testUnbound47a1" unbound47a1 (snd res47_11)
testResult47a2  = testGr "testResult47a2"  result47a2  [fst res47_12]
testUnbound47a2 = testLs "testUnbound47a2" unbound47a2 (snd res47_12)
testResult47b1  = testGr "testResult47b1"  result47b1  [fst res47_21]
testUnbound47b1 = testLs "testUnbound47b1" unbound47b1 (snd res47_21)
testResult47b2  = testGr "testResult47b2"  result47b2  [fst res47_22]
testUnbound47b2 = testLs "testUnbound47b2" unbound47b2 (snd res47_22)
testResult47c1  = testGr "testResult47c1"  result47c1  [fst res47_31]
testUnbound47c1 = testLs "testUnbound47c1" unbound47c1 (snd res47_31)
testResult47c2  = testGr "testResult47c2"  result47c2  [fst res47_32]
testUnbound47c2 = testLs "testUnbound47c2" unbound47c2 (snd res47_32)
testResult47d1  = testGr "testResult47d1"  result47d1  [fst res47_41]
testUnbound47d1 = testLs "testUnbound47d1" unbound47d1 (snd res47_41)
testResult47d2  = testGr "testResult47d2"  result47d2  [fst res47_42]
testUnbound47d2 = testLs "testUnbound47d2" unbound47d2 (snd res47_42)


--  test48:  redundant multiple ways to get solution
--
--  (?a son ?b, ?a son ?c) => (?b brother ?c, ?c brother ?b)
--
--  (a brother b) if
--      (_:c1 son a, _:c1 son b) || (_:c2 son b, _:c2 son a)

graph48    = graphFromString graph48str
graph48str = prefix4 ++
    "pers:Gr3 rel:brother pers:La3 . \n"

query48    = graphFromString query48str
query48str = prefix4 ++
    "?b rel:brother ?c . \n" ++
    "?c rel:brother ?b . \n"

result48    = graphFromString result48str
result48str = prefix4 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result48a = prefix4 ++
    "?a rel:son pers:La3 . \n" ++
    "?a rel:son pers:Gr3 . \n"
unbound48a = [(Var "a")]

result48b = prefix4 ++
    "?a rel:son pers:Gr3 . \n" ++
    "?a rel:son pers:La3 . \n"
unbound48b = [(Var "a")]

var48          = rdfQueryBack query48 graph48
testQuery48    = test "testQuery48" (not $ null var48)
testQuery48a   = testEq "testQuery48a"   2 (length var48)
res48          = rdfQueryBackSubs var48 result48
testResult48   = testEq "testResult48"   2 (length res48)
[res48_1,res48_2] = res48
testResult48_1 = testEq "testResult48_1" 1 (length res48_1)
testResult48_2 = testEq "testResult48_2" 1 (length res48_2)
[res48_11] = res48_1
[res48_21] = res48_2
testResult48a  = testGr "testResult48a"  result48a  [fst res48_11]
testUnbound48a = testLs "testUnbound48a" unbound48a (snd res48_11)
testResult48b  = testGr "testResult48b"  result48b  [fst res48_21]
testUnbound48b = testLs "testUnbound48b" unbound48b (snd res48_21)


-- test49: goal not satisfiable by rule
--
--  (?a foo ?b, ?b foo ?a) => (?a bar ?a)
--
--  (a bar b) cannot be deduced directly

graph49    = graphFromString graph49str
graph49str = prefix4 ++
    "pers:Gr3 rel:foo pers:La3 . \n"

query49    = graphFromString query49str
query49str = prefix4 ++
    "?a rel:bar ?a . \n"

result49    = graphFromString result49str
result49str = prefix4 ++
    "?a rel:foo ?b . \n" ++
    "?b rel:foo ?a . \n"

var49          = rdfQueryBack query49 graph49
testQuery49    = test "testQuery49" (null var49)
testQuery49a   = testEq "testQuery49a"   0 (length var49)
res49          = rdfQueryBackSubs var49 result49
testResult49   = testEq "testResult49"   0 (length res49)

--  test50:  back-chaining with filter
--
--  (?a son ?b, ?a son ?c) => (?b brother ?c, ?c brother ?b)
--
--  (a brother b) if
--      (_:c1 son a, _:c1 son b) || (_:c2 son b, _:c2 son a)

graph50    = graphFromString graph50str
graph50str = prefix4 ++
    "pers:Gr3 rel:brother pers:Gr3 . \n"

query50    = graphFromString query50str
query50str = prefix4 ++
    "?b rel:brother ?c . \n" ++
    "?c rel:brother ?b . \n"

result50    = graphFromString result50str
result50str = prefix4 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result50a = prefix4 ++
    "?a rel:son pers:Gr3 . \n" ++
    "?a rel:son pers:Gr3 . \n"
unbound50a = [(Var "a")]

result50b = prefix4 ++
    "?a rel:son pers:Gr3 . \n" ++
    "?a rel:son pers:Gr3 . \n"
unbound50b = [(Var "a")]

var50          = rdfQueryBack query50 graph50
testQuery50    = test "testQuery50" (not $ null var50)
testQuery50a   = testEq "testQuery50a"   2 (length var50)
res50          = rdfQueryBackSubs var50 result50
testResult50   = testEq "testResult50"   2 (length res50)
[res50_1,res50_2] = res50
testResult50_1 = testEq "testResult50_1" 1 (length res50_1)
testResult50_2 = testEq "testResult50_2" 1 (length res50_2)
[res50_11] = res50_1
[res50_21] = res50_2
testResult50a  = testGr "testResult50a"  result50a  [fst res50_11]
testUnbound50a = testLs "testUnbound50a" unbound50a (snd res50_11)
testResult50b  = testGr "testResult50b"  result50b  [fst res50_21]
testUnbound50b = testLs "testUnbound50b" unbound50b (snd res50_21)

filter50       = varFilterNE (Var "b") (Var "c") :: RDFVarBindingFilter
var50F         = rdfQueryBackFilter filter50 var50
res50F         = rdfQueryBackSubs var50F result50
testResult50F  = testEq "testResult50F" 0 (length res50F)


--  Backward substitution query test suite

test4 = TestList
    [ testQuery41, testQuery41a, testResult41
    , testResult41a, testUnbound41a
    , testQuery42, testQuery42a, testResult42
    , testResult42a, testUnbound42a
    , testQuery43, testQuery43a, testResult43
    , testResult43a, testUnbound43a
    , testQuery44, testQuery44a, testResult44
    , testResult44a, testUnbound44a
    , testResult44b, testUnbound44b
    , testQuery45, testQuery45a, testResult45
    , testResult45_1
    , testResult45a1, testUnbound45a1
    , testResult45a2, testUnbound45a2
    , testQuery46, testQuery46a, testResult46
    , testResult46_1, testResult46_2
    , testResult46a, testUnbound46a
    , testResult46b, testUnbound46b
    , testQuery47, testQuery47a, testResult47
    , testResult47_1, testResult47_2, testResult47_3, testResult47_4
    , testResult47a1, testUnbound47a1
    , testResult47a2, testUnbound47a2
    , testResult47b1, testUnbound47b1
    , testResult47b2, testUnbound47b2
    , testResult47c1, testUnbound47c1
    , testResult47c2, testUnbound47c2
    , testResult47d1, testUnbound47d1
    , testResult47d2, testUnbound47d2
    , testQuery48, testQuery48a, testResult48
    , testResult48_1, testResult48_2
    , testResult48a, testUnbound48a
    , testResult48b, testUnbound48b
    , testQuery49, testQuery49a, testResult49
    , testQuery50, testQuery50a, testResult50
    , testResult50_1, testResult50_2
    , testResult50a, testUnbound50a
    , testResult50b, testUnbound50b
    , testResult50F
    ]

------------------------------------------------------------
--  Instance query test suite
------------------------------------------------------------
--
--  The test plan is this:
--  (1) perform a backward chaining query against some desired result.
--      ?f father ?a, ?f father ?b, ?a /= ?b => ?a brother ?b
--      against
--      Gr3 brother La3, Gr3 brother Si3
--      should yield:
--      _:a father Gr3
--      _:a father La3
--      _:b father Gr3
--      _:b father Si3
--  (2) Perform instance query of result against 'graph2' (see above)
--      should yield:
--      _:a = Pa2
--      _:b = Pa2
--  (3) Substitute this into query, should yield:
--      Pa2 father Gr3
--      Pa2 father La3
--      Pa2 father Gr3
--      Pa2 father Si3
--  (4) Use this result in an instance query against 'graph2':  it should
--      match without any variable substitutions, indicating that it is
--      a subgraph

graph61    = graphFromString graph61str
graph61str = prefix4 ++
    "pers:Gr3 rel:brother pers:La3 . \n" ++
    "pers:Gr3 rel:brother pers:Si3 . \n"

query61    = graphFromString query61str
query61str = prefix4 ++
    "?b rel:brother ?c . \n"

result61    = graphFromString result61str
result61str = prefix4 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result61a = prefix4 ++
    "_:a1 rel:son pers:Gr3 . \n" ++
    "_:a1 rel:son pers:La3 . \n" ++
    "_:a2 rel:son pers:Gr3 . \n" ++
    "_:a2 rel:son pers:Si3 . \n"

result63a = prefix4 ++
    "pers:Pa2 rel:son pers:Gr3 . \n" ++
    "pers:Pa2 rel:son pers:La3 . \n" ++
    "pers:Pa2 rel:son pers:Gr3 . \n" ++
    "pers:Pa2 rel:son pers:Si3 . \n"

--  1. Backchain query with blank substutions
var61          = rdfQueryBack query61 graph61
testQuery61    = test   "testQuery61" (not $ null var61)
testQuery61a   = testEq "testQuery61a" 1 (length var61)
res61          = rdfQueryBackSubsBlank var61 result61
testResult61   = testEq "testResult61" 1 (length res61)
[[res61a1,res61a2]] = res61
res61a         = merge res61a1 res61a2
testResult61a  = testGr "testResult61a" result61a [res61a]
--  2. Instance query against 'graph2'
var62          = rdfQueryInstance res61a graph2
testQuery62    = test   "testQuery62" (not $ null var62)
testQuery62a   = testEq "testQuery62a" 1 (length var62)
--  3. Substitute into instance query graph
res63          = rdfQuerySubs var62 res61a
testQuery63    = test   "testQuery63" (not $ null res63)
testQuery63a   = testEq "testQuery63a" 1 (length res63)
[res63a]       = res63
testResult63a  = testGr "testResult63a" result63a [res63a]
--  4. Repeat instance query against 'graph2'
--     Query bindings should be null.
var64          = rdfQueryInstance res63a graph2
testQuery64    = test   "testQuery64" (not $ null var64)
testQuery64a   = testEq "testQuery64a" 1 (length var64)
[var64a]       = var64
testQuery64b   = test   "testQuery64b" (null $ vbEnum var64a)

test6 = TestList
    [ testQuery61, testQuery61a, testResult61, testResult61a
    , testQuery62, testQuery62a
    , testQuery63, testQuery63a, testResult63a
    , testQuery64, testQuery64a, testQuery64b
    ]

------------------------------------------------------------
--  Specific test cases
------------------------------------------------------------

--  Back-chaining query binding modifier

--  Set up call of rdfQueryBackModify
--  (1) simple filter
--  (2) allocate new binding
{-
rdfQueryBackModify ::
    RDFVarBindingModify -> [[RDFVarBinding]] -> [[RDFVarBinding]]
rdfQueryBackModify qbm qbss = concatMap (rdfQueryBackModify1 qbm) qbss
-}

baseex   = "http://example.org/"
baserdf  = nsURI namespaceRDF
q_dattyp = (makeScopedName "" baseex "datatype")

v_a   = Var "a"
v_b   = Var "b"
v_c   = Var "c"
v_x   = Var "x"
v_y   = Var "y"
v_z   = Var "z"
u_s   = Res (makeScopedName "" baseex "s")
u_o   = Res (makeScopedName "" baseex "o")
u_p   = Res (makeScopedName "" baseex "p")
u_p1  = Res (makeScopedName "" baseex "p1")
u_p2a = Res (makeScopedName "" baseex "p2a")
u_p2b = Res (makeScopedName "" baseex "p2b")
u_m1  = Res (makeScopedName "" baserdf "_1")
u_m2  = Res (makeScopedName "" baserdf "_2")
u_rt  = Res rdf_type
u_xt  = Res rdf_XMLLiteral
u_dt  = Res q_dattyp
l_1   = Lit "l1" Nothing
l_2   = Lit "l2" (Just $ langName "fr")
l_3   = Lit "l3" (Just q_dattyp)
l_4   = Lit "l4" (Just q_dattyp) -- was: (Lang "fr")
l_5   = Lit "l5" (Just rdf_XMLLiteral)
b_1   = Blank "1"
b_2   = Blank "2"
b_3   = Blank "3"
b_l1  = Blank "l1"
b_l2  = Blank "l2"

vbss01a =               -- ?a is uri, ?b is uri
    [ makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,u_o) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,b_1) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_1) ]
    ]

vbss01b =               -- ?c is blank
    [ makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,b_1) ]
    ]

vbss01c =               -- ?c is literal
    [ makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_1) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_2) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_3) ]
    ]

vbss01d =               -- ?c is untyped literal
    [ makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_1) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_2) ]
    ]

vbss01e =               -- ?c is typed literal
    [ makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_3) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_4) ]
    , makeVarBinding [ (v_a,b_3), (v_b,u_p),  (v_c,l_5) ]
    ]

vbss01f =               -- ?c is XML literal
    [ makeVarBinding [ (v_a,b_1), (v_b,u_p),  (v_c,l_5) ]
    ]

vbss01g =               -- ?b is member property
    [ makeVarBinding [ (v_a,b_1), (v_b,u_m1), (v_c,u_o) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_m2), (v_c,b_1) ]
    ]

vbss01h =               -- ?c is datatyped with ?x
    [ makeVarBinding [ (v_a,b_1), (v_b,u_p),  (v_c,l_3), (v_x,u_dt) ]
    , makeVarBinding [ (v_a,b_2), (v_b,u_p),  (v_c,l_4), (v_x,u_dt) ]
    , makeVarBinding [ (v_a,u_s), (v_b,u_p),  (v_c,l_5), (v_x,u_xt) ]
    ]

vbss01i =               -- ?c is not datatyped with ?x
    [ makeVarBinding [ (v_a,b_1), (v_b,u_p),  (v_c,l_3), (v_x,u_dt) ]
    , makeVarBinding [ (v_a,b_2), (v_b,u_p),  (v_c,l_4), (v_x,u_xt) ]
    , makeVarBinding [ (v_a,b_3), (v_b,u_p),  (v_c,l_5), (v_x,u_xt) ]
    ]

vbss01  = [ vbss01a     -- ?a is uri, ?b is uri
          , vbss01b     -- ?c is blank
          , vbss01c     -- ?c is literal
          , vbss01d     -- ?c is untyped literal
          , vbss01e     -- ?c is typed literal
          , vbss01f     -- ?c is XML literal
          , vbss01g     -- ?b is member property
          , vbss01h     -- ?c is datatyped with ?x
          , vbss01i     -- ?c is not datatyped with ?x
          ]

testBackMod01 = testEq "testBackMod01" vbss01 $
                rdfQueryBackModify varBindingId vbss01

testBackMod02 = testEq "testBackMod02" [vbss01a,vbss01b,vbss01c,vbss01d] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingUriRef v_a)
                    vbss01

testBackMod03 = testEq "testBackMod03" [vbss01f,vbss01i] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingBlank v_a)
                    vbss01

testBackMod04 = testEq "testBackMod04" vbss01 $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingUriRef v_b)
                    vbss01

testBackMod05 = testEq "testBackMod05"
                [vbss01c,vbss01d,vbss01e,vbss01f,vbss01h,vbss01i] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingLiteral v_c)
                    vbss01

testBackMod06 = testEq "testBackMod06" [vbss01d] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingUntypedLiteral v_c)
                    vbss01

testBackMod07 = testEq "testBackMod07" [vbss01e,vbss01f,vbss01h,vbss01i] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingTypedLiteral v_c)
                    vbss01

testBackMod08 = testEq "testBackMod08" [vbss01f] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingXMLLiteral v_c)
                    vbss01

testBackMod09 = testEq "testBackMod09" [vbss01g] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingMemberProp v_b)
                    vbss01

testBackMod10 = testEq "testBackMod10" [vbss01h] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingDatatyped v_x v_c)
                    vbss01

vbss02a = [ makeVarBinding [ (v_x,u_s), (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_x,u_s), (v_a,u_p2a), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,u_s), (v_a,u_p2b), (v_b,b_l2) ]
          , makeVarBinding [ (v_b,b_l1) ]
          , makeVarBinding [ (v_b,b_l2) ]
          ]

vbss02b = [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_xt) ]
          , makeVarBinding [ (v_b,b_l2) ]
          ]

vbss02c = [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
          , makeVarBinding [ (v_b,b_l1) ]
          , makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_xt) ]
          ]

vbss02d = [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
          , makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_xt) ]
          , makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_xt) ]
          ]

vbss02  = [ vbss02a
          , vbss02b
          , vbss02c
          , vbss02d
          ]

testBackMod20 = testEq "testBackMod20" vbss02 $
                rdfQueryBackModify varBindingId vbss02

testBackMod21 = testEq "testBackMod21" [vbss02d] $
                rdfQueryBackModify
                    (makeVarFilterModify $ rdfVarBindingUriRef v_a)
                    vbss02

--  Variable binding modifier that adds new bindings, if certain
--  others are present.
vbm22 = VarBindingModify
        { vbmName  = swishName "vbm22"
        , vbmApply = concatMap apply1
        , vbmVocab = [v_a,v_b,v_x,v_y]
        , vbmUsage = [[v_y]]
        }
    where
        apply1 :: RDFVarBinding -> [RDFVarBinding]
        apply1 vb = apply2 vb (vbMap vb v_a) (vbMap vb v_b) (vbMap vb v_x)
        apply2 vb (Just a) (Just b) (Just _) =
            [ joinVarBindings nva vb, joinVarBindings nvb vb ]
            where
                nva = makeVarBinding [(v_y,a)]
                nvb = makeVarBinding [(v_y,b)]
        apply2 _ _ _ _ = []

vbss02dy = sequence
    [ [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1), (v_y,u_p1)  ]
      , makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1), (v_y,b_l1)  ]
      ]
    , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2), (v_y,u_p2a) ]
      , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2), (v_y,b_l2)  ]
      ]
    , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2), (v_y,u_p2b) ]
      , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2), (v_y,b_l2)  ]
      ]
    , [ makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_xt), (v_y,u_rt)  ]
      , makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_xt), (v_y,u_xt)  ]
      ]
    , [ makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_xt), (v_y,u_rt)  ]
      , makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_xt), (v_y,u_xt)  ]
      ]
    ]

testBackMod22 = testEq "testBackMod22" vbss02dy $
                rdfQueryBackModify vbm22 vbss02


--  simplified version of above for debugging --

vbss03a = [ makeVarBinding [ (v_x,u_s), (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_b,b_l1) ]
          ]

vbss03b = [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
          , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
          ]

vbss03  = [ vbss03a
          , vbss03b
          ]

vbss03by = sequence
    [ [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1), (v_y,u_p1)  ]
      , makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1), (v_y,b_l1)  ]
      ]
    , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2), (v_y,u_p2a) ]
      , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2), (v_y,b_l2)  ]
      ]
    ]

testBackMod30 = testEq "testBackMod30" vbss03by $
                rdfQueryBackModify vbm22 vbss03

test7 = TestList
    [ testBackMod01, testBackMod02, testBackMod03, testBackMod04
    , testBackMod05, testBackMod06, testBackMod07, testBackMod08
    , testBackMod09, testBackMod10
    , testBackMod20, testBackMod21, testBackMod22
    , testBackMod30
    ]

------------------------------------------------------------
--  Test simple value and list queries
------------------------------------------------------------

namespacetest    =
    Namespace   "test"   "urn:test:"
namespacelist    =
    Namespace   "list"   "urn:list:"

qntest loc = ScopedName namespacetest loc
qnlist loc = ScopedName namespacelist loc

prefixlist =
    "@prefix rdf  : <" ++ nsURI namespaceRDF ++ "> . \n"  ++
    "@prefix xsd  : <" ++ nsURI namespaceXSD ++ "> . \n"  ++
    "@prefix test : <" ++ nsURI namespacetest ++ "> . \n" ++
    "@prefix list : <" ++ nsURI namespacelist ++ "> . \n" ++
    " \n"

graphlist    = graphFromString graphliststr
graphliststr = prefixlist ++
    "test:a rdf:type test:C1 ; "                   ++
    "  test:p test:item1 ; "                       ++
    "  test:p test:item2 . "                       ++
    "test:b rdf:type test:C1 ; "                   ++
    "  test:p \"1\"^^xsd:integer ; "               ++
    "  test:p \"2\"^^xsd:integer ; "               ++
    "  test:p \"3\"^^xsd:integer . "               ++
    "test:c rdf:type test:C1 ; "                   ++
    "  test:q \"1\"^^xsd:integer ; "               ++
    "  test:q \"2\"^^xsd:boolean ; "               ++
    "  test:q \"3\" . "                            ++
    "list:three :- (list:_1 list:_2 list:_3) . \n" ++
    "list:empty :- () . \n"

testC1  = Res (qntest "C1")
testabc = [ Res (qntest "a"),Res (qntest "b"),Res (qntest "c") ]
testp   = Res (qntest "p")
testq   = Res (qntest "q")
testi12 = [ Res (qntest "item1"),Res (qntest "item2") ]
test123 = [ Lit "1" (Just xsd_integer)
          , Lit "2" (Just xsd_integer)
          , Lit "3" (Just xsd_integer)
          ]
test1fp = [ Lit "1" (Just xsd_integer)
          , Lit "2" (Just xsd_boolean)
          , Lit "3" Nothing
          ]

list01 = [Res (qnlist "_1"),Res (qnlist "_2"),Res (qnlist "_3")]
list02 = []

testVal01  = testEqv "testVal01" testabc $
                rdfFindValSubj res_rdf_type testC1 graphlist
testVal02  = testEqv "testVal02" testi12 $
                rdfFindPredVal (testabc!!0) testp graphlist
testVal03  = testEqv "testVal03" test123 $
                rdfFindPredVal (testabc!!1) testp graphlist
testVal04  = testEqv "testVal04" test1fp $
                rdfFindPredVal (testabc!!2) testq graphlist
testVal05  = testEqv "testVal05" [] $
                rdfFindPredVal (testabc!!2) testp graphlist
testVal06  = testEqv "testVal06" [] $
                rdfFindPredInt (testabc!!0) testp graphlist
testVal07  = testEqv "testVal07" [1,2,3] $
                rdfFindPredInt (testabc!!1) testp graphlist
testVal08  = testEqv "testVal08" [1] $
                rdfFindPredInt (testabc!!2) testq graphlist

testlist01 = testEq "testlist01" list01 $
    rdfFindList graphlist (Res $ qnlist "three")
testlist02 = testEq "testlist02" list02 $
    rdfFindList graphlist (Res $ qnlist "empty")

test8 = TestList
    [ testVal01, testVal02, testVal03, testVal04
    , testVal05, testVal06, testVal07, testVal08
    , testlist01, testlist02
    ]

{-----
queryList :: RDFGraph -> RDFLabel -> [RDFLabel]
-- queryList gr res_rdf_nil = []
-- queryList gr hd          = findhead g:rdfQueryList gr (findrest g)
queryList gr hd
    | hd == res_rdf_nil = []
    | otherwise         = (findhead g):(queryList gr (findrest g))
    where
        g = subgr gr hd

findhead g = headOrNil [ ob | Arc _ sb ob <- g, sb == res_rdf_first ]
findrest g = headOrNil [ ob | Arc _ sb ob <- g, sb == res_rdf_rest  ]
subgr g h  = filter ((==) h . arcSubj) $ getArcs g
headOrNil  = foldr const res_rdf_nil

th1  = (Res $ qnlist "empty")
th3  = (Res $ qnlist "three")
th3a = subgr graphlist th3
th3b = findhead th3a
th3c = findrest th3a
tl3c = queryList graphlist th3c
th3d = subgr graphlist th3c
th3e = findhead th3d
th3f = findrest th3d

tl3  = queryList graphlist th3
-----}

------------------------------------------------------------
--  Full test suite, main program,
--  and useful expressions for interactive use
------------------------------------------------------------

allTests = TestList
  [ test1
  , test2
  , test3
  , test4
  , test6
  , test7
  , test8
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

shres32 = TestCase $ assertString (show res32)

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
-- $Source: /file/cvsdev/HaskellRDF/RDFQueryTest.hs,v $
-- $Author: graham $
-- $Revision: 1.23 $
-- $Log: RDFQueryTest.hs,v $
-- Revision 1.23  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.22  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.21  2003/12/20 12:53:40  graham
-- Fix up code to compile and test with GHC 5.04.3
--
-- Revision 1.20  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.19  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.18  2003/11/24 15:46:03  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.17  2003/11/14 16:04:43  graham
-- Add primitive query to get integer values from a graph.
--
-- Revision 1.16  2003/11/14 16:01:30  graham
-- Separate RDFVarBinding from module RDFQuery.
--
-- Revision 1.15  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.14  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.13  2003/10/15 16:40:52  graham
-- Reworked RDFQuery to use new query binding framework.
-- (Note: still uses VarBindingFilter rather than VarBindingModify.
-- The intent is to incorproate the VarBindingModify logic into RDFProof,
-- displaying the existing use of BindingFilter.)
--
-- Revision 1.12  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.11  2003/07/02 22:39:36  graham
-- Subgraph entailment and Graph closure instance entailment rules
-- now tested.  RDF forward chaining revised to combine output graphs,
-- to preserve blank node relationships.
--
-- Revision 1.10  2003/06/26 15:37:23  graham
-- Added rdfQueryInstance, and tests, all works.
--
-- Revision 1.9  2003/06/19 00:26:29  graham
-- Query binding filter methods tested.
--
-- Revision 1.8  2003/06/18 14:59:27  graham
-- Augmented query variable binding structure.
-- RDFQuery tests OK.
--
-- Revision 1.7  2003/06/18 13:47:33  graham
-- Backchaining query tests complete.
--
-- Revision 1.6  2003/06/18 01:29:29  graham
-- Fixed up some problems with backward chaining queries.
-- Query test cases still to complete.
-- Proof incomplete.
--
-- Revision 1.5  2003/06/17 17:53:08  graham
-- Added backward chaining query primitive.
--
-- Revision 1.4  2003/06/17 16:29:20  graham
-- Eliminate redundant Maybe in return type of rdfQueryPrim.
-- (A null list suffices for the Nothing case.)
--
-- Revision 1.3  2003/06/17 15:59:09  graham
-- Update to use revised version of remapNodes, which accepts a
-- node-mapping function rather than just a Boolean to control conversion
-- of query variable nodes to blank
-- nodes.
--
-- Revision 1.2  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.1  2003/06/12 00:49:06  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
