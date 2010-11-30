--------------------------------------------------------------------------------
--  $Id: RDFProofTest.hs,v 1.21 2004/01/06 13:53:10 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFProofTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module tests the RDFproof module, which instantiates the proof
--  rule class over RDF graphs.
--
--------------------------------------------------------------------------------

--  WNH RIP OUTmodule Swish.HaskellRDF.RDFProofTest where

import Swish.HaskellRDF.RDFProof
    ( RDFProof, RDFProofStep
    , makeRDFProof, makeRDFProofStep
    , makeRdfInstanceEntailmentRule
    , makeRdfSubgraphEntailmentRule
    , makeRdfSimpleEntailmentRule
    )

import Swish.HaskellRDF.RDFQuery
    ( rdfQueryFind, rdfQuerySubs )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBindingFilter, RDFVarBindingModify )

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFClosure, RDFRuleset
    , GraphClosure(..), makeGraphClosureRule
    , makeRDFGraphFromN3String
    , makeRDFFormula
    , makeN3ClosureAllocatorRule
    , makeN3ClosureRule
    , makeN3ClosureSimpleRule
    , makeNodeAllocTo
    )

import Swish.HaskellRDF.RDFGraph
    ( Label(..), RDFLabel(..), NSGraph(..), RDFGraph
    , getArcs, add, allLabels, allNodes )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..), nullVarBinding
    , VarBindingModify(..)
    , makeVarFilterModify
    , varBindingId -- , varFilterDisjunction, varFilterConjunction
    , varFilterEQ, varFilterNE
    )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..) )

import Swish.HaskellUtils.Namespace
    ( Namespace(..), ScopedName(..) )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

import Data.Maybe
    ( isJust, fromJust )

--  misc helpers

test :: String -> Bool -> Test
test lab tst = TestCase $ assertBool lab tst

testEq :: (Eq a, Show a) => String -> a -> a -> Test
testEq lab e a = TestCase $ assertEqual lab e a

testJe :: (Eq a, Show a) => String -> a -> Maybe a -> Test
testJe lab e a = TestList
    [ TestCase $ assertBool  lab (isJust a)
    , TestCase $ assertEqual lab e (fromJust a)
    ]

testJl :: (Eq a, Show a) => String -> Int -> Maybe [a] -> Test
testJl lab e a = TestList
    [ TestCase $ assertBool  lab   (isJust a)
    , TestCase $ assertEqual lab e (length (fromJust a))
    ]

testNo :: (Eq a, Show a) => String -> [[a]] -> Test
testNo lab a =
    TestCase $ assertBool  lab   (null a)

testIn :: (Eq a, Show a) => String -> a -> [a] -> Test
testIn lab eg a = TestCase $ assertBool lab (eg `elem` a)

--  test1:  simple query with URI, literal and blank nodes.

scope1 = Namespace "scope1"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope1"

prefix1 =
    "@prefix ex: <http://example.org/> . \n" ++
    " \n"

graph1    = makeRDFGraphFromN3String graph1str
graph1str = prefix1 ++
    "ex:s1  ex:p  ex:o1 . \n"  ++
    "ex:s2  ex:p  \"lit1\" . \n" ++
    "[ ex:p ex:o3 ] . \n"

query11    = makeRDFGraphFromN3String query11str
query11str = prefix1 ++
    "?s  ex:p  ?o . \n"

result11    = makeRDFGraphFromN3String result11str
result11str = prefix1 ++
    "?s  ex:r  ?o . \n"

result11a    = makeRDFGraphFromN3String result11astr
result11astr = prefix1 ++
    "ex:s1  ex:r  ex:o1    . \n" ++
    "ex:s2  ex:r  \"lit1\" . \n" ++
    "[ ex:r ex:o3 ]        . \n"

result11b    = makeRDFGraphFromN3String result11bstr
result11bstr = prefix1 ++
    "ex:s1  ex:r  ex:o1    . \n"

result11c    = makeRDFGraphFromN3String result11cstr
result11cstr = prefix1 ++
    "ex:s2  ex:r  \"lit1\" . \n"

backsub11a    = makeRDFGraphFromN3String backsub11astr
backsub11astr = prefix1 ++
    "ex:s1  ex:p  ex:o1    . \n" ++
    "ex:s2  ex:p  \"lit1\" . \n"

backsub11b    = makeRDFGraphFromN3String backsub11bstr
backsub11bstr = prefix1 ++
    "ex:s2  ex:p  \"lit1\" . \n"

rul11 = makeN3ClosureSimpleRule scope1 "rul11" query11str result11str
fwd11 = fwdApply rul11 [graph1]
testFwd11  = testEq "testFwd11" 1 (length fwd11)
testFwd11a = testIn "testFwd11a" result11a fwd11
bwd11      = bwdApply rul11 (add result11b result11c)
testBwd11  = testEq "testBwd11"  1 (length (head bwd11))
testBwd11a = testIn "testBwd11a" backsub11a (head bwd11)

test1 = TestList
    [ testFwd11
    , testFwd11a
    , testBwd11
    , testBwd11a
    ]


--  test2:  a range of more complex queries based on a
--  single relationship graph.

scope2 = Namespace "scope2"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope2"

prefix2 =
    "@prefix pers: <urn:pers:> . \n"      ++
    "@prefix rel:  <urn:rel:> . \n"       ++
    " \n"

graph2    = makeRDFGraphFromN3String graph2str
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

query21    = makeRDFGraphFromN3String query21str
query21str = prefix2 ++
    "?a rel:wife ?b . \n"

result21    = makeRDFGraphFromN3String result21str
result21str = prefix2 ++
    "?b rel:husband ?a . \n"

result21a    = makeRDFGraphFromN3String result21astr
result21astr = prefix2 ++
    "pers:Do1 rel:husband pers:St1 . \n" ++
    "pers:Ma2 rel:husband pers:Pa2 . \n" ++
    "pers:Ri2 rel:husband pers:Br2 . \n" ++
    "pers:Ma3 rel:husband pers:Gr3 . \n" ++
    "pers:Jo3 rel:husband pers:Si3 . \n" ++
    "pers:Su3 rel:husband pers:Al3 . \n"

result21b    = makeRDFGraphFromN3String result21bstr
result21bstr = prefix2 ++
    "pers:Do1 rel:husband pers:St1 . \n" ++
    "pers:Ma2 rel:husband pers:Pa2 . \n"

bwd21a    = makeRDFGraphFromN3String bwd21astr
bwd21astr = prefix2 ++
    "pers:St1 rel:wife     pers:Do1 . \n" ++
    "pers:Pa2 rel:wife     pers:Ma2 . \n"

rul21 = makeN3ClosureSimpleRule scope2 "rul21" query21str result21str
fwd21 = fwdApply rul21 [graph2]
testFwd21  = testEq "testResult21" 1 (length fwd21)
testFwd21a = testIn "testResult21a" result21a fwd21
bwd21 = bwdApply rul21 result21b
testBwd21  = testEq "testBwd21"  1 (length $ head bwd21)
testBwd21a = testIn "testBwd21a" bwd21a (head bwd21)


query22    = makeRDFGraphFromN3String query22str
query22str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?b rel:son ?c . \n"

result22    = makeRDFGraphFromN3String result22str
result22str = prefix2 ++
    "?a rel:grandparent ?c . \n"

result22a    = makeRDFGraphFromN3String result22astr
result22astr = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ro4 . \n" ++
    "pers:Pa2 rel:grandparent pers:Ol4 . \n" ++
    "pers:Pa2 rel:grandparent pers:Lo4 . \n" ++
    "pers:Pa2 rel:grandparent pers:Ha4 . \n" ++
    "pers:Pa2 rel:grandparent pers:El4 . \n"

result22b    = makeRDFGraphFromN3String result22bstr
result22bstr = prefix2 ++
    "pers:Pa2 rel:grandparent pers:Ro4 . \n" ++
    "pers:Pa2 rel:grandparent pers:Ol4 . \n"

bwd22a    = makeRDFGraphFromN3String bwd22astr
bwd22astr = prefix2 ++
    "pers:Pa2 rel:son      _:p1 . \n" ++
    "_:p1 rel:son      pers:Ro4 . \n" ++
    "pers:Pa2 rel:son      _:p2 . \n" ++
    "_:p2 rel:son      pers:Ol4 . \n"

rul22 = makeN3ClosureSimpleRule scope2 "rul22" query22str result22str
fwd22 = fwdApply rul22 [graph2]
testFwd22  = testEq "testResult22" 1 (length fwd22)
testFwd22a = testIn "testResult22a" result22a fwd22
bwd22 = bwdApply rul22 result22b
testBwd22  = testEq "testBwd22"  1 (length $ head bwd22)
testBwd22a = testIn "testBwd22a" bwd22a (head bwd22)


query23    = makeRDFGraphFromN3String query23str
query23str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

result23    = makeRDFGraphFromN3String result23str
result23str = prefix2 ++
    "?b rel:brother ?c . \n"

result23a    = makeRDFGraphFromN3String result23astr
result23astr = prefix2 ++
    "pers:Gr3 rel:brother pers:Gr3 . \n" ++
    "pers:Gr3 rel:brother pers:La3 . \n" ++
    "pers:Gr3 rel:brother pers:Si3 . \n" ++
    "pers:Gr3 rel:brother pers:Al3 . \n" ++
    "pers:La3 rel:brother pers:Gr3 . \n" ++
    "pers:La3 rel:brother pers:La3 . \n" ++
    "pers:La3 rel:brother pers:Si3 . \n" ++
    "pers:La3 rel:brother pers:Al3 . \n" ++
    "pers:Si3 rel:brother pers:Gr3 . \n" ++
    "pers:Si3 rel:brother pers:La3 . \n" ++
    "pers:Si3 rel:brother pers:Si3 . \n" ++
    "pers:Si3 rel:brother pers:Al3 . \n" ++
    "pers:Al3 rel:brother pers:Gr3 . \n" ++
    "pers:Al3 rel:brother pers:La3 . \n" ++
    "pers:Al3 rel:brother pers:Si3 . \n" ++
    "pers:Al3 rel:brother pers:Al3 . \n" ++
    "pers:Wi3 rel:brother pers:Wi3 . \n" ++
    "pers:Ro4 rel:brother pers:Ro4 . \n" ++
    "pers:Ol4 rel:brother pers:Lo4 . \n" ++
    "pers:Ol4 rel:brother pers:Ol4 . \n" ++
    "pers:Lo4 rel:brother pers:Lo4 . \n" ++
    "pers:Lo4 rel:brother pers:Ol4 . \n" ++
    "pers:Ha4 rel:brother pers:El4 . \n" ++
    "pers:Ha4 rel:brother pers:Ha4 . \n" ++
    "pers:El4 rel:brother pers:El4 . \n" ++
    "pers:El4 rel:brother pers:Ha4 . \n"

result23b    = makeRDFGraphFromN3String result23bstr
result23bstr = prefix2 ++
    "pers:Gr3 rel:brother pers:Gr3 . \n" ++
    "pers:Gr3 rel:brother pers:La3 . \n"

bwd23a    = makeRDFGraphFromN3String bwd23astr
bwd23astr = prefix2 ++
    "_:a1 rel:son pers:Gr3 . \n" ++
    "_:a1 rel:son pers:Gr3 . \n" ++
    "_:a2 rel:son pers:Gr3 . \n" ++
    "_:a2 rel:son pers:La3 . \n"

rul23 = makeN3ClosureSimpleRule scope2 "rul23" query23str result23str
fwd23 = fwdApply rul23 [graph2]
testFwd23  = testEq "testResult23" 1 (length fwd23)
testFwd23a = testIn "testResult23a" result23a fwd23
bwd23 = bwdApply rul23 result23b
testBwd23  = testEq "testBwd23"  1 (length $ head bwd23)
testBwd23a = testIn "testBwd23a" bwd23a (head bwd23)


--  Test case to return multiple alternative bindings
--
--  (?c son ?a, ?c stepSon b) => (?a stepBrother ?b, ?b stepBrother ?a)
--
--  a stepBrother b if
--      (_:c1 son a, _:c1 stepSon b) || (_:c2 stepSon a, _:c2 son b)

graph24    = makeRDFGraphFromN3String graph24str
graph24str = prefix2 ++
    "pers:Ma2 rel:son     pers:Gr3 . \n" ++
    "pers:Ma2 rel:stepson pers:St3 . \n"

query24    = makeRDFGraphFromN3String query24str
query24str = prefix2 ++
    "?c rel:son ?a     . \n" ++
    "?c rel:stepson ?b . \n"

result24    = makeRDFGraphFromN3String result24str
result24str = prefix2 ++
    "?a rel:stepbrother ?b . \n" ++
    "?b rel:stepbrother ?a . \n"

result24a    = makeRDFGraphFromN3String result24astr
result24astr = prefix2 ++
    "pers:Gr3 rel:stepbrother pers:St3 . \n" ++
    "pers:St3 rel:stepbrother pers:Gr3 . \n"

bwd24a1    = makeRDFGraphFromN3String bwd24a1str
bwd24a1str = prefix2 ++
    "_:c1 rel:son     pers:Gr3 . \n" ++
    "_:c1 rel:stepson pers:St3 . \n" ++
    "_:c2 rel:stepson pers:Gr3 . \n" ++
    "_:c2 rel:son     pers:St3 . \n"

bwd24a2    = makeRDFGraphFromN3String bwd24a2str
bwd24a2str = prefix2 ++
    "_:c1 rel:son     pers:Gr3 . \n" ++
    "_:c1 rel:stepson pers:St3 . \n"

bwd24a3    = makeRDFGraphFromN3String bwd24a3str
bwd24a3str = prefix2 ++
    "_:c2 rel:stepson pers:Gr3 . \n" ++
    "_:c2 rel:son     pers:St3 . \n"

bwd24a4    = makeRDFGraphFromN3String bwd24a4str
bwd24a4str = prefix2 ++
    "_:c1 rel:son     pers:Gr3 . \n" ++
    "_:c1 rel:stepson pers:St3 . \n" ++
    "_:c2 rel:stepson pers:Gr3 . \n" ++
    "_:c2 rel:son     pers:St3 . \n"

rul24 = makeN3ClosureSimpleRule scope2 "rul24" query24str result24str
fwd24 = fwdApply rul24 [graph24]
testFwd24  = testEq "testResult24" 1 (length fwd24)
testFwd24a = testIn "testResult24a" result24a fwd24
bwd24 = bwdApply rul24 result24a
testBwd24   = testEq "testBwd24"  4 (length bwd24)
testBwd24a1 = testIn "testBwd24a1" bwd24a1 (bwd24!!0)
testBwd24a2 = testIn "testBwd24a2" bwd24a2 (bwd24!!1)
testBwd24a3 = testIn "testBwd24a3" bwd24a3 (bwd24!!2)
testBwd24a4 = testIn "testBwd24a4" bwd24a4 (bwd24!!3)


--  bwd chain from partial conclusion
--  Also, fail because conclusion is more than the rule
--  can derive from any input.

query25    = makeRDFGraphFromN3String query25str
query25str = prefix2 ++
    "?a rel:son      ?b . \n" ++
    "?a rel:daughter ?c . \n"

result25    = makeRDFGraphFromN3String result25str
result25str = prefix2 ++
    "?b rel:sister  ?c . \n" ++
    "?c rel:brother ?b . \n"

result25a    = makeRDFGraphFromN3String result25astr
result25astr = prefix2 ++
    "pers:Wi3 rel:sister  pers:Ma3 . \n" ++
    "pers:Ma3 rel:brother pers:Wi3 . \n" ++
    "pers:Ro4 rel:sister  pers:Rh4 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n"

{-
result25b    = makeRDFGraphFromN3String result25bstr
result25bstr = prefix2 ++
    "pers:Ro4 rel:sister  pers:Rh4 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n"
-}

result25c    = makeRDFGraphFromN3String result25cstr
result25cstr = prefix2 ++
    "pers:Wi3 rel:sister  pers:Ma3 . \n" ++
    "pers:Ma3 rel:brother pers:Wi3 . \n" ++
    "pers:Ro4 rel:sister  pers:Rh4 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n" ++
    "pers:xx3 rel:mother  pers:yy3 . \n" ++
    "pers:yy3 rel:brother pers:xx3 . \n"

result25d    = makeRDFGraphFromN3String result25dstr
result25dstr = prefix2 ++
    "pers:Wi3 rel:sister  pers:Ma3 . \n" ++
    "pers:Ma3 rel:brother pers:Wi3 . \n" ++
    "pers:Ro4 rel:sister  pers:Rh4 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n" ++
    "pers:xx3 rel:father  pers:yy3 . \n"

conc25    = makeRDFGraphFromN3String conc25str
conc25str = prefix2 ++
    "pers:Wi3 rel:sister  pers:Ma3 . \n" ++
    "pers:Rh4 rel:brother pers:Ro4 . \n"

bwd25a    = makeRDFGraphFromN3String bwd25astr
bwd25astr = prefix2 ++
    "_:a1 rel:son      pers:Wi3 . \n" ++
    "_:a1 rel:daughter pers:Ma3 . \n" ++
    "_:a2 rel:son      pers:Ro4 . \n" ++
    "_:a2 rel:daughter pers:Rh4 . \n"

rul25 = makeN3ClosureSimpleRule scope2 "rul25" query25str result25str
fwd25 = fwdApply rul25 [graph2]
testFwd25  = testEq "testResult25" 1 (length fwd25)
testFwd25a = testIn "testResult25a" result25a fwd25
bwd25 = bwdApply rul25 conc25
testBwd25  = testEq "testBwd25"  1 (length $ head bwd25)
testBwd25a = testIn "testBwd25a" bwd25a (head bwd25)
-- testBwd25a1 = testEq "testBwd25a" bwd25a (head $ head bwd25)
bwd25c = bwdApply rul25 result25c
testBwd25c = testNo "testBwd25c" bwd25c
bwd25d = bwdApply rul25 result25d
testBwd25d = testNo "testBwd25d" bwd25d


test2 = TestList
    [ testFwd21
    , testFwd21a
    , testBwd21
    , testBwd21a
    , testFwd22
    , testFwd22a
    , testBwd22
    , testBwd22a
    , testFwd23
    , testFwd23a
    , testBwd23
    , testBwd23a
    , testFwd24, testFwd24a
    , testBwd24, testBwd24a1, testBwd24a2, testBwd24a3, testBwd24a4
    , testFwd25
    , testFwd25a
    , testBwd25
    , testBwd25a, testBwd25c, testBwd25d
    ]

--  test3:  check variable binding filters

scope3 = Namespace "scope3"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope3"

query31    = makeRDFGraphFromN3String query31str
query31str = prefix2 ++
    "?a rel:son ?b . \n" ++
    "?a rel:son ?c . \n"

modify31 :: RDFVarBindingModify
modify31 = makeVarFilterModify $ varFilterNE (Var "b") (Var "c")

result31    = makeRDFGraphFromN3String result31str
result31str = prefix2 ++
    "?b rel:brother ?c . \n"

result31a    = makeRDFGraphFromN3String result31astr
result31astr = prefix2 ++
    "pers:Gr3 rel:brother pers:La3 . \n" ++
    "pers:Gr3 rel:brother pers:Si3 . \n" ++
    "pers:Gr3 rel:brother pers:Al3 . \n" ++
    "pers:La3 rel:brother pers:Gr3 . \n" ++
    "pers:La3 rel:brother pers:Si3 . \n" ++
    "pers:La3 rel:brother pers:Al3 . \n" ++
    "pers:Si3 rel:brother pers:Gr3 . \n" ++
    "pers:Si3 rel:brother pers:La3 . \n" ++
    "pers:Si3 rel:brother pers:Al3 . \n" ++
    "pers:Al3 rel:brother pers:Gr3 . \n" ++
    "pers:Al3 rel:brother pers:La3 . \n" ++
    "pers:Al3 rel:brother pers:Si3 . \n" ++
    "pers:Ol4 rel:brother pers:Lo4 . \n" ++
    "pers:Lo4 rel:brother pers:Ol4 . \n" ++
    "pers:Ha4 rel:brother pers:El4 . \n" ++
    "pers:El4 rel:brother pers:Ha4 . \n"

result31b    = makeRDFGraphFromN3String result31bstr
result31bstr = prefix2 ++
    "pers:Gr3 rel:brother pers:Gr3 . \n"

result31c    = makeRDFGraphFromN3String result31cstr
result31cstr = prefix2 ++
    "pers:Gr3 rel:brother pers:La3 . \n"

bwd31c    = makeRDFGraphFromN3String bwd31cstr
bwd31cstr = prefix2 ++
    "_:a rel:son pers:Gr3 . \n" ++
    "_:a rel:son pers:La3 . \n"

rul31 = makeN3ClosureRule scope3 "rul31" query31str result31str modify31
fwd31 = fwdApply rul31 [graph2]
testFwd31  = testEq "testResult31" 1 (length fwd31)
testFwd31a = testIn "testResult31a" result31a fwd31
calcbwd31b = bwdApply rul31 result31b
testBwd31b = testEq "testBwd31"  0 (length calcbwd31b)
calcbwd31c = bwdApply rul31 result31c
testBwd31cn = testEq "testBwd31"  1 (length $ head calcbwd31c)
testBwd31c  = testIn "testBwd31c" bwd31c (head calcbwd31c)

test3 = TestList
    [ testFwd31
    , testFwd31a
    , testBwd31b
    , testBwd31cn, testBwd31c
    ]

--  Instance entailment tests

scope4 = Namespace "scope4"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope4"

graph4    = makeRDFGraphFromN3String graph4str
graph4str = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter pers:Rh4 . \n"

vocab4 = allNodes (not . labelIsVar) graph4

name4 = ScopedName scope4 "instance4"

rule4 = makeRdfInstanceEntailmentRule name4 vocab4

fwd42a    = makeRDFGraphFromN3String fwd42astr
fwd42astr = prefix2 ++
    "pers:Gr3 rel:son      _:Ro4 ;    \n" ++
    "         rel:daughter pers:Rh4 . \n"

fwd42b    = makeRDFGraphFromN3String fwd42bstr
fwd42bstr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter _:Rh4 .    \n"

fwd42c    = makeRDFGraphFromN3String fwd42cstr
fwd42cstr = prefix2 ++
    "pers:Gr3 rel:son      _:Ro4 ;    \n" ++
    "         rel:daughter _:Rh4 .    \n"

fwd42d    = makeRDFGraphFromN3String fwd42dstr
fwd42dstr = prefix2 ++
    "_:Gr3    rel:son      _:Ro4 ;    \n" ++
    "         rel:daughter pers:Rh4 . \n"

fwd42e    = makeRDFGraphFromN3String fwd42estr
fwd42estr = prefix2 ++
    "_:Gr3    rel:son      _:Ro4 ;    \n" ++
    "         rel:daughter pers:Rh4 . \n"

fwd42f    = makeRDFGraphFromN3String fwd42fstr
fwd42fstr = prefix2 ++
    "_:Gr3    rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter _:Rh4 .    \n"

fwd42g    = makeRDFGraphFromN3String fwd42gstr
fwd42gstr = prefix2 ++
    "_:Gr3    rel:son      _:Ro4 ;    \n" ++
    "         rel:daughter _:Rh4 .    \n"

--  Non-entailments

fwd42w    = makeRDFGraphFromN3String fwd42wstr
fwd42wstr = prefix2 ++
    "pers:Gr3 rel:daughter pers:Ro4 . \n"

fwd42x    = makeRDFGraphFromN3String fwd42xstr
fwd42xstr = prefix2 ++
    "pers:Gr3 rel:daughter pers:Ro4 . \n"

fwd42y    = makeRDFGraphFromN3String fwd42ystr
fwd42ystr = prefix2 ++
    "_:Gr3    rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter pers:Ro4 . \n"

fwd42z    = makeRDFGraphFromN3String fwd42zstr
fwd42zstr = prefix2 ++
    "_:Gr3    rel:son      _:Ro4 ; \n" ++
    "         rel:son      _:Rh4 . \n"


bwd43 = makeRDFGraphFromN3String bwd43str
bwd43str = prefix2 ++
    "_:a1 rel:son      pers:Ro4 . \n" ++
    "_:a2 rel:daughter pers:Rh4 . \n"

bwd43a = makeRDFGraphFromN3String bwd43astr
bwd43astr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n" ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n"

bwd43b = makeRDFGraphFromN3String bwd43bstr
bwd43bstr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n" ++
    "pers:Ro4 rel:daughter pers:Rh4 . \n"

bwd43c = makeRDFGraphFromN3String bwd43cstr
bwd43cstr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n" ++
    "pers:Rh4 rel:daughter pers:Rh4 . \n"

bwd43d = makeRDFGraphFromN3String bwd43dstr
bwd43dstr = prefix2 ++
    "pers:Ro4 rel:son      pers:Ro4 . \n" ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n"

bwd43e = makeRDFGraphFromN3String bwd43estr
bwd43estr = prefix2 ++
    "pers:Ro4 rel:son      pers:Ro4 . \n" ++
    "pers:Ro4 rel:daughter pers:Rh4 . \n"

bwd43f = makeRDFGraphFromN3String bwd43fstr
bwd43fstr = prefix2 ++
    "pers:Ro4 rel:son      pers:Ro4 . \n" ++
    "pers:Rh4 rel:daughter pers:Rh4 . \n"

bwd43g = makeRDFGraphFromN3String bwd43gstr
bwd43gstr = prefix2 ++
    "pers:Rh4 rel:son      pers:Ro4 . \n" ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n"

bwd43h = makeRDFGraphFromN3String bwd43hstr
bwd43hstr = prefix2 ++
    "pers:Rh4 rel:son      pers:Ro4 . \n" ++
    "pers:Ro4 rel:daughter pers:Rh4 . \n"

bwd43i = makeRDFGraphFromN3String bwd43istr
bwd43istr = prefix2 ++
    "pers:Rh4 rel:son      pers:Ro4 . \n" ++
    "pers:Rh4 rel:daughter pers:Rh4 . \n"

--  Check basics
testRuleName41 = testEq "testRuleName41" name4 (ruleName rule4)
testVocab41    = testEq "testVocab41"    3     (length vocab4)

--  Forward chaining
fwdApply42      = fwdApply rule4 [graph4]
testFwdLength42 = testEq "testFwdLength42" 7 (length fwdApply42)
testFwdApply42a = testIn "testFwdApply42a"  fwd42a fwdApply42
testFwdApply42b = testIn "testFwdApply42b"  fwd42b fwdApply42
testFwdApply42c = testIn "testFwdApply42c"  fwd42c fwdApply42
testFwdApply42d = testIn "testFwdApply42d"  fwd42d fwdApply42
testFwdApply42e = testIn "testFwdApply42e"  fwd42e fwdApply42
testFwdApply42f = testIn "testFwdApply42f"  fwd42f fwdApply42
testFwdApply42g = testIn "testFwdApply42g"  fwd42g fwdApply42

--  Backward chaining
bwdApply43      = bwdApply rule4 bwd43
testBwdLength43 = testEq "testBwdLength43" 9 (length bwdApply43)
testBwdApply43a = testIn "testBwdApply43a"  [bwd43a] bwdApply43
testBwdApply43b = testIn "testBwdApply43b"  [bwd43b] bwdApply43
testBwdApply43c = testIn "testBwdApply43c"  [bwd43c] bwdApply43
testBwdApply43d = testIn "testBwdApply43d"  [bwd43d] bwdApply43
testBwdApply43e = testIn "testBwdApply43e"  [bwd43e] bwdApply43
testBwdApply43f = testIn "testBwdApply43f"  [bwd43f] bwdApply43
testBwdApply43g = testIn "testBwdApply43g"  [bwd43g] bwdApply43
testBwdApply43h = testIn "testBwdApply43h"  [bwd43h] bwdApply43
testBwdApply43i = testIn "testBwdApply43i"  [bwd43i] bwdApply43

--  Entailment checks
testEntail44a   = testEq "testEntail44a" True  (checkInference rule4 [graph4] fwd42a)
testEntail44b   = testEq "testEntail44b" True  (checkInference rule4 [graph4] fwd42b)
testEntail44g   = testEq "testEntail44g" True  (checkInference rule4 [graph4] fwd42g)
testEntail44w   = testEq "testEntail44w" False (checkInference rule4 [graph4] fwd42w)
testEntail44x   = testEq "testEntail44x" False (checkInference rule4 [graph4] fwd42x)
testEntail44y   = testEq "testEntail44y" False (checkInference rule4 [graph4] fwd42y)
testEntail44z   = testEq "testEntail44z" False (checkInference rule4 [graph4] fwd42z)

test4 = TestList
    [ testRuleName41
    , testVocab41
    , testFwdLength42
    , testFwdApply42a
    , testFwdApply42b
    , testFwdApply42c
    , testFwdApply42d
    , testFwdApply42e
    , testFwdApply42f
    , testFwdApply42g
    , testBwdLength43
    , testBwdApply43a
    , testBwdApply43b
    , testBwdApply43c
    , testBwdApply43d
    , testBwdApply43e
    , testBwdApply43f
    , testBwdApply43g
    , testBwdApply43h
    , testBwdApply43i
    , testEntail44a
    , testEntail44b
    , testEntail44g
    , testEntail44w
    , testEntail44x
    , testEntail44y
    , testEntail44z
    ]

--  Subgraph entailment tests

scope5 = Namespace "scope5"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope5"

graph5    = makeRDFGraphFromN3String graph5str
graph5str = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter pers:Rh4 . \n" ++
    "pers:Si3 rel:son      pers:Ol4 . \n"

name5 = ScopedName scope5 "subgraph5"

rule5 = makeRdfSubgraphEntailmentRule name5

--  Forward chaining excludes null agraph and copy of antecedent
fwd52a    = makeRDFGraphFromN3String fwd52astr
fwd52astr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n"

fwd52b    = makeRDFGraphFromN3String fwd52bstr
fwd52bstr = prefix2 ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n"

fwd52c    = makeRDFGraphFromN3String fwd52cstr
fwd52cstr = prefix2 ++
    "pers:Si3 rel:son      pers:Ol4 . \n"

fwd52d    = makeRDFGraphFromN3String fwd52dstr
fwd52dstr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n" ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n"

fwd52e    = makeRDFGraphFromN3String fwd52estr
fwd52estr = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 . \n" ++
    "pers:Si3 rel:son      pers:Ol4 . \n"

fwd52f    = makeRDFGraphFromN3String fwd52fstr
fwd52fstr = prefix2 ++
    "pers:Gr3 rel:daughter pers:Rh4 . \n" ++
    "pers:Si3 rel:son      pers:Ol4 . \n"

--  Check basics
testRuleName51 = testEq "testRuleName51" name5 (ruleName rule5)

--  Forward chaining
fwdApply52      = fwdApply rule5 [graph5]
testFwdLength52 = testEq "testFwdLength52" 6 (length fwdApply52)
testFwdApply52a = testIn "testFwdApply52a"  fwd52a fwdApply52
testFwdApply52b = testIn "testFwdApply52b"  fwd52b fwdApply52
testFwdApply52c = testIn "testFwdApply52c"  fwd52c fwdApply52
testFwdApply52d = testIn "testFwdApply52d"  fwd52d fwdApply52
testFwdApply52e = testIn "testFwdApply52e"  fwd52e fwdApply52
testFwdApply52f = testIn "testFwdApply52f"  fwd52f fwdApply52

test5 = TestList
    [ testRuleName51
    , testFwdLength52
    , testFwdApply52a
    , testFwdApply52b
    , testFwdApply52c
    , testFwdApply52d
    , testFwdApply52e
    , testFwdApply52f
    ]

--  Simple entailment test
--  Simple entailment provides entailment check only, no forward or
--  backward chaining.  For that use instance- and subgraph- rules.

scope6 = Namespace "scope6"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope6"

graph6    = makeRDFGraphFromN3String graph6str
graph6str = prefix2 ++
    "pers:Gr3 rel:son      pers:Ro4 ; \n" ++
    "         rel:daughter pers:Rh4 . \n" ++
    "pers:Si3 rel:son      pers:Ol4 ; \n" ++
    "         rel:son      pers:Lo4 . \n"

name6 = ScopedName scope5 "subgraph6"

rule6 = makeRdfSimpleEntailmentRule name6

simple6a    = makeRDFGraphFromN3String simple6astr
simple6astr = prefix2 ++
    "_:Gr3 rel:son      pers:Ro4 ; \n" ++
    "      rel:daughter pers:Rh4 . \n"

simple6b    = makeRDFGraphFromN3String simple6bstr
simple6bstr = prefix2 ++
    "_:Si3 rel:son      pers:Ol4 ; \n" ++
    "      rel:son      pers:Lo4 . \n"

simple6c    = makeRDFGraphFromN3String simple6cstr
simple6cstr = prefix2 ++
    "_:Si3 rel:son      _:Ol4 ; \n" ++
    "      rel:son      _:Lo4 . \n"

simple6d    = makeRDFGraphFromN3String simple6dstr
simple6dstr = prefix2 ++
    "_:Si3 rel:son      _:Ol4 ; \n" ++
    "      rel:daughter _:Lo4 . \n"

simple6e    = makeRDFGraphFromN3String simple6estr
simple6estr = prefix2 ++
    "_:Si3 rel:daughter _:Ol4 ; \n" ++
    "      rel:mother   _:Lo4 . \n"

testRuleName61 = testEq "testRuleName61" name6 (ruleName rule6)
testSimple62 = test "testSimple62" (checkInference rule6 [graph6] simple6a)
testSimple63 = test "testSimple63" (checkInference rule6 [graph6] simple6b)
testSimple64 = test "testSimple64" (checkInference rule6 [graph6] simple6c)
testSimple65 = test "testSimple65" (checkInference rule6 [graph6] simple6d)
testSimple66 = test "testSimple66" (not $ checkInference rule6 [graph6] simple6e)
testFwd67    = test "testFwd64"    (null $ fwdApply rule6 [graph6])
testBwd68    = test "testBwd65"    (null $ bwdApply rule6 graph6)

test6 = TestList
    [ testRuleName61
    , testSimple62
    , testSimple63
    , testSimple64
    , testSimple65
    , testSimple66
    , testFwd67
    , testBwd68
    ]

--  Test forward chaining node allocation logic
--
--  ?a uncle ?c => ?a father ?b, ?b brother ?c,   ?b allocTo ?a
--
--    Ro4 uncle La3, Ro4 uncle Si3, Rh4 uncle La3, Rh4 uncle Si3
--  =>
--    Ro4 father _:f1, _:f1 brother La3,
--    Ro4 father _:f1, _:f1 brother Si3,
--    Rh4 father _:f2, _:f2 brother La3,
--    Rh4 father _:f2, _:f2 brother Si3

scope7 = Namespace "scope7"
    "http://id.ninebynine.org/wip/2003/rdfprooftest/scope7"

graph7    = makeRDFGraphFromN3String graph7str
graph7str = prefix2 ++
    "pers:Ro4 rel:uncle pers:La3 ; \n" ++
    "         rel:uncle pers:Si3 . \n" ++
    "pers:Rh4 rel:uncle pers:La3 ; \n" ++
    "         rel:uncle pers:Si3 . \n"

query71    = makeRDFGraphFromN3String query71str
query71str = prefix2 ++
    "?a rel:uncle ?c . \n"

result71    = makeRDFGraphFromN3String result71str
result71str = prefix2 ++
    "?a rel:father  ?b . \n" ++
    "?b rel:brother ?c . \n"

result71a    = makeRDFGraphFromN3String result71astr
result71astr = prefix2 ++
    "pers:Ro4 rel:father  _:f1     . \n" ++
    "_:f1     rel:brother pers:La3 . \n" ++
    "pers:Ro4 rel:father  _:f1     . \n" ++
    "_:f1     rel:brother pers:Si3 . \n" ++
    "pers:Rh4 rel:father  _:f2     . \n" ++
    "_:f2     rel:brother pers:La3 . \n" ++
    "pers:Rh4 rel:father  _:f2     . \n" ++
    "_:f2     rel:brother pers:Si3 . \n"

rul71 = makeN3ClosureAllocatorRule scope7 "rul71"
    query71str result71str varBindingId mod71

mod71 = makeNodeAllocTo (Var "b") (Var "a")

var71      = rdfQueryFind query71 graph7
testVar71  = testEq "testVar71" 4 (length var71)
var71a     = vbmApply (mod71 (allLabels labelIsVar graph7)) var71
testVar71a = testEq "testVar71a" 4 (length var71a)
var71_1    = head var71a
map71a     = Just (Var "#a")
map71b     = Just (Var "#b")
map71c     = Just (Var "#c")
testVar71_1a = testEq "testVar71_1a" map71a ( vbMap var71_1 (Var "a"))
testVar71_1b = testEq "testVar71_1b" map71b ( vbMap var71_1 (Var "b"))
testVar71_1c = testEq "testVar71_1c" map71c ( vbMap var71_1 (Var "c"))
sub71a     = rdfQuerySubs var71a result71
testSub71a = testEq "testVar71a" 4 (length sub71a)

fwd71 = fwdApply rul71 [graph7]
testFwd71  = testEq "testResult71" 1 (length fwd71)
testFwd71a = testIn "testResult71a" result71a fwd71

test7 = TestList
    [ testVar71,  testVar71a
    -- , testVar71_1a, testVar71_1b, testVar71_1c
    , testSub71a
    , testFwd71
    , testFwd71a
    ]

--  Full test suite, main program, and useful expressions for interactive use

allTests = TestList
  [ test1
  , test2
  , test3
  , test4
  , test5
  , test6
  , test7
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
-- $Source: /file/cvsdev/HaskellRDF/RDFProofTest.hs,v $
-- $Author: graham $
-- $Revision: 1.21 $
-- $Log: RDFProofTest.hs,v $
-- Revision 1.21  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.20  2003/12/20 12:53:40  graham
-- Fix up code to compile and test with GHC 5.04.3
--
-- Revision 1.19  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.18  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.17  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.16  2003/10/24 21:05:09  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
-- Revision 1.15  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.14  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.13  2003/09/30 20:02:39  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.12  2003/09/30 16:39:41  graham
-- Refactor proof code to use new ruleset logic.
-- Moved some support code from RDFProofCheck to RDFRuleset.
--
-- Revision 1.11  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.10  2003/07/02 22:39:36  graham
-- Subgraph entailment and Graph closure instance entailment rules
-- now tested.  RDF forward chaining revised to combine output graphs,
-- to preserve blank node relationships.
--
-- Revision 1.9  2003/07/02 21:27:30  graham
-- Graph closure with instance rule tested.
-- About to change ProofTest for graph forward chaining to return
-- a single result graph.
--
-- Revision 1.8  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.7  2003/06/27 20:46:00  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.6  2003/06/25 10:18:55  graham
-- Added variable binding filter test case for forward and backward chaining.
--
-- Revision 1.5  2003/06/25 09:52:25  graham
-- Replaced Rule class with algebraic data type
--
-- Revision 1.4  2003/06/19 19:49:07  graham
-- RDFProofCheck compiles, but test fails
--
-- Revision 1.3  2003/06/18 18:40:08  graham
-- Basic proof backchaining tests OK.
-- Next:  add filtering on variable bindings.
--
-- Revision 1.2  2003/06/18 01:29:29  graham
-- Fixed up some problems with backward chaining queries.
-- Query test cases still to complete.
-- Proof incomplete.
--
-- Revision 1.1  2003/06/13 21:43:47  graham
-- Add proof test module.
-- Many tests pass, backward chaining still problem.
-- Need to add proof-checker test cases.
--
