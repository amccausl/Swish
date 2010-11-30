--------------------------------------------------------------------------------
--  $Id: RDFRulesetTest.hs,v 1.12 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFRulesetTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains test cases for ruleset data.
--
--  Note that the proof-related methods defined in RDFRuleset are tested
--  by RDFProofTest and/or RDFProofCheck.
--
{--------+---------+---------+---------+---------+---------+---------+---------}

--   WNH RIP OUTmodule Swish.HaskellRDF.RDFRulesetTest where

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFClosure, RDFRuleset
    , nullRDFFormula
    , GraphClosure(..), makeGraphClosureRule
    , makeRDFGraphFromN3String
    , makeRDFFormula
    , makeN3ClosureAllocatorRule
    , makeN3ClosureRule
    , makeN3ClosureSimpleRule
    , makeNodeAllocTo
    -- for debugging
    , graphClosureFwdApply, graphClosureBwdApply
    )

import Swish.HaskellRDF.RDFQuery
    ( rdfQueryBack, rdfQueryBackFilter, rdfQueryBackModify )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding
    , RDFVarBindingModify
    , RDFVarBindingFilter
    , rdfVarBindingUriRef, rdfVarBindingBlank
    , rdfVarBindingLiteral
    , rdfVarBindingUntypedLiteral, rdfVarBindingTypedLiteral
    , rdfVarBindingXMLLiteral, rdfVarBindingDatatyped
    , rdfVarBindingMemberProp
    )

import Swish.HaskellRDF.RDFGraph
    ( Label (..), RDFLabel(..), RDFGraph
    , setArcs, getArcs, addArc, add, delete, extract, labels, merge
    , allLabels, allNodes, remapLabels, remapLabelList
    , toRDFGraph, emptyRDFGraph
    , Label (..), Arc(..), arc, arcSubj, arcPred, arcObj, Selector
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..), nullVarBinding
    , makeVarBinding
    , vbmCompatibility, vbmCompose
    , makeVarFilterModify
    )

import Swish.HaskellRDF.Ruleset
    ( Ruleset(..)
    , makeRuleset, getRulesetNamespace, getRulesetAxioms, getRulesetRules
    , getRulesetAxiom, getRulesetRule
    , getContextAxiom, getContextRule, getMaybeContextRule )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..)
    , fwdCheckInference
    , showsFormula, showsFormulae, showsWidth )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI
    , makeScopedName
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceRDFO
    , namespaceOWL
    , scopeRDF
    )

import Swish.HaskellUtils.QName
    ( QName(..) )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle
    )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn
    )

import Data.List
    ( nub, sort )

import Data.Maybe
    ( isJust, fromJust )

------------------------------------------------------------
--  Test case helpers
------------------------------------------------------------

test :: String -> Bool -> Test
test lab bv =
    TestCase ( assertBool ("test:"++lab) bv )

testVal :: (Eq a, Show a) => String -> a -> a -> Test
testVal lab a1 a2 =
    TestCase ( assertEqual ("testVal:"++lab) a1 a2 )

testEq :: (Eq a, Show a) => String -> Bool -> a -> a -> Test
testEq lab eq a1 a2 =
    TestCase ( assertEqual ("testEq:"++lab) eq (a1==a2) )

testEqual :: (Eq a, Show a) => String -> a -> a -> Test
testEqual lab a1 a2 =
    TestCase ( assertEqual ("testEq:"++lab) a1 a2 )

testLe :: (Ord a, Show a) => String -> Bool -> a -> a -> Test
testLe lab eq a1 a2 =
    TestCase ( assertEqual ("testLe:"++lab) eq (a1<=a2) )

testStringEq :: String -> String -> String -> Test
testStringEq lab s1 s2 =
    TestCase ( assertEqual ("testStringEq:"++lab) s1 s2 )

testSameNamespace :: String -> Namespace -> Namespace -> Test
testSameNamespace lab n1 n2 =
    TestCase ( assertBool ("testSameNamespace:"++lab) ((p1==p2)&&(u1==u2)) )
    where
        p1 = nsPrefix n1
        p2 = nsPrefix n2
        u1 = nsURI n1
        u2 = nsURI n2

testScopedNameEq :: String -> Bool -> ScopedName -> ScopedName -> Test
testScopedNameEq lab eq n1 n2 =
    TestCase ( assertEqual ("testScopedNameEq:"++lab) eq (n1==n2) )

{-
testQNameEq :: String -> Bool -> QName -> QName -> Test
testQNameEq lab eq n1 n2 =
    TestCase ( assertEqual ("testQNameEq:"++lab) eq (n1==n2) )
-}

testSameAxioms :: String -> [RDFFormula] -> [RDFFormula] -> Test
testSameAxioms lab as1 as2 =
    TestCase ( assertBool ("testSameAxioms:"++lab) sameas )
    where
        sameas = (sort as1) == (sort as2)

testSameRules :: String -> [RDFRule] -> [RDFRule] -> Test
testSameRules lab rs1 rs2 =
    TestCase ( assertBool ("testSameRules:"++lab) samers )
    where
        samers = (sort rs1) == (sort rs2)

------------------------------------------------------------
--  Common values
------------------------------------------------------------

pref_rdf = nsURI namespaceRDF
pref_op  = nsURI namespaceRDFO
pref_owl = nsURI namespaceOWL

------------------------------------------------------------
--  Define and manipulate rulesets
------------------------------------------------------------
--
--  A ruleset is essentially a collection of axioms and rules
--  associated with a namespace.
--
--  Rulesets for RDF, RDFS and basic datatyping are predefined:
--  see RDFRuleset, RDFSRuleset and RDFDRuleset.
--  Additional rulesets may be defined for specific datatypes.
--
--  A proof context is a list of rulesets,
--  which may be cited by a proof.

rn1  = Namespace "r1" "http://id.ninebynine.org/wip/2003/rulesettest/r1"

-- Common prefix declarations for graph expressions
pref =
    "@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . \n" ++
    "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . \n" ++
    "@prefix ex:   <http://example.org/> . \n" ++
    " \n"

a11  = makeRDFFormula rn1 "a11" (pref++"ex:R1 rdf:type ex:C1 .")
a12  = makeRDFFormula rn1 "a12" (pref++"ex:R2 rdf:type ex:C2 .")

r11  = makeN3ClosureSimpleRule rn1 "r11"
            ( pref++"?r1 rdf:type ex:C1 . ?r2 rdf:type ex:C2 ." )
            ( pref++"?r1 ex:P1 ?r2 ." )

r12  = makeN3ClosureSimpleRule rn1 "r12"
            ( pref++"?r1 rdf:type ex:C1 . ?r2 rdf:type ex:C2 ." )
            ( pref++"?r2 ex:P2 ?r1 ." )

--  Basic formula and rule comparison tests
--  (tests support code added in module Proof.hs)

testCmpAX01 = testEq "testCmpAX01" True  a11 a11
testCmpAX02 = testEq "testCmpAX02" False a11 a12
testCmpAX03 = testLe "testCmpAX03" True  a11 a11
testCmpAX04 = testLe "testCmpAX04" True  a11 a12
testCmpAX05 = testLe "testCmpAX05" False a12 a11

testFormulaSuite = TestList
    [ testCmpAX01, testCmpAX02, testCmpAX03, testCmpAX04, testCmpAX05
    ]

testCmpRU01 = testEq "testCmpRU01" True  r11 r11
testCmpRU02 = testEq "testCmpRU02" False r11 r12
testCmpRU03 = testLe "testCmpRU03" True  r11 r11
testCmpRU04 = testLe "testCmpRU04" True  r11 r12
testCmpRU05 = testLe "testCmpRU05" False r12 r11

testRuleSuite = TestList
    [ testCmpRU01, testCmpRU02, testCmpRU03, testCmpRU04, testCmpRU05
    ]

--  Test simple ruleset construction and access

a1s  = [ a11, a12 ]

r1s  = [ r11, r12 ]

r1   = makeRuleset rn1 a1s r1s

testNS01  = testSameNamespace "testNS01" rn1 (getRulesetNamespace r1)
testAX01  = testSameAxioms    "testAX01" a1s (getRulesetAxioms r1)
testRU01  = testSameRules     "testRU01" r1s (getRulesetRules r1)

testGeta11 = testEqual "testGeta11" (Just a11) $
    getRulesetAxiom (ScopedName rn1 "a11") r1
testGeta12 = testEqual "testGeta11" (Just a12) $
    getRulesetAxiom (ScopedName rn1 "a12") r1
testGetr11 = testEqual "testGetr11" (Just r11) $
    getRulesetRule (ScopedName rn1 "r11") r1
testGetr12 = testEqual "testGetr12" (Just r12) $
    getRulesetRule (ScopedName rn1 "r12") r1
testGetnone = testEqual "testGetnone" Nothing $
    getRulesetRule (ScopedName rn1 "none") r1

testRulesetSuite = TestList
    [ testNS01, testAX01, testRU01
    , testGeta11, testGeta12
    , testGetr11, testGetr12
    , testGetnone
    ]

------------------------------------------------------------
--  Component tests for RDF proof context
------------------------------------------------------------

prefix =
    "@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . \n" ++
    "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . \n" ++
    "@prefix ex:   <http://example.org/> . \n" ++
    " \n"

scopeex   = Namespace "ex"   "http://id.ninebynine.org/wip/2003/RDFProofCheck#"

makeFormula :: Namespace -> String -> String -> RDFFormula
makeFormula scope local gr =
    makeRDFFormula scope local (prefix++gr)

allocateTo :: String -> String -> [RDFLabel] -> RDFVarBindingModify
allocateTo bv av = makeNodeAllocTo (vn bv) (vn av)
    where
        vn ('?':n) = Var n

isXMLLit     ('?':x) = rdfVarBindingXMLLiteral     (Var x)

queryBack :: [Arc RDFLabel] -> RDFGraph -> [[RDFVarBinding]]
queryBack qas tg = rdfQueryBack (toRDFGraph qas) tg

-- Backward chaining rdf:r2

rdfr2ant  = makeRDFGraphFromN3String "?x  ?a ?l . "
rdfr2con  = makeRDFGraphFromN3String "?x  ?a ?b . ?b rdf:type rdf:XMLLiteral ."
rdfr2modv = (allocateTo "?b" "?l") (allLabels labelIsVar rdfr2ant)
rdfr2modc = vbmCompose (makeVarFilterModify $ isXMLLit "?l") rdfr2modv

testRDF01 = test    "testRDF01" $ isJust rdfr2modc

rdfr2grc = GraphClosure
            { nameGraphRule = ScopedName scopeRDF "r2"
            , ruleAnt       = getArcs rdfr2ant
            , ruleCon       = getArcs rdfr2con
            , ruleModify    = fromJust rdfr2modc
            }

rdfr2rul = Rule
            { ruleName       = nameGraphRule rdfr2grc
            , fwdApply       = graphClosureFwdApply rdfr2grc
            , bwdApply       = graphClosureBwdApply rdfr2grc
            , checkInference = fwdCheckInference rdfr2rul
            }

con03  = formExpr $ makeFormula scopeex "con03" $
    "ex:s ex:p1 _:l1 ; ex:p2a _:l2; ex:p2b _:l2 ." ++
    "_:l1 rdf:type rdf:XMLLiteral ." ++
    "_:l2 rdf:type rdf:XMLLiteral ."

v_a   = Var "a"
v_b   = Var "b"
v_x   = Var "x"
u_s   = Res (makeScopedName "" "http://example.org/" "s")
u_p1  = Res (makeScopedName "" "http://example.org/" "p1")
u_p2a = Res (makeScopedName "" "http://example.org/" "p2a")
u_p2b = Res (makeScopedName "" "http://example.org/" "p2b")
u_rt  = Res (makeScopedName "" pref_rdf "type")
u_rx  = Res (makeScopedName "" pref_rdf "XMLLiteral")
b_l1  = Blank "l1"
b_l2  = Blank "l2"

rdfr2v1 = queryBack (ruleCon rdfr2grc) con03
rdfr2b1 = [ [ makeVarBinding [ (v_x,u_s), (v_a,u_p1),  (v_b,b_l1) ]
            , makeVarBinding [ (v_x,u_s), (v_a,u_p2a), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,u_s), (v_a,u_p2b), (v_b,b_l2) ]
            , makeVarBinding [ (v_b,b_l1) ]
            , makeVarBinding [ (v_b,b_l2) ]
            ]
          , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_rx) ]
            , makeVarBinding [ (v_b,b_l2) ]
            ]
          , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
            , makeVarBinding [ (v_b,b_l1) ]
            , makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_rx) ]
            ]
          , [ makeVarBinding [ (v_x,u_s),  (v_a,u_p1),  (v_b,b_l1) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2a), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,u_s),  (v_a,u_p2b), (v_b,b_l2) ]
            , makeVarBinding [ (v_x,b_l1), (v_a,u_rt),  (v_b,u_rx) ]
            , makeVarBinding [ (v_x,b_l2), (v_a,u_rt),  (v_b,u_rx) ]
            ]
          ]

rdfr2v2 = rdfQueryBackModify (ruleModify rdfr2grc) rdfr2v1
rdfr2v3 = map nub rdfr2v2

testRDF02 = testVal "testRDF02" rdfr2b1 rdfr2v1
testRDF03 = testVal "testRDF03" [] rdfr2v2
testRDF04 = testVal "testRDF04" [] rdfr2v3

testRDF09 = testEq "testRDF09" True [] $ bwdApply rdfr2rul con03

testRDFSuite = TestList
    [ testRDF01, testRDF02, testRDF03, testRDF04
    , testRDF09
    ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ testFormulaSuite
  , testRuleSuite
  , testRulesetSuite
  , testRDFSuite
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
-- $Source: /file/cvsdev/HaskellRDF/RDFRulesetTest.hs,v $
-- $Author: graham $
-- $Revision: 1.12 $
-- $Log: RDFRulesetTest.hs,v $
-- Revision 1.12  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.11  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.10  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.9  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.8  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.7  2003/11/24 15:46:04  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.6  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.5  2003/10/22 16:18:37  graham
-- Move common namespace definitions into Namespace module
-- (May later move these into separate modules.)
--
-- Revision 1.4  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.3  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.2  2003/09/30 20:02:40  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.1  2003/09/30 16:38:19  graham
-- Add Ruleset and RDFRuleset modules to provide proof context elements
--
