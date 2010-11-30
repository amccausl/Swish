--------------------------------------------------------------------------------
--  $Id: RDFProofContextTest.hs,v 1.14 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFProofContextTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains RDF proof-checking test cases based on the RDF
--  semantics specifications, as capured in module RDFProofContext.
--
--------------------------------------------------------------------------------

-- WNH RIP OUTmodule Swish.HaskellRDF.RDFProofContextTest where

import Swish.HaskellRDF.BuiltInMap
    ( rdfRulesetMap, allRulesets )

import Swish.HaskellRDF.RDFProofContext
    ( rulesetRDF
    , rulesetRDFS
    , rulesetRDFD )

import Swish.HaskellRDF.RDFProof
    ( RDFProof, RDFProofStep
    , makeRDFProof, makeRDFProofStep
    , makeRdfInstanceEntailmentRule
    , makeRdfSubgraphEntailmentRule
    , makeRdfSimpleEntailmentRule )

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFClosure, RDFRuleset
    , nullRDFFormula
    , makeRDFGraphFromN3String
    , makeRDFFormula
    , makeNodeAllocTo )

import Swish.HaskellRDF.RDFGraph
    ( RDFGraph )

import Swish.HaskellRDF.RDFGraphShowM()

import Swish.HaskellRDF.Proof
    ( Proof(..), Step(..)
    , checkProof, checkStep, showProof, showsProof, showsFormula
    , explainProof)

import Swish.HaskellRDF.Ruleset
    ( getContextAxiom, getContextRule )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..)
    , nullScope, nullFormula, nullRule )

import Swish.HaskellUtils.Namespace
    ( Namespace(..), ScopedName(..) )

import Swish.HaskellUtils.LookupMap
    ( mapFindMaybe )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceRDFS
    , namespaceRDFD
    , namespaceXSD
    , namespaceXsdType
    , scopeRDF
    , scopeRDFS
    , scopeRDFD
    )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn
    , putStr )

import Data.Maybe
    ( isJust, isNothing, fromJust, fromMaybe )

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

testGr :: String -> RDFGraph -> [RDFGraph] -> Test
testGr lab eg a = TestCase $ assertBool lab (eg `elem` a)

-- testProof "rdfProof01" True rdfProof01
testProof :: String -> Bool -> RDFProof -> Test
testProof lab valid proof = TestList
    [ TestCase $ assertEqual lab valid (checkProof proof)
    , TestCase $ assertBool  (lab++": "++ex) (valid == (isNothing $ expl))
    ]
    where
        expl = explainProof proof
        ex   = fromMaybe "(Proof OK)" expl

-- testProofStep "rdfStep01" True [rules] [antes] rdfStep01
testProofStep ::
    String -> Bool -> [RDFRule] -> [RDFGraph] -> Step RDFGraph
    -> Test
testProofStep lab valid rules antes step =
    TestCase $ assertEqual lab valid (checkStep rules antes step)

--  Various support methods

makeFormula :: Namespace -> String -> String -> RDFFormula
makeFormula scope local gr =
    makeRDFFormula scope local (prefix++gr)

getRule :: String -> RDFRule
getRule nam = getContextRule (makeSName nam) nullRule $
    rdfdContext++[rulesetXsdInt,rulesetXsdStr]

getAxiom :: String -> RDFFormula
getAxiom nam = getContextAxiom (makeSName nam) nullRDFFormula rdfdContext

makeSName :: String -> ScopedName
makeSName nam = ScopedName ns loc
    where
        (pre,_:loc) = break (==':') nam
        ns = case pre of
            "rs_rdf"  -> scopeRDF
            "rs_rdfs" -> scopeRDFS
            "rs_rdfd" -> scopeRDFD
            "xsd_integer" -> (namespaceXsdType "integer")
            "xsd_string"  -> (namespaceXsdType "string")
            otherwise -> error ("makeSName: Unrecognized prefix in rule name: "++nam)

--  Common definitions

prefix =
    "@prefix rdf:  <" ++ nsURI namespaceRDF  ++ "> . \n" ++
    "@prefix rdfs: <" ++ nsURI namespaceRDFS ++ "> . \n" ++
    "@prefix rdfd: <" ++ nsURI namespaceRDFD ++ "> . \n" ++
    "@prefix xsd:  <" ++ nsURI namespaceXSD  ++ "> . \n" ++
    "@prefix ex:   <http://example.org/> . \n" ++
    " \n"

scopeex   = Namespace "ex"   "http://id.ninebynine.org/wip/2003/RDFProofCheck#"

rdfContext  = [ rulesetRDF ]

rdfsContext = [ rulesetRDF, rulesetRDFS ]

rdfdContext = [ rulesetRDF, rulesetRDFS, rulesetRDFD ]

xsdintContext = [ rulesetRDF, rulesetRDFS, rulesetRDFD, rulesetXsdInt ]

xsdstrContext = [ rulesetRDF, rulesetRDFS, rulesetRDFD, rulesetXsdStr ]

Just rulesetXsdInt = mapFindMaybe (namespaceXsdType "integer") rdfRulesetMap

Just rulesetXsdStr = mapFindMaybe (namespaceXsdType "string") rdfRulesetMap

------------------------
--  RDF/S rule tests
------------------------
--
--  These tests aim to exercise the specific closure rule constructs
--  that are used by the RDF/S rules.  They have been prepared as a
--  regression test for a refactoring of the variable binding
--  filtering and modification logic.

--  Simple rule test - forward and backward chaining
--
--  rdfr1 = "?x ?a ?y ." => "?a rdf:type rdf:Property ."
--
rdfr1  = getRule "rs_rdf:r1"
ant01  = formExpr $ makeFormula scopeex "ant01" $
    "ex:s ex:p1 ex:o1 ; ex:p2 ex:o2 ."
con01  = formExpr $ makeFormula scopeex "con01" $
    "ex:p1 rdf:type rdf:Property ." ++
    "ex:p2 rdf:type rdf:Property ."
bwd01  = formExpr $ makeFormula scopeex "bwd01a" $
    "_:s1 ex:p1 _:o1 . " ++
    "_:s2 ex:p2 _:o2 . "
testRule01a = testEq "testRule01a" "rs_rdf:r1" (show $ ruleName rdfr1)
testRule01b = testEq "testRule01b" [con01]     (fwdApply rdfr1 [ant01])
testRule01c = testEq "testRule01c" [[bwd01]]   (bwdApply rdfr1 con01)
testRule01d = test   "testRule01d" (checkInference rdfr1 [ant01] con01)
testRule01e = test   "testRule01e" (checkInference rdfr1 [bwd01] con01)

--  Simple rule test - no match forward or backward
--
--  rdfsr2 = "?x ?a ?y . ?a rdfs:domain ?z ." => "?x rdf:type ?z ."
--
rdfsr2 = getRule "rs_rdfs:r2"
ant02  = formExpr $ makeFormula scopeex "ant02" $
    "ex:s ex:p1 ex:o1 . ex:p2 rdfs:domain ex:d2 ."
con02  = formExpr $ makeFormula scopeex "con02" $
    "ex:s ex:p1 ex:o1 . ex:p2 rdfs:domain ex:d2 ."
testRule02a = testEq "testRule02a" "rs_rdfs:r2" (show $ ruleName rdfsr2)
testRule02b = testEq "testRule02b" []           (fwdApply rdfsr2 [ant02])
testRule02c = testEq "testRule02c" []           (bwdApply rdfsr2 con02)
testRule02d = testEq "testRule02d" False (checkInference rdfsr2 [ant02] con02)

--  Rule with literal test and "allocateTo":
--  match forward, but not backward
--
--  This is a two-part rule: (a) apply rdflg, (b) apply rdfr2
--
--  rdflg = "?x ?a ?l . " => "?x  ?a ?b . ?b rdf:_allocatedTo ?l ."
--  where:
--          (isLiteral "?l")
--          (allocateTo "?b" "?l")
--
--  rdfr2 = "?x ?a ?l . ?b rdf:_allocatedTo ?l . "
--          => "?b rdf:type rdf:XMLLiteral ."
--  where:
--          (isXMLLit "?l")
--
rdflg  = getRule "rs_rdf:lg"
rdfr2  = getRule "rs_rdf:r2"
ant03  = formExpr $ makeFormula scopeex "ant03" $
    "ex:s ex:p1  \"lit1\"^^rdf:XMLLiteral ; " ++
    "     ex:p2a \"lit2\"^^rdf:XMLLiteral ; " ++
    "     ex:p2b \"lit2\"^^rdf:XMLLiteral ."
con03lg  = formExpr $ makeFormula scopeex "con03" $
    "ex:s ex:p1 _:l1 ; ex:p2a _:l2; ex:p2b _:l2 ." ++
    "_:l1 rdf:_allocatedTo \"lit1\"^^rdf:XMLLiteral ." ++
    "_:l2 rdf:_allocatedTo \"lit2\"^^rdf:XMLLiteral ."
con03r2  = formExpr $ makeFormula scopeex "con03" $
    "_:l1 rdf:type rdf:XMLLiteral ." ++
    "_:l2 rdf:type rdf:XMLLiteral ."

testRule03a = testEq "testRule03a" "rs_rdf:lg" (show $ ruleName rdflg)
testRule03b = testEq "testRule03b" "rs_rdf:r2" (show $ ruleName rdfr2)
testRule03c = testEq "testRule03c" [con03lg]   (fwdApply rdflg [ant03])
testRule03d = testEq "testRule03d" []          (bwdApply rdflg con03lg)
testRule03e = test   "testRule03e" (checkInference rdflg [ant03] con03lg)
testRule03f = testEq "testRule03f" [con03r2]   (fwdApply rdfr2 [con03lg])
testRule03g = testEq "testRule03g" []          (bwdApply rdfr2 con03r2)
testRule03h = test   "testRule03h" (checkInference rdfr2 [con03lg] con03r2)

--  Rule with member property test, match forwards and backwards
--  rdfcp1 = "?x  ?c ?y . " => "?c rdf:type rdf:Property ."
--  where:
--          (isMemberProp "?c")
--
rdfcp  = getRule "rs_rdf:cp1"
ant04  = formExpr $ makeFormula scopeex "ant04" $
    "ex:s rdf:_123 ex:o1 ; " ++
    "     rdf:_2   ex:o2 . "
con04  = formExpr $ makeFormula scopeex "con04" $
    "rdf:_123 rdf:type rdf:Property ." ++
    "rdf:_2   rdf:type rdf:Property ."
bwd04  = formExpr $ makeFormula scopeex "bwd04a" $
    "_:s1 rdf:_123 _:o1 . " ++
    "_:s2 rdf:_2   _:o2 . "
testRule04a = testEq "testRule04a" "rs_rdf:cp1" (show $ ruleName rdfcp)
testRule04b = testEq "testRule04b" [con04]      (fwdApply rdfcp [ant04])
testRule04c = testEq "testRule04c" [[bwd04]]    (bwdApply rdfcp con04)
testRule04d = test   "testRule04d" (checkInference rdfcp [ant04] con04)
testRule04e = test   "testRule01e" (checkInference rdfcp [bwd04] con04)

--  Rule with disjunction test, match forwards and backwards
--
--  rdfsr3 = "?x ?a ?u . ?a rdfs:range ?z ." => "?u rdf:type ?z ."
--  where:
--          (requireAny [isUriRef "?u",isBlank "?u"])
--
rdfsr3 = getRule "rs_rdfs:r3"
ant05  = formExpr $ makeFormula scopeex "ant05" $
    "ex:s ex:p1 ex:o1 ; "        ++
    "     ex:p2 _:o2  . "        ++
    "ex:p1 rdfs:range ex:pr1 . " ++
    "ex:p2 rdfs:range ex:pr2 . "
con05  = formExpr $ makeFormula scopeex "con05" $
    "ex:o1 rdf:type ex:pr1 ." ++
    "_:o2  rdf:type ex:pr2 ."
bwd05  = formExpr $ makeFormula scopeex "bwd05a" $
    "_:s1 _:p1 ex:o1 . "        ++
    "_:s2 _:p2 _:o2  . "        ++
    "_:p1 rdfs:range ex:pr1 . " ++
    "_:p2 rdfs:range ex:pr2 . "
testRule05a = testEq "testRule05a" "rs_rdfs:r3" (show $ ruleName rdfsr3)
testRule05b = testEq "testRule05b" [con05]      (fwdApply rdfsr3 [ant05])
testRule05c = testEq "testRule05c" [[bwd05]]    (bwdApply rdfsr3 con05)
testRule05d = test   "testRule05d" (checkInference rdfsr3 [ant05] con05)
testRule05e = test   "testRule01e" (checkInference rdfsr3 [bwd05] con05)

--  Rule with disjunction test, fail forwards
--
--  rdfsr3 = "?x ?a ?u . ?a rdfs:range ?z ." => "?u rdf:type ?z ."
--  where:
--          (requireAny [isUriRef "?u",isBlank "?u"])
--
ant06  = formExpr $ makeFormula scopeex "ant06" $
    "ex:s ex:p1 \"lit1\" . "     ++
    "ex:p1 rdfs:range ex:pr1 . "
con06  = formExpr $ makeFormula scopeex "con06" $
    "_:o1  rdf:type ex:pr1 ."
bwd06  = formExpr $ makeFormula scopeex "bwd06a" $
    "_:s1 _:p1 _:o1 . "      ++
    "_:p1 rdfs:range ex:pr1 . "
chk06  = formExpr $ makeFormula scopeex "bwd06a" $
    "_:s1 _:p1 \"lit1\" . "      ++
    "_:p1 rdfs:range ex:pr1 . "
testRule06a = testEq "testRule06a" "rs_rdfs:r3" (show $ ruleName rdfsr3)
testRule06b = testEq "testRule06b" []           (fwdApply rdfsr3 [ant06])
testRule06c = testEq "testRule06c" [[bwd06]]    (bwdApply rdfsr3 con06)
testRule06d = testEq "testRule06d" False (checkInference rdfsr3 [ant06] con06)
testRule06e = testEq "testRule06e" True  (checkInference rdfsr3 [bwd06] con06)
testRule06f = testEq "testRule06e" False (checkInference rdfsr3 [chk06] con06)

--  Collected rule tests

testRules = TestList
    [ testRule01a, testRule01b, testRule01c, testRule01d, testRule01e
    , testRule02a, testRule02b, testRule02c, testRule02d
    , testRule03a, testRule03b, testRule03c, testRule03d, testRule03e
    , testRule03f, testRule03g, testRule03h
    , testRule04a, testRule04b, testRule04c, testRule04d, testRule04e
    , testRule05a, testRule05b, testRule05c, testRule05d, testRule05e
    , testRule06a, testRule06b, testRule06c, testRule06d, testRule06e
    , testRule06f
    ]

------------------------
--  Complete proof tests
------------------------
--
--  These are a few tests of complete RDF proof chains based on the
--  RDF semantic rules.


--  RDF entailment proof checks

rdfBase01  = makeFormula scopeex "rdfBase01" "ex:s ex:p ex:o ."
rdfGoal01  = makeFormula scopeex "rdfGoal01" "ex:p rdf:type rdf:Property ."
rdfStep01a = makeRDFProofStep (getRule "rs_rdf:r1") [rdfBase01] rdfGoal01
rdfProof01 = makeRDFProof rdfsContext rdfBase01 rdfGoal01
                [ rdfStep01a ]

rdfBase02  = makeFormula scopeex "rdfBase02" $
                "ex:s ex:p \"l1\"^^rdf:XMLLiteral ."
rdfCon02a  = makeFormula scopeex "rdfStep02a" $
                "ex:s ex:p _:lll . "             ++
                "_:lll rdf:_allocatedTo \"l1\"^^rdf:XMLLiteral . "
rdfGoal02  = makeFormula scopeex "rdfGoal02" $
                "_:lll rdf:type rdf:XMLLiteral . "
rdfStep02a = makeRDFProofStep (getRule "rs_rdf:lg") [rdfBase02] rdfCon02a
rdfStep02b = makeRDFProofStep (getRule "rs_rdf:r2") [rdfCon02a] rdfGoal02
rdfProof02 = makeRDFProof rdfsContext rdfBase02 rdfGoal02
                [ rdfStep02a, rdfStep02b ]

rdfBase03  = makeFormula scopeex "rdfBase03" $
                "ex:s ex:p ex:o ."
rdfCon03a  = makeFormula scopeex "rdfStep03a" $
                "ex:s ex:p _:lll . "             ++
                "_:lll rdf:_allocatedTo \"l1\"^^rdf:XMLLiteral . "
rdfGoal03  = makeFormula scopeex "rdfGoal03" $
                "_:lll rdf:type rdf:XMLLiteral . "
rdfStep03a = makeRDFProofStep (getRule "rs_rdf:lg") [rdfBase03] rdfCon03a
rdfStep03b = makeRDFProofStep (getRule "rs_rdf:r2") [rdfCon03a] rdfGoal03
rdfProof03 = makeRDFProof rdfsContext rdfBase03 rdfGoal03
                [ rdfStep03a, rdfStep03b ]

rdfBase04  = makeFormula scopeex "rdfBase04" "ex:s ex:p ex:o ."
rdfGoal04  = makeFormula scopeex "rdfGoal04" "_:s  ex:p _:o ."
rdfStep04a = makeRDFProofStep (getRule "rs_rdf:se") [rdfBase04] rdfGoal04
rdfProof04 = makeRDFProof rdfsContext rdfBase04 rdfGoal04
                [ rdfStep04a ]

rdfBase05  = makeFormula scopeex "rdfBase05" $
                "ex:s ex:p rdf:nil ."
rdfStep05a = makeRDFProofStep (getRule "rs_rdf:r1") [rdfBase05]  rdfCons05a
rdfCons05a = makeFormula scopeex "rdfCons05a" $
                "ex:p  rdf:type rdf:Property ."
rdfStep05b = makeRDFProofStep (getRule "rs_rdf:se")
                [rdfBase05,rdfCons05a,(getAxiom "rs_rdf:a8")] rdfGoal05
rdfGoal05  = makeFormula scopeex "rdfGoal05" $
                "ex:s _:p _:n ."               ++
                "_:p  rdf:type rdf:Property ." ++
                "_:n  rdf:type rdf:List ."
rdfProof05 = makeRDFProof rdfsContext rdfBase05 rdfGoal05
                [ rdfStep05a, rdfStep05b ]

--  Swap rdfProof05 proof steps:
rdfProof06 = makeRDFProof rdfsContext rdfBase05 rdfGoal05
                [ rdfStep05b, rdfStep05a ]

--  Proof using rdfsr1 and rdfsub
--
--    ex:s1 ex:p1 "lll"
--    ex:s2 ex:p2 "lll"
--  =>
--    ex:s1 ex:p1 _:l
--    ex:s2 ex:p2 _:l
--    _:l   rdf:type rdfs:Literal

rdfBase07  = makeFormula scopeex "rdfBase07" $
                "ex:s1 ex:p1 \"lll\" ." ++
                "ex:s2 ex:p2 \"lll\" ." ++
                "ex:s3 ex:p3 \"mmm\" ."
rdfStep07a = makeRDFProofStep (getRule "rs_rdf:lg") [rdfBase07]  rdfCons07a
rdfCons07a = makeFormula scopeex "rdfCons07a" $
                "ex:s1 ex:p1 _:l ."              ++
                "ex:s2 ex:p2 _:l ."              ++
                "_:l rdf:_allocatedTo \"lll\" ." ++
                "ex:s3 ex:p3 _:m ."              ++
                "_:m rdf:_allocatedTo \"mmm\" ."
rdfStep07b = makeRDFProofStep (getRule "rs_rdfs:r1") [rdfCons07a]  rdfCons07b
rdfCons07b = makeFormula scopeex "rdfCons07a" $
                "_:l rdf:type rdfs:Literal ." ++
                "_:m rdf:type rdfs:Literal ."
rdfStep07c = makeRDFProofStep (getRule "rs_rdf:sub")
                [rdfCons07a,rdfCons07b] rdfGoal07
rdfGoal07  = makeFormula scopeex "rdfGoal07" $
                "ex:s1 ex:p1 _:l ."           ++
                "ex:s2 ex:p2 _:l ."           ++
                "_:l rdf:type rdfs:Literal ."
rdfProof07 = makeRDFProof rdfsContext rdfBase07 rdfGoal07
                [ rdfStep07a, rdfStep07b, rdfStep07c ]

--  Proof of:
--    rdf:_123 rdfs:supPropertyOf rdfs:member

rdfBase08  = makeFormula scopeex "rdfBase08" $
                "ex:s1 rdf:_123 ex:o ."
rdfStep08a = makeRDFProofStep (getRule "rs_rdfs:cp1") [rdfBase08]  rdfCons08a
rdfCons08a = makeFormula scopeex "rdfCons08a" $
                "rdf:_123 rdf:type rdfs:ContainerMembershipProperty ."
rdfStep08b = makeRDFProofStep (getRule "rs_rdfs:r12")  [rdfCons08a]  rdfGoal08
rdfGoal08  = makeFormula scopeex "rdfCons08b" $
                "rdf:_123 rdfs:subPropertyOf rdfs:member ."
rdfProof08 = makeRDFProof rdfsContext rdfBase08 rdfGoal08
                [ rdfStep08a, rdfStep08b ]


--  Proof of:
--    ex:s ex:p "010"^^xsd:Integer .
--  =>
--    ex:s ex:p "10"^^xsd:Integer .
--    ex:s ex:p _:b
--    _:b rdf:type xsd:integer .

rdfAxiomIntDt = getContextAxiom
                    (ScopedName (namespaceXsdType "integer") "dt")
                    nullFormula
                    allRulesets

rdfAxiom09 = testEq "rdfAxiom09" "xsd_integer:dt" $
                show (formName rdfAxiomIntDt)

rdfBase09  = makeFormula scopeex "rdfBase09" $
                "ex:s ex:p \"010\"^^xsd:integer ."
rdfStep09a = makeRDFProofStep (getRule "rs_rdfd:r2")
                [rdfAxiomIntDt,rdfBase09]  rdfCons09a
rdfCons09a = makeFormula scopeex "rdfCons09a" $
                "ex:s ex:p \"10\"^^xsd:integer ."
rdfStep09b = makeRDFProofStep (getRule "rs_rdf:lg")
                [rdfCons09a]  rdfCons09b
rdfCons09b = makeFormula scopeex "rdfCons09b" $
                "ex:s ex:p _:l ." ++
                "_:l rdf:_allocatedTo \"10\"^^xsd:integer ."
rdfStep09c = makeRDFProofStep (getRule "rs_rdfd:r1")
                [rdfAxiomIntDt,rdfCons09a,rdfCons09b]  rdfCons09c
rdfCons09c = makeFormula scopeex "rdfCons09c" $
                "_:l rdf:type xsd:integer ."
rdfStep09d = makeRDFProofStep (getRule "rs_rdf:sub")
                [rdfCons09a,rdfCons09b,rdfCons09c]  rdfGoal09
rdfGoal09  = makeFormula scopeex "rdfGoal09" $
                "ex:s ex:p  \"10\"^^xsd:integer ."           ++
                "_:l rdf:_allocatedTo \"10\"^^xsd:integer ." ++
                "_:l rdf:type xsd:integer ."
rdfProof09 = makeRDFProof xsdintContext rdfBase09 rdfGoal09
                [ rdfStep09a, rdfStep09b, rdfStep09c, rdfStep09d ]

-- {- test data
p09t1 = fwdApply (getRule "rs_rdfd:r2")
    [(formExpr rdfAxiomIntDt),(formExpr rdfBase09)]
p09sh = putStrLn ("\n"++showProof "\n" rdfProof09++"\n")
-- -}


--  Proof of:
--    ex:s ex:p "abc" .
--    ex:s ex:p "def"^^xsd:string .
--  =>
--    ex:s ex:p "abc"^^xsd:string .
--    ex:s ex:p "def" .
--    xsd:string rdf:type rdfs:Datatype .

rdfAxiomStrDt = getContextAxiom
                    (ScopedName (namespaceXsdType "string") "dt")
                    nullFormula
                    allRulesets

rdfAxiom10 = testEq "rdfAxiom10" "xsd_string:dt" $
                show (formName rdfAxiomStrDt)

rdfRule10 = testEq "rdfRule10" "xsd_string:ls" $
                show (ruleName (getRule "xsd_string:ls"))

rdfBase10  = makeFormula scopeex "rdfBase10" $
                "ex:s ex:p \"abc\" . " ++
                "ex:s ex:p \"def\"^^xsd:string . "
rdfStep10a = makeRDFProofStep (getRule "xsd_string:ls")
                [rdfBase10]  rdfCons10a
rdfCons10a = makeFormula scopeex "rdfCons10a" $
                "ex:s ex:p \"abc\"^^xsd:string . "
rdfStep10b = makeRDFProofStep (getRule "xsd_string:sl")
                [rdfBase10]  rdfCons10b
rdfCons10b = makeFormula scopeex "rdfCons10b" $
                "ex:s ex:p \"def\" . "
rdfStep10c = makeRDFProofStep (getRule "rs_rdf:sub")
                [rdfCons10a,rdfCons10b,rdfAxiomStrDt] rdfGoal10
rdfGoal10  = makeFormula scopeex "rdfGoal10" $
                "ex:s ex:p \"abc\"^^xsd:string . " ++
                "ex:s ex:p \"def\" . "             ++
                "xsd:string rdf:type rdfs:Datatype . "
rdfProof10 = makeRDFProof xsdstrContext rdfBase10 rdfGoal10
                [ rdfStep10a, rdfStep10b, rdfStep10c ]

testRdf = TestList
    [ testProofStep "rdfStep01a" True  [(getRule "rs_rdf:r1")] [formExpr rdfBase01] rdfStep01a
    , testProof     "rdfProof01" True  rdfProof01
    --   Really should have support for scoped bnodes
    , testProof     "rdfProof02" True  rdfProof02
    , testProof     "rdfProof03" False rdfProof03
    , testProof     "rdfProof04" True  rdfProof04
    , testProof     "rdfProof05" True  rdfProof05
    , testProof     "rdfProof06" False rdfProof06
    , testProof     "rdfProof07" True  rdfProof07
    , testProof     "rdfProof08" True  rdfProof08
    , rdfAxiom09
    , testProof     "rdfProof09" True  rdfProof09
    , rdfAxiom10, rdfRule10
    , testProof     "rdfProof10" True  rdfProof10
    {-
    , TestCase $ putStrLn ("\n"++showProof "\n" rdfProof01)
    , TestCase $ putStrLn ("\n"++showProof "\n" rdfProof05)
    -}
    ]

------------------------------------------------------------
--  Full test suite, main program,
--  and useful expressions for interactive use
------------------------------------------------------------

allTests = TestList
  [ testRules
  , testRdf
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

p10 = runTestTT $ TestList
    [ rdfAxiom10
    , rdfRule10
    , testProof     "rdfProof10" True  rdfProof10
    ]

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
-- $Source: /file/cvsdev/HaskellRDF/RDFProofContextTest.hs,v $
-- $Author: graham $
-- $Revision: 1.14 $
-- $Log: RDFProofContextTest.hs,v $
-- Revision 1.14  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.13  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.12  2003/12/20 12:53:40  graham
-- Fix up code to compile and test with GHC 5.04.3
--
-- Revision 1.11  2003/12/18 20:46:24  graham
-- Added xsd:string module to capture equivalence of xsd:string
-- and plain literals without a language tag
--
-- Revision 1.10  2003/12/18 18:27:47  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.9  2003/12/16 07:05:37  graham
-- Working on updated RDFProofContext
--
-- Revision 1.8  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.7  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.6  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.5  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.4  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.3  2003/10/09 17:16:13  graham
-- Added test cases to exercise features of rules used to capture
-- RDF semantics.  Also added proof test case using XML literal.
--
-- Revision 1.2  2003/10/09 13:58:59  graham
-- Sync with CVS.  Preparing to eliminate QueryBindingFilter in favour
-- of using just QueryBindingModifier.
--
-- Revision 1.1  2003/10/02 13:39:41  graham
-- RDF axioms and rules defined as Rulesets, and moved out of module
-- RDFProofCheck into RDFProorfContext, with corresponding test cases
-- moved to module RDFProorfContextTest.
--
