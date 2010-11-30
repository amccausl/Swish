--------------------------------------------------------------------------------
--  $Id: RDFGraphTest.hs,v 1.32 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFGraphTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains test cases for module RDFGraph.
--
--------------------------------------------------------------------------------

--  WNH RIP OUT module Swish.HaskellRDF.RDFGraphTest where

import Swish.HaskellUtils.FunctorM
    ( FunctorM(..) )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..)
    , mapFind, mapFindMaybe, mapContains )

import Swish.HaskellUtils.ListHelpers
    ( equiv )

import Swish.HaskellRDF.GraphClass
    ( Label(..), Arc, arcSubj, arcPred, arcObj, arc )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , makeQNameScopedName
    , nullScopedName
    , makeUriScopedName
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    , newQName, qnameFromPair, qnameFromURI
    , getNamespace, getLocalName, getQNameURI
    , splitURI
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFTriple, RDFGraph, RDFLabel(..), NSGraph(..)
    , isLiteral, isUntypedLiteral, isTypedLiteral, isXMLLiteral
    , isDatatyped, isMemberProp
    , isUri, isBlank, isQueryVar, makeBlank
    , getScopedName
    -- , LookupNamespace(..), Namespace
    , NamespaceMap, emptyNamespaceMap
    , LookupFormula(..), Formula, FormulaMap, emptyFormulaMap
    , setArcs, getArcs, addArc, add, delete, extract, labels, merge
    , allLabels, remapLabels, remapLabelList
    , setNamespaces, getNamespaces
    , setFormulae, getFormulae, setFormula, getFormula
    , emptyRDFGraph, toRDFGraph
    , newNode, newNodes
    , grMatchMap, grEq )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
{-
    , namespaceRDFS
    , namespaceRDFD
    , namespaceRDFC
    , namespaceRDFO
    , namespaceXSD
    , namespaceXsdType
    , namespaceOWL
    , namespaceMATH
    , namespaceLOG
    , namespaceDAML
-}
    , namespaceLang, langName, langTag, isLang
    , rdf_type
    , rdf_first, rdf_rest, rdf_nil, rdf_XMLLiteral
    , rdfs_member
    , rdfd_GeneralRestriction
    , rdfd_onProperties, rdfd_constraint, rdfd_maxCardinality
    , owl_sameAs
    , operator_plus, operator_minus, operator_slash, operator_star
    )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

import Data.List
    ( elemIndex )

import Data.Maybe
    ( fromJust )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertBool, assertEqual, assertString
    , runTestTT, runTestText, putTextToHandle )

------------------------------------------------------------
--  Common definitions
------------------------------------------------------------

testEq :: (Eq a, Show a) => String -> a -> a -> Test
testEq lab a1 a2 =
    TestCase ( assertEqual ("testEq:"++lab) a1 a2 )

------------------------------------------------------------
--  Test language tag comparisons
------------------------------------------------------------

type Lang = Maybe ScopedName

lt0 = Nothing
lt1 = Just (langName "en")
lt2 = Just (langName "EN")
lt3 = Just (langName "fr")
lt4 = Just (langName "FR")
lt5 = Just (langName "en-us")
lt6 = Just (langName "en-US")
lt7 = Just (langName "EN-us")
lt8 = Just (langName "EN-US")

langlist =
  [ ("lt0",lt0),
    ("lt1",lt1), ("lt2",lt2), ("lt3",lt3), ("lt4",lt4),
    ("lt5",lt5), ("lt6",lt6), ("lt7",lt7), ("lt8",lt8) ]

langeqlist =
  [
    ("lt1","lt2"),
    ("lt3","lt4"),
    ("lt5","lt6"),
    ("lt5","lt7"),
    ("lt5","lt8"),
    ("lt6","lt7"),
    ("lt6","lt8"),
    ("lt7","lt8")
  ]

testLangEq :: String -> Bool -> Lang -> Lang -> Test
testLangEq lab eq l1 l2 =
    TestCase ( assertEqual ("testLangEq:"++lab) eq (l1==l2) )

testLangEqSuite = TestList
  [ testLangEq (testLab l1 l2) (testEq  l1 l2) t1 t2
      | (l1,t1) <- langlist , (l2,t2) <- langlist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` langeqlist ||
            (l2,l1) `elem` langeqlist

------------------------------------------------------------
--  Define some common values
------------------------------------------------------------

base1 = Namespace "base1" "http://id.ninebynine.org/wip/2003/test/graph1/node#"
base2 = Namespace "base2" "http://id.ninebynine.org/wip/2003/test/graph2/node/"
base3 = Namespace "base3" "http://id.ninebynine.org/wip/2003/test/graph3/node"
base4 = Namespace "base4" "http://id.ninebynine.org/wip/2003/test/graph3/nodebase"

qb1s1 = ScopedName base1 "s1"
qb2s2 = ScopedName base2 "s2"
qb3s3 = ScopedName base3 "s3"
qb3   = ScopedName base3 ""
qb3bm = ScopedName base3 "basemore"
qb4m  = ScopedName base4 "more"

s1 = Res qb1s1  :: RDFLabel
s2 = Res qb2s2  :: RDFLabel
s3 = Res qb3s3  :: RDFLabel
s4 = Res qb3    :: RDFLabel
s5 = Blank "s5" :: RDFLabel
s6 = Res qb3bm  :: RDFLabel
s7 = Res qb4m   :: RDFLabel
s8 = Blank "s8" :: RDFLabel

qb1st1 = ScopedName base1 "st1"
qb2st2 = ScopedName base2 "st2"
qb3st3 = ScopedName base3 "st3"

st1 = Res qb1st1  :: RDFLabel
st2 = Res qb2st2  :: RDFLabel
st3 = Res qb3st3  :: RDFLabel

bb  = Blank "bb"  :: RDFLabel
bb0 = Blank "bb0" :: RDFLabel
b1  = Blank "b1"  :: RDFLabel
b2  = Blank "b2"  :: RDFLabel
b3  = Blank "b3"  :: RDFLabel
b4  = Blank "b4"  :: RDFLabel
b5  = Blank "b5"  :: RDFLabel
b6  = Blank "b6"  :: RDFLabel
b7  = Blank "b7"  :: RDFLabel
b8  = Blank "b8"  :: RDFLabel
b9  = Blank "b9"  :: RDFLabel
b10 = Blank "b10" :: RDFLabel

c1 = Blank "c1" :: RDFLabel
c2 = Blank "c2" :: RDFLabel
c3 = Blank "c3" :: RDFLabel
c4 = Blank "c4" :: RDFLabel

ba1 = Blank "_1" :: RDFLabel
ba2 = Blank "_2" :: RDFLabel
ba3 = Blank "_3" :: RDFLabel
ba4 = Blank "_4" :: RDFLabel

bn3 = Blank "3" :: RDFLabel
bn4 = Blank "4" :: RDFLabel
bn5 = Blank "5" :: RDFLabel
bn6 = Blank "6" :: RDFLabel

qb1p1 = ScopedName base1 "p1"
qb2p2 = ScopedName base2 "p2"
qb3p3 = ScopedName base3 "p3"
qb4p4 = ScopedName base3 "p4"
qb1o1 = ScopedName base1 "o1"
qb2o2 = ScopedName base2 "o2"
qb3o3 = ScopedName base3 "o3"

p1 = Res qb1p1  :: RDFLabel
p2 = Res qb2p2  :: RDFLabel
p3 = Res qb3p3  :: RDFLabel
p4 = Res qb4p4  :: RDFLabel

o1 = Res qb1o1  :: RDFLabel
o2 = Res qb2o2  :: RDFLabel
o3 = Res qb3o3  :: RDFLabel
o4 = Res qb3    :: RDFLabel
o5 = Blank "o5" :: RDFLabel
o6 = Blank "s5" :: RDFLabel

qb1t1 = ScopedName base1 "type1"
qb1t2 = ScopedName base1 "type2"

l1  = Lit "l1"  Nothing                 :: RDFLabel
l2  = Lit "l2"  (Just (langName "en"))  :: RDFLabel
l3  = Lit "l2"  (Just (langName "fr"))  :: RDFLabel
l4  = Lit "l4"  (Just qb1t1)            :: RDFLabel
l5  = Lit "l4"  (Just qb1t1)            :: RDFLabel -- (Lang "en")
l6  = Lit "l4"  (Just qb1t1)            :: RDFLabel -- (Lang "fr")
l7  = Lit "l4"  (Just qb1t2)            :: RDFLabel
l8  = Lit "l4"  (Just qb1t2)            :: RDFLabel -- (Lang "en")
l9  = Lit "l4"  (Just qb1t2)            :: RDFLabel -- (Lang "fr")
l10 = Lit "l10" (Just rdf_XMLLiteral)   :: RDFLabel
l11 = Lit "l10" (Just rdf_XMLLiteral)   :: RDFLabel -- (Lang "en")
l12 = Lit "l10" (Just rdf_XMLLiteral)   :: RDFLabel -- (Lang "fr")

v1  = Var "v1"   :: RDFLabel
v2  = Var "v2"   :: RDFLabel
v3  = Var "v3"   :: RDFLabel
v4  = Var "v4"   :: RDFLabel
vb3 = Blank "v3" :: RDFLabel
vb4 = Blank "v4" :: RDFLabel

-- Test cases for isMemberProp
qcm1 = ScopedName namespaceRDF "_1"
qcm2 = ScopedName namespaceRDF "_234567"
qnm1 = ScopedName namespaceRDF "987"
qnm2 = ScopedName namespaceRDF "_987a65"

cm1  = Res qcm1  :: RDFLabel
cm2  = Res qcm2  :: RDFLabel
nm1  = Res qnm1  :: RDFLabel
nm2  = Res qnm2  :: RDFLabel

------------------------------------------------------------
--  RDFLabel construction and equality tests
------------------------------------------------------------

testLabelEq :: String -> Bool -> RDFLabel -> RDFLabel -> Test
testLabelEq lab eq n1 n2 =
    TestCase ( assertEqual ("testLabelEq:"++lab) eq (n1==n2) )

nodelist =
  [ ("s1",s1), ("s2",s2), ("s3",s3), ("s4",s4), ("s5",s5)
  , ("s6",s6), ("s7",s7), ("s8",s8)
  , ("b1",b1), ("b2",b2), ("b3",b3), ("b4",b4)
  , ("p1",p1), ("p2",p2), ("p3",p3), ("p4",p4)
  , ("o1",o1), ("o2",o2), ("o3",o3), ("o4",o4), ("o5",o5)
  , ("l1",l1), ("l2",l2), ("l3",l3)
  , ("l4",l4), ("l5",l5), ("l6",l6)
  , ("l7",l7), ("l8",l8), ("l9",l9)
  , ("l10",l10), ("l11",l11), ("l12",l12)
  , ("v1",v1), ("v2",v2)
  ]

nodeeqlist =
  [ ("s4","o4")
  , ("s5","o6")
  , ("s6","s7")
  , ("l4","l5")
  , ("l4","l6")
  , ("l5","l6")
  , ("l7","l8")
  , ("l7","l9")
  , ("l8","l9")
  , ("l10","l11")
  , ("l10","l12")
  , ("l11","l12")
  ]

testNodeEqSuite = TestList
  [ testLabelEq (testLab l1 l2) (testEq  l1 l2) n1 n2
      | (l1,n1) <- nodelist , (l2,n2) <- nodelist ]
    where
    testLab l1 l2 = l1 ++ "-" ++ l2
    testEq  l1 l2 = (l1 == l2)        ||
            (l1,l2) `elem` nodeeqlist ||
            (l2,l1) `elem` nodeeqlist

------------------------------------------------------------
--  RDFLabel classification tests
------------------------------------------------------------

testClass :: String -> (RDFLabel -> Bool) -> RDFLabel -> Bool -> Test
testClass lab clsf nod eq =
    TestCase ( assertEqual ("testClass:"++lab) eq (clsf nod) )

testClass01 = testClass "testClass01" isUri            s1  True
testClass02 = testClass "testClass02" isUri            s5  False
testClass03 = testClass "testClass03" isUri            ba1 False
testClass04 = testClass "testClass04" isUri            l1  False
testClass05 = testClass "testClass05" isUri            l10 False
testClass06 = testClass "testClass06" isUri            cm1 True
testClass07 = testClass "testClass07" isUri            nm1 True
testClass08 = testClass "testClass08" isUri            v1  False

testClass10 = testClass "testClass10" isLiteral        s1  False
testClass11 = testClass "testClass11" isLiteral        s5  False
testClass12 = testClass "testClass12" isLiteral        ba1 False
testClass13 = testClass "testClass13" isLiteral        l1  True
testClass14 = testClass "testClass14" isLiteral        l4  True
testClass15 = testClass "testClass15" isLiteral        l5  True
testClass16 = testClass "testClass16" isLiteral        l10 True
testClass17 = testClass "testClass17" isLiteral        l11 True
testClass18 = testClass "testClass18" isLiteral        cm1 False
testClass19 = testClass "testClass19" isLiteral        v1  False

testClass20 = testClass "testClass20" isTypedLiteral   s1  False
testClass21 = testClass "testClass21" isTypedLiteral   s5  False
testClass22 = testClass "testClass22" isTypedLiteral   ba1 False
testClass23 = testClass "testClass23" isTypedLiteral   l1  False
testClass24 = testClass "testClass24" isTypedLiteral   l2  False
testClass25 = testClass "testClass25" isTypedLiteral   l4  True
testClass26 = testClass "testClass26" isTypedLiteral   l5  True
testClass27 = testClass "testClass27" isTypedLiteral   l10 True
testClass28 = testClass "testClass28" isTypedLiteral   l11 True
testClass29 = testClass "testClass29" isTypedLiteral   v1  False

testClass30 = testClass "testClass30" isUntypedLiteral s1  False
testClass31 = testClass "testClass31" isUntypedLiteral s5  False
testClass32 = testClass "testClass32" isUntypedLiteral ba1 False
testClass33 = testClass "testClass33" isUntypedLiteral l1  True
testClass34 = testClass "testClass34" isUntypedLiteral l2  True
testClass35 = testClass "testClass35" isUntypedLiteral l4  False
testClass36 = testClass "testClass36" isUntypedLiteral l5  False
testClass37 = testClass "testClass37" isUntypedLiteral l10 False
testClass38 = testClass "testClass38" isUntypedLiteral l11 False
testClass39 = testClass "testClass39" isUntypedLiteral v1  False

testClass40 = testClass "testClass40" isXMLLiteral     s1  False
testClass41 = testClass "testClass41" isXMLLiteral     s5  False
testClass42 = testClass "testClass42" isXMLLiteral     ba1 False
testClass43 = testClass "testClass43" isXMLLiteral     l1  False
testClass44 = testClass "testClass44" isXMLLiteral     l2  False
testClass45 = testClass "testClass45" isXMLLiteral     l4  False
testClass46 = testClass "testClass46" isXMLLiteral     l5  False
testClass47 = testClass "testClass47" isXMLLiteral     l10 True
testClass48 = testClass "testClass48" isXMLLiteral     l11 True
testClass49 = testClass "testClass49" isXMLLiteral     v1  False

altIsXmlLit = isDatatyped rdf_XMLLiteral
testClass50 = testClass "testClass50" altIsXmlLit      s1  False
testClass51 = testClass "testClass51" altIsXmlLit      s5  False
testClass52 = testClass "testClass52" altIsXmlLit      ba1 False
testClass53 = testClass "testClass53" altIsXmlLit      l1  False
testClass54 = testClass "testClass54" altIsXmlLit      l2  False
testClass55 = testClass "testClass55" altIsXmlLit      l4  False
testClass56 = testClass "testClass56" altIsXmlLit      l5  False
testClass57 = testClass "testClass57" altIsXmlLit      l10 True
testClass58 = testClass "testClass58" altIsXmlLit      l11 True

testClass60 = testClass "testClass60" isMemberProp     s1  False
testClass61 = testClass "testClass61" isMemberProp     s5  False
testClass62 = testClass "testClass62" isMemberProp     ba1 False
testClass63 = testClass "testClass63" isMemberProp     l1  False
testClass64 = testClass "testClass64" isMemberProp     l10 False
testClass65 = testClass "testClass65" isMemberProp     cm1 True
testClass66 = testClass "testClass66" isMemberProp     cm2 True
testClass67 = testClass "testClass67" isMemberProp     nm1 False
testClass68 = testClass "testClass68" isMemberProp     nm2 False

testClass70 = testClass "testClass70" isBlank          s7  False
testClass71 = testClass "testClass71" isBlank          s5  True
testClass72 = testClass "testClass72" isBlank          ba1 True
testClass73 = testClass "testClass73" isBlank          l1  False
testClass74 = testClass "testClass74" isBlank          l4  False
testClass75 = testClass "testClass75" isBlank          l5  False
testClass76 = testClass "testClass76" isBlank          l10 False
testClass77 = testClass "testClass77" isBlank          l11 False
testClass78 = testClass "testClass78" isBlank          cm1 False
testClass79 = testClass "testClass79" isBlank          v1  False

testClass80 = testClass "testClass80" isQueryVar       s8  False
testClass81 = testClass "testClass81" isQueryVar       s5  False
testClass82 = testClass "testClass82" isQueryVar       ba1 False
testClass83 = testClass "testClass83" isQueryVar       l1  False
testClass84 = testClass "testClass84" isQueryVar       l4  False
testClass85 = testClass "testClass85" isQueryVar       l5  False
testClass86 = testClass "testClass86" isQueryVar       l10 False
testClass87 = testClass "testClass87" isQueryVar       l11 False
testClass88 = testClass "testClass88" isQueryVar       cm1 False
testClass89 = testClass "testClass89" isQueryVar       v1  True

testNodeClassSuite = TestList
  [              testClass01, testClass02, testClass03, testClass04
  , testClass05, testClass06, testClass07, testClass08
  , testClass10, testClass11, testClass12, testClass13, testClass14
  , testClass15, testClass16, testClass17, testClass18, testClass19
  , testClass20, testClass21, testClass22, testClass23, testClass24
  , testClass25, testClass26, testClass27, testClass28, testClass29
  , testClass30, testClass31, testClass32, testClass33, testClass34
  , testClass35, testClass36, testClass37, testClass38, testClass39
  , testClass40, testClass41, testClass42, testClass43, testClass44
  , testClass45, testClass46, testClass47, testClass48, testClass49
  , testClass50, testClass51, testClass52, testClass53, testClass54
  , testClass55, testClass56, testClass57, testClass58
  , testClass60, testClass61, testClass62, testClass63, testClass64
  , testClass65, testClass66, testClass67, testClass68
  , testClass70, testClass71, testClass72, testClass73, testClass74
  , testClass75, testClass76, testClass77, testClass78, testClass79
  , testClass80, testClass81, testClass82, testClass83, testClass84
  , testClass85, testClass86, testClass87, testClass88, testClass89
  ]

------------------------------------------------------------
--  RDFLabel local part separation and recombination tests
------------------------------------------------------------

testLocalEq :: String -> String -> String -> Test
testLocalEq lab l1 l2 =
    TestCase ( assertEqual ("testLocalEq:"++lab) l1 l2 )

testLocalLabEq :: String -> RDFLabel -> RDFLabel -> Test
testLocalLabEq lab l1 l2 =
    TestCase ( assertEqual ("testLocalEq:"++lab) l1 l2 )

testNodeLocal01 = testLocalEq    "01" "b1"  (getLocal b1)
testNodeLocal02 = testLocalEq    "02" "b2"  (getLocal b2)
testNodeLocal03 = testLocalEq    "03" "?v1" (getLocal v1)
testNodeLocal04 = testLocalEq    "04" "?v2" (getLocal v2)
testNodeLocal05 = testLocalLabEq "05" b1    (makeLabel "b1")
testNodeLocal06 = testLocalLabEq "06" b2    (makeLabel "b2")
testNodeLocal07 = testLocalLabEq "07" v1    (makeLabel "?v1")
testNodeLocal08 = testLocalLabEq "08" v2    (makeLabel "?v2")

testNodeLocalSuite = TestList
  [ testNodeLocal01
  , testNodeLocal02
  , testNodeLocal03
  , testNodeLocal04
  , testNodeLocal05
  , testNodeLocal06
  , testNodeLocal07
  , testNodeLocal08
  ]

------------------------------------------------------------
--  Node generation tests
------------------------------------------------------------

testNodeEq :: String -> RDFLabel -> RDFLabel -> Test
testNodeEq lab l1 l2 =
    TestCase ( assertEqual ("testNodeEq:"++lab) l1 l2 )

tnn01 = (newNode  v1 [b1,b3,v1,v2])
tnn02 = (newNode  b1 [b1,b3,v1,v2])
tnn03 = (newNodes b1 [b1,b3,v1,v2])!!0
tnn04 = (newNodes b1 [b1,b3,v1,v2])!!1
tnn05 = (newNodes b1 [b1,b3,v1,v2])!!2
tnn06 = (newNodes s1 [b1,b3,v1,v2,tnns3])!!0
tnn07 = (newNodes s1 [b1,b3,v1,v2,tnns3])!!1
tnn08 = (newNodes s1 [b1,b3,v1,v2,tnns3])!!2
tnn09 = (newNodes l1 [b1,b3,v1,v2,tnns3])!!2

tnns1 = Blank "Res_s1"
tnns2 = Blank "Res_s2"
tnns3 = Blank "Res_s3"
tnns4 = Blank "Res_s4"
tnnl1 = Blank "Lit_2"

testNewNode01 = testNodeEq "testNewNode01" v3    tnn01
testNewNode02 = testNodeEq "testNewNode02" b2    tnn02
testNewNode03 = testNodeEq "testNewNode03" b2    tnn03
testNewNode04 = testNodeEq "testNewNode04" b4    tnn04
testNewNode05 = testNodeEq "testNewNode05" b5    tnn05
testNewNode06 = testNodeEq "testNewNode06" tnns1 tnn06
testNewNode07 = testNodeEq "testNewNode07" tnns2 tnn07
testNewNode08 = testNodeEq "testNewNode08" tnns4 tnn08
testNewNode09 = testNodeEq "testNewNode09" tnnl1 tnn09

testNewNodeSuite = TestList
  [ testNewNode01
  , testNewNode02
  , testNewNode03
  , testNewNode04
  , testNewNode05
  , testNewNode06
  , testNewNode07
  , testNewNode08
  , testNewNode09
  ]

------------------------------------------------------------
--  RDFLabel ordering tests
------------------------------------------------------------

testLabelOrd :: String -> Ordering -> RDFLabel -> RDFLabel -> Test
testLabelOrd lab order n1 n2 =
    TestCase ( assertEqual
               ("testLabelOrd:"++lab++"["++(show n1)++","++(show n2)++"]")
               order (compare n1 n2) )

nodeorder =
  -- literals
  [ "l1"
  , "l11", "l12", "l10"
  , "l2", "l3"
  , "l5", "l6", "l4", "l8", "l9", "l7"
  -- variables
  , "v1", "v2"
  -- URIs
  , "o1", "p1", "s1"
  , "o2", "p2", "s2"
  , "s4", "o4", "s6", "s7"
  , "o3", "p3", "p4", "s3"
  -- blank nodes
  , "b1", "b2", "b3", "b4"
  , "o5", "s5", "s8"
  ]

testNodeOrdSuite = TestList
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
--  Other RDFLabel tests
------------------------------------------------------------

testLabelName01 = testEq "testLabelName01" (getScopedName s1) qb1s1
testLabelName02 = testEq "testLabelName02" (getScopedName b1) nullScopedName
testLabelName03 = testEq "testLabelName03" (getScopedName l1) nullScopedName
testLabelName04 = testEq "testLabelName04" (getScopedName v1) nullScopedName

testLabelOtherSuite = TestList
    [ testLabelName01, testLabelName02, testLabelName03, testLabelName04
    ]

------------------------------------------------------------
--  Statement construction and equality tests
------------------------------------------------------------

testStmtEq :: String -> Bool -> RDFTriple -> RDFTriple -> Test
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
    trp (_,s) (_,p) (_,o) = arc s p o

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
--  Graph construction and equality tests
------------------------------------------------------------

testGraphEq :: String -> Bool -> RDFGraph -> RDFGraph -> Test
testGraphEq lab eq g1 g2 =
    --  Set test False to get extra trace info about graph differences
    --  Some tests will fail with this setting, so revert to True to
    --  get test result.
    if True then
        TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )
    else
        TestList
            [ TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )
            , TestCase ( assertEqual ("testGraphEq:"++lab) g1 g2 )
            ]

testGraphEqM :: String -> Bool -> Maybe RDFGraph -> Maybe RDFGraph -> Test
testGraphEqM lab eq g1 g2 =
    TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )

t01 = arc s1 p1 o1
t02 = arc s2 p1 o2
t03 = arc s3 p1 o3
t04 = arc s1 p1 l1
t05 = arc s2 p1 l4
t06 = arc s3 p1 l10

t10 = arc s1 p1 b1
t11 = arc b1 p2 b2
t12 = arc b2 p3 o1

t20 = arc s1 p1 b3
t21 = arc b3 p2 b4
t22 = arc b4 p3 o1

tt01 = arc st1 p1 o1
tt02 = arc st2 p1 o2
tt03 = arc st3 p1 o3
tt04 = arc st1 p1 l1
tt05 = arc st2 p1 l4
tt06 = arc st3 p1 l10

makeNewPrefixNamespace :: (String,Namespace) -> Namespace
makeNewPrefixNamespace (pre,ns) = Namespace pre (nsURI ns)

nslist = LookupMap $ map makeNewPrefixNamespace
    [ ("base1",base1)
    , ("base2",base2)
    , ("base3",base3)
    , ("base4",base4)
    ]

nslistalt = LookupMap $ map makeNewPrefixNamespace
    [ ("altbase1",base1)
    , ("altbase2",base2)
    , ("altbase3",base3)
    ]

g1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01]
        }

gt1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tt01]
        }

-- Check for nonsensitivety of graph equility to namespace differences:
g1alt = NSGraph
        { namespaces = nslistalt
        , formulae   = emptyFormulaMap
        , statements = [t01]
        }

--  Construct version of g1 using just URIs
uris1 = makeUriScopedName "http://id.ninebynine.org/wip/2003/test/graph1/node#s1"
urip1 = makeUriScopedName "http://id.ninebynine.org/wip/2003/test/graph1/node#p1"
urio1 = makeUriScopedName "http://id.ninebynine.org/wip/2003/test/graph1/node#o1"
tu01  = arc (Res uris1) (Res urip1) (Res urio1)
g1uri = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tu01]
        }

g2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03,t04,t05,t06]
        }

gt2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tt01,tt02,tt03,tt04,tt05,tt06]
        }

g3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t06,t05,t04,t03,t02,t01]
        }

gt3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tt06,tt05,tt04,tt03,tt02,tt01]
        }

g4 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03,t04,t05,t06,t10,t11,t12]
        }

g5 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03,t04,t05,t06,t20,t21,t22]
        }

g6 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03,t04,t05,t06,t10,t11,t12,t20,t21,t22]
        }

g7 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02]
        }

g8 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t02,t01]
        }

g9 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t03,t02,t01]
        }

g9a = addArc t03 g8

g10 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t02,t02,t01]
        }

g10a = addArc t02 g8

glist =
  [ ("g1",g1), ("g1alt",g1alt), ("g1uri",g1uri)
  , ("g2",g2), ("g3",g3), ("g4",g4), ("g5",g5), ("g6",g6)
  , ("g7",g7), ("g8",g8), ("g9",g9), ("g10",g10)
  , ("g9a",g9a), ("g10a",g10a)
  ]

grapheqlist =
  [ ("g1","g1alt")
  , ("g1","g1uri")
  , ("g1alt","g1uri")
  , ("g2","g3")
  , ("g4","g5")
  , ("g7","g8")
  , ("g7","g10")
  , ("g7","g10a")
  , ("g8","g10")
  , ("g8","g10a")
  , ("g9","g9a")
  , ("g10","g10a")
  ]

testGraphEqSuite = TestList
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
geq99a   = testGraphEq "g9-g9a"   True g9 g9a
geq1010a = testGraphEq "g10-g10a" True g10 g10a

testGraphEqSelSuite = TestList
  [ geq12
  , geq21
  , geq22
  , geq23
  , geq14
  , geq24
  , geq77
  , geq78
  , geq87
  , geq99a
  , geq1010a
  ]


------------------------------------------------------------
--  Test updating formulae
------------------------------------------------------------

testFormulaLookup ::
    String -> FormulaMap RDFLabel -> RDFLabel -> Maybe RDFGraph -> Test
testFormulaLookup lab fs fl gr =
    TestCase ( assertEqual ("testFormulaLookup:"++lab) gr jfg )
    where
        jfg  = mapFindMaybe fl fs

testMaybeEq :: (Eq a, Show a) => String -> Maybe a -> Maybe a -> Test
testMaybeEq lab m1 m2 =
    TestCase ( assertEqual ("testMaybeEq:"++lab) m1 m2 )

g1f1 = g1
f1   = getFormulae g1f1
testGraphFormula01a = testFormulaLookup "01a" f1 s1 Nothing
testGraphFormula01b = testFormulaLookup "01b" f1 s2 Nothing
testGraphFormula01c = testFormulaLookup "01c" f1 s3 Nothing

fm2  = LookupMap [Formula s2 g2]
g1f2 = setFormulae fm2 g1f1
f2   = getFormulae g1f2
testGraphFormula02a = testFormulaLookup "02a" f2 s1 Nothing
testGraphFormula02b = testFormulaLookup "02b" f2 s2 (Just g2)
testGraphFormula02c = testFormulaLookup "02c" f2 s3 Nothing

fm3  = LookupMap [Formula s1 g1,Formula s2 g2,Formula s3 g3]
g1f3 = setFormulae fm3 g1f1
f3   = getFormulae g1f3
testGraphFormula03a = testFormulaLookup "03a" f3 s1 (Just g1)
testGraphFormula03b = testFormulaLookup "03b" f3 s2 (Just g2)
testGraphFormula03c = testFormulaLookup "03c" f3 s3 (Just g3)

fm4  = LookupMap [Formula s1 g1,Formula s2 g3,Formula s3 g3]
g1f4 = setFormulae fm4 g1f1
f4   = getFormulae g1f4
testGraphFormula04a = testFormulaLookup "04a" f4 s1 (Just g1)
testGraphFormula04b = testFormulaLookup "04b" f4 s2 (Just g3)
testGraphFormula04c = testFormulaLookup "04c" f4 s3 (Just g3)

fm5  = LookupMap [Formula s1 g1,Formula s2 g4,Formula s3 g6]
g1f5 = setFormulae fm5 g1f1
f5   = getFormulae g1f5
testGraphFormula05a = testFormulaLookup "05a" f5 s1 (Just g1)
testGraphFormula05b = testFormulaLookup "05b" f5 s2 (Just g4)
testGraphFormula05c = testFormulaLookup "05c" f5 s3 (Just g6)

fm6  = LookupMap [Formula s1 g1,Formula s2 g5,Formula s3 g6]
g1f6 = setFormulae fm6 g1f1
f6   = getFormulae g1f6
testGraphFormula06a = testFormulaLookup "06a" f6 s1 (Just g1)
testGraphFormula06b = testFormulaLookup "06b" f6 s2 (Just g5)
testGraphFormula06c = testFormulaLookup "06c" f6 s3 (Just g6)

fm7  = LookupMap [Formula s1 g1,Formula s2 g7,Formula s3 g6]
g1f7 = setFormulae fm7 g1f1
f7   = getFormulae g1f7
testGraphFormula07a = testFormulaLookup "07a" f7 s1 (Just g1)
testGraphFormula07b = testFormulaLookup "07b" f7 s2 (Just g7)
testGraphFormula07c = testFormulaLookup "07c" f7 s3 (Just g6)

--  Same pattern as 1-3, but using base graph with more nodes used:
--  The graph comparison results are expected to be different,
--  because of formulae associated with nodes actually used in the
--  graph
g2f1 = g2
f8   = getFormulae g2f1
testGraphFormula08a = testFormulaLookup "08a" f8 s1 Nothing
testGraphFormula08b = testFormulaLookup "08b" f8 s2 Nothing
testGraphFormula08c = testFormulaLookup "08c" f8 s3 Nothing

g2f2 = setFormulae fm2 g2f1
f9   = getFormulae g2f2
testGraphFormula09a = testFormulaLookup "09a" f9 s1 Nothing
testGraphFormula09b = testFormulaLookup "09b" f9 s2 (Just g2)
testGraphFormula09c = testFormulaLookup "09c" f9 s3 Nothing

g2f3 = setFormulae fm3 g2f1
f10   = getFormulae g2f3
testGraphFormula10a = testFormulaLookup "10a" f10 s1 (Just g1)
testGraphFormula10b = testFormulaLookup "10b" f10 s2 (Just g2)
testGraphFormula10c = testFormulaLookup "10c" f10 s3 (Just g3)

--  Comparison of graphs containing formulae.
--  The intent is that graphs are matched if there is a bijection,
--  where the matched nodes are associated with matching formulae.
--  Definitions of formulae not used in the graphs don't affect the
--  match result.
testGraphFormula11a = testGraphEq "g1f1-g1f1" True  g1f1 g1f1
testGraphFormula11b = testGraphEq "g1f1-g1f2" True  g1f1 g1f2
testGraphFormula11c = testGraphEq "g1f1-g1f3" False g1f1 g1f3

testGraphFormula12a = testGraphEq "g1f2-g1f1" True  g1f2 g1f1
testGraphFormula12b = testGraphEq "g1f2-g1f2" True  g1f2 g1f2
testGraphFormula12c = testGraphEq "g1f2-g1f3" False g1f2 g1f3

testGraphFormula13a = testGraphEq "g1f3-g1f1" False g1f3 g1f1
testGraphFormula13b = testGraphEq "g1f3-g1f2" False g1f3 g1f2
testGraphFormula13c = testGraphEq "g1f3-g1f3" True  g1f3 g1f3

testGraphFormula14a = testGraphEq "g1f4-g1f3" True  g1f4 g1f3
testGraphFormula14b = testGraphEq "g1f4-g1f4" True  g1f4 g1f4
testGraphFormula14c = testGraphEq "g1f4-g1f5" True  g1f4 g1f5

testGraphFormula15a = testGraphEq "g1f5-g1f5" True  g1f5 g1f5
testGraphFormula15b = testGraphEq "g1f5-g1f6" True  g1f5 g1f6
testGraphFormula15c = testGraphEq "g1f5-g1f7" True  g1f5 g1f7

testGraphFormula16a = testGraphEq "g1f6-g1f5" True  g1f6 g1f5
testGraphFormula16b = testGraphEq "g1f6-g1f6" True  g1f6 g1f6
testGraphFormula16c = testGraphEq "g1f6-g1f7" True  g1f6 g1f7

testGraphFormula17a = testGraphEq "g1f7-g1f5" True  g1f7 g1f5
testGraphFormula17b = testGraphEq "g1f7-g1f6" True  g1f7 g1f6
testGraphFormula17c = testGraphEq "g1f7-g1f7" True  g1f7 g1f7

testGraphFormula18a = testGraphEq "g2f1-g2f1" True  g2f1 g2f1
testGraphFormula18b = testGraphEq "g2f1-g2f2" False g2f1 g2f2
testGraphFormula18c = testGraphEq "g2f1-g2f3" False g2f1 g2f3

testGraphFormula19a = testGraphEq "g2f2-g2f1" False g2f2 g2f1
testGraphFormula19b = testGraphEq "g2f2-g2f2" True  g2f2 g2f2
testGraphFormula19c = testGraphEq "g2f2-g2f3" False g2f2 g2f3

testGraphFormula20a = testGraphEq "g2f3-g2f1" False g2f3 g2f1
testGraphFormula20b = testGraphEq "g2f3-g2f2" False g2f3 g2f2
testGraphFormula20c = testGraphEq "g2f3-g2f3" True  g2f3 g2f3

--  Test methods to set/access an individual formula in a graph
g1f21 = setFormula  (Formula s1 g7) g1f2
f21   = getFormulae g1f21
testGraphFormula21a = testFormulaLookup "21a" f21 s1 (Just g7)
testGraphFormula21b = testFormulaLookup "21b" f21 s2 (Just g2)
testGraphFormula21c = testFormulaLookup "21c" f21 s3 Nothing

g1f22 = setFormula  (Formula s1 g1) g1f21
f22   = getFormulae g1f22
testGraphFormula22a = testFormulaLookup "22a" f22 s1 (Just g1)
testGraphFormula22b = testFormulaLookup "22b" f22 s2 (Just g2)
testGraphFormula22c = testFormulaLookup "22c" f22 s3 Nothing

f23a = getFormula g1f22 s1
f23b = getFormula g1f22 s2
f23c = getFormula g1f22 s3
testGraphFormula23a = testMaybeEq "23a" f23a (Just g1)
testGraphFormula23b = testMaybeEq "23b" f23b (Just g2)
testGraphFormula23c = testMaybeEq "23c" f23c Nothing


testGraphFormulaSuite = TestLabel "TestFormulae" $ TestList
  [ testGraphFormula01a, testGraphFormula01b, testGraphFormula01c
  , testGraphFormula02a, testGraphFormula02b, testGraphFormula02c
  , testGraphFormula03a, testGraphFormula03b, testGraphFormula03c
  , testGraphFormula04a, testGraphFormula04b, testGraphFormula04c
  , testGraphFormula05a, testGraphFormula05b, testGraphFormula05c
  , testGraphFormula06a, testGraphFormula06b, testGraphFormula06c
  , testGraphFormula07a, testGraphFormula07b, testGraphFormula07c
  , testGraphFormula08a, testGraphFormula08b, testGraphFormula08c
  , testGraphFormula09a, testGraphFormula09b, testGraphFormula09c
  , testGraphFormula10a, testGraphFormula10b, testGraphFormula10c
  , testGraphFormula11a, testGraphFormula11b, testGraphFormula11c
  , testGraphFormula12a, testGraphFormula12b, testGraphFormula12c
  , testGraphFormula13a, testGraphFormula13b, testGraphFormula13c
  , testGraphFormula14a, testGraphFormula14b, testGraphFormula14c
  , testGraphFormula15a, testGraphFormula15b, testGraphFormula15c
  , testGraphFormula16a, testGraphFormula16b, testGraphFormula16c
  , testGraphFormula17a, testGraphFormula17b, testGraphFormula17c
  , testGraphFormula18a, testGraphFormula18b, testGraphFormula18c
  , testGraphFormula19a, testGraphFormula19b, testGraphFormula19c
  , testGraphFormula20a, testGraphFormula20b, testGraphFormula20c
  , testGraphFormula21a, testGraphFormula21b, testGraphFormula21c
  , testGraphFormula22a, testGraphFormula22b, testGraphFormula22c
  , testGraphFormula23a, testGraphFormula23b, testGraphFormula23c
  ]

------------------------------------------------------------
--  Test fmap translations of graphs, including formulae
------------------------------------------------------------

translate lab
    | lab == s1 = st1
    | lab == s2 = st2
    | lab == s3 = st3
    | otherwise = lab

translateM lab
    | lab == s1   = Just st1
    | lab == s2   = Just st2
    | lab == s3   = Just st3
    | isBlank lab = Nothing
    | otherwise   = Just lab

gt1f1a = gt1
gt1f1b = fmap translate g1f1
ft1    = getFormulae gt1f1b
testGraphTranslate01a = testGraphEq "gt1f1a-gt1f1b" True gt1f1a gt1f1b
testGraphTranslate01b = testFormulaLookup "GraphTranslate01b" ft1 st1 Nothing
testGraphTranslate01c = testFormulaLookup "GraphTranslate01c" ft1 st2 Nothing
testGraphTranslate01d = testFormulaLookup "GraphTranslate01d" ft1 st3 Nothing
testGraphTranslate01e = testEq "gt1f1a-gt1f1b" gt1f1a gt1f1b

ftm2   = LookupMap [Formula st2 gt2]
gt1f2a = setFormulae ftm2 gt1
gt1f2b = fmap translate g1f2
ft2    = getFormulae gt1f2b
testGraphTranslate02a = testGraphEq "gt1f2a-gt1f2b" True gt1f2a gt1f2b
testGraphTranslate02b = testFormulaLookup "GraphTranslate02b" ft2 st1 Nothing
testGraphTranslate02c = testFormulaLookup "GraphTranslate02c" ft2 st2 (Just gt2)
testGraphTranslate02d = testFormulaLookup "GraphTranslate02d" ft2 st3 Nothing

ftm3   = LookupMap [Formula st1 gt1,Formula st2 gt2,Formula st3 gt3]
gt1f3a = setFormulae ftm3 gt1
gt1f3b = fmap translate g1f3
ft3    = getFormulae gt1f3b
testGraphTranslate03a = testGraphEq "gt1f3a-gt1f3b" True gt1f3a gt1f3b
testGraphTranslate03b = testFormulaLookup "GraphTranslate03b" ft3 st1 (Just gt1)
testGraphTranslate03c = testFormulaLookup "GraphTranslate03c" ft3 st2 (Just gt2)
testGraphTranslate03d = testFormulaLookup "GraphTranslate03d" ft3 st3 (Just gt3)

gt2f1a = gt2
gt2f1b = fmap translate g2f1
ft4    = getFormulae gt2f1b
testGraphTranslate04a = testGraphEq "gt2f1a-gt2f1b" True gt2f1a gt2f1b
testGraphTranslate04b = testFormulaLookup "GraphTranslate04b" ft4 st1 Nothing
testGraphTranslate04c = testFormulaLookup "GraphTranslate04c" ft4 st2 Nothing
testGraphTranslate04d = testFormulaLookup "GraphTranslate04d" ft4 st3 Nothing

gt2f2a = setFormulae ftm2 gt2
gt2f2b = fmap translate g2f2
ft5    = getFormulae gt2f2b
testGraphTranslate05a = testGraphEq "gt2f2a-gt2f2b" True gt2f2a gt2f2b
testGraphTranslate05b = testFormulaLookup "GraphTranslate05b" ft5 st1 Nothing
testGraphTranslate05c = testFormulaLookup "GraphTranslate05c" ft5 st2 (Just gt2)
testGraphTranslate05d = testFormulaLookup "GraphTranslate05d" ft5 st3 Nothing

gt2f3a = setFormulae ftm3 gt2
gt2f3b = fmap translate g2f3
ft6    = getFormulae gt2f3b
testGraphTranslate06a = testGraphEq "gt2f3a-gt2f3b" True gt2f3a gt2f3b
testGraphTranslate06b = testFormulaLookup "GraphTranslate06b" ft6 st1 (Just gt1)
testGraphTranslate06c = testFormulaLookup "GraphTranslate06c" ft6 st2 (Just gt2)
testGraphTranslate06d = testFormulaLookup "GraphTranslate06d" ft6 st3 (Just gt3)

-- Monadic translate tests, using Maybe Monad
gt1f1aM = Just gt1
gt1f1bM = fmapM translateM g1f1
ft1M    = getFormulae $ fromJust gt1f1bM
testGraphTranslate07a = testGraphEqM "gt1f1aM-gt1f1bM" True gt1f1aM gt1f1bM
testGraphTranslate07b = testFormulaLookup "GraphTranslate07b" ft1M st1 Nothing
testGraphTranslate07c = testFormulaLookup "GraphTranslate07c" ft1M st2 Nothing
testGraphTranslate07d = testFormulaLookup "GraphTranslate07d" ft1M st3 Nothing
testGraphTranslate07e = testEq "gt1f1aM-gt1f1bM" gt1f1aM gt1f1bM

gt1f2aM = Just gt1f2a
gt1f2bM = fmapM translateM g1f2
ft2M    = getFormulae $ fromJust gt1f2bM
testGraphTranslate08a = testGraphEqM "gt1f2aM-gt1f2bM" True gt1f2aM gt1f2bM
testGraphTranslate08b = testFormulaLookup "GraphTranslate08b" ft2M st1 Nothing
testGraphTranslate08c = testFormulaLookup "GraphTranslate08c" ft2M st2 (Just gt2)
testGraphTranslate08d = testFormulaLookup "GraphTranslate08d" ft2M st3 Nothing
testGraphTranslate08e = testEq "gt1f2aM-gt1f2bM" gt1f2aM gt1f1bM

gt1f5M = fmapM translateM g1f5
testGraphTranslate09a = testEq "GraphTranslate09a" Nothing gt1f5M

testGraphTranslateSuite = TestLabel "TestTranslate" $ TestList
  [ testGraphTranslate01a
  , testGraphTranslate01b, testGraphTranslate01c, testGraphTranslate01d
  , testGraphTranslate01e
  , testGraphTranslate02a
  , testGraphTranslate02b, testGraphTranslate02c, testGraphTranslate02d
  , testGraphTranslate03a
  , testGraphTranslate03b, testGraphTranslate03c, testGraphTranslate03d
  , testGraphTranslate04a
  , testGraphTranslate04b, testGraphTranslate04c, testGraphTranslate04d
  , testGraphTranslate05a
  , testGraphTranslate05b, testGraphTranslate05c, testGraphTranslate05d
  , testGraphTranslate06a
  , testGraphTranslate06b, testGraphTranslate06c, testGraphTranslate06d
  , testGraphTranslate07a
  , testGraphTranslate07b, testGraphTranslate07c, testGraphTranslate07d
  , testGraphTranslate07e
  , testGraphTranslate08a
  , testGraphTranslate08b, testGraphTranslate08c, testGraphTranslate08d
  , testGraphTranslate08e
  , testGraphTranslate09a
  ]

------------------------------------------------------------
--  Test merge with conflicting bnodes, including formulae
------------------------------------------------------------

testMerge :: String -> RDFGraph -> RDFGraph -> RDFGraph -> Test
testMerge lab g1 g2 gr =
    TestCase ( assertEquiv ("testMerge:"++lab) gr (merge g1 g2) )
        where
            grequiv g1 g2 = (getArcs g1) `equiv` (getArcs g2)
            assertEquiv lab g1 g2 = assertString $
                if grequiv g1 g2 then ""
                else lab++"\nExpected: "++(show g1)++"\nObtained: "++(show g2)


testEquiv :: (Eq a) => String -> [a] -> [a] -> Test
testEquiv lab l1 l2 = TestCase $ assertBool lab (l1 `equiv` l2)

tm01 = arc s1  p1 b1
tm02 = arc b1  p1 o2
tm03 = arc b1  p1 o3
tm04 = arc b2  p2 b3
tm05 = arc b3  p2 b4
tm06 = arc bb  p2 b5
tm07 = arc s2  p3 v1
tm08 = arc s3  p3 v2
tm09 = arc s4  p1 c1
tm10 = arc c2  p1 o4
tm11 = arc s4  p2 ba1
tm12 = arc ba2 p2 o4
tm13 = arc s4  p2 bn3
tm14 = arc bn4 p2 o4

tm21 = arc s1  p1 b6
tm22 = arc b6  p1 o2
tm23 = arc b6  p1 o3
tm24 = arc b7  p2 b8
tm25 = arc b8  p2 b9
tm26 = arc bb0 p2 b10
tm27 = arc s2  p3 v3
tm28 = arc s3  p3 v4
tm29 = arc s4  p1 c3
tm30 = arc c4  p1 o4
tm31 = arc s4  p2 ba3
tm32 = arc ba4 p2 o4
tm33 = arc s4  p2 bn5
tm34 = arc bn6 p2 o4

tm41  = arc s1  p1 b2
tm42  = arc b2  p1 o2
tm43  = arc b2  p1 o3
tm44  = arc b4  p2 b5

tm41a = arc s1  p1 b4
tm44a = arc b5  p2 b6

tm67 = arc s2  p3 v3
tm68 = arc s3  p3 v4
tm69 = arc s4  p1 c3
tm70 = arc c4  p1 o4
tm71 = arc s4  p2 ba3
tm72 = arc ba4 p2 o4
tm73 = arc s4  p2 bn5
tm74 = arc bn6 p2 o4

gm1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01,tm02,tm03,tm04,tm05,tm06,tm07,tm08
                       ,tm09,tm10,tm11,tm12,tm13,tm14
                       ]
        }

gm11  = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01,tm02,tm03,tm04,tm05,tm06,tm07,tm08
                       ,tm09,tm10,tm11,tm12,tm13,tm14
                       ,tm21,tm22,tm23,tm24,tm25,tm26,tm27,tm28
                       ,tm29,tm30,tm31,tm32,tm33,tm34
                       ]
        }

gm2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01]
        }

gm2f = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm41]
        }

gm22 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01,tm41]
        }

gm3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm04]
        }

gm3f = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm44]
        }

gm33 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm04,tm44]
        }

gm4 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01,tm04]
        }

gm44 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm01,tm04,tm41a,tm44a]
        }

gm5 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula b1 gm2]
        , statements = [tm01,tm02,tm03]
        }

gm55 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula b1 gm2,Formula b2 gm2f]
        , statements = [tm01,tm02,tm03,tm41,tm42,tm43]
        }

gm6 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula ba1 gm2,Formula bn3 gm3]
        , statements = [tm07,tm08,tm09,tm10,tm11,tm12,tm13,tm14]
        }

gm66 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap
                       [Formula ba1 gm2,Formula bn3 gm3
                       ,Formula ba3 gm2f,Formula bn5 gm3f
                       ]
        , statements = [tm07,tm08,tm09,tm10,tm11,tm12,tm13,tm14
                       ,tm67,tm68,tm69,tm70,tm71,tm72,tm73,tm74
                       ]
        }


tm81  = arc b1 p1 v1
tm82  = arc b2 p2 v2
tm811 = arc b1 p1 v3
tm821 = arc b2 p2 v4
tm812 = arc b1 p1 vb3
tm822 = arc b2 p2 vb4

gm81 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm81,tm82]
        }

gm82 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm811,tm821]
        }
gm82a = remapLabels [v1,v2] [v1,v2,b1,b2] id gm81
gm82b1 = remapLabelList [v1,v2] [v1,v2,b1,b2]
gm82b2 = [(v1,v3),(v2,v4)]

gm83 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tm811,tm821]
        }
gm83a = remapLabels [v1,v2] [v1,v2,b1,b2] makeBlank gm81

gm84  = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula b1 gm81,Formula v2 gm81]
        , statements = [tm81,tm82]
        }

gm85 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula b1 gm82,Formula v4 gm82]
        , statements = [tm811,tm821]
        }
gm85a = remapLabels [v1,v2] [v1,v2,b1,b2] id gm84

gm86 = NSGraph
        { namespaces = nslist
        , formulae   = LookupMap [Formula b1 gm82,Formula vb4 gm82]
        , statements = [tm812,tm822]
        }
gm86a = remapLabels [v1,v2] [v1,v2,b1,b2] makeBlank gm84

testMerge01 = testMerge "01" gm1 gm1 gm11
testMerge02 = testMerge "02" gm2 gm2 gm22
testMerge03 = testMerge "03" gm3 gm3 gm33
testMerge04 = testMerge "04" gm4 gm4 gm44
testMerge05 = testMerge "05" gm5 gm5 gm55
testMerge06 = testMerge "06" gm6 gm6 gm66

testRemap07 = testGraphEq "Remap07" True gm82 gm82a
testRemapList07 = testEquiv "testRemapList07" gm82b2 gm82b1
testRemap08 = testGraphEq "Remap08" True gm83 gm83a
testRemap09 = testGraphEq "Remap09" True gm85 gm85a
testRemap10 = testGraphEq "Remap10" True gm86 gm86a

testMergeSuite = TestList
  [ testMerge01
  , testMerge02
  , testMerge03
  , testMerge04
  , testMerge05
  , testMerge06
  , testRemap07
  , testRemapList07
  , testRemap08
  , testRemap09
  , testRemap10
  ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ testLangEqSuite
  , testNodeEqSuite
  , testNodeClassSuite
  , testNodeLocalSuite
  , testNewNodeSuite
  , testNodeOrdSuite
  , testLabelOtherSuite
  , testStmtEqSuite
  , testGraphEqSuite
  , testGraphEqSelSuite
  , testGraphFormulaSuite
  , testGraphTranslateSuite
  , testMergeSuite
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

geq  = testGraphEqSuite
nord = testNodeOrdSuite
gtr  = testGraphTranslateSuite

gmm g1 g2 = grMatchMap g1 g2

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
-- $Source: /file/cvsdev/HaskellRDF/RDFGraphTest.hs,v $
-- $Author: graham $
-- $Revision: 1.32 $
-- $Log: RDFGraphTest.hs,v $
-- Revision 1.32  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.31  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.30  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.29  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.28  2003/11/24 15:46:04  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.27  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.26  2003/10/01 00:36:25  graham
-- Added RDFGraph method to test for container membership property label.
-- Added RDFQuery filter function to select container membership properties.
--
-- Revision 1.25  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.24  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.23  2003/07/02 21:27:30  graham
-- Graph closure with instance rule tested.
-- About to change ProofTest for graph forward chaining to return
-- a single result graph.
--
-- Revision 1.22  2003/07/01 14:20:30  graham
-- Added instance entailment to proof check module.
--
-- Revision 1.21  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.20  2003/06/17 15:43:35  graham
-- remapNodes now accepts a node-mapping function rather than just
-- a Boolean to control conversion of query variable nodes to blank
-- nodes, and who knows what else.
--
-- Revision 1.19  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.18  2003/06/12 00:49:05  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
-- Revision 1.17  2003/06/10 17:38:34  graham
-- Remove some unneeded calss constraints from data type declarations
-- Reworked NSGraph to be an instance of Functor, replacing function
-- gmap with fmap.  Graph formulae are still not handled well:  the data types
-- will need re-working so that a "Formula lb" type constructor can be
-- introduced having the correct (* -> *) kind to be a Functor.
--
-- Revision 1.16  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.15  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.14  2003/05/29 00:57:37  graham
-- Resolved swish performance problem, which turned out to an inefficient
-- method used by the parser to add arcs to a graph.
--
-- Revision 1.13  2003/05/27 19:15:50  graham
-- Graph merge (with blank node renaming) complete and passes tests.
--
-- Revision 1.12  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.11  2003/05/23 19:33:36  graham
-- Added and tested RDF graph label translation functions
--
-- Revision 1.10  2003/05/14 16:50:32  graham
-- Graph matching seems solid now:
-- RDFGraphTest and N3ParserTest pass all tests
-- Updated TODO file with comments from code
--
-- Revision 1.9  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.8  2003/05/07 23:58:09  graham
-- More restructuring.
-- RDFGraphTest runs OK.
-- N3ParserTest needs to be updated to use new structure for formulae.
--
-- Revision 1.7  2003/05/07 19:25:00  graham
-- Restructured formula handling in RDF graph
--
-- Revision 1.6  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.5  2003/04/17 00:35:39  graham
-- Added module N3ParserTest
-- N3parser is mostly working
-- Formulae remain to test
--
-- Revision 1.4  2003/04/15 21:40:54  graham
-- N3Parser compiles
-- Some small changes to RDFGraph
-- Added some QName methods
--
-- Revision 1.3  2003/04/10 20:08:39  graham
-- Reorganized RDFGraph naming (RDFGraphTest OK)
-- Progressing N3Parser
--
-- Revision 1.2  2003/04/10 15:06:30  graham
-- RDFGraph now passes all test cases
--
-- Revision 1.1  2003/03/28 21:50:22  graham
-- Graph equality coded and nearly working
--
-- Revision 1.1  2003/03/12 23:00:43  graham
-- Graph model coded and working, except for graph isomorphism test.
--
