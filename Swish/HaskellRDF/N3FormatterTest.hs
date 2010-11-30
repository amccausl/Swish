--------------------------------------------------------------------------------
--  $Id: N3FormatterTest.hs,v 1.21 2004/01/09 12:57:08 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  N3FormatterTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This Module defines test cases for module Parse parsing functions.
--
--------------------------------------------------------------------------------

-- WNH module Swish.HaskellRDF.N3FormatterTest where

import Swish.HaskellRDF.N3Formatter
    ( formatGraphAsStringNl
    , formatGraphAsString
    , formatGraphDiag )

import Swish.HaskellRDF.N3Parser
    ( ParseResult(..)
    , parseN3fromString
    , parseTextFromString, parseAltFromString
    , parseNameFromString, parsePrefixFromString
    , parseAbsURIrefFromString, parseLexURIrefFromString
    , parseURIref2FromString )

import Swish.HaskellRDF.RDFGraph
    ( RDFTriple, RDFGraph, RDFLabel(..), NSGraph(..)
    , setArcs, getArcs, add, delete, extract, labels
    , NamespaceMap, emptyNamespaceMap
    , LookupFormula(..), Formula, FormulaMap, emptyFormulaMap
    , setNamespaces
    , emptyRDFGraph, toRDFGraph
      -- Export selected RDFLabel values
    , res_rdf_type, res_rdf_first, res_rdf_rest, res_rdf_nil
    , res_rdfs_member
    , res_rdfd_GeneralRestriction
    , res_rdfd_onProperties, res_rdfd_constraint, res_rdfd_maxCardinality
    , res_owl_sameAs
    , res_operator_plus, res_operator_minus
    , res_operator_slash, res_operator_star
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , makeNamespaceQName
    , getQName, getScopedNameURI
    , ScopedName(..)
    , makeScopedName, makeQNameScopedName
    , nullScopedName
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
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
    , rdf_type
    , rdf_first, rdf_rest, rdf_nil
    , rdfs_member
    , rdfd_GeneralRestriction
    , rdfd_onProperties, rdfd_constraint, rdfd_maxCardinality
    , owl_sameAs
    , operator_plus, operator_minus, operator_slash, operator_star
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    , newQName, qnameFromPair, qnameFromURI
    , getNamespace, getLocalName, getQNameURI
    , splitURI
    )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..)
    , emptyLookupMap, makeLookupMap, listLookupMap )

import Swish.HaskellRDF.GraphClass
    ( Arc, arcSubj, arcPred, arcObj, arc )

import Swish.HaskellUtils.ErrorM
    ( ErrorM(..) )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertEqual, runTestTT, runTestText, putTextToHandle )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

------------------------------------------------------------
--  Common test wrappers
------------------------------------------------------------

testLabelEq :: String -> Bool -> RDFLabel -> RDFLabel -> Test
testLabelEq lab eq n1 n2 =
    TestCase ( assertEqual ("testLabelEq:"++lab) eq (n1==n2) )

testGraphEq :: String -> Bool -> RDFGraph -> RDFGraph -> Test
testGraphEq lab eq g1 g2 =
    TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )

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

s1 = Res qb1s1  :: RDFLabel
s2 = Res qb2s2  :: RDFLabel
s3 = Res qb3s3  :: RDFLabel

b1 = Blank "b1" :: RDFLabel
b2 = Blank "b2" :: RDFLabel
b3 = Blank "b3" :: RDFLabel
b4 = Blank "b4" :: RDFLabel
b5 = Blank "b5" :: RDFLabel
b6 = Blank "b6" :: RDFLabel
b7 = Blank "b7" :: RDFLabel
b8 = Blank "b8" :: RDFLabel

c1 = Blank "c1" :: RDFLabel
c2 = Blank "c2" :: RDFLabel
c3 = Blank "c3" :: RDFLabel
c4 = Blank "c4" :: RDFLabel
c5 = Blank "c5" :: RDFLabel
c6 = Blank "c6" :: RDFLabel

qb1p1  = ScopedName base1 "p1"
qb2p2  = ScopedName base2 "p2"
qb3p3  = ScopedName base3 "p3"
qb2p21 = ScopedName base2 "p21"
qb2p22 = ScopedName base2 "p22"
qb2p23 = ScopedName base2 "p23"
qb2p24 = ScopedName base2 "p24"
qb2p25 = ScopedName base2 "p25"
qb2p26 = ScopedName base2 "p26"

p1  = Res qb1p1  :: RDFLabel
p2  = Res qb2p2  :: RDFLabel
p3  = Res qb3p3  :: RDFLabel
p21 = Res qb2p21 :: RDFLabel
p22 = Res qb2p22 :: RDFLabel
p23 = Res qb2p23 :: RDFLabel
p24 = Res qb2p24 :: RDFLabel
p25 = Res qb2p25 :: RDFLabel
p26 = Res qb2p26 :: RDFLabel

qb1o1 = ScopedName base1 "o1"
qb2o2 = ScopedName base2 "o2"
qb3o3 = ScopedName base3 "o3"

o1 = Res qb1o1 :: RDFLabel
o2 = Res qb2o2 :: RDFLabel
o3 = Res qb3o3 :: RDFLabel

l1txt = "l1"
l2txt = "l2-'\"line1\"'\n\nl2-'\"\"line2\"\"'"
l3txt = "l3--\r\"'\\--\x0020\&--\x00A0\&--"
l11txt = "lx11"
l12txt = "lx12"
l13txt = "lx13"
l14txt = "lx14"

l1  = Lit l1txt  Nothing    :: RDFLabel
l2  = Lit l2txt  Nothing    :: RDFLabel
l3  = Lit l3txt  Nothing    :: RDFLabel
l11 = Lit l11txt Nothing    :: RDFLabel
l12 = Lit l12txt Nothing    :: RDFLabel
l13 = Lit l13txt Nothing    :: RDFLabel
l14 = Lit l14txt Nothing    :: RDFLabel

qb1f1 = ScopedName base1 "f1"
qb2f2 = ScopedName base2 "f2"

f1 = Res qb1f1 :: RDFLabel
f2 = Res qb2f2 :: RDFLabel

v1 = Var "var1" :: RDFLabel
v2 = Var "var2" :: RDFLabel
v3 = Var "var3" :: RDFLabel
v4 = Var "var4" :: RDFLabel

------------------------------------------------------------
--  Construct graphs for testing
------------------------------------------------------------

t01 = arc s1 p1 o1
t02 = arc s2 p1 o2
t03 = arc s3 p1 o3
t04 = arc s1 p1 l1
t05 = arc s2 p1 b1
t06 = arc s3 p1 l2
t07 = arc s3 p2 l3

nslist = makeLookupMap
    [ base1
    , base2
    , base3
    , base4
    ]

g1np = NSGraph
        { namespaces = emptyNamespaceMap
        , formulae   = emptyFormulaMap
        , statements = [t01]
        }

g1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01]
        }

g1b1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [b01]
        }
    where
        b01 = arc b1 p1 o1

g1b3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [b01]
        }
    where
        b01 = arc b1 b2 b3

g1a1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [a01]
        }
    where
        a1  = Blank "1"  :: RDFLabel
        a01 = arc a1 p1 o1

g1l1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [l01]
        }
    where
        l01 = arc s1 p1 l1

g1l2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [l02]
        }
    where
        l02 = arc s1 p1 l2


g1f1 = NSGraph
        { namespaces = nslist
        , formulae   = formo1g1
        , statements = [f01]
        }
    where
        f01      = arc s1 p1 o1
        formo1g1 = LookupMap [Formula o1 g1]


g1f2 = NSGraph
        { namespaces = nslist
        , formulae   = formb2g1
        , statements = [f02]
        }
    where
        f02 = arc s1 p1 b2
        formb2g1 = LookupMap [Formula b2 g1]

g1f3 = NSGraph
        { namespaces = nslist
        , formulae   = formb3g1f2
        , statements = [f02]
        }
    where
        f02 = arc s1 p1 b3
        formb3g1f2 = LookupMap [Formula b3 g1f2]

----

g2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03]
        }

g3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t04]
        }

g4 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t05]
        }

g5 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t02,t03,t04,t05]
        }

g6 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t06]
        }

g7 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01,t07]
        }

pref_rdf = nsURI namespaceRDF
pref_op  = nsURI namespaceRDFO
pref_owl = nsURI namespaceOWL

t801 = arc s1 res_rdf_type       o1
t802 = arc s2 res_owl_sameAs     o2
t803 = arc s3 res_operator_plus  o3
t804 = arc s3 res_operator_minus o3
t805 = arc s3 res_operator_star  o3
t806 = arc s3 res_operator_slash o3
t807 = arc o1 p1 s1
t808 = arc s2 p1 o2
t809 = arc s1 p2 o1
t810 = arc o2 p2 s2

g8 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t801,t802,t803,t804,t805,t806,t807,t808,t809,t810]
        }

g81 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t801,t802]
        }

g82 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t803,t804,t805,t806]
        }

g83 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t807,t808,t809,t810]
        }

t911 = arc s1 p1 o1
t912 = arc s1 p1 o2
t913 = arc s1 p2 o2
t914 = arc s1 p2 o3
t921 = arc s2 p1 o1
t922 = arc s2 p1 o2
t923 = arc s2 p1 o3
t924 = arc s2 p1 l1
t925 = arc s2 p2 o1
t926 = arc s2 p2 o2
t927 = arc s2 p2 o3
t928 = arc s2 p2 l1

g9 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t911,t912,t913,t914,
                        t921,t922,t923,t924,
                        t925,t926,t927,t928]
        }

t1011 = arc s1 p1 o1
t1012 = arc o2 p1 s1
t1013 = arc s1 p2 o2
t1014 = arc o3 p2 s1
t1021 = arc s2 p1 o1
t1022 = arc s2 p1 o2
t1023 = arc s2 p1 o3
t1024 = arc s2 p1 l1
t1025 = arc o1 p2 s2
t1026 = arc o2 p2 s2
t1027 = arc o3 p2 s2
-- t1028 = arc l1 p2 s2
t1028 = arc s1 p2 s2

g10 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1011,t1012,t1013,t1014,
                        t1021,t1022,t1023,t1024,
                        t1025,t1026,t1027,t1028 ]
        }

t1111 = arc s1 p1 v1
t1112 = arc v2 p1 o1
t1113 = arc v3 p1 v4

g11 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1111,t1112,t1113]
        }

tx101 = arc b1 res_owl_sameAs s1
tx102 = arc s2 res_owl_sameAs b2
tx111 = arc b1 p1 o1
tx112 = arc b1 p1 o2
tx113 = arc b1 p2 o2
tx114 = arc b1 p2 o3
tx121 = arc b2 p1 o1
tx122 = arc b2 p1 o2
tx123 = arc b2 p1 o3
tx124 = arc b2 p1 l1
tx125 = arc b2 p2 o1
tx126 = arc b2 p2 o2
tx127 = arc b2 p2 o3
tx128 = arc b2 p2 l1

x1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx101,tx102,
                        tx111,tx112,tx113,tx114,
                        tx121,tx122,tx123,tx124,
                        tx125,tx126,tx127,tx128]
        }

tx201 = arc b1 res_owl_sameAs s1
tx202 = arc s2 res_owl_sameAs b2
tx211 = arc b1 p1 o1
tx212 = arc o2 p1 b1
tx213 = arc b1 p2 o2
tx214 = arc o3 p2 b1
tx221 = arc b2 p1 o1
tx222 = arc b2 p1 o2
tx223 = arc b2 p1 o3
tx224 = arc b2 p1 l1
tx225 = arc o1 p2 b2
tx226 = arc o2 p2 b2
tx227 = arc o3 p2 b2
-- tx228 = arc l1 p2 b2

x2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx201,tx202,
                        tx211,tx212,tx213,tx214,
                        tx221,tx222,tx223,tx224,
                        tx225,tx226,tx227]
        }

tx311 = arc s1 p1 o1
tx312 = arc o2 p1 s1
tx313 = arc s1 p2 o2
tx314 = arc o3 p2 s1
tx321 = arc s2 p1 o1
tx322 = arc s2 p1 o2
tx323 = arc s2 p1 o3
tx324 = arc s2 p1 l1
tx325 = arc o1 p2 s2
tx326 = arc o2 p2 s2
tx327 = arc o3 p2 s2
-- tx328 = arc l1 p2 s2

x3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx311,tx312,tx313,tx314,
                        tx321,tx322,tx323,tx324,
                        tx325,tx326,tx327]
        }

tx401 = arc s1 res_owl_sameAs b1
tx402 = arc b1 res_rdf_first  o1
tx403 = arc b1 res_rdf_rest   b2
tx404 = arc b2 res_rdf_first  o2
tx405 = arc b2 res_rdf_rest   b3
tx406 = arc b3 res_rdf_first  o3
tx407 = arc b3 res_rdf_rest   b4
tx408 = arc b4 res_rdf_first  l1
tx409 = arc b4 res_rdf_rest   res_rdf_nil

x4 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx401,tx402,tx403,tx404,
                        tx405,tx406,tx407,tx408,
                        tx409]
        }

tx501 = arc b1 res_owl_sameAs s1
tx502 = arc b1 res_rdf_first  o1
tx503 = arc b1 res_rdf_rest   b2
tx504 = arc b2 res_rdf_first  o2
tx505 = arc b2 res_rdf_rest   b3
tx506 = arc b3 res_rdf_first  o3
tx507 = arc b3 res_rdf_rest   b4
tx508 = arc b4 res_rdf_first  l1
tx509 = arc b4 res_rdf_rest   res_rdf_nil

x5 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx501,tx502,tx503,tx504,
                        tx505,tx506,tx507,tx508,
                        tx509]
        }

tx601 = arc s1 res_rdf_first o1
tx602 = arc s1 res_rdf_rest  b2
tx603 = arc b2 res_rdf_first o2
tx604 = arc b2 res_rdf_rest  b3
tx605 = arc b3 res_rdf_first o3
tx606 = arc b3 res_rdf_rest  b4
tx607 = arc b4 res_rdf_first l1
tx608 = arc b4 res_rdf_rest  res_rdf_nil

x6 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx601,tx602,tx603,tx604,
                        tx605,tx606,tx607,tx608]
        }

formb1g2 = LookupMap [Formula b1 g2]
tx701    = arc b1 p2 f2
x7       = NSGraph
        { namespaces = nslist
        , formulae   = formb1g2
        , statements = [tx701]
        }

formf1g2 = LookupMap [Formula f1 g2]
tx801    = arc f1 p2 f2
x8       = NSGraph
        { namespaces = nslist
        , formulae   = formf1g2
        , statements = [tx801]
        }

formf1g1 = LookupMap [Formula f1 g1]
tx901 = arc f1 p2 f2

x9 = NSGraph
        { namespaces = nslist
        , formulae   = formf1g1
        , statements = [tx801]
        }

--  Test allocation of bnodes carries over a nested formula
tx1201 = arc s1 p1 b1
tx1202 = arc b1 p1 o1
tx1203 = arc b2 p2 f2
tx1204 = arc s3 p3 b3
tx1205 = arc b3 p3 o3
tx1211 = arc s2 p2 b4
tx1212 = arc b4 p2 o2
x12fg  = NSGraph
        { namespaces = emptyNamespaceMap
        , formulae   = emptyFormulaMap
        , statements = [tx1211,tx1212]
        }
x12f   = LookupMap [Formula b2 x12fg]
x12    = NSGraph
        { namespaces = nslist
        , formulae   = x12f
        , statements = [tx1201,tx1202,tx1203,tx1204,tx1205]
        }

--  List of simple anon nodes
tx1301 = arc s1 res_rdf_first b1
tx1302 = arc s1 res_rdf_rest  c1
tx1303 = arc c1 res_rdf_first b2
tx1304 = arc c1 res_rdf_rest  c2
tx1305 = arc c2 res_rdf_first b3
tx1306 = arc c2 res_rdf_rest  res_rdf_nil
tx1307 = arc b1 p1 o1
tx1308 = arc b2 p1 o2
tx1309 = arc b3 p1 o3

x13    = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1301,tx1302,tx1303,tx1304,tx1305,tx1306,
                        tx1307,tx1308,tx1309]
        }

--  List of simple anon nodes using autogenerated bnodes
b_1 = Blank "1" :: RDFLabel
b_2 = Blank "2" :: RDFLabel
b_3 = Blank "3" :: RDFLabel
c_1 = Blank "4" :: RDFLabel
c_2 = Blank "5" :: RDFLabel

tx1301a = arc s1  res_rdf_first b_1
tx1302a = arc s1  res_rdf_rest  c_1
tx1303a = arc c_1 res_rdf_first b_2
tx1304a = arc c_1 res_rdf_rest  c_2
tx1305a = arc c_2 res_rdf_first b_3
tx1306a = arc c_2 res_rdf_rest  res_rdf_nil
tx1307a = arc b_1 p1 o1
tx1308a = arc b_2 p1 o2
tx1309a = arc b_3 p1 o3

x13a = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1301a,tx1302a,tx1303a,tx1304a,tx1305a,tx1306a,
                        tx1307a,tx1308a,tx1309a]
        }

--  List of more complex anon nodes
tx1401 = arc s1 res_rdf_first b1
tx1402 = arc s1 res_rdf_rest  c1
tx1403 = arc c1 res_rdf_first b2
tx1404 = arc c1 res_rdf_rest  c2
tx1405 = arc c2 res_rdf_first b3
tx1406 = arc c2 res_rdf_rest  res_rdf_nil
tx1407 = arc b1 p1 o1
tx1408 = arc b1 p2 o1
tx1409 = arc b2 p1 o2
tx1410 = arc b2 p2 o2
tx1411 = arc b3 p1 o3
tx1412 = arc b3 p2 o3

x14    = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1401,tx1402,tx1403,tx1404,tx1405,tx1406,
                        tx1407,tx1408,tx1409,tx1410,tx1411,tx1412]
        }

--  List with nested list
tx1501 = arc s1 res_rdf_first b1
tx1502 = arc s1 res_rdf_rest  c1
tx1503 = arc c1 res_rdf_first b2
tx1504 = arc c1 res_rdf_rest  c2
tx1505 = arc c2 res_rdf_first b3
tx1506 = arc c2 res_rdf_rest  res_rdf_nil
tx1507 = arc b1 p1 o1
tx1508 = arc b2 p2 c3
tx1509 = arc b3 p1 o3

tx1521 = arc c3 res_rdf_first b4
tx1522 = arc c3 res_rdf_rest  c4
tx1523 = arc c4 res_rdf_first b5
tx1524 = arc c4 res_rdf_rest  c5
tx1525 = arc c5 res_rdf_first b6
tx1526 = arc c5 res_rdf_rest  res_rdf_nil
tx1527 = arc b4 p1 o1
tx1528 = arc b5 p1 o2
tx1529 = arc b6 p1 o3

x15    = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1501,tx1502,tx1503,tx1504,tx1505,tx1506,
                        tx1507,tx1508,tx1509,
                        tx1521,tx1522,tx1523,tx1524,tx1525,tx1526,
                        tx1527,tx1528,tx1529]
        }



--  More complex list with nested list
tx1601 = arc s1 res_rdf_first b1
tx1602 = arc s1 res_rdf_rest  c1
tx1603 = arc c1 res_rdf_first b2
tx1604 = arc c1 res_rdf_rest  c2
tx1605 = arc c2 res_rdf_first b3
tx1606 = arc c2 res_rdf_rest  res_rdf_nil
tx1607 = arc b1 p1 o1
tx1608 = arc b1 p2 o1
tx1609 = arc b2 p2 c3
tx1610 = arc b3 p1 o3
tx1611 = arc b3 p2 o3

tx1621 = arc c3 res_rdf_first b4
tx1622 = arc c3 res_rdf_rest  c4
tx1623 = arc c4 res_rdf_first b5
tx1624 = arc c4 res_rdf_rest  c5
tx1625 = arc c5 res_rdf_first b6
tx1626 = arc c5 res_rdf_rest  res_rdf_nil
tx1627 = arc b4 p1 o1
tx1628 = arc b4 p2 o1
tx1629 = arc b5 p1 o2
tx1630 = arc b5 p2 o2
tx1631 = arc b6 p1 o3
tx1632 = arc b6 p2 o3

x16    = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1601,tx1602,tx1603,tx1604,tx1605,tx1606,
                        tx1607,tx1608,tx1609,tx1610,tx1611,
                        tx1621,tx1622,tx1623,tx1624,tx1625,tx1626,
                        tx1627,tx1628,tx1629,tx1630,tx1631,tx1632]
        }

--  Troublesome example
tx1701 = arc s1 res_rdf_type  o1
tx1702 = arc s1 res_rdf_first b1
tx1703 = arc s1 res_rdf_rest  c1
tx1704 = arc c1 res_rdf_first b2
tx1705 = arc c1 res_rdf_rest  res_rdf_nil

tx1706 = arc b1 p21 o2
tx1707 = arc b1 p22 c2

tx1708 = arc b2 p24 o3
tx1709 = arc b2 p25 l13

tx1710 = arc c2 res_rdf_first b3
tx1711 = arc c2 res_rdf_rest  c3
tx1712 = arc c3 res_rdf_first l12
tx1713 = arc c3 res_rdf_rest  res_rdf_nil

tx1714 = arc b3 p23 l11

x17    = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx1701,tx1702,tx1703,tx1704,tx1705,tx1706,
                        tx1707,tx1708,tx1709,
                        tx1710,tx1711,tx1712,tx1713,tx1714]
        }

------------------------------------------------------------
--  Trivial formatter tests
------------------------------------------------------------
--
--  These are very basic tests that confirm that output for a
--  simple graph corresponds exactly to some supplied string.

formatTest :: String -> RDFGraph -> String -> Test
formatTest lab gr out =
    TestList
      [ TestCase ( assertEqual ("formatTest:"++lab) out res )
      ]
    where
      res = formatGraphAsStringNl gr

diagTest :: String -> RDFGraph -> String -> Test
diagTest lab gr out =
    TestList
      [ TestCase ( assertEqual ("diag:text:"++lab) out (res "") )
      , TestCase ( assertEqual ("diag:map:"++lab) emptyLookupMap nmap )
      , TestCase ( assertEqual ("diag:gen:"++lab) 0 ngen )
      , TestCase ( assertEqual ("diag:trc:"++lab) [] trc )
      ]
    where
      (res,nmap,ngen,trc) = formatGraphDiag gr

commonPrefixes =
    "@prefix base1: <" ++ nsURI base1 ++ "> .\n" ++
    "@prefix base2: <" ++ nsURI base2 ++ "> .\n" ++
    "@prefix base3: <" ++ nsURI base3 ++ "> .\n" ++
    "@prefix base4: <" ++ nsURI base4 ++ "> .\n"

--  Single statement using <uri> form
simpleN3Graph_g1_01 =
    "<http://id.ninebynine.org/wip/2003/test/graph1/node#s1> " ++
    "<http://id.ninebynine.org/wip/2003/test/graph1/node#p1> " ++
    "<http://id.ninebynine.org/wip/2003/test/graph1/node#o1> .\n"

--  Single statement using prefix:name form
simpleN3Graph_g1_02 =
    commonPrefixes ++
    "base1:s1 base1:p1 base1:o1 .\n"

--  Single blank node
simpleN3Graph_g1_03 =
    commonPrefixes ++
    "_:b1 base1:p1 base1:o1 .\n"

--  Single auto-allocated blank node
simpleN3Graph_g1_04 =
    commonPrefixes ++
    "_:_1 base1:p1 base1:o1 .\n"

--  Single literal object
simpleN3Graph_g1_05 =
    commonPrefixes ++
    "base1:s1 base1:p1 \"l1\" .\n"

--  Single multiline literal object
simpleN3Graph_g1_06 =
    commonPrefixes ++
    "base1:s1 base1:p1 \"l2-'\\\"line1\\\"'\\n\\nl2-'\\\"\\\"line2\\\"\\\"'\" .\n"

--  Single statement with formula node
simpleN3Graph_g1_07 =
    commonPrefixes ++
    "base1:s1 base1:p1 base1:o1 .\n"++
    "base1:o1 :-\n"++
    "    {\n"++
    "    base1:s1 base1:p1 base1:o1\n"++
    "    } .\n"

--  Single statement with formula blank node
simpleN3Graph_g1_08 =
    commonPrefixes ++
    "base1:s1 base1:p1 _:b2 .\n"++
    "_:b2 :-\n"++
    "    {\n"++
    "    base1:s1 base1:p1 base1:o1\n"++
    "    } .\n"

--  Three blank nodes (or is that blind mice?)
simpleN3Graph_g1_09 =
    commonPrefixes ++
    "_:b1 _:b2 _:b3 .\n"

--  Simple nested foprmula case
simpleN3Graph_g1_10 =
    commonPrefixes ++
    "base1:s1 base1:p1 _:b3 .\n"           ++
    "_:b3 :-\n"                            ++
    "    {\n"                              ++
    "    base1:s1 base1:p1 _:b2 .\n"       ++
    "    _:b2 :-\n"                        ++
    "        {\n"                          ++
    "        base1:s1 base1:p1 base1:o1\n" ++
    "        }\n"                          ++
    "    } .\n"

--  Simple troublesome case
simpleN3Graph_x13a =
    commonPrefixes ++
    "base1:s1 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:_1 ;\n"++
    "         <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:_2 .\n"++
    "_:_1 base1:p1 base1:o1 .\n"++
    "_:_3 base1:p1 base2:o2 .\n"++
    "_:_4 base1:p1 base3:o3 .\n"++
    "_:_2 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:_3 ;\n"++
    "     <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:_5 .\n"++
    "_:_5 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> _:_4 ;\n"++
    "     <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n"

trivialTest01 = formatTest "trivialTest01" g1np simpleN3Graph_g1_01
trivialTest02 = formatTest "trivialTest02" g1   simpleN3Graph_g1_02
trivialTest03 = formatTest "trivialTest03" g1b1 simpleN3Graph_g1_03
trivialTest04 = formatTest "trivialTest04" g1a1 simpleN3Graph_g1_04
trivialTest05 = formatTest "trivialTest05" g1l1 simpleN3Graph_g1_05
trivialTest06 = formatTest "trivialTest06" g1l2 simpleN3Graph_g1_06
trivialTest07 = formatTest "trivialTest07" g1f1 simpleN3Graph_g1_07
trivialTest08 = formatTest "trivialTest08" g1f2 simpleN3Graph_g1_08
trivialTest09 = formatTest "trivialTest09" g1b3 simpleN3Graph_g1_09
trivialTest10 = formatTest "trivialTest10" g1f3 simpleN3Graph_g1_10
trivialTest13 = formatTest "trivialTest13" x13a simpleN3Graph_x13a

diag13 = diagTest "trivialTest13" x13a simpleN3Graph_x13a

trivialTestSuite = TestList
  [ trivialTest01
  , trivialTest02
  , trivialTest03
  , trivialTest04
  , trivialTest05
  , trivialTest06
  , trivialTest07
  , trivialTest08
  , trivialTest09
  , trivialTest10
  , trivialTest13
  ]

------------------------------------------------------------
--  Parser tests to cross-check round-trip testing
------------------------------------------------------------

parseTest :: String -> String -> RDFGraph -> String -> Test
parseTest lab inp gr er =
    TestList
      [ TestCase ( assertEqual ("parseTestError:"++lab) er pe )
      , TestCase ( assertEqual ("parseTestGraph:"++lab) gr pg )
      ]
    where
        (pe,pg) = case parseN3fromString inp of
            Result g -> ("",g)
            Error  s -> (s,emptyRDFGraph)

noError   = ""
errorText = "*"

parseTest01 = parseTest "01" simpleN3Graph_g1_01 g1np noError
parseTest02 = parseTest "02" simpleN3Graph_g1_02 g1   noError
parseTest03 = parseTest "03" simpleN3Graph_g1_03 g1b1 noError
parseTest04 = parseTest "04" simpleN3Graph_g1_04 g1a1 noError
parseTest05 = parseTest "05" simpleN3Graph_g1_05 g1l1 noError
parseTest06 = parseTest "06" simpleN3Graph_g1_06 g1l2 noError
parseTest07 = parseTest "07" simpleN3Graph_g1_07 g1f1 noError
parseTest08 = parseTest "08" simpleN3Graph_g1_08 g1f2 noError

parseTestSuite = TestList
  [ parseTest01
  , parseTest02
  , parseTest03
  , parseTest04
  , parseTest05
  , parseTest06
  , parseTest07
  , parseTest08
  ]

------------------------------------------------------------
--  Repeat above tests using parser and graph-comparison
------------------------------------------------------------
--
--  This establishes a framework that will be used for
--  more complex tests that are less susceptible to trivial
--  formatting differences.  The idea is to generate output
--  that can be parsed to obtain an equivalent graph.

roundTripTest :: String -> RDFGraph -> Test
roundTripTest lab gr =
    TestList
      [ TestCase ( assertEqual ("RoundTrip:gr:"++lab) gr pg )
      , TestCase ( assertEqual ("RoundTrip:er:"++lab) "" pe )
      -- , TestCase ( assertEqual ("Formatted:"++lab) "" out )
      ]
    where
        out     = formatGraphAsString gr
        (pe,pg) = case parseN3fromString out of
            Result g -> ("",g)
            Error  s -> (s,emptyRDFGraph)

--  Full round trip from graph source.  This test may pick up some errors
--  the bnode generation logic that are not tested by hand-assembled graph
--  data structures.
fullRoundTripTest :: String -> String -> Test
fullRoundTripTest lab grstr =
    TestList
      [ TestCase ( assertEqual ("FullRoundTrip:gr:"++lab) gr pg )
      , TestCase ( assertEqual ("FullRoundTrip:er:"++lab) "" pe )
      -- , TestCase ( assertEqual ("FullRoundTrip:"++lab) "" out )
      ]
    where
        (ge,gr) = case parseN3fromString grstr of
            Result g -> ("",g)
            Error  s -> (s,emptyRDFGraph)
        out     = formatGraphAsString gr
        (pe,pg) = case parseN3fromString out of
            Result g -> ("",g)
            Error  s -> (s,emptyRDFGraph)

roundTripTest01 = roundTripTest "01" g1np
roundTripTest02 = roundTripTest "02" g1
roundTripTest03 = roundTripTest "03" g1b1
roundTripTest04 = roundTripTest "04" g1a1
roundTripTest05 = roundTripTest "05" g1l1
roundTripTest06 = roundTripTest "06" g1l2
roundTripTest07 = roundTripTest "07" g1f1
roundTripTest08 = roundTripTest "08" g1f2
roundTripTest11 = fullRoundTripTest "11" simpleN3Graph_g1_01
roundTripTest12 = fullRoundTripTest "12" simpleN3Graph_g1_02
roundTripTest13 = fullRoundTripTest "13" simpleN3Graph_g1_03
roundTripTest14 = fullRoundTripTest "14" simpleN3Graph_g1_04
roundTripTest15 = fullRoundTripTest "15" simpleN3Graph_g1_05
roundTripTest16 = fullRoundTripTest "16" simpleN3Graph_g1_06
roundTripTest17 = fullRoundTripTest "17" simpleN3Graph_g1_07
roundTripTest18 = fullRoundTripTest "18" simpleN3Graph_g1_08

roundTripTestSuite = TestList
  [ roundTripTest01
  , roundTripTest02
  , roundTripTest03
  , roundTripTest04
  , roundTripTest05
  , roundTripTest06
  , roundTripTest07
  , roundTripTest08
  , roundTripTest11
  , roundTripTest12
  , roundTripTest13
  , roundTripTest14
  , roundTripTest15
  , roundTripTest16
  , roundTripTest17
  , roundTripTest18
  ]

------------------------------------------------------------
--  Simple formatter tests
------------------------------------------------------------
--
--  These are simple tests that format and re-parse a graph,
--  and make sure that the result graph compares the same as
--  the original.  Therefore, depends on a trusted parser and
--  graph compare function.

simpleTest :: String -> RDFGraph -> Test
simpleTest lab = roundTripTest ("SimpleTest:"++lab)

simpleTest01 = simpleTest "01" g2
simpleTest02 = simpleTest "02" g3
simpleTest03 = simpleTest "03" g4
simpleTest04 = simpleTest "04" g5
simpleTest05 = simpleTest "05" g6
simpleTest06 = simpleTest "06" g7
simpleTest07 = simpleTest "07" g8
simpleTest08 = simpleTest "08" g81
simpleTest09 = simpleTest "09" g82
simpleTest10 = simpleTest "10" g83
simpleTest11 = simpleTest "11" g9
simpleTest12 = simpleTest "12" g10
simpleTest13 = simpleTest "13" g11

simpleTestSuite = TestList
  [ simpleTest01
  , simpleTest02
  , simpleTest03
  , simpleTest04
  , simpleTest05
  , simpleTest06
  , simpleTest07
  , simpleTest08
  , simpleTest09
  , simpleTest10
  , simpleTest11
  , simpleTest12
  , simpleTest13
  ]

------------------------------------------------------------
--  Exotic parser tests
------------------------------------------------------------
--
--  These tests cover various forms of anonymous nodes
--  [...], lists and formulae. together with uses of ':-'
--

-- does a round-trip test starting with the
exoticTest :: String -> RDFGraph -> Test
exoticTest lab gr =
    TestList
      [ TestCase ( assertEqual ("ExoticTest:gr:"++lab) gr pg )
      , TestCase ( assertEqual ("ExoticTest:er:"++lab) "" pe )
      -- , TestCase ( assertEqual ("ExoticTest:"++lab)    "" out )
      ]
    where
        out     = formatGraphAsString gr
        (pe,pg) = case parseN3fromString out of
            Result g -> ("",g)
            Error  s -> (s,emptyRDFGraph)

--  Simple anon nodes, with semicolons and commas
exoticN3Graph_x1 =
    commonPrefixes ++
    " [ base1:p1 base1:o1 ; \n" ++
    "   base1:p1 base2:o2 ; \n" ++
    "   base2:p2 base2:o2 ; \n" ++
    "   base2:p2 base3:o3 ] = base1:s1 . \n" ++
    " base2:s2 = \n" ++
    " [ base1:p1 base1:o1 , \n" ++
    "   base2:o2 , \n" ++
    "   base3:o3 , \n" ++
    "   \"l1\"   ; \n" ++
    "   base2:p2 base1:o1 , \n" ++
    "            base2:o2 , \n" ++
    "            base3:o3 , \n" ++
    "            \"l1\"   ] . \n"

--  Simple anon nodes, with 'is ... of' and semicolons and commas
exoticN3Graph_x2 =
    commonPrefixes ++
    " [ has base1:p1 of base1:o1 ; \n" ++
    "   is  base1:p1 of base2:o2 ; \n" ++
    "   has base2:p2 of base2:o2 ; \n" ++
    "   is  base2:p2 of base3:o3 ] = base1:s1 . \n" ++
    " base2:s2 = \n" ++
    " [ has base1:p1 of base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 , \n" ++
    "                   \"l1\"   ; \n" ++
    "   is  base2:p2 of base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 ] . \n"
    -- "                   \"l1\"   ] . \n"

--  Simple anon nodes, attached to identified node
exoticN3Graph_x3 =
    commonPrefixes ++
    " base1:s1 :- \n" ++
    " [ has base1:p1 of base1:o1 ; \n" ++
    "   is  base1:p1 of base2:o2 ; \n" ++
    "   has base2:p2 of base2:o2 ; \n" ++
    "   is  base2:p2 of base3:o3 ] . \n" ++
    " base2:s2 :- \n" ++
    " [ has base1:p1 of base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 , \n" ++
    "                   \"l1\"   ; \n" ++
    "   is  base2:p2 of base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 ] . \n"
    -- "                   \"l1\"   ] . \n"

--  List nodes, with and without :-

exoticN3Graph_x4 =
    commonPrefixes ++
    " base1:s1 = (base1:o1 base2:o2 base3:o3 \"l1\") .\n"

exoticN3Graph_x5 =
    commonPrefixes ++
    " (base1:o1 base2:o2 base3:o3 \"l1\") = base1:s1 .\n"

exoticN3Graph_x6 =
    commonPrefixes ++
    " base1:s1 :- (base1:o1 base2:o2 base3:o3 \"l1\") .\n"

--  Formula nodes, with and without :-

exoticN3Graph_x7 =
    commonPrefixes ++
    " { base1:s1 base1:p1 base1:o1 .   \n" ++
    "   base2:s2 base1:p1 base2:o2 .   \n" ++
    "   base3:s3 base1:p1 base3:o3 . } \n" ++
    " base2:p2 base2:f2 . "

exoticN3Graph_x8 =
    commonPrefixes ++
    " base1:f1 :- \n" ++
    " { base1:s1 base1:p1 base1:o1 .     \n" ++
    "   base2:s2 base1:p1 base2:o2 .     \n" ++
    "   base3:s3 base1:p1 base3:o3 . } ; \n" ++
    " base2:p2 base2:f2 . "

exoticN3Graph_x9 =
    commonPrefixes ++
    " base1:f1 :- \n" ++
    " { base1:s1 base1:p1 base1:o1 . } ; \n" ++
    " base2:p2 base2:f2 . "

--  Test allocation of bnodes over a nested formula
exoticN3Graph_x12 =
    commonPrefixes ++
    " base1:s1 base1:p1 [ base1:p1 base1:o1 ] .     \n" ++
    " { base2:s2 base2:p2 [ base2:p2 base2:o2 ] . } \n" ++
    "            base2:p2 base2:f2 .                \n" ++
    " base3:s3 base3:p3 [ base3:p3 base3:o3 ] ."

--  List of bnodes
exoticN3Graph_x13 =
    commonPrefixes ++
    " base1:s1 :- \n" ++
    "  ( [base1:p1 base1:o1] \n" ++
    "    [base1:p1 base2:o2] \n" ++
    "    [base1:p1 base3:o3] ) .\n"

--  List of more complex bnodes
exoticN3Graph_x14 =
    commonPrefixes ++
    " base1:s1 :- \n" ++
    "  ( [base1:p1 base1:o1; base2:p2 base1:o1] \n" ++
    "    [base1:p1 base2:o2; base2:p2 base2:o2] \n" ++
    "    [base1:p1 base3:o3; base2:p2 base3:o3] ) .\n"

--  List with nested list
exoticN3Graph_x15 =
    commonPrefixes ++
    " base1:s1 :- \n" ++
    "  ( [base1:p1 base1:o1] \n"++
    "    [base2:p2 \n" ++
    "       ( [base1:p1 base1:o1] \n" ++
    "         [base1:p1 base2:o2] \n" ++
    "         [base1:p1 base3:o3] ) ] \n"++
    "    [base1:p1 base3:o3] ) .\n"

--  More complex list with nested list
exoticN3Graph_x16 =
    commonPrefixes ++
    " base1:s1 :- \n" ++
    "  ( [base1:p1 base1:o1; base2:p2 base1:o1] \n"++
    "    [base2:p2 \n" ++
    "       ( [base1:p1 base1:o1; base2:p2 base1:o1] \n" ++
    "         [base1:p1 base2:o2; base2:p2 base2:o2] \n" ++
    "         [base1:p1 base3:o3; base2:p2 base3:o3] ) ] \n"++
    "    [base1:p1 base3:o3; base2:p2 base3:o3] ) .\n"

--  Troublesome example
exoticN3Graph_x17 =
    commonPrefixes ++
    "base1:s1 a base1:o1 ; :- \n" ++
    "  ( [ base2:p21 base2:o2  ;  \n" ++
    "      base2:p22 ( [ base2:p23 \"lx11\" ] \"lx12\" ) ] \n" ++
    "    [ base2:p24 base3:o3 ; base2:p25 \"lx13\" ] \n" ++
    "  ) . \n"

--  Null prefixes
exoticN3Graph_x18 =
    commonPrefixes ++
    "@prefix : <#> . " ++
    ":s1 a :o1 ; :- \n" ++
    "  ( [ :p21 :o2  ;  \n" ++
    "      :p22 ( [ :p23 \"lx11\" ] \"lx12\" ) ] \n" ++
    "    [ :p24 :o3 ; :p25 \"lx13\" ] \n" ++
    "  ) . \n"

-- Check graph sources parse to expected values
exoticParseTest01 = parseTest "exoticParseTest01" exoticN3Graph_x1 x1 noError
exoticParseTest02 = parseTest "exoticParseTest02" exoticN3Graph_x2 x2 noError
exoticParseTest03 = parseTest "exoticParseTest03" exoticN3Graph_x3 x3 noError
exoticParseTest04 = parseTest "exoticParseTest04" exoticN3Graph_x4 x4 noError
exoticParseTest05 = parseTest "exoticParseTest05" exoticN3Graph_x5 x5 noError
exoticParseTest06 = parseTest "exoticParseTest06" exoticN3Graph_x6 x6 noError
exoticParseTest07 = parseTest "exoticParseTest07" exoticN3Graph_x7 x7 noError
exoticParseTest08 = parseTest "exoticParseTest08" exoticN3Graph_x8 x8 noError
exoticParseTest09 = parseTest "exoticParseTest09" exoticN3Graph_x9 x9 noError
exoticParseTest12 = parseTest "exoticParseTest12" exoticN3Graph_x12 x12 noError
exoticParseTest13 = parseTest "exoticParseTest13" exoticN3Graph_x13 x13 noError
exoticParseTest13a = parseTest "exoticParseTest13a" exoticN3Graph_x13 x13a noError
exoticParseTest14 = parseTest "exoticParseTest14" exoticN3Graph_x14 x14 noError
exoticParseTest15 = parseTest "exoticParseTest15" exoticN3Graph_x15 x15 noError
exoticParseTest16 = parseTest "exoticParseTest16" exoticN3Graph_x16 x16 noError
exoticParseTest17 = parseTest "exoticParseTest17" exoticN3Graph_x17 x17 noError

exoticTest01 = exoticTest "01" x1
exoticTest02 = exoticTest "02" x2
exoticTest03 = exoticTest "03" x3
exoticTest04 = exoticTest "04" x4
exoticTest05 = exoticTest "05" x5
exoticTest06 = exoticTest "06" x6
exoticTest07 = exoticTest "07" x7
exoticTest08 = exoticTest "08" x8
exoticTest09 = exoticTest "09" x9
exoticTest10 = testGraphEq  "exoticTest10" False x7 x8
exoticTest11 = testGraphEq  "exoticTest11" False x8 x9
exoticTest12 = exoticTest "12" x12
exoticTest13 = exoticTest "13" x13
exoticTest13a = exoticTest "13a" x13a
exoticTest14 = exoticTest "14" x14
exoticTest15 = exoticTest "15" x15
exoticTest16 = exoticTest "16" x16
exoticTest17 = exoticTest "17" x17

exoticRoundTripTest01 = fullRoundTripTest "Exotic01" exoticN3Graph_x1
exoticRoundTripTest02 = fullRoundTripTest "Exotic02" exoticN3Graph_x2
exoticRoundTripTest03 = fullRoundTripTest "Exotic03" exoticN3Graph_x3
exoticRoundTripTest04 = fullRoundTripTest "Exotic04" exoticN3Graph_x4
exoticRoundTripTest05 = fullRoundTripTest "Exotic05" exoticN3Graph_x5
exoticRoundTripTest06 = fullRoundTripTest "Exotic06" exoticN3Graph_x6
exoticRoundTripTest07 = fullRoundTripTest "Exotic07" exoticN3Graph_x7
exoticRoundTripTest08 = fullRoundTripTest "Exotic08" exoticN3Graph_x8
exoticRoundTripTest09 = fullRoundTripTest "Exotic09" exoticN3Graph_x9
exoticRoundTripTest12 = fullRoundTripTest "Exotic12" exoticN3Graph_x12
exoticRoundTripTest13 = fullRoundTripTest "Exotic13" exoticN3Graph_x13
exoticRoundTripTest14 = fullRoundTripTest "Exotic14" exoticN3Graph_x14
exoticRoundTripTest15 = fullRoundTripTest "Exotic15" exoticN3Graph_x15
exoticRoundTripTest16 = fullRoundTripTest "Exotic16" exoticN3Graph_x16
exoticRoundTripTest17 = fullRoundTripTest "Exotic17" exoticN3Graph_x17
exoticRoundTripTest18 = fullRoundTripTest "Exotic18" exoticN3Graph_x18

exoticTestSuite = TestList
  [ exoticParseTest01
  , exoticParseTest02
  , exoticParseTest03
  , exoticParseTest04
  , exoticParseTest05
  , exoticParseTest06
  , exoticParseTest07
  , exoticParseTest08
  , exoticParseTest09
  , exoticParseTest12
  , exoticParseTest13
  , exoticParseTest13a
  , exoticParseTest14
  , exoticParseTest15
  , exoticParseTest16
  , exoticParseTest17
  , exoticTest01
  , exoticTest02
  , exoticTest03
  , exoticTest04
  , exoticTest05
  , exoticTest06
  , exoticTest07
  , exoticTest08
  , exoticTest09
  , exoticTest10
  , exoticTest11
  , exoticTest12
  , exoticTest13
  , exoticTest13a
  , exoticTest14
  , exoticTest15
  , exoticTest16
  , exoticTest17
  , exoticRoundTripTest01
  , exoticRoundTripTest02
  , exoticRoundTripTest03
  , exoticRoundTripTest04
  , exoticRoundTripTest05
  , exoticRoundTripTest06
  , exoticRoundTripTest07
  , exoticRoundTripTest08
  , exoticRoundTripTest09
  , exoticRoundTripTest12
  , exoticRoundTripTest13
  , exoticRoundTripTest14
  , exoticRoundTripTest15
  , exoticRoundTripTest16
  , exoticRoundTripTest17
  , exoticRoundTripTest18
  ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ trivialTestSuite
  , parseTestSuite
  , roundTripTestSuite
  , simpleTestSuite
  , exoticTestSuite
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
-- $Source: /file/cvsdev/HaskellRDF/N3FormatterTest.hs,v $
-- $Author: graham $
-- $Revision: 1.21 $
-- $Log: N3FormatterTest.hs,v $
-- Revision 1.21  2004/01/09 12:57:08  graham
-- Remove space between perfix and ':' in @prefix declaractions,
-- for compatibility with new Notation 3 syntax (and Jena).
--
-- Revision 1.20  2004/01/09 12:44:52  graham
-- Fix up N3Formatter to suppress final statement-terminating '.' in a formula,
-- for compatibility with the current Notation3 syntax.
--
-- Revision 1.19  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.18  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.17  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.16  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.15  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.14  2003/11/24 15:46:04  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.13  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.12  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.11  2003/07/01 14:18:57  graham
-- Allow blank node in predicate position.
-- Add parser and formatter test case for this.
--
-- Revision 1.10  2003/06/25 21:16:52  graham
-- Reworked N3 formatting logic to support proof display.
-- Basic proof display is working.
--
-- Revision 1.9  2003/06/12 00:47:55  graham
-- Allowed variable node (?v) and bare anonymous nodes in N3 parser.
--
-- Revision 1.8  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.7  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.6  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.5  2003/05/23 00:02:42  graham
-- Fixed blank node id generation bug in N3Formatter
--
-- Revision 1.4  2003/05/14 22:39:23  graham
-- Initial formatter tests all run OK.
-- The formatter could still use so,me improvement,
-- but it
-- passes the minimal round-tripping tests.
--
-- Revision 1.3  2003/05/14 19:38:32  graham
-- Simple formatter tests all working with reworked graph and lookup structures.
-- More complex formatter tests still to be coded.
--
-- Revision 1.2  2003/05/07 23:58:09  graham
-- More restructuring.
-- RDFGraphTest runs OK.
-- N3ParserTest needs to be updated to use new structure for formulae.
--
-- Revision 1.1  2003/04/30 12:14:08  graham
-- Add formetter test to CVS
-- Noted problem with RDFGraph structure: preparing to rework
--
--
