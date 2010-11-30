--------------------------------------------------------------------------------
--  $Id: N3ParserTest.hs,v 1.25 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  N3ParserTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This Module contains test cases for module N3Parses.
--
--------------------------------------------------------------------------------

--  WNH RIP OUT module Swish.HaskellRDF.N3ParserTest where

import Swish.HaskellRDF.N3Parser
    ( ParseResult(..)
    , parseN3fromString
    , parseTextFromString, parseAltFromString
    , parseNameFromString, parsePrefixFromString
    , parseAbsURIrefFromString, parseLexURIrefFromString
    , parseURIref2FromString
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFTriple, RDFGraph, RDFLabel(..), NSGraph(..)
    -- LookupNamespace(..), Namespace
    , NamespaceMap, emptyNamespaceMap
    , LookupFormula(..), Formula, FormulaMap, emptyFormulaMap
    , setArcs, getArcs, add, delete, extract, labels
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
    , nullNamespace
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
    , namespaceLang, langName
    , rdf_type
    , rdf_first, rdf_rest, rdf_nil, rdf_XMLLiteral
    , rdfs_member
    , rdfd_GeneralRestriction
    , rdfd_onProperties, rdfd_constraint, rdfd_maxCardinality
    , owl_sameAs
    , operator_plus, operator_minus, operator_slash, operator_star
    )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..)
    , mapFind, mapFindMaybe )

import Swish.HaskellRDF.GraphClass
    ( Arc, arcSubj, arcPred, arcObj, arc )

import Swish.HaskellUtils.QName
    ( QName(..) )

import Swish.HaskellUtils.ErrorM
    ( ErrorM(..) )

import Test.HUnit
    ( Test(TestCase,TestList,TestLabel)
    , assertEqual, runTestTT, runTestText, putTextToHandle )

import System.IO
    ( Handle, IOMode(WriteMode)
    , openFile, hClose, hPutStr, hPutStrLn )

------------------------------------------------------------
--  Common values
------------------------------------------------------------

pref_rdf = nsURI namespaceRDF
pref_op  = nsURI namespaceRDFO
pref_owl = nsURI namespaceOWL

------------------------------------------------------------
--  Generic item parsing test wrapper
------------------------------------------------------------

type ParseFromString a = String -> (Either String a)

parseItemTest :: (Eq a, Show a) => ParseFromString a -> a
                 -> String -> String -> a -> String -> Test
parseItemTest ifroms def lab inp val err =
    TestList
      [ TestCase ( assertEqual ("parseItemError:"++lab) fixerr pe )
      , TestCase ( assertEqual ("parseItemValue:"++lab) val pv )
      ]
    where
        (pe,pv) = case ifroms inp of
            Left  e -> (e,def)
            Right v -> (noError,v)
        fixerr = if err /= noError then pe else noError

noError   = ""
errorText = "*"

------------------------------------------------------------
--  Common test wrappers
------------------------------------------------------------

testLabelEq :: String -> Bool -> RDFLabel -> RDFLabel -> Test
testLabelEq lab eq n1 n2 =
    TestCase ( assertEqual ("testLabelEq:"++lab) eq (n1==n2) )

testGraphEq :: String -> Bool -> RDFGraph -> RDFGraph -> Test
testGraphEq lab eq g1 g2 =
    TestCase ( assertEqual ("testGraphEq:"++lab) eq (g1==g2) )

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

------------------------------------------------------------
--  Test simple character parsing
------------------------------------------------------------

parseCharTest :: String -> String
                 -> String -> String -> String -> Test
parseCharTest c = parseItemTest (parseTextFromString c) ""

parseAltTest :: String -> String
                -> String -> String -> String -> String -> Test
parseAltTest c1 c2 = parseItemTest (parseAltFromString c1 c2) ""

charInp01 = ":"
char01    = ":"

charInp02 = "<>"
char02    = "<>"

charInp03 = "<="

parseCharTest01 = parseCharTest char01
                    "parseCharTest01" charInp01 char01 noError
parseCharTest02 = parseCharTest char02
                    "parseCharTest02" charInp02 char02 noError
parseCharTest03 = parseAltTest char01 char02
                    "parseCharTest03" charInp01 char01 noError
parseCharTest04 = parseAltTest char01 char02
                    "parseCharTest04" charInp02 char02 noError
parseCharTest05 = parseAltTest char01 char02
                    "parseCharTest04" charInp03 "" errorText

charTestSuite = TestList
  [ parseCharTest01
  , parseCharTest02
  , parseCharTest03
  , parseCharTest04
  , parseCharTest05
  ]

------------------------------------------------------------
--  Test simple name parsing
------------------------------------------------------------

parseNameTest :: String -> String -> String -> String -> Test
parseNameTest = parseItemTest parseNameFromString ""

nameInp01 = "name"
name01    = "name"

nameInp02 = "rdf"
name02    = "rdf"

parseNameTest01 = parseNameTest "parseNameTest01" nameInp01 name01 ""
parseNameTest02 = parseNameTest "parseNameTest02" nameInp02 name02 ""

nameTestSuite = TestList
  [ parseNameTest01
  , parseNameTest02
  ]

------------------------------------------------------------
--  Test simple prefix parsing
------------------------------------------------------------

parsePrefixTest :: String -> String -> Namespace -> String -> Test
parsePrefixTest = parseItemTest parsePrefixFromString nullNamespace

prefixInp01 = "pref"
prefix01    = Namespace "pref" "pref:"

prefixInp02 = "rdf"
prefix02    = Namespace "rdf" pref_rdf

parsePrefixTest01 = parsePrefixTest "parsePrefixTest01" prefixInp01 prefix01 ""
parsePrefixTest02 = parsePrefixTest "parsePrefixTest02" prefixInp02 prefix02 ""

prefixTestSuite = TestList
  [ parsePrefixTest01
  , parsePrefixTest02
  ]

------------------------------------------------------------
--  Test absolute URIref parsing
------------------------------------------------------------

parseAbsUriRefTest :: String -> String -> String -> String -> Test
parseAbsUriRefTest = parseItemTest parseAbsURIrefFromString ""

parseLexUriRefTest :: String -> String -> String -> String -> Test
parseLexUriRefTest = parseItemTest parseLexURIrefFromString ""

absUriRefInp01  = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
absUriRefInp01s = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
absUriRef01     = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

absUriRefInp02  = "<http://id.ninebynine.org/wip/2003/test/graph1/node#s1>"
absUriRefInp02s = "<http://id.ninebynine.org/wip/2003/test/graph1/node#s1> "
absUriRef02     = "http://id.ninebynine.org/wip/2003/test/graph1/node#s1"

parseAbsUriRefTest01 = parseAbsUriRefTest "parseAbsUriRefTest01" absUriRefInp01 absUriRef01 ""
parseAbsUriRefTest02 = parseAbsUriRefTest "parseAbsUriRefTest02" absUriRefInp02 absUriRef02 ""
parseAbsUriRefTest03 = parseLexUriRefTest "parseAbsUriRefTest03" absUriRefInp01s absUriRef01 ""
parseAbsUriRefTest04 = parseLexUriRefTest "parseAbsUriRefTest04" absUriRefInp02s absUriRef02 ""

absUriRefTestSuite = TestList
  [ parseAbsUriRefTest01
  , parseAbsUriRefTest02
  , parseAbsUriRefTest03
  , parseAbsUriRefTest04
  ]


------------------------------------------------------------
--  Test simple URIref parsing
------------------------------------------------------------

parseUriRef2Test :: String -> String -> ScopedName -> String -> Test
parseUriRef2Test = parseItemTest parseURIref2FromString nullScopedName

uriRef01 = "rdf:type "
sname01  = ScopedName namespaceRDF "type"

uriRef02 = "<http://id.ninebynine.org/wip/2003/test/graph1/node#s1> "
sname02  =
    makeScopedName "" "http://id.ninebynine.org/wip/2003/test/graph1/node#" "s1"

parseUriRef2Test01 = parseUriRef2Test "parseUriRef2Test01" uriRef01 sname01 ""
parseUriRef2Test02 = parseUriRef2Test "parseUriRef2Test02" uriRef02 sname02 ""

uriRef2TestSuite = TestList
  [ parseUriRef2Test01
  , parseUriRef2Test02
  ]

------------------------------------------------------------
--  Define some common values
------------------------------------------------------------

base1 = Namespace "base1" "http://id.ninebynine.org/wip/2003/test/graph1/node/"
base2 = Namespace "base2" "http://id.ninebynine.org/wip/2003/test/graph2/node#"
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

qb1p1 = ScopedName base1 "p1"
qb2p2 = ScopedName base2 "p2"
qb3p3 = ScopedName base3 "p3"

p1 = Res qb1p1  :: RDFLabel
p2 = Res qb2p2  :: RDFLabel
p3 = Res qb3p3  :: RDFLabel

qb1o1 = ScopedName base1 "o1"
qb2o2 = ScopedName base2 "o2"
qb3o3 = ScopedName base3 "o3"

o1 = Res qb1o1  :: RDFLabel
o2 = Res qb2o2  :: RDFLabel
o3 = Res qb3o3  :: RDFLabel

l1 = Lit "l1"  Nothing :: RDFLabel
l2 = Lit "l2-'\"line1\"'\n\nl2-'\"\"line2\"\"'" Nothing :: RDFLabel
l3 = Lit "l3--\r\"'\\--\x0020\&--\x00A0\&--" Nothing    :: RDFLabel

lfr    = Lit "chat"          (Just $ langName "fr")     :: RDFLabel
lxml   = Lit "<br/>"         (Just rdf_XMLLiteral )     :: RDFLabel
lfrxml = Lit "<em>chat</em>" (Just rdf_XMLLiteral )     :: RDFLabel -- was: lang "fr"

qb1f1 = ScopedName base1 "f1"
qb2f2 = ScopedName base2 "f2"

f1 = Res qb1f1  :: RDFLabel
f2 = Res qb2f2  :: RDFLabel

v1 = Var "var1" :: RDFLabel
v2 = Var "var2" :: RDFLabel
v3 = Var "var3" :: RDFLabel
v4 = Var "var4" :: RDFLabel

------------------------------------------------------------
--  Construct graphs for testing
------------------------------------------------------------

t01  = arc s1 p1 o1
t01b = arc b1 b2 b3
t02  = arc s2 p1 o2
t03  = arc s3 p1 o3
t04  = arc s1 p1 l1
t05  = arc s2 p1 b1
t06  = arc s3 p1 l2
t07  = arc s3 p2 l3

makeNewPrefixNamespace :: (String,Namespace) -> Namespace
makeNewPrefixNamespace (pre,ns) = Namespace pre (nsURI ns)

nslist = LookupMap $ map makeNewPrefixNamespace
    [ ("base1",base1)
    , ("base2",base2)
    , ("base3",base3)
    , ("base4",base4)
    ]

g1 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01]
        }

g1b = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t01b]
        }

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
t1028 = arc l1 p2 s2

g10 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1011,t1012,t1013,t1014,
                        t1021,t1022,t1023,t1024,
                        t1025,t1026,t1027,t1028]
        }

t1111 = arc s1 p1 v1
t1112 = arc v2 p1 o1
t1113 = arc v3 p1 v4

g11 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1111,t1112,t1113]
        }

t1211 = arc b1 p1 o1
t1221 = arc b2 res_rdf_first v1
t1222 = arc b2 res_rdf_rest  b3
t1223 = arc b3 res_rdf_first v2
t1224 = arc b3 res_rdf_rest  res_rdf_nil

g12 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1211,t1221,t1222,t1223,t1224]
        }

t1711 = arc s1 p1 lfr
t1722 = arc s2 p2 lxml
t1733 = arc s3 p3 lfrxml

g17 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [t1711,t1722,t1733]
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
tx228 = arc l1 p2 b2

x2 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx201,tx202,
                        tx211,tx212,tx213,tx214,
                        tx221,tx222,tx223,tx224,
                        tx225,tx226,tx227,tx228]
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
tx328 = arc l1 p2 s2

x3 = NSGraph
        { namespaces = nslist
        , formulae   = emptyFormulaMap
        , statements = [tx311,tx312,tx313,tx314,
                        tx321,tx322,tx323,tx324,
                        tx325,tx326,tx327,tx328]
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

tx701 = arc b1 p2 f2
x7f   = LookupMap [Formula b1 g2]
x7    = NSGraph
        { namespaces = nslist
        , formulae   = x7f
        , statements = [tx701]
        }

tx801 = arc f1 p2 f2
x8f   = LookupMap [Formula f1 g2]
x8    = NSGraph
        { namespaces = nslist
        , formulae   = x8f
        , statements = [tx801]
        }

tx901 = tx801
x9f   = LookupMap [Formula f1 g1]
x9    = NSGraph
        { namespaces = nslist
        , formulae   = x9f
        , statements = [tx901]
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

------------------------------------------------------------
--  Simple parser tests
------------------------------------------------------------

commonPrefixes =
    "@prefix base1 : <" ++ nsURI base1 ++ "> . \n" ++
    "@prefix base2 : <" ++ nsURI base2 ++ "> . \n" ++
    "@prefix base3 : <" ++ nsURI base3 ++ "> . \n"

--  Single statement using <uri> form
simpleN3Graph_g1_01 =
    " <http://id.ninebynine.org/wip/2003/test/graph1/node/s1> " ++
    " <http://id.ninebynine.org/wip/2003/test/graph1/node/p1> " ++
    " <http://id.ninebynine.org/wip/2003/test/graph1/node/o1> . "

--  Single statement using prefix:name form
simpleN3Graph_g1_02 =
    "@prefix base1 : <" ++ nsURI base1 ++ "> ." ++
    " base1:s1 base1:p1 base1:o1 . "

--  Single statement using :name form
simpleN3Graph_g1_03 =
    "@prefix : <" ++ nsURI base1 ++ "> .\n" ++
    " :s1 :p1 :o1 . "

--  Single statement using relative URI form
simpleN3Graph_g1_04 =
    "@base <" ++ nsURI base1 ++ "> .\n" ++
    " <s1> <p1> <o1> . "

--  Single statement using blank nodes
simpleN3Graph_g1_05 =
    "@base <" ++ nsURI base1 ++ "> .\n" ++
    " _:b1 _:b2 _:b3 . "

--  Single statement with junk following
simpleN3Graph_g1_06 =
    "@prefix base1 : <" ++ nsURI base1 ++ "> ." ++
    " base1:s1 base1:p1 base1:o1 . " ++
    " **** "

--  Multiple statements
simpleN3Graph_g2 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base2:s2 base1:p1 base2:o2 . \n" ++
    " base3:s3 base1:p1 base3:o3 . \n"

--  Graph with literal
simpleN3Graph_g3 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base1:s1 base1:p1 \"l1\" . \n"

--  Graph with nodeid
simpleN3Graph_g4 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base2:s2 base1:p1 _:b1 . \n"

--  Graph with literal and nodeid
simpleN3Graph_g5 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base2:s2 base1:p1 base2:o2 . \n" ++
    " base3:s3 base1:p1 base3:o3 . \n" ++
    " base1:s1 base1:p1 \"l1\" . \n"   ++
    " base2:s2 base1:p1 _:b1 . \n"

--  Triple-quoted literal
simpleN3Graph_g6 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base3:s3 base1:p1 \"\"\"l2-'\"line1\"'\n\nl2-'\"\"line2\"\"'\"\"\" . \n"

--  String escapes
simpleN3Graph_g7 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 . \n" ++
    " base3:s3 base2:p2 " ++
    " \"l3--\\r\\\"\\'\\\\--\\u0020--\\U000000A0--\" " ++
    " . \n"

--  Different verb forms
simpleN3Graph_g8 =
    commonPrefixes ++
    " base1:s1 a base1:o1 . \n" ++
    " base2:s2 = base2:o2 . \n" ++
    " base3:s3 + base3:o3 . \n" ++
    " base3:s3 - base3:o3 . \n" ++
    " base3:s3 * base3:o3 . \n" ++
    " base3:s3 / base3:o3 . \n" ++
    " base1:s1 is  base1:p1 of base1:o1 . \n" ++
    " base2:s2 has base1:p1 of base2:o2 . \n" ++
    " base1:s1 >-  base2:p2 -> base1:o1 . \n" ++
    " base2:s2 <-  base2:p2 <- base2:o2 . \n"

simpleN3Graph_g81 =
    commonPrefixes ++
    " base1:s1 a base1:o1 . \n" ++
    " base2:s2 = base2:o2 . \n"

simpleN3Graph_g82 =
    commonPrefixes ++
    " base3:s3 + base3:o3 . \n" ++
    " base3:s3 - base3:o3 . \n" ++
    " base3:s3 * base3:o3 . \n" ++
    " base3:s3 / base3:o3 . \n"

simpleN3Graph_g83 =
    commonPrefixes ++
    " base1:s1 is  base1:p1 of base1:o1 . \n" ++
    " base2:s2 has base1:p1 of base2:o2 . \n" ++
    " base1:s1 >-  base2:p2 -> base1:o1 . \n" ++
    " base2:s2 <-  base2:p2 <- base2:o2 . \n"

--  Semicolons and commas
simpleN3Graph_g9 =
    commonPrefixes ++
    " base1:s1 base1:p1 base1:o1 ; \n" ++
    "          base1:p1 base2:o2 ; \n" ++
    "          base2:p2 base2:o2 ; \n" ++
    "          base2:p2 base3:o3 . \n" ++
    " base2:s2 base1:p1 base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 , \n" ++
    "                   \"l1\"   ; \n" ++
    "          base2:p2 base1:o1 , \n" ++
    "                   base2:o2 , \n" ++
    "                   base3:o3 , \n" ++
    "                   \"l1\"   . \n"

--  'is ... of' and semicolons and commas
simpleN3Graph_g10 =
    commonPrefixes ++
    " base1:s1 has base1:p1 of base1:o1 ; \n" ++
    "          is  base1:p1 of base2:o2 ; \n" ++
    "          has base2:p2 of base2:o2 ; \n" ++
    "          is  base2:p2 of base3:o3 . \n" ++
    " base2:s2 has base1:p1 of base1:o1 , \n" ++
    "                          base2:o2 , \n" ++
    "                          base3:o3 , \n" ++
    "                          \"l1\"   ; \n" ++
    "          is  base2:p2 of base1:o1 , \n" ++
    "                          base2:o2 , \n" ++
    "                          base3:o3 , \n" ++
    "                          \"l1\"   . \n"

--  Simple statements using ?var form
simpleN3Graph_g11 =
    "@prefix base1 : <" ++ nsURI base1 ++ "> . \n" ++
    " base1:s1 base1:p1 ?var1 . \n"          ++
    " ?var2 base1:p1 base1:o1 . \n"          ++
    " ?var3 base1:p1 ?var4 .    \n"

--  Bare anonymous nodes
simpleN3Graph_g12 =
    "@prefix base1 : <" ++ nsURI base1 ++ "> . \n" ++
    " [ base1:p1 base1:o1 ] .  \n"          ++
    " ( ?var1 ?var2 ) .    \n"

--  Literals with dataype and language
simpleN3Graph_g17 =
    commonPrefixes ++
    " base1:s1 base1:p1 \"chat\"@fr . \n "                          ++
    " base2:s2 base2:p2 \"<br/>\"^^rdf:XMLLiteral . \n "            ++
    " base3:s3 base3:p3 \"<em>chat</em>\"^^rdf:XMLLiteral . \n "

simpleTest011 = parseTest "simpleTest011" simpleN3Graph_g1_01 g1  noError
simpleTest012 = parseTest "simpleTest012" simpleN3Graph_g1_02 g1  noError
simpleTest013 = parseTest "simpleTest013" simpleN3Graph_g1_03 g1  noError
simpleTest014 = parseTest "simpleTest014" simpleN3Graph_g1_04 g1  noError
simpleTest015 = parseTest "simpleTest015" simpleN3Graph_g1_05 g1b noError
simpleTest016 = parseTest "simpleTest016" simpleN3Graph_g1_06 emptyRDFGraph
                ( "(line 1, column 103):\n"++
                  "unexpected \"*\"\n"++
                  "expecting URI or blank node or end of input" )
simpleTest03  = parseTest "simpleTest03"  simpleN3Graph_g2    g2  noError
simpleTest04  = parseTest "simpleTest04"  simpleN3Graph_g3    g3  noError
simpleTest05  = parseTest "simpleTest05"  simpleN3Graph_g4    g4  noError
simpleTest06  = parseTest "simpleTest06"  simpleN3Graph_g5    g5  noError
simpleTest07  = parseTest "simpleTest07"  simpleN3Graph_g6    g6  noError
simpleTest08  = parseTest "simpleTest08"  simpleN3Graph_g7    g7  noError
simpleTest09  = parseTest "simpleTest09"  simpleN3Graph_g8    g8  noError
simpleTest10  = parseTest "simpleTest10"  simpleN3Graph_g81   g81 noError
simpleTest11  = parseTest "simpleTest11"  simpleN3Graph_g82   g82 noError
simpleTest12  = parseTest "simpleTest12"  simpleN3Graph_g83   g83 noError
simpleTest13  = parseTest "simpleTest13"  simpleN3Graph_g9    g9  noError
simpleTest14  = parseTest "simpleTest14"  simpleN3Graph_g10   g10 noError
simpleTest15  = parseTest "simpleTest15"  simpleN3Graph_g11   g11 noError
simpleTest16  = parseTest "simpleTest16"  simpleN3Graph_g12   g12 noError
simpleTest17  = parseTest "simpleTest17"  simpleN3Graph_g17   g17 noError

simpleTestSuite = TestList
  [ simpleTest011
  , simpleTest012
  , simpleTest013
  , simpleTest014
  , simpleTest015
  , simpleTest016
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
  , simpleTest14
  , simpleTest15
  , simpleTest16
  , simpleTest17
  ]

------------------------------------------------------------
--  Exotic parser tests
------------------------------------------------------------
--
--  These tests cover various forms of anonymous nodes
--  [...], lists and formula. together with uses of ':-'
--

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
    "                   base3:o3 , \n" ++
    "                   \"l1\"   ] . \n"


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
    "                   base3:o3 , \n" ++
    "                   \"l1\"   ] . \n"


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
    "   { base1:s1 base1:p1 base1:o1 } ; \n" ++
    "   base2:p2 base2:f2 "
    -- (also omits final periods)

exoticN3Graph_x8a =
    commonPrefixes ++
    " base1:f1 :- \n" ++
    " { base1:s1 base1:p1 base1:o1 .     \n" ++
    "   base2:s2 base1:p1 base2:o2 .     \n" ++
    "   base3:s3 base1:p1 base3:o3 . } . \n" ++
    " base1:f1 base2:p2 base2:f2 . "

exoticN3Graph_x9a =
    commonPrefixes ++
    " base1:f1 :- \n" ++
    " { base1:s1 base1:p1 base1:o1 . } . \n" ++
    " base1:f1 base2:p2 base2:f2 . "

--  Test allocation of bnodes carries over a nested formula
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

exoticTest01 = parseTest "exoticTest01" exoticN3Graph_x1  x1  noError
exoticTest02 = parseTest "exoticTest02" exoticN3Graph_x2  x2  noError
exoticTest03 = parseTest "exoticTest03" exoticN3Graph_x3  x3  noError
exoticTest04 = parseTest "exoticTest04" exoticN3Graph_x4  x4  noError
exoticTest05 = parseTest "exoticTest05" exoticN3Graph_x5  x5  noError
exoticTest06 = parseTest "exoticTest06" exoticN3Graph_x6  x6  noError
exoticTest07 = parseTest "exoticTest07" exoticN3Graph_x7  x7  noError
exoticTest08 = parseTest "exoticTest08" exoticN3Graph_x8  x8  noError
exoticTest09 = parseTest "exoticTest09" exoticN3Graph_x9  x9  noError
exoticTest10 = parseTest "exoticTest10" exoticN3Graph_x8a x8  noError
exoticTest11 = parseTest "exoticTest11" exoticN3Graph_x9a x9  noError
exoticTest12 = parseTest "exoticTest12" exoticN3Graph_x12 x12 noError
exoticTest13 = parseTest "exoticTest13" exoticN3Graph_x13 x13 noError
exoticTest14 = parseTest "exoticTest14" exoticN3Graph_x14 x14 noError
exoticTest15 = parseTest "exoticTest15" exoticN3Graph_x15 x15 noError
exoticTest16 = parseTest "exoticTest16" exoticN3Graph_x16 x16 noError
exoticTest20 = testGraphEq "exoticTest20" False x7 x8
exoticTest21 = testGraphEq "exoticTest21" False x8 x9

exoticTestSuite = TestList
  [ exoticTest01
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
  , exoticTest14
  , exoticTest15
  , exoticTest16
  , exoticTest20
  , exoticTest21
  ]

------------------------------------------------------------
--  All tests
------------------------------------------------------------

allTests = TestList
  [ charTestSuite
  , nameTestSuite
  , prefixTestSuite
  , absUriRefTestSuite
  , uriRef2TestSuite
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
-- $Source: /file/cvsdev/HaskellRDF/N3ParserTest.hs,v $
-- $Author: graham $
-- $Revision: 1.25 $
-- $Log: N3ParserTest.hs,v $
-- Revision 1.25  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.24  2004/01/09 11:23:54  graham
-- Fix up N3Parser so that the final statement-terminating '.' in a formula
-- or file is optional.
--
-- Revision 1.23  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.22  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.21  2003/12/03 17:07:23  graham
-- Replace occurrences of QName in N3Parser with ScopedName.
--
-- Revision 1.20  2003/12/03 15:42:09  graham
-- Eliminate special return type in favour of ErrorM
--
-- Revision 1.19  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.18  2003/11/24 15:46:04  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.17  2003/10/09 16:26:31  graham
-- Added parser support for literal language tags and datatypes.
-- (Language tags are names, not strictly per RFC3066)
--
-- Revision 1.16  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.15  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.14  2003/07/01 14:18:57  graham
-- Allow blank node in predicate position.
-- Add parser and formatter test case for this.
--
-- Revision 1.13  2003/06/12 00:47:56  graham
-- Allowed variable node (?v) and bare anonymous nodes in N3 parser.
--
-- Revision 1.12  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.11  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.10  2003/05/23 00:02:42  graham
-- Fixed blank node id generation bug in N3Formatter
--
-- Revision 1.9  2003/05/22 15:16:39  graham
-- Added additional parser test cases for lists
--
-- Revision 1.8  2003/05/21 13:55:13  graham
-- N3 parser now handles relative URIs and default prefixes.
-- (Still need to figure better default base URI handling; i.e. current document)
--
-- Revision 1.7  2003/05/21 13:34:13  graham
-- Various N3 parser bug fixes.
-- Need to fix handling of :name terms.
--
-- Revision 1.6  2003/05/14 16:50:32  graham
-- Graph matching seems solid now:
-- RDFGraphTest and N3ParserTest pass all tests
-- Updated TODO file with comments from code
--
-- Revision 1.5  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.4  2003/05/07 23:58:09  graham
-- More restructuring.
-- RDFGraphTest runs OK.
-- N3ParserTest needs to be updated to use new structure for formulae.
--
-- Revision 1.3  2003/04/30 12:14:08  graham
-- Add formetter test to CVS
-- Noted problem with RDFGraph structure: preparing to rework
--
-- Revision 1.2  2003/04/17 12:28:05  graham
-- Formula parsing seems OK.
-- There remains a question about how to represent
-- and compare graphs containing formulae.
--
-- Revision 1.1  2003/04/17 00:35:38  graham
-- Added module N3ParserTest
-- N3parser is mostly working
-- Formulae remain to test
--
