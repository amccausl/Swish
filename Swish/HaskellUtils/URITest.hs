--------------------------------------------------------------------------------
--  $Id: URITest.hs,v 1.2 2004/01/22 19:52:27 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  URITest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + multi-parameter classes
--
-- This Module contains test cases for module URI.
--
--------------------------------------------------------------------------------

-- WNH RIP OUT module Swish.HaskellUtils.URITest where

import Test.HUnit
import Swish.HaskellUtils.Parse
import Swish.HaskellUtils.ProcessURI
import System.IO ( Handle, openFile, IOMode(WriteMode), hClose, hPutStr, hPutStrLn )

-- Test supplied string for valid URI reference syntax
--   isValidURIRef :: String -> Bool
-- Test supplied string for valid absolute URI reference syntax
--   isAbsoluteURIRef :: String -> Bool
-- Test supplied string for valid absolute URI syntax
--   isAbsoluteURI :: String -> Bool

data URIType = AbsId    -- URI form (absolute, no fragment)
             | AbsRf    -- Absolute URI reference
             | RelRf    -- Relative URI reference
             | InvRf    -- Invalid URI reference
isValidT :: URIType -> Bool
isValidT InvRf = False
isValidT _     = True

isAbsRfT :: URIType -> Bool
isAbsRfT AbsId = True
isAbsRfT AbsRf = True
isAbsRfT _     = False

isAbsIdT :: URIType -> Bool
isAbsIdT AbsId = True
isAbsIdT _     = False

testURIRef :: URIType -> String -> Test
testURIRef t u = TestList
  [
    TestCase ( assertEqual ("testValidURIRef:"++u)    (isValidT t) (isValidURIRef    u) ),
    TestCase ( assertEqual ("testAbsoluteURIRef:"++u) (isAbsRfT t) (isAbsoluteURIRef u) ),
    TestCase ( assertEqual ("testAbsoluteURI:"++u)    (isAbsIdT t) (isAbsoluteURI    u) )
  ]

testURIRef001 = testURIRef AbsRf "http://example.org/aaa/bbb#ccc"
testURIRef002 = testURIRef AbsId "mailto:local@domain.org"
testURIRef003 = testURIRef AbsRf "mailto:local@domain.org#frag"
testURIRef004 = testURIRef AbsRf "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
testURIRef005 = testURIRef RelRf "//example.org/aaa/bbb#ccc"
testURIRef006 = testURIRef RelRf "/aaa/bbb#ccc"
testURIRef007 = testURIRef RelRf "bbb#ccc"
testURIRef008 = testURIRef RelRf "#ccc"
testURIRef009 = testURIRef RelRf "#"
testURIRef010 = testURIRef RelRf "/"
-- escapes
testURIRef011 = testURIRef AbsRf "http://example.org/aaa%2fbbb#ccc"
testURIRef012 = testURIRef AbsRf "http://example.org/aaa%2Fbbb#ccc"
testURIRef013 = testURIRef RelRf "%2F"
testURIRef014 = testURIRef RelRf "aaa%2Fbbb"
-- ports
testURIRef015 = testURIRef AbsRf "http://example.org:80/aaa/bbb#ccc"
testURIRef016 = testURIRef AbsRf "http://example.org:/aaa/bbb#ccc"
testURIRef017 = testURIRef AbsRf "http://example.org./aaa/bbb#ccc"
testURIRef018 = testURIRef InvRf "http://example.123./aaa/bbb#ccc"
-- IPv6 literals (from RFC2732):
testURIRef021 = testURIRef AbsId "http://[FEDC:BA98:7654:3210:FEDC:BA98:7654:3210]:80/index.html"
testURIRef022 = testURIRef AbsId "http://[1080:0:0:0:8:800:200C:417A]/index.html"
testURIRef023 = testURIRef AbsId "http://[3ffe:2a00:100:7031::1]"
testURIRef024 = testURIRef AbsId "http://[1080::8:800:200C:417A]/foo"
testURIRef025 = testURIRef AbsId "http://[::192.9.5.5]/ipng"
testURIRef026 = testURIRef AbsId "http://[::FFFF:129.144.52.38]:80/index.html"
testURIRef027 = testURIRef AbsId "http://[2010:836B:4179::836B:4179]"
testURIRef028 = testURIRef RelRf "//[2010:836B:4179::836B:4179]"
testURIRef029 = testURIRef InvRf "[2010:836B:4179::836B:4179]"
-- RFC2396 test cases
testURIRef031 = testURIRef RelRf "./aaa"
testURIRef032 = testURIRef RelRf "../aaa"
testURIRef033 = testURIRef AbsId "g:h"
testURIRef034 = testURIRef RelRf "g"
testURIRef035 = testURIRef RelRf "./g"
testURIRef036 = testURIRef RelRf "g/"
testURIRef037 = testURIRef RelRf "/g"
testURIRef038 = testURIRef RelRf "//g"
testURIRef039 = testURIRef RelRf "?y"
testURIRef040 = testURIRef RelRf "g?y"
testURIRef041 = testURIRef RelRf "#s"
testURIRef042 = testURIRef RelRf "g#s"
testURIRef043 = testURIRef RelRf "g?y#s"
testURIRef044 = testURIRef RelRf ";x"
testURIRef045 = testURIRef RelRf "g;x"
testURIRef046 = testURIRef RelRf "g;x?y#s"
testURIRef047 = testURIRef RelRf "."
testURIRef048 = testURIRef RelRf "./"
testURIRef049 = testURIRef RelRf ".."
testURIRef050 = testURIRef RelRf "../"
testURIRef051 = testURIRef RelRf "../g"
testURIRef052 = testURIRef RelRf "../.."
testURIRef053 = testURIRef RelRf "../../"
testURIRef054 = testURIRef RelRf "../../g"
testURIRef055 = testURIRef RelRf "../../../g"
testURIRef056 = testURIRef RelRf "../../../../g"
testURIRef057 = testURIRef RelRf "/./g"
testURIRef058 = testURIRef RelRf "/../g"
testURIRef059 = testURIRef RelRf "g."
testURIRef060 = testURIRef RelRf ".g"
testURIRef061 = testURIRef RelRf "g.."
testURIRef062 = testURIRef RelRf "..g"
testURIRef063 = testURIRef RelRf "./../g"
testURIRef064 = testURIRef RelRf "./g/."
testURIRef065 = testURIRef RelRf "g/./h"
testURIRef066 = testURIRef RelRf "g/../h"
testURIRef067 = testURIRef RelRf "g;x=1/./y"
testURIRef068 = testURIRef RelRf "g;x=1/../y"
testURIRef069 = testURIRef RelRf "g?y/./x"
testURIRef070 = testURIRef RelRf "g?y/../x"
testURIRef071 = testURIRef RelRf "g#s/./x"
testURIRef072 = testURIRef RelRf "g#s/../x"
-- Invalid
testURIRef081 = testURIRef RelRf ""
testURIRef082 = testURIRef InvRf " "
testURIRef083 = testURIRef InvRf "%"
testURIRef084 = testURIRef InvRf "A%Z"
testURIRef085 = testURIRef InvRf "%ZZ"
testURIRef086 = testURIRef InvRf "%AZ"
testURIRef087 = testURIRef InvRf "A C"
testURIRef088 = testURIRef InvRf "A\"C"
testURIRef089 = testURIRef RelRf "A'C"
testURIRef090 = testURIRef InvRf "A\"C"
testURIRef091 = testURIRef InvRf "A`C"
testURIRef092 = testURIRef InvRf "A<C"
testURIRef093 = testURIRef InvRf "A>C"
testURIRef094 = testURIRef InvRf "A^C"
testURIRef095 = testURIRef InvRf "A\\C"
testURIRef096 = testURIRef InvRf "A{C"
testURIRef097 = testURIRef InvRf "A|C"
testURIRef098 = testURIRef InvRf "A}C"
-- From RFC2396:
-- rel_segment   = 1*( unreserved | escaped |
--                     ";" | "@" | "&" | "=" | "+" | "$" | "," )
-- unreserved    = alphanum | mark
-- mark          = "-" | "_" | "." | "!" | "~" | "*" | "'" |
--                 "(" | ")"
-- Note RFC 2732 allows '[', ']' ONLY for reserved purpose of IPv6 literals,
-- or does it?
testURIRef101 = testURIRef InvRf "A[C"
testURIRef102 = testURIRef InvRf "A]C"
testURIRef103 = testURIRef InvRf "A[**]C"
testURIRef104 = testURIRef InvRf "http://[xyz]/"
testURIRef105 = testURIRef InvRf "http://]/"
testURIRef106 = testURIRef InvRf "http://example.org/[2010:836B:4179::836B:4179]"
testURIRef107 = testURIRef InvRf "http://example.org/abc#[2010:836B:4179::836B:4179]"
testURIRef108 = testURIRef InvRf "http://example.org/xxx/[qwerty]#a[b]"
-- Random other things that crop up
testURIRef111 = testURIRef AbsRf "http://example/Andr&#567;"

testURIRefSuite = TestLabel "Test URIrefs" testURIRefList
testURIRefList = TestList
  [
    testURIRef001, testURIRef002, testURIRef003, testURIRef004,
    testURIRef005, testURIRef006, testURIRef007, testURIRef008,
    testURIRef009, testURIRef010,
    --
    testURIRef011, testURIRef012, testURIRef013, testURIRef014,
    testURIRef015, testURIRef016, testURIRef017, testURIRef018,
    --
    testURIRef021, testURIRef022, testURIRef023, testURIRef024,
    testURIRef025, testURIRef026, testURIRef027, testURIRef028,
    testURIRef029,
    --
    testURIRef031, testURIRef032, testURIRef033, testURIRef034,
    testURIRef035, testURIRef036, testURIRef037, testURIRef038,
    testURIRef039,
    testURIRef040, testURIRef041, testURIRef042, testURIRef043,
    testURIRef044, testURIRef045, testURIRef046, testURIRef047,
    testURIRef048, testURIRef049,
    testURIRef050, testURIRef051, testURIRef052, testURIRef053,
    testURIRef054, testURIRef055, testURIRef056, testURIRef057,
    testURIRef058, testURIRef059,
    testURIRef060, testURIRef061, testURIRef062, testURIRef063,
    testURIRef064, testURIRef065, testURIRef066, testURIRef067,
    testURIRef068, testURIRef069,
    testURIRef070, testURIRef071, testURIRef072,
    --
    testURIRef081, testURIRef082, testURIRef083, testURIRef084,
    testURIRef085, testURIRef086, testURIRef087, testURIRef088,
    testURIRef089,
    testURIRef090, testURIRef091, testURIRef092, testURIRef093,
    testURIRef094, testURIRef095, testURIRef096, testURIRef097,
    testURIRef098, -- testURIRef099,
    --
    testURIRef101, testURIRef102, testURIRef103, testURIRef104,
    testURIRef105, testURIRef106, testURIRef107, testURIRef108,
    --
    testURIRef111
  ]

-- Parser tests:  these are fairtly cursory, as the validating tests above
-- are assumed to be conducted using the parser logic.

testParser :: ( Show a, Show b, Eq a, Eq b ) =>
              String -> Parser a b -> [a] -> [(b,[a])] -> Test
testParser label parser input result =
    TestCase ( assertEqual label result ( parser input ) )

noResult :: [ ( String,[Char] ) ]
noResult = []

-- URI parser (see Parse module)
--   parseURIRef :: Parser Char String

testParseRef01 = testParser "testParseRef01" parseURIRef "http://example.org/aaa/bbb#ccc"
                    [("http://example.org/aaa/bbb#ccc","")]
testParseRef02 = testParser "testParseRef02" parseURIRef "mailto:local@domain.org ****"
                    [("mailto:local@domain.org"," ****")]
testParseRef03 = testParser "testParseRef03" parseURIRef "mailto:local@domain.org#frag|****"
                    [("mailto:local@domain.org#frag","|****")]
testParseRef04 = testParser "testParseRef04" parseURIRef "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
                    [("HTTP://EXAMPLE.ORG/AAA/BBB#CCC","")]
testParseRef05 = testParser "testParseRef05" parseURIRef "//example.org/aaa/bbb#ccc"
                    [("//example.org/aaa/bbb#ccc","")]
testParseRef06 = testParser "testParseRef06" parseURIRef "/aaa/bbb#ccc"
                    [("/aaa/bbb#ccc","")]
testParseRef07 = testParser "testParseRef07" parseURIRef "bbb#c%aac"    [("bbb#c%aac","")]
testParseRef08 = testParser "testParseRef08" parseURIRef "#ccc"       [("#ccc","")]
testParseRef09 = testParser "testParseRef09" parseURIRef "#"          [("#","")]
testParseRef10 = testParser "testParseRef10" parseURIRef "/"          [("/","")]
testParseRef11 = testParser "testParseRef11" parseURIRef "A^C"        [("A","^C")]
testParseRef12 = testParser "testParseRef12" parseURIRef "bbb#ccc%z"  [("bbb#ccc","%z")]
testParseRef13 = testParser "testParseRef13" parseURIRef "bbb?ccc"    [("bbb?ccc","")]
testParseRef14 = testParser "testParseRef14" parseURIRef "?ccc"       [("?ccc","")]

testParseRefSuite = TestLabel "Test parseURIRef" testParseRefList
testParseRefList  = TestList
  [
    testParseRef01, testParseRef02, testParseRef03, testParseRef04,
    testParseRef05, testParseRef06, testParseRef07, testParseRef08,
    testParseRef09,
    testParseRef10, testParseRef11, testParseRef12, testParseRef13,
    testParseRef14
  ]

-- Absolute URI reference parser (see Parse module)
--   parseAbsoluteURIRef :: Parser Char String

testParseAbs01 = testParser "testParseAbs01" parseAbsoluteURIRef
                    "http://example.org/aaa/bbb#ccc"
                    [("http://example.org/aaa/bbb#ccc","")]
testParseAbs02 = testParser "testParseAbs02" parseAbsoluteURIRef
                    "mailto:local@domain.org ****"
                    [("mailto:local@domain.org"," ****")]
testParseAbs03 = testParser "testParseAbs03" parseAbsoluteURIRef
                    "mailto:local@domain.org#frag|****"
                    [("mailto:local@domain.org#frag","|****")]
testParseAbs04 = testParser "testParseAbs04" parseAbsoluteURIRef
                    "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
                    [("HTTP://EXAMPLE.ORG/AAA/BBB#CCC","")]
testParseAbs05 = testParser "testParseAbs05" parseAbsoluteURIRef
                    "//example.org/aaa/bbb#ccc"
                    noResult
testParseAbs06 = testParser "testParseAbs06" parseAbsoluteURIRef
                    "/aaa/bbb#ccc"
                    noResult
testParseAbs07 = testParser "testParseAbs07" parseAbsoluteURIRef
                    "bbb#c%aac"
                    noResult
testParseAbs08 = testParser "testParseAbs08" parseAbsoluteURIRef
                    "#ccc"
                    noResult
testParseAbs09 = testParser "testParseAbs09" parseAbsoluteURIRef
                    "#"
                    noResult
testParseAbs10 = testParser "testParseAbs10" parseAbsoluteURIRef
                    "/"
                    noResult
testParseAbs11 = testParser "testParseAbs11" parseAbsoluteURIRef
                    "A'C"
                    noResult
testParseAbs12 = testParser "testParseAbs12" parseAbsoluteURIRef
                    "bbb#ccc%z"
                    noResult

testParseAbsSuite = TestLabel "Test parseAbsoluteURIRef" testParseAbsList
testParseAbsList  = TestList
  [
    testParseAbs01, testParseAbs02, testParseAbs03, testParseAbs04,
    testParseAbs05, testParseAbs06, testParseAbs07, testParseAbs08,
    testParseAbs09,
    testParseAbs10, testParseAbs11, testParseAbs12
  ]

-- Absolute URI parser (see Parse module)
--  parseAbsoluteURI :: Parser Char String

testParseURI01 = testParser "testParseURI01" parseAbsoluteURI
                    "http://example.org/aaa/bbb#ccc"
                    [("http://example.org/aaa/bbb","#ccc")]
testParseURI02 = testParser "testParseURI02" parseAbsoluteURI
                    "mailto:local@domain.org ****"
                    [("mailto:local@domain.org"," ****")]
testParseURI03 = testParser "testParseURI03" parseAbsoluteURI
                    "mailto:local@domain.org#frag|****"
                    [("mailto:local@domain.org","#frag|****")]
testParseURI04 = testParser "testParseURI04" parseAbsoluteURI
                    "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
                    [("HTTP://EXAMPLE.ORG/AAA/BBB","#CCC")]
testParseURI05 = testParser "testParseURI05" parseAbsoluteURI
                    "//example.org/aaa/bbb#ccc"
                    noResult
testParseURI06 = testParser "testParseURI06" parseAbsoluteURI
                    "/aaa/bbb#ccc"
                    noResult
testParseURI07 = testParser "testParseURI07" parseAbsoluteURI
                    "bbb#c%aac"
                    noResult
testParseURI08 = testParser "testParseURI08" parseAbsoluteURI
                    "#ccc"
                    noResult
testParseURI09 = testParser "testParseURI09" parseAbsoluteURI
                    "#"
                    noResult
testParseURI10 = testParser "testParseURI10" parseAbsoluteURI
                    "/"
                    noResult
testParseURI11 = testParser "testParseURI11" parseAbsoluteURI
                    "A'C"
                    noResult
testParseURI12 = testParser "testParseURI12" parseAbsoluteURI
                    "bbb#ccc%z"
                    noResult

testParseURISuite = TestLabel "Test parseAbsoluteURI" testParseURIList
testParseURIList  = TestList
  [
    testParseURI01, testParseURI02, testParseURI03, testParseURI04,
    testParseURI05, testParseURI06, testParseURI07, testParseURI08,
    testParseURI09,
    testParseURI10, testParseURI11, testParseURI12
  ]

-- Compare two URIs
-- Takes account of normalizations that can be applied to all URIs
-- (2003-02-20, currently subject to W3C TAG debate)
--   compareURI :: String -> String -> Bool

testCompare :: String -> Bool -> String -> String  -> Test
testCompare label eq uri1 uri2 =
    TestCase ( assertEqual label eq ( compareURI uri1 uri2 ) )

testCompare01 = testCompare "testCompare01" True
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/aaa/bbb#ccc"
testCompare02 = testCompare "testCompare02" False
                    "http://example.org/aaa/bbb#ccc"
                    "HTTP://example.org/aaa/bbb#ccc"
testCompare03 = testCompare "testCompare03" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://EXAMPLE.ORG/aaa/bbb#ccc"
testCompare04 = testCompare "testCompare04" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/AAA/bbb#ccc"
testCompare05 = testCompare "testCompare05" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/a%61a/bbb#ccc"
testCompare06 = testCompare "testCompare06" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/aaa/b%62b#ccc"
testCompare07 = testCompare "testCompare07" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/aaa/bbb#c%63c"
testCompare08 = testCompare "testCompare08" False
                    "mailto:local@example.org"
                    "mailto:local@ex%61mple.org"
testCompare09 = testCompare "testCompare09" False
                    "http://example.org/aaa/bbb#ccc"
                    "http://example.org/aaa%2Fbbb#ccc"
testCompare10 = testCompare "testCompare10" False
                    "http://example.org/aaa%2fbbb#ccc"
                    "http://example.org/aaa%2Fbbb#ccc"

testCompareSuite = TestLabel "Test compareURI" testCompareList
testCompareList  = TestList
  [
    testCompare01, testCompare02, testCompare03, testCompare04,
    testCompare05, testCompare06, testCompare07, testCompare08,
    testCompare09,
    testCompare10 -- , testCompare11, testCompare12
  ]

-- Separate URI-with-fragment into URI and fragment ID
--   splitURIFragment :: String -> ( String, Maybe String )
-- Construct URI-with-fragment using URI and supplied fragment id
--   makeURIWithFragment :: String -> Maybe String -> String

testSplitFrag :: String -> String -> ( String, Maybe String ) -> Test
testSplitFrag label input ( main, frag ) = TestList
    [
    TestCase ( assertEqual (label++"(split)") ( main, frag ) ( splitURIFragment input ) ),
    TestCase ( assertEqual (label++"(make)")  input          ( makeURIWithFragment main frag ) )
    ]

testSplitFrag01 = testSplitFrag "testSplitFrag01"
                    "http://example.org/aaa/bbb#ccc"
                    ( "http://example.org/aaa/bbb", Just "ccc" )
testSplitFrag02 = testSplitFrag "testSplitFrag02"
                    "mailto:local@domain.org"
                    ( "mailto:local@domain.org", Nothing )
testSplitFrag03 = testSplitFrag "testSplitFrag03"
                    "mailto:local@domain.org#frag"
                    ( "mailto:local@domain.org", Just "frag" )
testSplitFrag04 = testSplitFrag "testSplitFrag04"
                    "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
                    ( "HTTP://EXAMPLE.ORG/AAA/BBB", Just "CCC" )
testSplitFrag05 = testSplitFrag "testSplitFrag05"
                    "//example.org/aaa/bbb#ccc"
                    ( "//example.org/aaa/bbb", Just "ccc" )
testSplitFrag06 = testSplitFrag "testSplitFrag06"
                    "/aaa/bbb#ccc"
                    ( "/aaa/bbb", Just "ccc" )
testSplitFrag07 = testSplitFrag "testSplitFrag07"
                    "bbb#ccc"
                    ( "bbb", Just "ccc" )
testSplitFrag08 = testSplitFrag "testSplitFrag08"
                    "#ccc"
                    ( "", Just "ccc" )
testSplitFrag09 = testSplitFrag "testSplitFrag09"
                    "#"
                    ( "", Just "" )
testSplitFrag10 = testSplitFrag "testSplitFrag10"
                    "/"
                    ( "/", Nothing )
testSplitFrag11 = testSplitFrag "testSplitFrag11"
                    "aaa%12ccc"
                    ( "aaa%12ccc", Nothing )
testSplitFrag12 = testSplitFrag "testSplitFrag12"
                    "aaa%23ccc"                     -- %23 = '#'
                    ( "aaa%23ccc", Nothing )
testSplitFrag13 = testSplitFrag "testSplitFrag13"
                    "http://example.org/aaa/bbb#"
                    ( "http://example.org/aaa/bbb", Just "" )
testSplitFrag14 = testSplitFrag "testSplitFrag14"
                    ""
                    ( "", Nothing )
testSplitFrag15 = testSplitFrag "testSplitFrag15"
                    "abc"
                    ( "abc", Nothing )
testSplitFrag16 = testSplitFrag "testSplitFrag16"
                    "abc#de:f"
                    ( "abc", Just "de:f" )
testSplitFrag17 = testSplitFrag "testSplitFrag17"
                    "abc#de?f"
                    ( "abc", Just "de?f" )
testSplitFrag18 = testSplitFrag "testSplitFrag18"
                    "abc#de/f"
                    ( "abc", Just "de/f" )

testSplitFragSuite = TestLabel "Test splitURIFragment" testSplitFragList
testSplitFragList  = TestList
  [
    testSplitFrag01, testSplitFrag02, testSplitFrag03, testSplitFrag04,
    testSplitFrag05, testSplitFrag06, testSplitFrag07, testSplitFrag08,
    testSplitFrag09,
    testSplitFrag10, testSplitFrag11, testSplitFrag12, testSplitFrag13,
    testSplitFrag14, testSplitFrag15, testSplitFrag16, testSplitFrag17,
    testSplitFrag18
  ]


-- Above tests most cases of makeURIWithFragment,
-- but a couple of extra tests are needed for when the main URI already
-- has a fragment:
testOverrideFrag label ( main, frag ) result =
    TestCase ( assertEqual label result ( makeURIWithFragment main frag ) )

testOverrideFrag01 = testOverrideFrag "testOverrideFrag01"
                        ( "http://example.org/aaa#bbb", (Just "fff") )
                        "http://example.org/aaa#fff"
testOverrideFrag02 = testOverrideFrag "testOverrideFrag02"
                        ( "http://example.org/aaa#bbb", Nothing )
                        "http://example.org/aaa"
testOverrideFrag03 = testOverrideFrag "testOverrideFrag03"
                        ( "http://example.org/aaa#bbb", Just "" )
                        "http://example.org/aaa#"

testOverrideFragSuite = TestLabel "Test Override Fragment" testOverrideFragList
testOverrideFragList  = TestList
  [
    testOverrideFrag01, testOverrideFrag02, testOverrideFrag03
  ]

-- test getURIRef function
testGetURIRef :: String -> String -> URI -> Test
testGetURIRef label strval urival =
    TestCase ( assertEqual label urival ( getURIRef strval ) )


testGetURIRef01 = testGetURIRef "testGetURIRef01"
                    "foo:xyz"
                    (URI "foo:" "xyz" [] "" "")
testGetURIRef02 = testGetURIRef "testGetURIRef02"
                    "http://example/x/y/z"
                    (URI "http:" "//example" ["/","x/","y/","z"] "" "")
testGetURIRef03 = testGetURIRef "testGetURIRef03"
                    "../abc"
                    (URI "" "" ["../","abc"] "" "")
testGetURIRef04 = testGetURIRef "testGetURIRef04"
                    "http://example/a/b/../../c"
                    (URI "http:" "//example" ["/","a/","b/","../","../","c"] "" "")
testGetURIRef05 = testGetURIRef "testGetURIRef04"
                    "http://example/a/./b/./../c/"
                    (URI "http:" "//example" ["/","a/","./","b/","./","../","c/",""] "" "")


testGetURIRefSuite = TestLabel "Test getURIReg" testGetURIRefList
testGetURIRefList  = TestList
  [
    testGetURIRef01, testGetURIRef02, testGetURIRef03, testGetURIRef04, testGetURIRef05
  ]

-- test normalizeURI function
testNormalizeURI :: String -> String -> String -> Test
testNormalizeURI label strval normval =
    TestCase ( assertEqual (label++": "++strval) normval ( normalizeURI strval ) )


testNormalizeURI01 = testNormalizeURI "testNormalizeURI01"
                    "../abc"
                    "../abc"
testNormalizeURI02 = testNormalizeURI "testNormalizeURI02"
                    "http://example/x/y/z"
                    "http://example/x/y/z"
testNormalizeURI03 = testNormalizeURI "testNormalizeURI03"
                    "http://example/a/b/../../c"
                    "http://example/c"
testNormalizeURI04 = testNormalizeURI "testNormalizeURI04"
                    "http://example/a/b/c/../../"
                    "http://example/a/"
testNormalizeURI05 = testNormalizeURI "testNormalizeURI05"
                    "http://example/a/b/c/./"
                    "http://example/a/b/c/"
testNormalizeURI06 = testNormalizeURI "testNormalizeURI06"
                    "http://example/a/b/c/.././"
                    "http://example/a/b/"
testNormalizeURI07 = testNormalizeURI "testNormalizeURI07"
                    "http://example/a/b/c/d/../../../../e"
                    "http://example/e"
testNormalizeURI08 = testNormalizeURI "testNormalizeURI08"
                    "http://example/a/b/c/d/../.././../../e"
                    "http://example/e"

testNormalizeURISuite = TestLabel "Test normalizeURI" testNormalizeURIList
testNormalizeURIList  = TestList
  [
    testNormalizeURI01, testNormalizeURI02, testNormalizeURI03, testNormalizeURI04,
    testNormalizeURI05, testNormalizeURI06, testNormalizeURI07, testNormalizeURI08
  ]

-- Get reference relative to given base
--   relativeRef :: String -> String -> String
-- Get absolute URI given base and relative reference
--   absoluteURI :: String -> String -> String
--
-- Test cases taken from: http://www.w3.org/2000/10/swap/uripath.py
-- (Thanks, Dan Connolly)
--
-- NOTE:  absoluteURI base (relativeRef base u) is always equivalent to u.
-- cf. http://lists.w3.org/Archives/Public/uri/2003Jan/0008.html

testRelSplit :: String -> String -> String -> String -> Test
testRelSplit label base uabs urel =
    TestCase ( assertEqual label urel ( relativeRefPart base uabs ) )

testRelJoin  :: String -> String -> String -> String -> Test
testRelJoin label base urel uabs =
    TestCase ( assertEqual label uabs ( absoluteUriPart base urel ) )

testRelative :: String -> String -> String -> String -> Test
testRelative label base uabs urel = TestList
    [
    (testRelSplit (label++"(rel)") base uabs urel),
    (testRelJoin  (label++"(abs)") base urel (normalizeURI uabs))
    ]

testRelative01 = testRelative "testRelative01"
                    "foo:xyz" "bar:abc" "bar:abc"
testRelative02 = testRelative "testRelative02"
                    "http://example/x/y/z" "http://example/x/abc" "../abc"
testRelative03 = testRelative "testRelative03"
                    "http://example2/x/y/z" "http://example/x/abc" "//example/x/abc"
                    -- "http://example2/x/y/z" "http://example/x/abc" "http://example/x/abc"
testRelative04 = testRelative "testRelative04"
                    "http://ex/x/y/z" "http://ex/x/r" "../r"
testRelative05 = testRelative "testRelative05"
                    "http://ex/x/y/z" "http://ex/r" "/r"
                    -- "http://ex/x/y/z" "http://ex/r" "../../r"
testRelative06 = testRelative "testRelative06"
                    "http://ex/x/y" "http://ex/x/q/r" "q/r"
testRelative07 = testRelative "testRelative07"
                    "http://ex/x/y" "http://ex/x/q/r#s" "q/r#s"
testRelative08 = testRelative "testRelative08"
                    "http://ex/x/y" "http://ex/x/q/r#s/t" "q/r#s/t"
testRelative09 = testRelative "testRelative09"
                    "http://ex/x/y" "ftp://ex/x/q/r" "ftp://ex/x/q/r"
testRelative10 = testRelative "testRelative10"
                    "http://ex/x/y" "http://ex/x/y" "y"
                    -- "http://ex/x/y" "http://ex/x/y" ""
testRelative11 = testRelative "testRelative11"
                    "http://ex/x/y/" "http://ex/x/y/" "./"
                    -- "http://ex/x/y/" "http://ex/x/y/" ""
testRelative12 = testRelative "testRelative12"
                    "http://ex/x/y/pdq" "http://ex/x/y/pdq" "pdq"
                    -- "http://ex/x/y/pdq" "http://ex/x/y/pdq" ""
testRelative13 = testRelative "testRelative13"
                    "http://ex/x/y/" "http://ex/x/y/z/" "z/"
testRelative14 = testRelative "testRelative14"
                    "file:/swap/test/animal.rdf" "file:/swap/test/animal.rdf#Animal" "animal.rdf#Animal"
testRelative15 = testRelative "testRelative15"
                    "file:/e/x/y/z" "file:/e/x/abc" "../abc"
testRelative16 = testRelative "testRelative16"
                    "file:/example2/x/y/z" "file:/example/x/abc" "/example/x/abc"
testRelative17 = testRelative "testRelative17"
                    "file:/ex/x/y/z" "file:/ex/x/r" "../r"
testRelative18 = testRelative "testRelative18"
                    "file:/ex/x/y/z" "file:/r" "/r"
testRelative19 = testRelative "testRelative19"
                    "file:/ex/x/y" "file:/ex/x/q/r" "q/r"
testRelative20 = testRelative "testRelative20"
                    "file:/ex/x/y" "file:/ex/x/q/r#s" "q/r#s"
testRelative21 = testRelative "testRelative21"
                    "file:/ex/x/y" "file:/ex/x/q/r#" "q/r#"
testRelative22 = testRelative "testRelative22"
                    "file:/ex/x/y" "file:/ex/x/q/r#s/t" "q/r#s/t"
testRelative23 = testRelative "testRelative23"
                    "file:/ex/x/y" "ftp://ex/x/q/r" "ftp://ex/x/q/r"
testRelative24 = testRelative "testRelative24"
                    "file:/ex/x/y" "file:/ex/x/y" "y"
                    -- "file:/ex/x/y" "file:/ex/x/y" ""
testRelative25 = testRelative "testRelative25"
                    "file:/ex/x/y/" "file:/ex/x/y/" "./"
                    -- "file:/ex/x/y/" "file:/ex/x/y/" ""
testRelative26 = testRelative "testRelative26"
                    "file:/ex/x/y/pdq" "file:/ex/x/y/pdq" "pdq"
                    -- "file:/ex/x/y/pdq" "file:/ex/x/y/pdq" ""
testRelative27 = testRelative "testRelative27"
                    "file:/ex/x/y/" "file:/ex/x/y/z/" "z/"
testRelative28 = testRelative "testRelative28"
                    "file:/devel/WWW/2000/10/swap/test/reluri-1.n3"
                    "file://meetings.example.com/cal#m1" "//meetings.example.com/cal#m1"
                    -- "file:/devel/WWW/2000/10/swap/test/reluri-1.n3"
                    -- "file://meetings.example.com/cal#m1" "file://meetings.example.com/cal#m1"
testRelative29 = testRelative "testRelative29"
                    "file:/home/connolly/w3ccvs/WWW/2000/10/swap/test/reluri-1.n3"
                    "file://meetings.example.com/cal#m1" "//meetings.example.com/cal#m1"
                    -- "file:/home/connolly/w3ccvs/WWW/2000/10/swap/test/reluri-1.n3"
                    -- "file://meetings.example.com/cal#m1" "file://meetings.example.com/cal#m1"
testRelative30 = testRelative "testRelative30"
                    "file:/some/dir/foo" "file:/some/dir/#blort" "./#blort"
testRelative31 = testRelative "testRelative31"
                    "file:/some/dir/foo" "file:/some/dir/#" "./#"
testRelative32 = testRelative "testRelative32"
                    "http://ex/x/y" "http://ex/x/q:r" "./q:r"
                    -- see RFC2396bis, section 5       ^^
testRelative33 = testRelative "testRelative33"
                    "http://ex/x/y" "http://ex/x/p=q:r" "./p=q:r"
                    -- "http://ex/x/y" "http://ex/x/p=q:r" "p=q:r"
testRelative34 = testRelative "testRelative34"
                    "http://ex/x/y?pp/qq" "http://ex/x/y?pp/rr" "y?pp/rr"
testRelative35 = testRelative "testRelative35"
                    "http://ex/x/y?pp/qq" "http://ex/x/y/z" "y/z"
testRelative36 = testRelative "testRelative36"
                    "mailto:local"
                    "mailto:local/qual@domain.org#frag"
                    "local/qual@domain.org#frag"
-- relativeRefPart "mailto:local/qual@domain.org" "mailto:local/qual@domain.org#frag"
testRelative37 = testRelative "testRelative37"
                    "mailto:local/qual@domain.org"
                    "mailto:local/qual@domain.org#frag"
                    "local/qual@domain.org#frag"
testRelative38 = testRelative "testRelative38"
                    "http://ex/x/y?q" "http://ex/x/y?q" "y?q"
testRelative39 = testRelative "testRelative39"
                    "http://ex?p" "http://ex/x/y?q" "/x/y?q"

-- add escape tests
testRelative40 = testRelative "testRelative40"
                    "http://example/x/y%2Fz" "http://example/x/abc" "abc"
testRelative41 = testRelative "testRelative41"
                    "http://example/a/x/y/z" "http://example/a/x%2Fabc" "../../x%2Fabc"
testRelative42 = testRelative "testRelative42"
                    "http://example/a/x/y%2Fz" "http://example/a/x%2Fabc" "../x%2Fabc"
testRelative43 = testRelative "testRelative43"
                    "http://example/x%2Fy/z" "http://example/x%2Fy/abc" "abc"
testRelative44 = testRelative "testRelative44"
                    "http://ex/x/y" "http://ex/x/q%3Ar" "q%3Ar"
testRelative45 = testRelative "testRelative45"
                    "http://example/x/y%2Fz" "http://example/x%2Fabc" "/x%2Fabc"
-- Apparently, TimBL prefers the following way to 41, 42 above
-- cf. http://lists.w3.org/Archives/Public/uri/2003Feb/0028.html
-- He also notes that there may be different relative fuctions
-- that satisfy the basic equivalence axiom:
-- cf. http://lists.w3.org/Archives/Public/uri/2003Jan/0008.html
testRelative46 = testRelative "testRelative46"
                    "http://example/x/y/z" "http://example/x%2Fabc" "/x%2Fabc"
testRelative47 = testRelative "testRelative47"
                    "http://example/x/y%2Fz" "http://example/x%2Fabc" "/x%2Fabc"

-- Other oddball tests
    -- Check segment normalization code:
testRelative50 = testRelative "testRelative50"
                    "ftp://example/x/y" "http://example/a/b/../../c"  "http://example/c"
testRelative51 = testRelative "testRelative51"
                    "ftp://example/x/y" "http://example/a/b/c/../../" "http://example/a/"
testRelative52 = testRelative "testRelative52"
                    "ftp://example/x/y" "http://example/a/b/c/./"     "http://example/a/b/c/"
testRelative53 = testRelative "testRelative53"
                    "ftp://example/x/y" "http://example/a/b/c/.././"  "http://example/a/b/"
testRelative54 = testRelative "testRelative54"
                    "ftp://example/x/y" "http://example/a/b/c/d/../../../../e" "http://example/e"
testRelative55 = testRelative "testRelative55"
                    "ftp://example/x/y" "http://example/a/b/c/d/../.././../../e" "http://example/e"
    -- Check handling of queries and fragments with non-relative paths
testRelative60 = testRelative "testRelative60"
                    "mailto:local1@domain1?query1" "mailto:local2@domain2"
                    "local2@domain2"
testRelative61 = testRelative "testRelative61"
                    "mailto:local1@domain1" "mailto:local2@domain2?query2"
                    "local2@domain2?query2"
testRelative62 = testRelative "testRelative62"
                    "mailto:local1@domain1?query1" "mailto:local2@domain2?query2"
                    "local2@domain2?query2"
testRelative63 = testRelative "testRelative63"
                    "mailto:local@domain?query1" "mailto:local@domain?query2"
                    "local@domain?query2"
testRelative64 = testRelative "testRelative64"
                    "mailto:?query1" "mailto:local@domain?query2"
                    "local@domain?query2"
testRelative65 = testRelative "testRelative65"
                    "mailto:local@domain?query1" "mailto:?query2"
                    "?query2"

-- testRelative  base abs rel
-- testRelSplit  base abs rel
-- testRelJoin   base rel abs
testRelative70 = testRelative "testRelative70"
                    "http://example.org/base/uri" "http:this"
                    "this"  -- no round-tripping this case
testRelative71 = testRelSplit "testRelative71"
                    "http://example.org/base/uri" "http:this"
                    "this"
testRelative72 = testRelJoin "testRelative72"
                    "http://example.org/base/uri" "http:this"
                    "http:this"
testRelative73 = testRelJoin "testRelative73"
                    "http:base" "http:this"
                    "http:this"
testRelative74 = testRelJoin "testRelative74"
                    "f:/a" ".//g"
                    "f://g"
testRelative75 = testRelJoin "testRelative74"
                    "f://example.org/base/a" "b/c//d/e"
                    "f://example.org/base/b/c//d/e"
testRelative76 = testRelJoin "testRelative74"
                    "mid:m@example.ord/c@example.org" "m2@example.ord/c2@example.org"
                    "mid:m2@example.ord/c2@example.org"


testRelativeSuite = TestLabel "Test Relative URIs" testRelativeList
testRelativeList  = TestList
  [ testRelative01, testRelative02, testRelative03, testRelative04
  , testRelative05, testRelative06, testRelative07, testRelative08
  , testRelative09
  , testRelative10, testRelative11, testRelative12, testRelative13
  , testRelative14, testRelative15, testRelative16, testRelative17
  , testRelative18, testRelative19
  , testRelative21, testRelative21, testRelative22, testRelative23
  , testRelative24, testRelative25, testRelative26, testRelative27
  , testRelative28, testRelative29
  , testRelative30, testRelative31, testRelative32, testRelative33
  , testRelative34, testRelative35, testRelative36, testRelative37
    --
  , testRelative40, testRelative41, testRelative42, testRelative43
  , testRelative44, testRelative45, testRelative46, testRelative47
    --
  , testRelative50, testRelative51, testRelative52, testRelative53
  , testRelative54, testRelative55
    --
  , testRelative60, testRelative61, testRelative62, testRelative63
  , testRelative64, testRelative65
    --
  -- , testRelative70
  , testRelative71, testRelative72, testRelative73
  , testRelative74, testRelative75, testRelative76
  ]

-- RFC2396 relative-to-absolute URI tests

rfcbase  = "http://a/b/c/d;p?q"
-- normal cases, RFC2396 C.1
testRFC01 = testRelJoin "testRFC01" rfcbase "g:h" "g:h"
testRFC02 = testRelJoin "testRFC02" rfcbase "g" "http://a/b/c/g"
testRFC03 = testRelJoin "testRFC03" rfcbase "./g" "http://a/b/c/g"
testRFC04 = testRelJoin "testRFC04" rfcbase "g/" "http://a/b/c/g/"
testRFC05 = testRelJoin "testRFC05" rfcbase "/g" "http://a/g"
testRFC06 = testRelJoin "testRFC06" rfcbase "//g" "http://g"
testRFC07 = testRelJoin "testRFC07" rfcbase "?y" "http://a/b/c/d;p?y"
testRFC08 = testRelJoin "testRFC08" rfcbase "g?y" "http://a/b/c/g?y"
testRFC09 = testRelJoin "testRFC09" rfcbase "?q#s" "http://a/b/c/d;p?q#s"
testRFC10 = testRelJoin "testRFC10" rfcbase "g#s" "http://a/b/c/g#s"
testRFC11 = testRelJoin "testRFC11" rfcbase "g?y#s" "http://a/b/c/g?y#s"
testRFC12 = testRelJoin "testRFC12" rfcbase ";x" "http://a/b/c/;x"
testRFC13 = testRelJoin "testRFC13" rfcbase "g;x" "http://a/b/c/g;x"
testRFC14 = testRelJoin "testRFC14" rfcbase "g;x?y#s" "http://a/b/c/g;x?y#s"
testRFC15 = testRelJoin "testRFC15" rfcbase "." "http://a/b/c/"
testRFC16 = testRelJoin "testRFC16" rfcbase "./" "http://a/b/c/"
testRFC17 = testRelJoin "testRFC17" rfcbase ".." "http://a/b/"
testRFC18 = testRelJoin "testRFC18" rfcbase "../" "http://a/b/"
testRFC19 = testRelJoin "testRFC19" rfcbase "../g" "http://a/b/g"
testRFC20 = testRelJoin "testRFC20" rfcbase "../.." "http://a/"
testRFC21 = testRelJoin "testRFC21" rfcbase "../../" "http://a/"
testRFC22 = testRelJoin "testRFC22" rfcbase "../../g" "http://a/g"
testRFC23 = testRelJoin "testRFC23" rfcbase "#s" "#s"   -- current document
testRFC24 = testRelJoin "testRFC24" rfcbase "" ""       -- current document
-- abnormal cases, RFC2396 C.2
testRFC31 = testRelJoin "testRFC31" rfcbase "?q" rfcbase
testRFC32 = testRelJoin "testRFC32" rfcbase "../../../g" "http://a/../g"
testRFC33 = testRelJoin "testRFC33" rfcbase "../../../../g" "http://a/../../g"
testRFC34 = testRelJoin "testRFC34" rfcbase "/./g" "http://a/g"
--testRFC34 = testRelJoin "testRFC34" rfcbase "/./g" "http://a/./g"  -- RFC2396 says don't remove '.'
testRFC35 = testRelJoin "testRFC35" rfcbase "/../g" "http://a/../g"
testRFC36 = testRelJoin "testRFC36" rfcbase "g." "http://a/b/c/g."
testRFC37 = testRelJoin "testRFC37" rfcbase ".g" "http://a/b/c/.g"
testRFC38 = testRelJoin "testRFC38" rfcbase "g.." "http://a/b/c/g.."
testRFC39 = testRelJoin "testRFC39" rfcbase "..g" "http://a/b/c/..g"
testRFC40 = testRelJoin "testRFC40" rfcbase "./../g" "http://a/b/g"
testRFC41 = testRelJoin "testRFC41" rfcbase "./g/." "http://a/b/c/g/"
testRFC42 = testRelJoin "testRFC42" rfcbase "g/./h" "http://a/b/c/g/h"
testRFC43 = testRelJoin "testRFC43" rfcbase "g/../h" "http://a/b/c/h"
testRFC44 = testRelJoin "testRFC44" rfcbase "g;x=1/./y" "http://a/b/c/g;x=1/y"
testRFC45 = testRelJoin "testRFC45" rfcbase "g;x=1/../y" "http://a/b/c/y"
testRFC46 = testRelJoin "testRFC46" rfcbase "g?y/./x" "http://a/b/c/g?y/./x"
testRFC47 = testRelJoin "testRFC47" rfcbase "g?y/../x" "http://a/b/c/g?y/../x"
testRFC48 = testRelJoin "testRFC48" rfcbase "g#s/./x" "http://a/b/c/g#s/./x"
testRFC49 = testRelJoin "testRFC49" rfcbase "g#s/../x" "http://a/b/c/g#s/../x"
testRFC50 = testRelJoin "testRFC50" rfcbase "http:x" "http:x"

-- Null path tests
-- See RFC2396bis, section 5.2,
-- "If the base URI's path component is the empty string, then a single
--  slash character is copied to the buffer"
testRFC60 = testRelative "testRFC60" "http://ex"     "http://ex/x/y?q" "/x/y?q"
testRFC61 = testRelJoin  "testRFC61" "http://ex"     "x/y?q"           "http://ex/x/y?q"
testRFC62 = testRelative "testRFC62" "http://ex?p"   "http://ex/x/y?q" "/x/y?q"
testRFC63 = testRelJoin  "testRFC63" "http://ex?p"   "x/y?q"           "http://ex/x/y?q"
testRFC64 = testRelative "testRFC64" "http://ex#f"   "http://ex/x/y?q" "/x/y?q"
testRFC65 = testRelJoin  "testRFC65" "http://ex#f"   "x/y?q"           "http://ex/x/y?q"
testRFC66 = testRelative "testRFC66" "http://ex?p"   "http://ex/x/y#g" "/x/y#g"
testRFC67 = testRelJoin  "testRFC67" "http://ex?p"   "x/y#g"           "http://ex/x/y#g"
testRFC68 = testRelative "testRFC68" "http://ex"     "http://ex/"      "/"
testRFC69 = testRelJoin  "testRFC69" "http://ex"     "./"              "http://ex/"
testRFC70 = testRelative "testRFC70" "http://ex"     "http://ex/a/b"   "/a/b"
testRFC71 = testRelative "testRFC71" "http://ex/a/b" "http://ex"       "./"

testRFC2396Suite = TestLabel "Test RFC2396 examples" testRFC2396List
testRFC2396List  = TestList
  [
    testRFC01, testRFC02, testRFC03, testRFC04,
    testRFC05, testRFC06, testRFC07, testRFC08,
    testRFC09,
    testRFC10, testRFC11, testRFC12, testRFC13,
    testRFC14, testRFC15, testRFC16, testRFC17,
    testRFC18, testRFC19,
    testRFC20, testRFC21, testRFC22, testRFC23,
    testRFC24,
    -- testRFC30,
    testRFC31, testRFC32, testRFC33,
    testRFC34, testRFC35, testRFC36, testRFC37,
    testRFC38, testRFC39,
    testRFC40, testRFC41, testRFC42, testRFC43,
    testRFC44, testRFC45, testRFC46, testRFC47,
    testRFC48, testRFC49,
    testRFC50,
    --
    testRFC60, testRFC61, testRFC62, testRFC63,
    testRFC64, testRFC65, testRFC66, testRFC67,
    testRFC68, testRFC69,
    testRFC70
  ]

-- And some other oddballs:
mailbase = "mailto:local/option@domain.org?notaquery#frag"
testMail01 = testRelJoin "testMail01"
            mailbase "local@domain"
            "mailto:local@domain"
testMail02 = testRelJoin "testMail02"
            mailbase "#newfrag"
            "mailto:#newfrag"
            -- "mailto:local/option@domain.org?notaquery#newfrag"
testMail03 = testRelJoin "testMail03"
            mailbase "l1/q1@domain"
            "mailto:l1/q1@domain"

testMail11 = testRelJoin "testMail11"
             "mailto:local1@domain1?query1" "mailto:local2@domain2"
             "mailto:local2@domain2"
testMail12 = testRelJoin "testMail12"
             "mailto:local1@domain1" "mailto:local2@domain2?query2"
             "mailto:local2@domain2?query2"
testMail13 = testRelJoin "testMail13"
             "mailto:local1@domain1?query1" "mailto:local2@domain2?query2"
             "mailto:local2@domain2?query2"
testMail14 = testRelJoin "testMail14"
             "mailto:local@domain?query1" "mailto:local@domain?query2"
             "mailto:local@domain?query2"
testMail15 = testRelJoin "testMail15"
             "mailto:?query1" "mailto:local@domain?query2"
             "mailto:local@domain?query2"
testMail16 = testRelJoin "testMail16"
             "mailto:local@domain?query1" "?query2"
             "mailto:?query2"
testInfo17 = testRelJoin "testInfo17"
             "info:name/1234/../567" "name/9876/../543"
             "info:name/9876/../543"
testInfo18 = testRelJoin "testInfo18"
             "info:/name/1234/../567" "name/9876/../543"
             "info:/name/name/543"

testOddballSuite = TestLabel "Test oddball examples" testOddballList
testOddballList  = TestList
  [ testMail01, testMail02, testMail03
  , testMail11, testMail12, testMail13, testMail14, testMail15, testMail16
  , testInfo17
  ]

-- Full test suite
allTests = TestList
  [ testURIRefSuite,
    testParseRefSuite,
    testParseAbsSuite,
    testParseURISuite,
    testCompareSuite,
    testSplitFragSuite,
    testOverrideFragSuite,
    testGetURIRefSuite,
    testNormalizeURIList,
    testRelativeSuite,
    testRFC2396Suite,
    testOddballSuite
  ]

main = runTestTT allTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT

uref = testURIRefSuite
pref = testParseRefSuite
pabs = testParseAbsSuite
puri = testParseURISuite
comp = testCompareSuite
frag = testSplitFragSuite
over = testOverrideFragSuite
guri = testGetURIRefSuite
nuri = testNormalizeURIList
tr01 = testRelative01
tr02 = testRelative02
tr03 = testRelative03
tr04 = testRelative04
rel  = testRelativeSuite
rfc  = testRFC2396Suite
oddb = testOddballSuite

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
-- $Source: /file/cvsdev/HaskellUtils/URITest.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: URITest.hs,v $
-- Revision 1.2  2004/01/22 19:52:27  graham
-- Rename module URI to avoid awkward clash with Haskell libraries
--
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.21  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.20  2003/11/07 21:45:47  graham
-- Started rework of datatype to use new DatatypeRel structure.
--
-- Revision 1.19  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.18  2003/09/24 13:35:43  graham
-- QName splitting moved from URI module to QName module
--
-- Revision 1.17  2003/06/24 19:55:50  graham
-- Another test case added
--
-- Revision 1.16  2003/06/18 23:37:09  graham
-- Another test case.
--
-- Revision 1.15  2003/06/17 15:42:36  graham
-- Misc updates
--
-- Revision 1.14  2003/06/10 01:04:46  graham
-- Proof framework in progress;  compiles, incomplete
--
-- Revision 1.13  2003/06/03 19:24:14  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.12  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.11  2003/04/17 00:35:39  graham
-- Added module N3ParserTest
-- N3parser is mostly working
-- Formulae remain to test
--
-- Revision 1.10  2003/03/05 22:16:24  graham
-- URI code passes all unit tests
--
-- Revision 1.9  2003/03/05 14:47:45  graham
-- Relative URI code complete, not tested
-- Fixed a URI parser bug
--
-- Revision 1.8  2003/02/28 14:02:52  graham
-- A few new test cases
--
-- Revision 1.7  2003/02/27 23:33:54  graham
-- QName splitting tested OK
--
-- Revision 1.6  2003/02/27 20:29:53  graham
-- Fixed some more parser bugs.
-- All parser tests pass.
-- QName and relative path handling to do.
--
-- Revision 1.5  2003/02/27 18:48:05  graham
-- Fix URI parser bug.
-- Add more URI parser test cases.
--
-- Revision 1.4  2003/02/27 15:28:45  graham
-- Updated internal structure of parsed URI.
-- Passes parser unit tests
--
-- Revision 1.3  2003/02/27 09:50:25  graham
-- Add URI parser test cases, some name changes
--
-- Revision 1.2  2003/02/27 00:30:14  graham
-- Syntax code nearly complete, untested
--
-- Revision 1.1  2003/02/20 19:45:07  graham
-- Add URI module and unit tests.
-- Code incomplete.
--
