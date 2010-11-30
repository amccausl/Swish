--------------------------------------------------------------------------------
--  $Id: ParseURITest.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ParseURITest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines test cases for module ParseURI.
--
--  The tests here are intended to be confidence-setting rather than
--  exhaustive:  the module URITest exercises a far wider range of
--  URI forms, via the URI module which uses this parser to break a
--  URI into its component parts.
--
--------------------------------------------------------------------------------

-- WNH RIP OUT module Swish.HaskellUtils.ParseURITest where

import Test.HUnit
import Swish.HaskellUtils.Parse
import Swish.HaskellUtils.ParseURI
import System.IO ( Handle, openFile, IOMode(WriteMode), hClose, hPutStr, hPutStrLn )

testParser :: ( Show a, Show b, Eq a, Eq b ) =>
    String -> Parser a b -> [a] -> [(b,[a])] -> Test
testParser lab parser inp res =
    TestCase ( assertEqual lab res (pend inp) )
    where
    pend = ( parser >*> (parseEnd []) ) `parseApply` fst

-- hostname

hostnameTest lab inp res =
    testParser ("hostnameTest"++lab) hostname inp res

hostnameTest01 = hostnameTest "01" "example.org" [ ("example.org","") ]

hostnameTests = TestList
      [ hostnameTest01 --, hostnameTest02, hostnameTest03, hostnameTest04,
      ]

-- ipv6

ipv6Test lab inp res =
    testParser ("ipv6Test"++lab) ipv6address inp res

ipv6Test01 = ipv6Test "01" "FEDC:BA98:7654:3210:FEDC:BA98:7654:3210"
                [ ("FEDC:BA98:7654:3210:FEDC:BA98:7654:3210","") ]

ipv6Test02 = ipv6Test "02" "FEDC:BA98:7654:3210:FEDC:BA98:192.9.5.5"
                [ ("FEDC:BA98:7654:3210:FEDC:BA98:192.9.5.5","") ]

ipv6Test03 = ipv6Test "03" "1080:0:0:0:8:800:200C:417A"
                [ ("1080:0:0:0:8:800:200C:417A","") ]

ipv6Test04 = ipv6Test "04" "3ffe:2a00:100:7031::1"
                [ ("3ffe:2a00:100:7031::1","") ]

ipv6Test05 = ipv6Test "05" "1080::8:800:200C:417A"
                [ ("1080::8:800:200C:417A","") ]

ipv6Test06 = ipv6Test "06" "::192.9.5.5"
                [ ("::192.9.5.5","") ]

ipv6Test07 = ipv6Test "07" "::FFFF:129.144.52.38"
                [ ("::FFFF:129.144.52.38","") ]

ipv6Test08 = ipv6Test "08" "2010:836B:4179::836B:4179"
                [ ("2010:836B:4179::836B:4179","") ]

ipv6Test09 = ipv6Test "09" "::200C:417A"
                [ ("::200C:417A","") ]

ipv6Test10 = ipv6Test "10" "::417A"
                [ ("::417A","") ]

ipv6Test11 = ipv6Test "11" "3ffe:2a00::417A"
                [ ("3ffe:2a00::417A","") ]

ipv6Tests = TestList
      [ ipv6Test01, ipv6Test02, ipv6Test03, ipv6Test04,
        ipv6Test05, ipv6Test06, ipv6Test07, ipv6Test08,
        ipv6Test09, ipv6Test10, ipv6Test11
      ]

-- absoluteUri :: Parser Char URI

absoluteUriTest lab inp res =
    testParser ("absoluteUriTest"++lab++": "++inp) absoluteUri inp res

absoluteUriTest01 = absoluteUriTest "01"
    "http://example.org/aaa/bbb"
    [ ( URI "http:" "//example.org" ["/","aaa/","bbb"] "" "", "" ) ]

absoluteUriTest02 = absoluteUriTest "02"
    "mailto:local@domain.org"
    [ ( URI "mailto:" "local@domain.org" [] "" "", "" ) ]

absoluteUriTest03 = absoluteUriTest "03"
    "mailto:local@domain.org"
    [ ( URI "mailto:" "local@domain.org" [] "" "", "" ) ]

absoluteUriTest04 = absoluteUriTest "04"
    "HTTP://EXAMPLE.ORG/AAA/BBB"
    [ ( URI "HTTP:" "//EXAMPLE.ORG" ["/","AAA/","BBB"] "" "", "" ) ]

absoluteUriTest05 = absoluteUriTest "05"
    "http://example.org/aaa/bbb?qqq/rrr"
    [ ( URI "http:" "//example.org" ["/","aaa/","bbb"] "?qqq/rrr" "", "" ) ]

absoluteUriTest06 = absoluteUriTest "06"
    "//example.org/aaa/bbb"
    []

absoluteUriTest07 = absoluteUriTest "07"
    "/aaa/bbb"
    []

absoluteUriTest08 = absoluteUriTest "08"
    "bbb"
    []

absoluteUriTest09 = absoluteUriTest "09"
    "#ccc"
    []

absoluteUriTest10 = absoluteUriTest "10"
    "#"
    []

absoluteUriTest11 = absoluteUriTest "11"
    "/"
    []

absoluteUriTest12 = absoluteUriTest "12"
    "http://[1080::8:800:200C:417A]/foo"
    [ ( URI "http:" "//[1080::8:800:200C:417A]" ["/","foo"] "" "", "" ) ]

absoluteUriTest13 = absoluteUriTest "13"
    "http://[::192.9.5.5]/ipng"
    [ ( URI "http:" "//[::192.9.5.5]" ["/","ipng"] "" "", "" ) ]

absoluteUriTest14 = absoluteUriTest "14"
    "http://[1080::8:800:192.9.5.5]/foo"
    [ ( URI "http:" "//[1080::8:800:192.9.5.5]" ["/","foo"] "" "", "" ) ]

absoluteUriTest15 = absoluteUriTest "15"
    "http://[::200C:417A]/ipng"
    [ ( URI "http:" "//[::200C:417A]" ["/","ipng"] "" "", "" ) ]

absoluteUriTest16 = absoluteUriTest "16"
    "http://[::417A]/ipng"
    [ ( URI "http:" "//[::417A]" ["/","ipng"] "" "", "" ) ]

absoluteUriTest17 = absoluteUriTest "17"
    "http://192.9.5.5/ipng"
    [ ( URI "http:" "//192.9.5.5" ["/","ipng"] "" "", "" ) ]

absoluteUriTest18 = absoluteUriTest "18"
    "http://example.org:/aaa/bbb"
    [ ( URI "http:" "//example.org:" ["/","aaa/","bbb"] "" "", "" ) ]

absoluteUriTests = TestList
      [ absoluteUriTest01, absoluteUriTest02, absoluteUriTest03,
        absoluteUriTest04, absoluteUriTest05, absoluteUriTest06,
        absoluteUriTest07, absoluteUriTest08, absoluteUriTest09,
        absoluteUriTest10, absoluteUriTest11, absoluteUriTest12,
        absoluteUriTest13, absoluteUriTest14, absoluteUriTest15,
        absoluteUriTest16, absoluteUriTest17, absoluteUriTest18 ]

-- relativeUri :: Parser Char URI

relativeUriTest lab inp res =
    testParser ("relativeUriTest"++lab) relativeUri inp res

relativeUriTest01 = relativeUriTest "01"
    "//example.org/aaa/bbb"
    [ ( URI "" "//example.org" ["/","aaa/","bbb"] "" "", "" ) ]

relativeUriTest02 = relativeUriTest "02"
    "local@domain.org"
    [ ( URI "" "" ["local@domain.org"] "" "", "" ) ]

relativeUriTest03 = relativeUriTest "03"
    "mailto:local@domain.org"
    []

relativeUriTest04 = relativeUriTest "04"
    "//EXAMPLE.ORG/AAA/BBB"
    [ ( URI "" "//EXAMPLE.ORG" ["/","AAA/","BBB"] "" "", "" ) ]

relativeUriTest05 = relativeUriTest "05"
    "//example.org/aaa/bbb?qqq/rrr"
    [ ( URI "" "//example.org" ["/","aaa/","bbb"] "?qqq/rrr" "", "" ) ]

relativeUriTest06 = relativeUriTest "06"
    "//example.org/aaa/bbb"
    [ ( URI "" "//example.org" ["/","aaa/","bbb"] "" "", "" ) ]

relativeUriTest07 = relativeUriTest "07"
    "/aaa/bbb"
    [ ( URI "" "" ["/","aaa/","bbb"] "" "", "" ) ]

relativeUriTest08 = relativeUriTest "08"
    "bbb"
    [ ( URI "" "" ["bbb"] "" "", "" ) ]

relativeUriTest09 = relativeUriTest "09"
    "#ccc"
    []

relativeUriTest10 = relativeUriTest "10"
    "#"
    []

relativeUriTest11 = relativeUriTest "11"
    "/"
    [ ( URI "" "" ["/",""] "" "", "" ) ]

relativeUriTest12 = relativeUriTest "12"
    "/aaa/"
    [ ( URI "" "" ["/","aaa/",""] "" "", "" ) ]

relativeUriTest13 = relativeUriTest "13"
    "/aaa/?bbb"
    [ ( URI "" "" ["/","aaa/",""] "?bbb" "", "" ) ]

relativeUriTest14 = relativeUriTest "14"
    "?y"
    [ ( URI "" "" [] "?y" "", "" ) ]

relativeUriTest15 = relativeUriTest "15"
    "g?y"
    [ ( URI "" "" ["g"] "?y" "", "" ) ]

relativeUriTest16 = relativeUriTest "16"
    "g;x?y#s"
    []


relativeUriTests = TestList
      [ relativeUriTest01, relativeUriTest02, relativeUriTest03,
        relativeUriTest04, relativeUriTest05, relativeUriTest06,
        relativeUriTest07, relativeUriTest08, relativeUriTest09,
        relativeUriTest10, relativeUriTest11, relativeUriTest12,
        relativeUriTest13, relativeUriTest14, relativeUriTest15,
        relativeUriTest16 ]


-- uriReference :: Parser Char URI

uriReferenceTest lab inp res =
    testParser ("uriReferenceTest"++lab) uriReference inp res

uriReferenceTest01 = uriReferenceTest "01"
    "http://example.org/aaa/bbb#ccc"
    [ ( URI "http:" "//example.org" ["/","aaa/","bbb"] "" "#ccc", "" ) ]

uriReferenceTest02 = uriReferenceTest "02"
    "mailto:local@domain.org"
    [ ( URI "mailto:" "local@domain.org" [] "" "", "" ) ]

uriReferenceTest03 = uriReferenceTest "03"
    "mailto:local@domain.org#frag"
    [ ( URI "mailto:" "local@domain.org" [] "" "#frag", "" ) ]

uriReferenceTest04 = uriReferenceTest "04"
    "HTTP://EXAMPLE.ORG/AAA/BBB#CCC"
    [ ( URI "HTTP:" "//EXAMPLE.ORG" ["/","AAA/","BBB"] "" "#CCC", "" ) ]

uriReferenceTest05 = uriReferenceTest "05"
    "http://example.org/aaa/bbb?qqq/rrr#ccc"
    [ ( URI "http:" "//example.org" ["/","aaa/","bbb"] "?qqq/rrr" "#ccc", "" ) ]

uriReferenceTest06 = uriReferenceTest "06"
    "//example.org/aaa/bbb#ccc"
    [ ( URI "" "//example.org" ["/","aaa/","bbb"] "" "#ccc", "" ) ]

uriReferenceTest07 = uriReferenceTest "07"
    "/aaa/bbb#ccc"
    [ ( URI "" "" ["/","aaa/","bbb"] "" "#ccc", "" ) ]

uriReferenceTest08 = uriReferenceTest "08"
    "bbb#ccc"
    [ ( URI "" "" ["bbb"] "" "#ccc", "" ) ]

uriReferenceTest09 = uriReferenceTest "09"
    "#ccc"
    [ ( URI "" "" [] "" "#ccc", "" ) ]

uriReferenceTest10 = uriReferenceTest "10"
    "#"
    [ ( URI "" "" [] "" "#", "" ) ]

uriReferenceTest11 = uriReferenceTest "11"
    "/"
    [ ( URI "" "" ["/",""] "" "", "" ) ]

uriReferenceTest12 = uriReferenceTest "12"
    "/aaa/#fff/ggg"
    [ ( URI "" "" ["/","aaa/",""] "" "#fff/ggg", "" ) ]

uriReferenceTest13 = uriReferenceTest "13"
    "/aaa/?bbb/ccc#fff/ggg"
    [ ( URI "" "" ["/","aaa/",""] "?bbb/ccc" "#fff/ggg", "" ) ]

uriReferenceTest14 = uriReferenceTest "14"
    "?y"
    [ ( URI "" "" [] "?y" "", "" ) ]

uriReferenceTest15 = uriReferenceTest "15"
    "g?y"
    [ ( URI "" "" ["g"] "?y" "", "" ) ]

uriReferenceTest16 = uriReferenceTest "16"
    "g;x?y#s"
    [ ( URI "" "" ["g;x"] "?y" "#s", "" ) ]

uriReferenceTest17 = uriReferenceTest "17"
    "http://example.123./aaa/bbb#ccc"
    [ ]

uriReferenceTest18 = uriReferenceTest "18"
    "http://example.org:/aaa/bbb#ccc"
    [ ( URI "http:" "//example.org:" ["/","aaa/","bbb"] "" "#ccc", "" ) ]

uriReferenceTest19 = uriReferenceTest "19"
    "http://example/Andr&#567;"
    [ ( URI "http:" "//example" ["/","Andr&"] "" "#567;", "" ) ]

uriReferenceTest20 = uriReferenceTest "20"
    "abc/def"
    [ ( URI "" "" ["abc/", "def"] "" "", "" ) ]

uriReferenceTest21 = uriReferenceTest "21"
    "../abc#def"
    [ ( URI "" "" ["../","abc"] "" "#def", "" ) ]

uriReferenceTest22 = uriReferenceTest "22"
    "file://meetings.example.com/cal#m1"
    [ ( URI "file:" "//meetings.example.com" ["/","cal"] "" "#m1", "" ) ]


uriReferenceTests = TestList
      [ uriReferenceTest01, uriReferenceTest02, uriReferenceTest03,
        uriReferenceTest04, uriReferenceTest05, uriReferenceTest06,
        uriReferenceTest07, uriReferenceTest08, uriReferenceTest09,
        uriReferenceTest10, uriReferenceTest11, uriReferenceTest12,
        uriReferenceTest13, uriReferenceTest14, uriReferenceTest15,
        uriReferenceTest16, uriReferenceTest17, uriReferenceTest18,
        uriReferenceTest19, uriReferenceTest20, uriReferenceTest21,
        uriReferenceTest22 ]

-- Check for ambiguous parse:
-- These tests don't force end-of-input, so potential ambiguous parses can be detected,

uriAmbiguousTest lab inp res =
    TestCase ( assertEqual ("uriAmbiguousTest"++lab++": "++inp) res (uriReference inp) )

uriAmbiguousTest01 = uriAmbiguousTest "01"
    "http://example.org/aaa/bbb#ccc"
    [ ( URI "http:" "//example.org" ["/","aaa/","bbb"] "" "#ccc", "" ) ]

uriAmbiguousTest02 = uriAmbiguousTest "02"
    "mailto:local@domain.org"
    [ ( URI "mailto:" "local@domain.org" [] "" "", "" ) ]

uriAmbiguousTest03 = uriAmbiguousTest "03"
    "mailto:local@domain.org#frag"
    [ ( URI "mailto:" "local@domain.org" [] "" "#frag", "" ) ]

uriAmbiguousTest04 = uriAmbiguousTest "04"
    "file://meetings.example.com/cal#m1"
    [ ( URI "file:" "//meetings.example.com" ["/","cal"] "" "#m1", "" ) ]


uriAmbiguousTests = TestList
  [ uriAmbiguousTest01, uriAmbiguousTest02, uriAmbiguousTest03, uriAmbiguousTest04 ]


-- All tests

allTests = TestList
  [ hostnameTests,
    ipv6Tests,
    absoluteUriTests,
    relativeUriTests,
    uriReferenceTests,
    uriAmbiguousTests
  ]

main = runTestTT allTests

hn     = hostnameTests
ipv6   = ipv6Tests
absu   = absoluteUriTests
absu01 = absoluteUriTest01
relu   = relativeUriTests
uref   = uriReferenceTests

runTestFile t = do
    h <- openFile "a.tmp" WriteMode
    runTestText (putTextToHandle h False) t
    hClose h
tf = runTestFile
tt = runTestTT
tp p s = runTestTT ( testParser "tp" p s [("<",">")] )

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
-- $Source: /file/cvsdev/HaskellUtils/ParseURITest.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: ParseURITest.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.13  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.12  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.11  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.10  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.9  2003/03/05 22:16:23  graham
-- URI code passes all unit tests
--
-- Revision 1.8  2003/03/05 14:47:45  graham
-- Relative URI code complete, not tested
-- Fixed a URI parser bug
--
-- Revision 1.7  2003/02/28 14:02:52  graham
-- A few new test cases
--
-- Revision 1.6  2003/02/27 23:33:54  graham
-- QName splitting tested OK
--
-- Revision 1.5  2003/02/27 20:29:53  graham
-- Fixed some more parser bugs.
-- All parser tests pass.
-- QName and relative path handling to do.
--
-- Revision 1.4  2003/02/27 18:48:05  graham
-- Fix URI parser bug.
-- Add more URI parser test cases.
--
-- Revision 1.3  2003/02/27 15:28:45  graham
-- Updated internal structure of parsed URI.
-- Passes parser unit tests
--
-- Revision 1.2  2003/02/27 13:54:30  graham
-- ParseURI module passes unit test
--
-- Revision 1.1  2003/02/20 19:45:07  graham
-- Add URI module and unit tests.
-- Code incomplete.
--
