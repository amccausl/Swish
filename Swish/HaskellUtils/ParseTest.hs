--------------------------------------------------------------------------------
--  $Id: ParseTest.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ParseTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
-- This module contains test cases for module Parse functions.
--
--------------------------------------------------------------------------------

-- WNH RIP OUT module Swish.HaskellUtils.ParseTest where

import Test.HUnit

import Swish.HaskellUtils.Parse

testParser :: ( Show a, Show b, Eq a, Eq b ) => String -> Parser a b -> [a] -> [(b,[a])] -> Test
testParser s p i r =
    TestCase ( assertEqual s r ( p i ) )

noResult :: [ ( (),[Char] ) ]
noResult = []

testParseReturn1 = testParser "parseReturn1" (parseReturn "FOO") ""   [("FOO","")]
testParseReturn2 = testParser "parseReturn2" (parseReturn "BAR") "**" [("BAR","**")]

testParseItem1 = testParser "parseItem1" (parseItem (=='1')) "2"   []
testParseItem2 = testParser "parseItem2" (parseItem (=='2')) "abc" []
testParseItem3 = testParser "parseItem3" (parseItem (=='3')) "3"   [('3',"")]
testParseItem4 = testParser "parseItem4" (parseItem (=='4')) "456" [('4',"56")]
testParseItem5 = testParser "parseItem5" (parseItem (=='5')) ""    []

testParseAlpha1 = testParser "parseAlpha1" parseAlpha "123" []
testParseAlpha2 = testParser "parseAlpha2" parseAlpha "a**" [('a',"**")]
testParseAlpha3 = testParser "parseAlpha3" parseAlpha "z//" [('z',"//")]
testParseAlpha4 = testParser "parseAlpha4" parseAlpha "Abc" [('A',"bc")]
testParseAlpha5 = testParser "parseAlpha5" parseAlpha "Zyx" [('Z',"yx")]

testParseDigit1 = testParser "parseDigit1" parseDigit "ab"   []
testParseDigit2 = testParser "parseDigit2" parseDigit "1ab"  [('1',"ab")]
testParseDigit3 = testParser "parseDigit3" parseDigit "9ab"  [('9',"ab")]
testParseDigit4 = testParser "parseDigit4" parseDigit "55ab" [('5',"5ab")]

testParseAlphaNum1 = testParser "parseAlphaNum1" parseAlphaNum "..." []
testParseAlphaNum2 = testParser "parseAlphaNum2" parseAlphaNum "a**" [('a',"**")]
testParseAlphaNum3 = testParser "parseAlphaNum3" parseAlphaNum "z//" [('z',"//")]
testParseAlphaNum4 = testParser "parseAlphaNum4" parseAlphaNum "Abc" [('A',"bc")]
testParseAlphaNum5 = testParser "parseAlphaNum5" parseAlphaNum "Zyx" [('Z',"yx")]
testParseAlphaNum6 = testParser "parseAlphaNum6" parseAlphaNum "123" [('1',"23")]
testParseAlphaNum7 = testParser "parseAlphaNum7" parseAlphaNum "987" [('9',"87")]

parseAltParser = parseAlt parseDigit parseAlpha
testParseAlt1 = testParser "parseAlt1" parseAltParser "..." []
testParseAlt2 = testParser "parseAlt2" parseAltParser "123" [('1',"23")]
testParseAlt3 = testParser "parseAlt3" parseAltParser "ABC" [('A',"BC")]

parseOneParser = parseOne parseDigit parseAlpha
testParseOne1 = testParser "parseOne1" parseOneParser "###" []
testParseOne2 = testParser "parseOne2" parseOneParser "123" [('1',"23")]
testParseOne3 = testParser "parseOne3" parseOneParser "ABC" [('A',"BC")]

parseOptParser = parseOptional ( parseDigit `parseApply` makeList )
testParseOpt1 = testParser "parseOpt1" parseOptParser "###" [([],"###")]
testParseOpt2 = testParser "parseOpt2" parseOptParser "123" [(['1'],"23")]
testParseOpt3 = testParser "parseOpt3" parseOptParser "ABC" [([],"ABC")]

parseSeqParser
  = ( parseAlpha >*> p1 ) `parseApply` toList
    where
    p1 = ( ( parseItem (== '-') ) >*> p2 )   `parseApply` toList
    p2 = ( parseDigit >*> (parseReturn []) ) `parseApply` toList

testParseSeq1 = testParser "parseSeq1" parseSeqParser "???"    []
testParseSeq2 = testParser "parseSeq2" parseSeqParser "A-1>>>" [("A-1",">>>")]
testParseSeq3 = testParser "parseSeq3" parseSeqParser "Z-9"    [("Z-9","")]
testParseSeq4 = testParser "parseSeq4" parseSeqParser "1-A>>>" []
testParseSeq5 = testParser "parseSeq5" parseSeqParser "A#1>>>" []

-- parseMany   :: Parser a b -> Parser a [b]
parseManyParser = parseMany parseDigit

testParseMany1 = testParser "parseMany1" parseManyParser "ab"      [("","ab")]
testParseMany2 = testParser "parseMany2" parseManyParser "2ab"     [("2","ab")]
testParseMany3 = testParser "parseMany3" parseManyParser "3"       [("3","")]
testParseMany4 = testParser "parseMany4" parseManyParser "444"     [("444","")]
testParseMany5 = testParser "parseMany5" parseManyParser "54321ab" [("54321","ab")]
testParseMany6 = testParser "parseMany6" parseManyParser ""        [("","")]

-- parseSequence :: ( a -> Bool , a -> Bool) -> Parser a [a]
parseIdParser = parseSequence ( isAlpha, isAlphaNum )

testParseId1 = testParser "parseId1" parseIdParser "123"     []
testParseId2 = testParser "parseId2" parseIdParser "b2z9"    [("b2z9","")]
testParseId3 = testParser "parseId3" parseIdParser "c"       [("c","")]
testParseId4 = testParser "parseId4" parseIdParser "d444**"  [("d444","**")]
testParseId5 = testParser "parseId5" parseIdParser "efg55.6" [("efg55",".6")]
testParseId6 = testParser "parseId6" parseIdParser ""        []

-- infixr 5 >:>
-- (>:>) :: Parser a b -> Parser a [b] -> Parser a [b]

-- skip whitespace then use supplied parser
skipWS :: Parser Char a -> Parser Char a
skipWS = skipToken parseWS

parseIdent :: Parser Char String
parseIdent = parseSequence ( isAlpha, isAlphaNum )

parseNumber :: Parser Char String
parseNumber = parseSequence ( isDigit, isDigit )

-- type Parser a b = [a] -> [(b,[a])] -- e.g. [Char] -> [(Result,[Char])]
parseOp :: String -> Parser Char String
parseOp op = foldr (>:>) (parseReturn "") [ parseItem (==c) | c <- op ]

parseExprParser = (skipWS parseIdent)     >:>
                  (skipWS (parseOp ":=")) >:>
                  (skipWS parseNumber)    >:>
                  (skipWS (parseOp "+"))  >:>
                  (skipWS parseNumber )   >:>
                  (skipWS (parseOp ";"))  >:>
                  (skipWS (parseReturn []))

testParseExpr1 = testParser "parseExpr1" parseExprParser "// yyy" []
testParseExpr2 = testParser "parseExpr2" parseExprParser "A:=1+1;"
                            [(["A",":=","1","+","1",";"],"")]
testParseExpr3 = testParser "parseExpr3" parseExprParser " B := 2 + 2 ; "
                            [(["B",":=","2","+","2",";"],"")]
testParseExpr4 = testParser "parseExpr4" parseExprParser "CCC := 33+34 ; // xxx"
                            [(["CCC",":=","33","+","34",";"],"// xxx")]
testParseExpr5 = testParser "parseExpr5" parseExprParser "D5 := 5 + 55 ;//yyy"
                            [(["D5",":=","5","+","55",";"],"//yyy")]
testParseExpr6 = testParser "parseExpr6" parseExprParser "D5 :* 5 + 55 ;//yyy" []
testParseExpr7 = testParser "parseExpr7" parseExprParser "" []

parseExprLstParser = (skipWS parseIdent)     >++>
                     (skipWS (parseOp ":=")) >++>
                     (skipWS parseNumber)    >++>
                     (skipWS (parseOp "+"))  >++>
                     (skipWS parseNumber )   >++>
                     (skipWS (parseOp ";"))  >++>
                     (skipWS (parseReturn []))

testParseExprLst1 = testParser "parseExprLst1" parseExprLstParser
                            "// yyy"
                            []
testParseExprLst2 = testParser "parseExprLst2" parseExprLstParser
                            "A:=1+1;"
                            [("A:=1+1;","")]
testParseExprLst3 = testParser "parseExprLst3" parseExprLstParser
                            " B := 2 + 2 ; "
                            [("B:=2+2;","")]
testParseExprLst4 = testParser "parseExprLst4" parseExprLstParser
                            "CCC := 33+34 ; // xxx"
                            [("CCC:=33+34;","// xxx")]
testParseExprLst5 = testParser "parseExprLst5" parseExprLstParser
                            "D5 := 5 + 55 ;//yyy"
                            [("D5:=5+55;","//yyy")]
testParseExprLst6 = testParser "parseExprLst6" parseExprLstParser
                            "D5 :* 5 + 55 ;//yyy"
                            []
testParseExprLst7 = testParser "parseExprLst7" parseExprLstParser
                            ""
                            []

makeListParser = parseManyParser `parseApply` makeList

testMakeList1 = testParser "testMakeList1" makeListParser "ab"  [([""],"ab")]
testMakeList2 = testParser "testMakeList2" makeListParser "2ab" [(["2"],"ab")]

catListParser = makeListParser `parseApply` catList
catExprParser = parseExprParser `parseApply` catList

testCatList1 = testParser "testCatList1" catListParser "ab"  [("","ab")]
testCatList2 = testParser "testCatList2" catListParser "2ab" [("2","ab")]
testCatList3 = testParser "testCatList3" catExprParser
                            "D5 := 5 + 55 ;//yyy"   [("D5:=5+55;","//yyy")]
testCatList4 = testParser "testCatList4" catExprParser
                            "D5 :* 5 + 55 ;//yyy"   []
testCatList5 = testParser "testCatList5" catExprParser
                            ""                      []

testParseNull1 = testParser "parseNull1"
                 parseNull "a" noResult
testParseNull2 = testParser "parseNull2"
                 parseNull "" [((),"")]

testIsValid :: String -> Parser a b -> Bool -> [a] -> Test
testIsValid label parser match input =
    TestCase ( assertEqual label match ( (isValid parser) input ) )

testParseEnd1   = testParser "parseEnd1" (parseEnd "") ""   [("",[])]
testParseEnd2   = testParser "parseEnd2" (parseEnd "") "xx" []

testIsValid1 = testIsValid "testIsValid1" parseExprParser False "// yyy"
testIsValid2 = testIsValid "testIsValid2" parseExprParser True  "A:=1+1;"
testIsValid3 = testIsValid "testIsValid3" parseExprParser True  " B := 2 + 2 ; "
testIsValid4 = testIsValid "testIsValid4" parseExprParser False "CCC := 33+34 ; // xxx"
testIsValid5 = testIsValid "testIsValid5" parseExprParser False "D5 := 5 + 55 ;//yyy"
testIsValid6 = testIsValid "testIsValid6" parseExprParser False "D5 :* 5 + 55 ;//yyy"
testIsValid7 = testIsValid "testIsValid7" parseExprParser False ""

allTests = TestList
  [ testParseReturn1, testParseReturn2,
    testParseItem1,  testParseItem2,  testParseItem3,  testParseItem4,  testParseItem5,
    testParseAlpha1, testParseAlpha2, testParseAlpha3, testParseAlpha4, testParseAlpha5,
    testParseDigit1, testParseDigit2, testParseDigit3, testParseDigit4,
    testParseAlphaNum1, testParseAlphaNum2, testParseAlphaNum3, testParseAlphaNum4,
                        testParseAlphaNum5, testParseAlphaNum6, testParseAlphaNum7,
    testParseAlt1, testParseAlt2, testParseAlt3,
    testParseOne1, testParseOne2, testParseOne3,
    testParseOpt1, testParseOpt2, testParseOpt3,
    testParseSeq1, testParseSeq2, testParseSeq3, testParseSeq4, testParseSeq5,
    testParseMany1, testParseMany2, testParseMany3, testParseMany4,
                    testParseMany5, testParseMany6,
    testParseId1,   testParseId2,   testParseId3,   testParseId4,
                    testParseId5,   testParseId6,
    testParseExpr1, testParseExpr2, testParseExpr3, testParseExpr4,
                    testParseExpr5, testParseExpr6, testParseExpr7,
    testParseExprLst1, testParseExprLst2, testParseExprLst3,
                       testParseExprLst4, testParseExprLst5,
                       testParseExprLst6, testParseExprLst7,
    testMakeList1,  testMakeList2,
    testCatList1,   testCatList2,   testCatList3,   testCatList4,
    testCatList5,
    testParseNull1, testParseNull2,
    testIsValid1,   testIsValid2,   testIsValid3,   testIsValid4,
                    testIsValid5,   testIsValid6,   testIsValid7,
    testParseEnd1,  testParseEnd2 ]

main = runTestTT allTests

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
-- $Source: /file/cvsdev/HaskellUtils/ParseTest.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: ParseTest.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.12  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.11  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.10  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.9  2003/05/29 13:04:42  graham
-- All tests now compile and pass as stand-alone programs compiled
-- using GHC.  Added batch files to compile programs and run tests.
--
-- Revision 1.8  2003/02/27 13:54:30  graham
-- ParseURI module passes unit test
--
-- Revision 1.7  2003/02/27 00:29:53  graham
-- Add additional parse functions for lists of values
--
-- Revision 1.6  2003/02/20 19:44:37  graham
-- Added isValid and parseNull to Pase module.
-- All tests pass.
--
-- Revision 1.5  2003/02/19 20:20:50  graham
-- Some small parser enhancements
--
-- Revision 1.4  2003/02/19 18:45:00  graham
-- Parser unit tests done.
-- Worked out some details for simplified parser construction.
--
-- Revision 1.3  2003/02/13 16:14:14  graham
-- >*> function works
--
-- Revision 1.2  2003/02/13 15:09:47  graham
-- Initial parser tests all pass.
--
-- Revision 1.1  2003/02/13 11:31:18  graham
-- Separate parser tests from parser code
--
