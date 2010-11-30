--------------------------------------------------------------------------------
--  $Id: SwishTest.hs,v 1.10 2004/01/06 13:53:10 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  SwishTest
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  SwishTest:  Test cases for Swish program.
--
--------------------------------------------------------------------------------

--  WNH RIP OUT   module Swish.HaskellRDF.SwishTest where

import System.Exit

import System.Time

import Test.HUnit
      ( Test(..), Assertable(..),
        assertEqual, runTestTT, runTestText, putTextToHandle )

import Swish.HaskellRDF.SwishMain


------------------------------------------------------------
--  Interactive test cases
------------------------------------------------------------

testSwish :: String -> IO Bool
testSwish cmdline =
    do  { exitcode <- runSwish cmdline
        -- ; putStr $ "Exit status: "++(show exitcode)
        ; return $ exitcode == ExitSuccess
        }

swishTestCase :: String -> Test
swishTestCase cmdline = TestCase ( assert $ testSwish cmdline )

test1 = runSwish "-?"
test2 = runSwish "-!not=validcommand"

test3 = swishTestCase "-i=Data/N3TestGenReport.n3"
test4 = swishTestCase "-i=Data/sbp-data.n3"
test5 = swishTestCase "-i=Data/Simple.n3 "
test6 = swishTestCase "-i=Data/Simple.n3 -o=Data/Simple.tmp"
test7 = swishTestCase "-i=Data/Simple.n3 -c=Data/Simple.n3"
test8 = swishTestCase "-i=Data/Simple.n3 -c=Data/Simple.tmp"
test9 = swishTestCase "-i=Data/Simple.tmp -c=Data/Simple.tmp"

test10a = swishTestCase "-i=Data/Simple3.n3"
test10b = swishTestCase "-i=Data/Simple3.n3 -o"

test10 = swishTestCase "-i=Data/Simple3.n3 -o=Data/Simple3.tmp"
test11 = swishTestCase "-i=Data/Simple3.n3 -c=Data/Simple3.n3"
test12 = swishTestCase "-i=Data/Simple3.n3 -c=Data/Simple3.tmp"
test13 = swishTestCase "-i=Data/Simple3.tmp -c=Data/Simple3.tmp"

test20a = swishTestCase "-i=Data/N3TestGenReport.n3"
test20b = swishTestCase "-i=Data/N3TestGenReport.n3 -o"

test20 = swishTestCase "-i=Data/N3TestGenReport.n3 -o=Data/N3TestGenReport.tmp"
test21 = swishTestCase "-i=Data/N3TestGenReport.n3 -c=Data/N3TestGenReport.n3"
test22 = swishTestCase "-i=Data/N3TestGenReport.n3 -c=Data/N3TestGenReport.tmp"
test23 = swishTestCase "-i=Data/N3TestGenReport.tmp -c=Data/N3TestGenReport.tmp"

test30 = swishTestCase "-i=Data/Merge1.n3 -m=Data/Merge2.n3 -c=Data/Merge3.n3"

test31 = swishTestCase "-s=Swishtest.ss"

tests1a = swishTestCase "-i=Data/Simple2.n3 -o=Data/Simple2.tmp"
tests1b = swishTestCase "-i=Data/Simple2.n3 -c=Data/Simple2.tmp"

allTests = TestList
    [ test3
    , test4
    , test5
    , test6
    , test7
    , test8
    , test9
    , test10
    , test11
    , test12
    , test13
    , tests1a
    , tests1b
    , test20
    , test21
    , test22
    , test23
    , test30
    , test31
    ]

runTest t =
    do  { st <- getClockTime
        ; putStr $ "Test started:  "++show st++"\n"
        ; runTestTT t
        ; ft <- getClockTime
        ; putStr $ "Test finished: "++show ft++"\n"
        ; let et = diffClockTimes ft st
        ; return et
        ; putStr $ "Test duration: "++show et++"\n"
        }

testAll = runTest allTests

tt   = runTest
t20a = runTest test20a
t20b = runTest test20b

main = testAll

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
-- $Source: /file/cvsdev/HaskellRDF/SwishTest.hs,v $
-- $Author: graham $
-- $Revision: 1.10 $
-- $Log: SwishTest.hs,v $
-- Revision 1.10  2004/01/06 13:53:10  graham
-- Created consolidated test harness (SwishTestAll.hs)
--
-- Revision 1.9  2003/09/24 18:50:53  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.8  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.7  2003/05/29 11:53:31  graham
-- Juggle Swish code:  SwishMain.hs is main program logic, with
-- Swish.hs and SwishTest.hs being alternative "Main" modules for
-- the real program and test harness respectively.
--
-- Revision 1.6  2003/05/29 10:49:08  graham
-- Added and tested merge option (-m) for Swish program
--
-- Revision 1.5  2003/05/29 01:50:56  graham
-- More performance tuning, courtesy of GHC profiler.
-- All modules showing reasonable performance now.
--
-- Revision 1.4  2003/05/29 00:57:37  graham
-- Resolved swish performance problem, which turned out to an inefficient
-- method used by the parser to add arcs to a graph.
--
-- Revision 1.3  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.2  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.1  2003/05/23 00:03:55  graham
-- Added HUnit test module for swish program.
-- Greatly enhanced N3Formatter tests
--
