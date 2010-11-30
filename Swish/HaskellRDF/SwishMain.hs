--------------------------------------------------------------------------------
--  $Id: SwishMain.hs,v 1.15 2004/02/11 17:37:02 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  SwishMain
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  Swish:  Semantic Web Inference Scripting in Haskell
--
--  This program is a simple skeleton for constructing Semantic Web [1]
--  inference tools in Haskell, using the RDF graph, Notation 3 parser
--  and Notation 3 formatter modules.
--
--  It might be viewed as a kind of embroyonic CWM [2] in Haskell, except
--  that the intent is that Haskell will be used as a primary language for
--  defining inferences.  As such, Swish is an open-ended toolkit for
--  constructing new special-purpose Semantic Web applications rather
--  than a closed, self-contained general-purpose SW application.
--  I anticipate that this module may be used as a starting point for
--  creating new programs rathar then as a complete program in its own right.
--  The functionality built into this code is selected with a view to testing
--  the Haskell modules for handling RDF rather than for performing any
--  particular application processing (though development as a tool with
--  some broader utility is not ruled out).  As such, it is part of
--  another experiment along the lines described in [3].
--
--  [1] Semantic werb: http://www.w3.org/2001/sw/
--  [2] CWM:           http://www.w3.org/2000/10/swap/doc/cwm.html
--  [3] Motivation:    http://www.w3.org/2000/10/swap/doc/Motivation.html
--  [4] Notation 3:    http://www.w3.org/DesignIssues/Notation3.html
--  [5] RDF:           http://www.w3.org/RDF/
--
--  For command line details, see 'usageText' below.
--
--  TODO:
--  + Add RDF/XML input and output
--  + Add N-triples input and output
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.SwishMain(runSwish,runSwishArgs) where

import Swish.HaskellRDF.SwishCommands
    ( swishFormat
    , swishInput
    , swishOutput
    , swishMerge
    , swishCompare
    , swishGraphDiff
    , swishScript
    )

import Swish.HaskellRDF.SwishMonad
    ( SwishStateIO, SwishState(..)
    , emptyState
    , SwishFormat(..)
    , swishError
    , reportLines 
    )

import Swish.HaskellUtils.ListHelpers
    ( breakAll )

import Control.Monad.State
    ( execStateT )

import Data.Char
    ( isSpace )

import Control.Monad
    ( when )

import System.Exit
    ( ExitCode(ExitSuccess) )

------------------------------------------------------------
--  Command line description
------------------------------------------------------------

usageText :: [[Char]]
usageText =
    [ "Swish 0.2.1"
    , "Read, merge, write, compare and process RDF graphs."
    , ""
    , "Usage: swish option option ..."
    , ""
    , "where the options are processed from left to right, and may be"
    , "any of the following:"
    , "-?        display this message."
    , "-n3       use Notation3 format for subsequent input and output."
    , "-i[=file] read file in selected format into the graph workspace,"
    , "          replacing any existing graph."
    , "-m[=file] merge file in selected format with the graph workspace."
    , "-c[=file] compare file in selected format with the graph workspace."
    , "-d[=file] show graph differences between the file in selected"
    , "          format and the graph workspace.  Differences are displayed"
    , "          to the standard output stream."
    , "-o[=file] write the graph workspace to a file in the selected format."
    , "-s[=file] read and execute Swish script commands from the named file."
    , ""
    , "    If an optional filename value is omitted, the standard input"
    , "    or output stream is used, as appropriate."
    , ""
    , "Exit status codes:"
    , "Success - operation completed successfully/graphs compare equal"
    , "1 - graphs compare different"
    , "2 - input data format error"
    , "3 - file access problem"
    , "4 - command line error"
    , "5 - script file execution error"
    , ""
    , "Examples:"
    , ""
    , "swish -n3 -i=file"
    , "    read file as Notation3, and report any syntax errors."
    , "swich -n3 -i=file1 -c=file2"
    , "    read file1 and file2 as notation3, report any syntax errors, and"
    , "    if both are OK, compare the resulting graphs to indicate whether"
    , "    or not they are equivalent."
    , "swish -n3 -i=file1 -o=file2"
    , "    read file1 as Notation3, report any syntax errors, and output the"
    , "    resulting graph as reformatted Notation3.  (The output may be"
    , "    unedifying, but is intended to be used to test round-tripping"
    , "    of Notation 3 data.  The Notation3 formatter may be improved in"
    , "    subsequent versions.)"
    ]

------------------------------------------------------------
--  Swish command line interpreter
------------------------------------------------------------
--
--  This is a composite monad combining some state with an IO
--  Monad.  "lift" allows a pure IO monad to be used as a step
--  of the computation.
--
--  sequence_ is a Monad sequencer, returning a new monad that
--  executes members of a list in turn, passing state along the
--  chain.
--
swishCommands :: [String] -> SwishStateIO ()
swishCommands args =
    do  { sequence_ (map swishCommand args)
        }

swishCommand :: String -> SwishStateIO ()
swishCommand cmd =
        let
            (nam,more) = break (=='=') cmd
            arg        = drop 1 more
        in
        case nam of
            ""      -> return ()    -- do nothing
            "-?"    -> swishHelp
            "-n3"   -> swishFormat N3
            "-i"    -> swishInput arg
            "-m"    -> swishMerge arg
            "-c"    -> swishCompare arg
            "-d"    -> swishGraphDiff arg
            "-o"    -> swishOutput arg
            "-s"    -> swishScript arg
            _       -> swishError ("Invalid command line element: "++cmd) 4

swishHelp :: SwishStateIO ()
swishHelp = reportLines usageText

------------------------------------------------------------
--  Interactive test function (e.g. for use in Hugs)
------------------------------------------------------------

runSwish :: String -> IO ExitCode
runSwish cmdline =
    do  { let args = breakAll isSpace cmdline
        ; ec <- runSwishArgs args
        ; when (ec /= ExitSuccess) (putStrLn $ "Swish exit: "++show ec)
        ; return ec
        }

runSwishArgs :: [String] -> IO ExitCode
runSwishArgs args =
    do  { state <- execStateT (swishCommands args) emptyState
        ; return $ exitcode state
        }

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
-- $Source: /file/cvsdev/HaskellRDF/SwishMain.hs,v $
-- $Author: graham $
-- $Revision: 1.15 $
-- $Log: SwishMain.hs,v $
-- Revision 1.15  2004/02/11 17:37:02  graham
-- Update for Swish 0.2.1
--
-- Revision 1.14  2004/02/11 14:19:36  graham
-- Add graph-difference option to Swish
--
-- Revision 1.13  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.12  2003/12/20 17:07:48  graham
-- Display swish version number in usage message
--
-- Revision 1.11  2003/12/20 14:34:21  graham
-- Update command line options help message.
--
-- Revision 1.10  2003/12/19 21:29:33  graham
-- Minor edits
--
-- Revision 1.9  2003/12/19 16:34:12  graham
-- Add 'test' function to run SwishTest script
--
-- Revision 1.8  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.7  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.6  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.5  2003/12/01 18:51:38  graham
-- Described syntax for Swish script.
-- Created Swish scripting test data.
-- Edited export/import lists in Swish main program modules.
--
-- Revision 1.4  2003/09/24 18:50:53  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.3  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.2  2003/05/29 12:39:49  graham
-- Improved error handling for stand-alone swish program
--
-- Revision 1.1  2003/05/29 11:52:41  graham
-- Juggle Swish code:  SwishMain.hs is main program logic, with
-- Swish.hs and SwishTest.hs being alternative "Main" modules for
-- the real program and test harness respectively.
