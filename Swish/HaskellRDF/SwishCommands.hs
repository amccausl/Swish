--------------------------------------------------------------------------------
--  $Id: SwishCommands.hs,v 1.14 2004/02/11 14:19:36 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  SwishCommands
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  SwishCommands:  functions to deal with indivudual Swish command options.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.SwishCommands
    ( swishFormat
    , swishInput
    , swishOutput
    , swishMerge
    , swishCompare
    , swishGraphDiff
    , swishScript
    )
where

import Swish.HaskellRDF.SwishMonad
    ( SwishStateIO, SwishState(..)
    , setFormat, setGraph
    , resetInfo, resetError, setExitcode
    , SwishFormat(..)
    , swishError
    , reportLine
    )

import Swish.HaskellRDF.SwishScript
    ( parseScriptFromString
    )

import Swish.HaskellRDF.GraphPartition
    ( GraphPartition(..)
    , partitionGraph, comparePartitions
    , partitionShowP
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFGraph, merge )

import Swish.HaskellRDF.N3Formatter
    ( formatGraphAsShowS )

import Swish.HaskellRDF.N3Parser
    ( parseN3fromString )

import Swish.HaskellRDF.GraphClass
    ( LDGraph(..)
    , Label(..)
    )

import Swish.HaskellUtils.ErrorM( ErrorM(..) )

import System.IO
    ( Handle, openFile, IOMode(..)
    , hPutStr, hPutStrLn, hClose, hGetContents
    , hIsReadable, hIsWritable
    , stdin, stdout, stderr
    )

import Control.Monad.Trans( MonadTrans(..) )

import Control.Monad.State
    ( modify, gets
    )

import Data.Maybe
    ( Maybe(..), isJust, fromJust )

import Control.Monad
    ( when )

import System.Exit
    ( ExitCode(..) )

import System.IO.Error

------------------------------------------------------------
--  Set file format to supplied value
------------------------------------------------------------

swishFormat :: SwishFormat -> SwishStateIO ()
swishFormat fmt = modify $ setFormat fmt

------------------------------------------------------------
--  Read graph from named file
------------------------------------------------------------

swishInput :: String -> SwishStateIO ()
swishInput fnam =
    do  { maybegraph <- swishReadGraph fnam
        ; case maybegraph of
            Just g    -> modify $ setGraph g
            _         -> return ()
        }

------------------------------------------------------------
--  Merge graph from named file
------------------------------------------------------------

swishMerge :: String -> SwishStateIO ()
swishMerge fnam =
    do  { maybegraph <- swishReadGraph fnam
        ; case maybegraph of
            Just g    -> modify $ mergeGraph g
            _         -> return ()
        }

mergeGraph gr state = state { graph = newgr }
    where
        newgr = merge gr (graph state)

------------------------------------------------------------
--  Compare graph from named file
------------------------------------------------------------

swishCompare :: String -> SwishStateIO ()
swishCompare fnam =
    do  { maybegraph <- swishReadGraph fnam
        ; case maybegraph of
            Just g    -> compareGraph g
            _         -> return ()
        }

compareGraph :: RDFGraph -> SwishStateIO ()
compareGraph gr =
    do  { oldgr <- gets graph
        ; let exitCode = if gr == oldgr then ExitSuccess
                                        else ExitFailure 1
        ; modify $ setExitcode exitCode
        }

------------------------------------------------------------
--  Display graph differences from named file
------------------------------------------------------------

swishGraphDiff :: String -> SwishStateIO ()
swishGraphDiff fnam =
    do  { maybegraph <- swishReadGraph fnam
        ; case maybegraph of
            Just g    -> diffGraph g
            _         -> return ()
        }

diffGraph :: RDFGraph -> SwishStateIO ()
diffGraph gr =
    do  { oldgr <- gets graph
        ; let p1 = partitionGraph (getArcs oldgr)
        ; let p2 = partitionGraph (getArcs gr)
        ; let diffs = comparePartitions p1 p2
        ; maybehandleclose <- swishWriteFile "" -- null filename -> stdout
        ; case maybehandleclose of
            Just (h,c) ->
                do  { swishOutputDiffs "" h diffs
                    ; if c then lift $ hClose h else return ()
                    }
            _          -> return ()
        }

swishOutputDiffs :: (Label lb) =>
    String -> Handle
    -> [(Maybe (GraphPartition lb),Maybe (GraphPartition lb))]
    -> SwishStateIO ()
swishOutputDiffs fnam hnd diffs =
    do  { lift $ hPutStrLn hnd ("Graph differences: "++show (length diffs))
        ; sequence_ $ map (swishOutputDiff fnam hnd) (zip [1..] diffs)
        }

swishOutputDiff :: (Label lb) =>
    String -> Handle
    -> (Int,(Maybe (GraphPartition lb),Maybe (GraphPartition lb)))
    -> SwishStateIO ()
swishOutputDiff fnam hnd (diffnum,(part1,part2)) =
    do  { lift $ hPutStrLn hnd ("---- Difference "++show diffnum++" ----")
        ; lift $ hPutStr hnd "Graph 1:"
        ; swishOutputPart fnam hnd part1
        ; lift $ hPutStr hnd "Graph 2:"
        ; swishOutputPart fnam hnd part2
        }

swishOutputPart :: (Label lb) =>
    String -> Handle -> Maybe (GraphPartition lb) -> SwishStateIO ()
swishOutputPart fnam hnd part =
    do  { let out = case part of
                Just p  -> partitionShowP "\n" p
                Nothing -> "\n(No arcs)"
        ; lift $ hPutStrLn hnd out
        }

------------------------------------------------------------
--  Execute script from named file
------------------------------------------------------------

swishScript :: String -> SwishStateIO ()
swishScript fnam =
    do  { scs <- swishReadScript fnam
        ; sequence_ (map swishCheckResult scs)
        }

swishReadScript :: String -> SwishStateIO [SwishStateIO ()]
swishReadScript fnam =
    do  { maybefile <- swishOpenFile fnam
        ; case maybefile of
            Just (h,i) ->
                do  { res <- swishParseScript fnam i
                    ; lift $ hClose h
                    ; return res
                    }
            _          -> return []
        }

swishParseScript ::
    String -> String -> SwishStateIO [SwishStateIO ()]
swishParseScript fnam inp =
    do  { let base = if null fnam then Nothing else Just fnam
        ; let sres = parseScriptFromString base inp
        ; case sres of
            Error err ->
                do  { swishError ("Script syntax error in file "++fnam++": "++err) 2
                    ; return []
                    }
            Result scs -> return scs
        }

swishCheckResult :: SwishStateIO () -> SwishStateIO ()
swishCheckResult swishcommand =
    do  { swishcommand
        ; er <- gets errormsg
        ; when (isJust er) $
            do  { swishError (fromJust er) 5
                ; modify $ resetError
                }
        ; ms <- gets infomsg
        ; when (isJust ms) $
            do  { reportLine (fromJust ms)
                ; modify $ resetInfo
                }
        }

------------------------------------------------------------
--  Output graph to named file
------------------------------------------------------------

swishOutput :: String -> SwishStateIO ()
swishOutput fnam =
    do  { maybehandleclose <- swishWriteFile fnam
        ; case maybehandleclose of
            Just (h,c) ->
                do  { swishOutputGraph fnam h
                    ; if c then lift $ hClose h else return ()
                    }
            _          -> return ()
        }

swishOutputGraph :: String -> Handle -> SwishStateIO ()
swishOutputGraph fnam hnd =
    do  { fmt <- gets $ format
        ; case fmt of
            N3        -> swishFormatN3 fnam hnd
            _         -> swishError
                         ("Unsupported file format: "++(show fmt)) 4
        }

swishFormatN3 :: String -> Handle -> SwishStateIO ()
swishFormatN3 fnam hnd =
    do  { out <- gets $ formatGraphAsShowS . graph
        ; lift $ hPutStr hnd (out "")
        }

------------------------------------------------------------
--  Common input functions
------------------------------------------------------------
--
--  Keep the logic separate for reading file data and
--  parsing it to an RDF graph value.

swishReadGraph :: String -> SwishStateIO (Maybe RDFGraph)
swishReadGraph fnam =
    do  { maybefile <- swishOpenFile fnam
        ; case maybefile of
            Just (h,i) ->
                do  { res <- swishParse fnam i
                    ; lift $ hClose h
                    ; return res
                    }
            _          -> return Nothing
        }

-- Open and read file, returning its handle and content, or Nothing
-- WARNING:  the handle must not be closed until input is fully evaluated
swishOpenFile :: String -> SwishStateIO (Maybe (Handle,String))
swishOpenFile fnam =
    do  { (hnd,hop) <- lift $
            if null fnam then
                return (stdin,True)
            else
            do  { o <- try (openFile fnam ReadMode)
                ; case o of
                    Left  e -> return (stdin,False)
                    Right h -> return (h,True)
                }
        ; hrd <- lift $ hIsReadable hnd
        ; res <- if hop && hrd then
            do  {
                ; fc <- lift $ hGetContents hnd
                ; return $ Just (hnd,fc)
                }
            else
            do  { lift $ hClose hnd
                ; swishError ("Cannot read file: "++fnam) 3
                ; return Nothing
                }
        ; return res
        }

swishParse :: String -> String -> SwishStateIO (Maybe RDFGraph)
swishParse fnam inp =
    do  { fmt <- gets $ format
        ; case fmt of
            N3        -> swishParseN3 fnam inp
            _         ->
                do  { swishError ("Unsupported file format: "++(show fmt)) 4
                    ; return Nothing
                    }
        }

swishParseN3 :: String -> String -> SwishStateIO (Maybe RDFGraph)
swishParseN3 fnam inp =
    do  { let pres = parseN3fromString inp
        ; case pres of
            Error err ->
                do  { swishError ("N3 syntax error in file "++fnam++": "++err) 2
                    ; return Nothing
                    }
            Result gr -> return $ Just gr
        }

--  Open file for writing, returning its handle, or Nothing
--  Also returned is a flag indicating whether or not the
--  handled should be closed when writing is done (if writing
--  to standard output, the handle should not be closed as the
--  run-time system should deal with that).
swishWriteFile :: String -> SwishStateIO (Maybe (Handle,Bool))
swishWriteFile fnam =
    do  { (hnd,hop,cls) <- lift $
            if null fnam then
                return (stdout,True,False)
            else
            do  { o <- try (openFile fnam WriteMode)
                ; case o of
                    Left  e -> return (stderr,False,False)
                    Right h -> return (h,True,True)
                }
        ; hwt <- lift $ hIsWritable hnd
        ; if hop && hwt then
                return $ Just (hnd,cls)
            else
            do  { if cls then lift $ hClose hnd else return ()
                ; swishError ("Cannot write file: "++fnam) 3
                ; return Nothing
                }
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
-- $Source: /file/cvsdev/HaskellRDF/SwishCommands.hs,v $
-- $Author: graham $
-- $Revision: 1.14 $
-- $Log: SwishCommands.hs,v $
-- Revision 1.14  2004/02/11 14:19:36  graham
-- Add graph-difference option to Swish
--
-- Revision 1.13  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.12  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.11  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.10  2003/12/01 18:51:38  graham
-- Described syntax for Swish script.
-- Created Swish scripting test data.
-- Edited export/import lists in Swish main program modules.
--
-- Revision 1.9  2003/09/24 18:50:53  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.8  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.7  2003/05/29 12:39:49  graham
-- Improved error handling for stand-alone swish program
--
-- Revision 1.6  2003/05/29 10:49:08  graham
-- Added and tested merge option (-m) for Swish program
--
-- Revision 1.5  2003/05/29 00:57:37  graham
-- Resolved swish performance problem, which turned out to an inefficient
-- method used by the parser to add arcs to a graph.
--
-- Revision 1.4  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.3  2003/05/23 00:03:55  graham
-- Added HUnit test module for swish program.
-- Greatly enhanced N3Formatter tests
--
-- Revision 1.2  2003/05/21 13:34:13  graham
-- Various N3 parser bug fixes.
-- Need to fix handling of :name terms.
--
-- Revision 1.1  2003/05/20 23:36:30  graham
-- Add new Swish modules
--
