--------------------------------------------------------------------------------
--  $Id: Swish.hs,v 1.11 2004/01/09 14:36:33 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Swish
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module is a wrapper for the main program of Swish.
--
--------------------------------------------------------------------------------

--     WNH RIP OUT module Swish.HaskellRDF.Swish where
-- module Main where      WNH RIP OUT!!!!

import Swish.HaskellRDF.SwishMain


import System.Environment
       ( getArgs )

import System.Exit
    ( ExitCode(ExitSuccess,ExitFailure), exitWith )


------------------------------------------------------------
--  Swish main program
------------------------------------------------------------
--
--  This is a minimal wrapper for the real main program, to facilitate
--  interactive execution (e.g. in HUGS) of different command lines.
--
--  execStateT runs the monad with a supplied initial state,
--  then separates the resulting state from the IO monad.

main :: IO ()
main =
    do  { 
          putStrLn ("Swish-0.2.1 CLI\n\n")
        ;
          args <- getArgs
        ; code <- runSwishArgs args
        ; if code == ExitSuccess then
            return ()
          else
          if code == (ExitFailure 1) then
            putStrLn $ "Swish: graphs compare different"
          else
            putStrLn $ "Swish: "++show code
        ; exitWith code
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
-- $Source: /file/cvsdev/HaskellRDF/Swish.hs,v $
-- $Author: graham $
-- $Revision: 1.11 $
-- $Log: Swish.hs,v $
-- Revision 1.11  2004/01/09 14:36:33  graham
-- Revert Swish.hs and Sw3ishtestAll.hs to declare module Main.
-- GHC compilation without -main-is option.  Tests OK.
--
-- Revision 1.10  2004/01/06 16:29:56  graham
-- Fix up module exports to avoid GHC warnings
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
-- Revision 1.6  2003/05/29 11:52:41  graham
-- Juggle Swish code:  SwishMain.hs is main program logic, with
-- Swish.hs and SwishTest.hs being alternative "Main" modules for
-- the real program and test harness respectively.
--
-- Revision 1.5  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.4  2003/05/23 00:02:42  graham
-- Fixed blank node id generation bug in N3Formatter
--
-- Revision 1.3  2003/05/21 13:34:13  graham
-- Various N3 parser bug fixes.
-- Need to fix handling of :name terms.
--
-- Revision 1.2  2003/05/20 23:35:28  graham
-- Modified code to compile with GHC hierarchical libraries
--
-- Revision 1.1  2003/05/20 17:30:48  graham
-- Initial swish program skeleton runs using isolated tests under Hugs
--
