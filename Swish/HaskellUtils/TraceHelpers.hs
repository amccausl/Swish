--------------------------------------------------------------------------------
--  $Id: TraceHelpers.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  TraceHelpers
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module provides access to tracing functions from the pre-2003
--  Hugs trace module.  Over time, it may accumulate other tracing
--  functions that I find useful.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.TraceHelpers
    ( trace, traceShow
    )
where

import Debug.Trace
    ( trace )

------------------------------------------------------------
--  traceShow function from older Hugs trace module
------------------------------------------------------------

traceShow :: Show a => String -> a -> a
traceShow msg x = trace (msg ++ show x) x

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
-- $Source: /file/cvsdev/HaskellUtils/TraceHelpers.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: TraceHelpers.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.1  2003/12/20 12:02:08  graham
-- Introduced new TraceHelpers module for Hugs-2003 compatibility.
--
-- Revision 1.3  2003/12/18 18:29:03  graham
-- ??????
--
