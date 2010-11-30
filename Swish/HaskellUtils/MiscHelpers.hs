--------------------------------------------------------------------------------
--  $Id: MiscHelpers.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  MiscHelpers
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines some generic list and related helper functions
--  used by the graph handling code.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.MiscHelpers
      ( assert, lower, stricmp, quote, hash, hashModulus )
where

import Data.Char
    ( toLower )

------------------------------------------------------------
--  assert test
------------------------------------------------------------

assert :: Bool -> String -> a -> a
assert cond msg expr = if not cond then error msg else expr

------------------------------------------------------------
--  Generate lowercase form of supplied string
------------------------------------------------------------

lower (c:st)   = (toLower c):(lower st)
lower []       = ""

------------------------------------------------------------
--  Case insensitive compare.
------------------------------------------------------------
--
--  Should be used only for values using just the US ASCII
--  character set.  Use with richer character sets can yield
--  surprising results.

stricmp :: String -> String -> Bool
stricmp (c1:s1) (c2:s2) = (toLower c1) == (toLower c2) && (stricmp s1 s2)
stricmp []      []      = True
stricmp _       _       = False

------------------------------------------------------------
--  Generate quoted form of supplied string:
------------------------------------------------------------
--
--  [[[TODO: The list of quoting options here is incomplete]]]

quote  st = ['"'] ++ (quote1 st) ++ ['"']
quote1 ('"': st)    = '\\':'"' :(quote1 st)
quote1 ('\\':st)    = '\\':'\\':(quote1 st)
quote1 ('\n':st)    = '\\':'n':(quote1 st)
quote1 ('\r':st)    = '\\':'r':(quote1 st)
quote1 (c:st)       = c:(quote1 st)
quote1 []           = ""

------------------------------------------------------------
--  Hash function and values
------------------------------------------------------------
--
--  Simple hash function based on Sedgewick, Algorithms in C, p 233
--  (choose mx*cm+255 < maxBound)
--  'seed' is an additional parameter that allows the function
--  to be varied for re-hashing.

hashModulus = 16000001::Int

hash :: Int -> String -> Int
hash seed str = hash1 seed (64+seed) hashModulus str

hash1 :: Int -> Int -> Int -> String -> Int
hash1 sofar cm mx (c:str) = hash1 (( (sofar*cm) + (fromEnum c) ) `rem` mx) cm mx str
hash1 sofar _ _ []        = sofar


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
-- $Source: /file/cvsdev/HaskellUtils/MiscHelpers.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: MiscHelpers.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.6  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.5  2004/01/07 14:29:15  graham
-- Move stricmp to MiscHelpers
--
-- Revision 1.4  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.3  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.2  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.1  2003/05/20 17:29:44  graham
-- Split original helper functions module into ListHelpers and MiscHelpers
--
