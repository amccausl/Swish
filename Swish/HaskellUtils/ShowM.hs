--------------------------------------------------------------------------------
--  $Id: ShowM.hs,v 1.1 2004/02/11 16:31:01 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ShowM
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines an extension of the Show class for displaying
--  multi-line values.  It serves the following purposes:
--  (1) provides a method with greater layout control of multiline values,
--  (2) provides a possibility to override the default Show behaviour
--      for programs that use the extended ShowM interface, and
--  (3) uses a ShowS intermediate value to avoid unnecessary
--      concatenation of long strings.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.ShowM
    ( ShowM(..), showm
    )
where

------------------------------------------------------------
--  ShowM framework
------------------------------------------------------------

-- |ShowM is a type class for values that may be formatted in
--  multi-line displays.
class (Show sh) => ShowM sh where
    -- |Multi-line value display method
    --  Create a multiline displayable form of a value, returned
    --  as a ShowS value.  The default implementation behaves just
    --  like a normal instance of Show.
    --
    --  This function is intended to allow the calling function some control
    --  of multiline displays by providing:
    --  (1) the first line of the value is not preceded by any text, so
    --      it may be appended to some preceding text on the same line,
    --  (2) the supplied line break string is used to separate lines of the
    --      formatted text, and may include any desired indentation, and
    --  (3) no newline is output following the final line of text.
    showms :: String -> sh -> ShowS
    showms linebreak val = shows val

-- |showm
--  Return a string representation of a ShowM value.
showm :: (ShowM sh) => String -> sh -> String
showm linebreak val = showms linebreak val ""


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
-- $Source: /file/cvsdev/HaskellUtils/ShowM.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: ShowM.hs,v $
-- Revision 1.1  2004/02/11 16:31:01  graham
-- Move ShowM to HaskellUtils directory.
--
-- Revision 1.2  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.1  2003/06/25 21:20:12  graham
-- Add ShowM class and RDF graph instance to CVS.
-- This is part of reworking N3 formatting logic to support proof display,
-- and other multiline display requirements.
--
