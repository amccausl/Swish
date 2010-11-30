--------------------------------------------------------------------------------
--  $Id: MapXsdInteger.hs,v 1.1 2003/11/14 15:59:51 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  MapXsdInteger
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + ????
--
--  This module defines the datatytpe mapping and relation values
--  used for RDF dataype xsd:integer
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.MapXsdInteger
    ( mapXsdInteger
    )
where

import Swish.HaskellRDF.Datatype
    ( DatatypeMap(..)
    )


import Swish.HaskellRDF.Dfa.Dfa
    ( Re(..)
    , matchRe
    )

------------------------------------------------------------
--  Implementation of DatatypeMap for xsd:integer
------------------------------------------------------------

-- |mapXsdInteger contains functions that perform lexical-to-value
--  and value-to-canonical-lexical mappings for xsd:integer values
--
mapXsdInteger :: DatatypeMap Integer
mapXsdInteger = DatatypeMap
    { -- mapL2V :: String -> Maybe Integer
      mapL2V = \s -> case [ x
                          | matchRe reInteger s
                          , (x,t) <- reads $ skipPlus s
                          , ("","") <- lex t
                          ] of
                    [] -> Nothing
                    is -> Just $ head is
      -- mapV2L :: Integer -> Maybe String
    , mapV2L = Just . show
    }

skipPlus :: String -> String
skipPlus ('+':s) = s
skipPlus s       = s

reInteger = ReCat [ReOpt (alt "+-"), digits1]
    where
        digits0 = ReStar digit
        digits1 = RePlus digit
        digit   = alt "0123456789"
        alt cs  = ReOr $ map (\c -> ReTerm [c]) cs

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
-- $Source: /file/cvsdev/HaskellRDF/MapXsdInteger.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: MapXsdInteger.hs,v $
-- Revision 1.1  2003/11/14 15:59:51  graham
-- Separate MapXsdInteger from RDFDatatypeXsdInteger.
--
