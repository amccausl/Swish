--------------------------------------------------------------------------------
--  $Id: BuiltInDatatypes.hs,v 1.2 2003/12/18 20:46:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  BuiltInDatatypes
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module collects references and provides access to all of the
--  datatypes built in to Swish.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.BuiltInDatatypes
    ( allDatatypes, findRDFDatatype )
where

import Swish.HaskellRDF.RDFDatatype
    ( RDFDatatype
    )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..), mapFindMaybe
    )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..) )

import Swish.HaskellRDF.RDFDatatypeXsdString
    ( rdfDatatypeXsdString )

import Swish.HaskellRDF.RDFDatatypeXsdInteger
    ( rdfDatatypeXsdInteger )

------------------------------------------------------------
--  Declare datatype map
------------------------------------------------------------

allDatatypes :: [RDFDatatype]
allDatatypes =
    [ rdfDatatypeXsdString
    , rdfDatatypeXsdInteger
    ]

findRDFDatatype :: ScopedName -> Maybe RDFDatatype
findRDFDatatype nam = mapFindMaybe nam (LookupMap allDatatypes)

------------------------------------------------------------
--  Declare datatype subtypes map
------------------------------------------------------------

allDatatypeSubtypes :: [xxx]
allDatatypeSubtypes = []
--  [[[details TBD]]]

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
-- $Source: /file/cvsdev/HaskellRDF/BuiltInDatatypes.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: BuiltInDatatypes.hs,v $
-- Revision 1.2  2003/12/18 20:46:24  graham
-- Added xsd:string module to capture equivalence of xsd:string
-- and plain literals without a language tag
--
-- Revision 1.1  2003/12/17 16:56:39  graham
-- Split content of BuiltInMap into separate modules, to avoid recursive
-- module dependency with RDFProofContext.
--
