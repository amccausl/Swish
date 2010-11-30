{-# OPTIONS -XTypeSynonymInstances #-}

--------------------------------------------------------------------------------
--  $Id: RDFGraphShowM.hs,v 1.2 2003/09/24 18:50:52 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFGraphShowM
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + ????
--
--  This module defines a ShowM class instance for RDFGraph, to be
--  used when displaying RDF Graph values as part of a proof sequence,
--  etc.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFGraphShowM()
where

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..)
    , isUri, isLiteral, isXMLLiteral, isBlank, isQueryVar, makeBlank
    , RDFTriple
    , NSGraph(..), RDFGraph )

import Swish.HaskellRDF.N3Formatter
    ( formatGraphIndent )

import Swish.HaskellUtils.ShowM
    ( ShowM(..), showm )


------------------------------------------------------------
--  ShowM instance for RDFGraph
------------------------------------------------------------

instance ShowM RDFGraph where
    showms linebreak graph = formatGraphIndent linebreak False graph


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
-- $Source: /file/cvsdev/HaskellRDF/RDFGraphShowM.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: RDFGraphShowM.hs,v $
-- Revision 1.2  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.1  2003/06/25 21:20:12  graham
-- Add ShowM class and RDF graph instance to CVS.
-- This is part of reworking N3 formatting logic to support proof display,
-- and other multiline display requirements.
--
