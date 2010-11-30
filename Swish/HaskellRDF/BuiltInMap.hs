--------------------------------------------------------------------------------
--  $Id: BuiltInMap.hs,v 1.5 2003/12/18 18:27:46 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  BuiltInMap
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module collects references and provides access to all of the
--  datatypes, variable binding modifiers and variable binding filters
--  built in to Swish.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.BuiltInMap
    ( findRDFOpenVarBindingModifier
    , findRDFDatatype
    , rdfRulesetMap
    , allRulesets, allDatatypeRulesets
    )
where

import Swish.HaskellRDF.BuiltInDatatypes
import Swish.HaskellRDF.BuiltInRules

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
-- $Source: /file/cvsdev/HaskellRDF/BuiltInMap.hs,v $
-- $Author: graham $
-- $Revision: 1.5 $
-- $Log: BuiltInMap.hs,v $
-- Revision 1.5  2003/12/18 18:27:46  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.4  2003/12/17 16:56:39  graham
-- Split content of BuiltInMap into separate modules, to avoid recursive
-- module dependency with RDFProofContext.
--
-- Revision 1.3  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.2  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.1  2003/12/08 23:56:07  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
