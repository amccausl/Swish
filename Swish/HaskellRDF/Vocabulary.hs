--------------------------------------------------------------------------------
--  $Id: Vocabulary.hs,v 1.7 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Vocabulary
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines some commonly used vocabulary terms,
--  using the Namespace and ScopedName data types.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.Vocabulary
    ( namespaceNull
    , namespaceRDF
    , namespaceRDFS
    , namespaceRDFD
    , namespaceRDFC
    , namespaceRDFO
    , namespaceOWL
    , namespaceXSD
    , namespaceXsdType
    , namespaceMATH
    , namespaceLOG
    , namespaceDAML
    , namespaceDefault
    , namespaceSwish, swishName
    , namespaceLang,  langName, langTag, isLang
    , scopeRDF
    , scopeRDFS
    , scopeRDFD
    , rdf_datatype, rdf_resource, rdf_about, rdf_ID
    , rdf_type
    , rdf_first, rdf_rest, rdf_nil, rdf_XMLLiteral
    , rdfs_member
    , rdfd_GeneralRestriction
    , rdfd_onProperties, rdfd_constraint, rdfd_maxCardinality
    , owl_sameAs
    , xsd_type, xsd_string, xsd_boolean
    , xsd_decimal, xsd_integer
    , xsd_nonneg_integer, xsd_nonpos_integer, xsd_pos_integer, xsd_neg_integer
    , xsd_float, xsd_double
    , operator_plus, operator_minus, operator_slash, operator_star
    , default_base
    )
where

import Swish.HaskellUtils.Namespace
    ( Namespace(..), ScopedName(..) )

import Swish.HaskellUtils.MiscHelpers
    ( lower )

------------------------------------------------------------
--  Define some common namespace values
------------------------------------------------------------

namespaceNull :: Namespace
namespaceNull
    = Namespace "" ""

namespaceRDF :: Namespace
namespaceRDF    =
    Namespace   "rdf"   "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

namespaceRDFS :: Namespace
namespaceRDFS   =
    Namespace   "rdfs"  "http://www.w3.org/2000/01/rdf-schema#"

namespaceRDFD :: Namespace
namespaceRDFD   =
    Namespace   "rdfd"  "http://id.ninebynine.org/2003/rdfext/rdfd#"

namespaceRDFC :: Namespace
namespaceRDFC   =
    Namespace   "rdfc"  "http://id.ninebynine.org/2003/rdfext/rdfc#"

namespaceRDFO :: Namespace
namespaceRDFO   =
    Namespace   "rdfo"  "http://id.ninebynine.org/2003/rdfext/rdfo#"

namespaceOWL :: Namespace
namespaceOWL    =
    Namespace   "owl"   "http://www.w3.org/2002/07/owl#"

namespaceXSD :: Namespace
namespaceXSD    =
    Namespace   "xsd"   "http://www.w3.org/2001/XMLSchema#"

namespaceXsdType :: String -> Namespace
namespaceXsdType dtname =
    Namespace   ("xsd_"++dtname)
                ("http://id.ninebynine.org/2003/XMLSchema/"++dtname++"#")

namespaceMATH :: Namespace
namespaceMATH   =
    Namespace   "math"  "http://www.w3.org/2000/10/swap/math#"

namespaceLOG :: Namespace
namespaceLOG    =
    Namespace   "log"   "http://www.w3.org/2000/10/swap/log.n3#"

namespaceDAML :: Namespace
namespaceDAML   =
    Namespace   "daml"  "http://www.daml.org/2000/10/daml-ont#"

namespaceDefault :: Namespace
namespaceDefault
    = Namespace "default" "http://id.ninebynine.org/default/"

namespaceSwish :: Namespace
namespaceSwish
    = Namespace "swish" "http://id.ninebynine.org/2003/Swish/"

swishName :: String -> ScopedName
swishName local = ScopedName namespaceSwish local

-----------------------------------------------------------
--  Language tags
------------------------------------------------------------
--
--  Note:  simple language tag URIs may be abbreviated as lang:tag,
--  but if the tag contains ahyphen, this would not be valid QName
--  form in Notation3, even though it is a valid QName component.
--  Fortunately, they do not currently need to appear in Notation3 as
--  distinct labels (but future developments m,ay change that).

namespaceLang :: Namespace
namespaceLang
    = Namespace "lang" "http://id.ninebynine.org/2003/Swish/Lang/"
    -- To be replaced by urn:ietf:params:lang?

langName :: String -> ScopedName
langName tag = ScopedName namespaceLang (lower tag)

langTag :: ScopedName -> String
langTag sname = snLocal sname

isLang :: ScopedName -> Bool
isLang sname = snScope sname == namespaceLang

------------------------------------------------------------
--  Define namespaces for RDF rules, axioms, etc
------------------------------------------------------------

scopeRDF :: Namespace
scopeRDF        =
    Namespace   "rs_rdf"   "http://id.ninebynine.org/2003/Ruleset/rdf#"

scopeRDFS :: Namespace
scopeRDFS       =
    Namespace   "rs_rdfs"  "http://id.ninebynine.org/2003/Ruleset/rdfs#"

scopeRDFD :: Namespace
scopeRDFD       =
    Namespace   "rs_rdfd"  "http://id.ninebynine.org/2003/Ruleset/rdfd#"

------------------------------------------------------------
--  Define some common vocabulary terms
------------------------------------------------------------

rdf_datatype            :: ScopedName
rdf_datatype            = ScopedName namespaceRDF  "datatype"

rdf_resource            :: ScopedName
rdf_resource            = ScopedName namespaceRDF  "resource"

rdf_about               :: ScopedName
rdf_about               = ScopedName namespaceRDF  "about"

rdf_ID                  :: ScopedName
rdf_ID                  = ScopedName namespaceRDF  "ID"

rdf_type                :: ScopedName
rdf_type                = ScopedName namespaceRDF  "type"

rdf_first               :: ScopedName
rdf_first               = ScopedName namespaceRDF  "first"

rdf_rest                :: ScopedName
rdf_rest                = ScopedName namespaceRDF  "rest"

rdf_nil                 :: ScopedName
rdf_nil                 = ScopedName namespaceRDF  "nil"

rdf_XMLLiteral          :: ScopedName
rdf_XMLLiteral          = ScopedName namespaceRDF  "XMLLiteral"

rdfs_member             :: ScopedName
rdfs_member             = ScopedName namespaceRDFS "member"

rdfd_GeneralRestriction :: ScopedName
rdfd_GeneralRestriction = ScopedName namespaceRDFD "GeneralRestriction"

rdfd_onProperties       :: ScopedName
rdfd_onProperties       = ScopedName namespaceRDFD "onProperties"

rdfd_constraint         :: ScopedName
rdfd_constraint         = ScopedName namespaceRDFD "constraint"

rdfd_maxCardinality     :: ScopedName
rdfd_maxCardinality     = ScopedName namespaceRDFD "maxCardinality"

xsd_type                :: String -> ScopedName
xsd_type typnam         = ScopedName namespaceXSD  typnam

xsd_string              :: ScopedName
xsd_string              = xsd_type "string"

xsd_boolean             :: ScopedName
xsd_boolean             = xsd_type "boolean"

xsd_decimal             :: ScopedName
xsd_decimal             = xsd_type "decimal"

xsd_integer             :: ScopedName
xsd_integer             = xsd_type "integer"

xsd_nonneg_integer      :: ScopedName
xsd_nonneg_integer      = xsd_type "nonNegativeInteger"

xsd_nonpos_integer      :: ScopedName
xsd_nonpos_integer      = xsd_type "nonPositiveInteger"

xsd_pos_integer         :: ScopedName
xsd_pos_integer         = xsd_type "positiveInteger"

xsd_neg_integer         :: ScopedName
xsd_neg_integer         = xsd_type "negativeInteger"

xsd_float               :: ScopedName
xsd_float               = xsd_type "float"

xsd_double              :: ScopedName
xsd_double              = xsd_type "double"

owl_sameAs              :: ScopedName
owl_sameAs              = ScopedName namespaceOWL  "sameAs"

operator_plus           :: ScopedName
operator_plus           = ScopedName namespaceRDFO "plus"

operator_minus          :: ScopedName
operator_minus          = ScopedName namespaceRDFO "minus"

operator_slash          :: ScopedName
operator_slash          = ScopedName namespaceRDFO "slash"

operator_star           :: ScopedName
operator_star           = ScopedName namespaceRDFO "star"

default_base            :: ScopedName
default_base            = ScopedName namespaceDefault "base"

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
-- $Source: /file/cvsdev/HaskellRDF/Vocabulary.hs,v $
-- $Author: graham $
-- $Revision: 1.7 $
-- $Log: Vocabulary.hs,v $
-- Revision 1.7  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.6  2004/01/06 16:29:56  graham
-- Fix up module exports to avoid GHC warnings
--
-- Revision 1.5  2003/12/16 07:05:37  graham
-- Working on updated RDFProofContext
--
-- Revision 1.4  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
--
-- Revision 1.3  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.2  2003/12/08 16:58:27  graham
-- Add name to variable binding modifiers and filters.
-- Add namespace for Swish-defined names.
--
-- Revision 1.1  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
