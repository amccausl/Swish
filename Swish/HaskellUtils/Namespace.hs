{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
--------------------------------------------------------------------------------
--  $Id: Namespace.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Namespace
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines algebraic datatypes for namespaces and scoped names.
--
--  For these purposes, a namespace is a prefix and URI used to identify
--  a namespace (cf. XML namespaces), and a scoped name is a name that
--  is scoped by a specified namespace.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , makeNamespaceQName
    , nullNamespace
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI
    , matchName
    , makeScopedName, makeQNameScopedName, makeUriScopedName
    , nullScopedName
    )
where

import Swish.HaskellUtils.QName
    ( QName(..), getQNameURI )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..) )

{- in Prelude???
import Maybe
    ( Maybe(..), fromJust )
-}

------------------------------------------------------------
--  Namespace, having a prefix and a URI
------------------------------------------------------------

-- |A NameSpace value consists of a prefix and a corresponding URI.
--  The prefix may be Nothing, in which case it is assumed to be inknown.
--
data Namespace = Namespace { nsPrefix :: String, nsURI :: String }

{-
getNamespacePrefix :: Namespace -> String
getNamespacePrefix = nsPrefix

getNamespaceURI    :: Namespace -> String
getNamespaceURI    = nsURI
-}

instance Eq Namespace where
    (==) = nsEq

instance Show Namespace where
    show (Namespace p u) =
        (if p == "?" then "" else p ++ ":") ++ "<" ++ u ++ ">"

instance LookupEntryClass Namespace String String where
    keyVal   (Namespace pre uri) = (pre,uri)
    newEntry (pre,uri)           = (Namespace pre uri)

nsEq :: Namespace -> Namespace -> Bool
nsEq (Namespace _ u1) (Namespace _ u2) = u1 == u2

makeNamespaceQName :: Namespace -> String -> QName
makeNamespaceQName ns loc = QName (nsURI ns) loc

nullNamespace :: Namespace
nullNamespace = Namespace "?" ""

------------------------------------------------------------
--  ScopedName, made from a namespace and a local name
------------------------------------------------------------

-- |A full ScopedName value has a QName prefix, namespace URI
--  and a local part.  ScopedName values may omit the prefix
--  (see Namespace) or the local part.
--
--  Some applications may handle null namespace URIs as meaning
--  the local part is relative to some base URI.
--
data ScopedName = ScopedName { snScope :: Namespace, snLocal :: String }

getScopePrefix :: ScopedName -> String
getScopePrefix = nsPrefix . snScope

getScopeURI :: ScopedName -> String
getScopeURI = nsURI . snScope

instance Eq ScopedName where
    (==) = snEq

instance Ord ScopedName where
    (<=) = snLe

instance Show ScopedName where
    show (ScopedName n l) =
        if pre == "?" then "<"++uri++l++">" else pre++":"++l
        where
            pre = nsPrefix n
            uri = nsURI n

--  Scoped names are equal of ther corresponding QNames are equal
snEq :: ScopedName -> ScopedName -> Bool
snEq s1 s2 = (getQName s1) == (getQName s2)

--  Scoped names are ordered by their QNames
snLe :: ScopedName -> ScopedName -> Bool
snLe s1 s2 = (getQName s1) <= (getQName s2)

-- |Get QName corresponding to a scoped name
getQName :: ScopedName -> QName
getQName n = QName (getScopeURI n) (snLocal n)

-- |Get URI corresponding to a scoped name (using RDF conventions)
getScopedNameURI :: ScopedName -> String
getScopedNameURI = getQNameURI . getQName

-- |Test if supplied string matches the display form of a
--  scoped name.
matchName :: String -> ScopedName -> Bool
matchName str nam = str == show nam

-- |Construct a ScopedName from prefix, URI and local name
makeScopedName :: String -> String -> String -> ScopedName
makeScopedName pre nsuri loc =
    ScopedName (Namespace pre nsuri) loc

-- |Construct a ScopedName from a QName
makeQNameScopedName :: QName -> ScopedName
makeQNameScopedName (QName u l) = makeScopedName "?" u l

-- |Construct a ScopedName for a bare URI
makeUriScopedName :: String -> ScopedName
makeUriScopedName u = makeScopedName "?" u ""

-- |Null scoped name:  this should never appear as a valid name
nullScopedName :: ScopedName
nullScopedName = makeScopedName "?" "" ""

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
-- $Source: /file/cvsdev/HaskellUtils/Namespace.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: Namespace.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.13  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.12  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.11  2003/12/03 17:07:24  graham
-- Replace occurrences of QName in N3Parser with ScopedName.
--
-- Revision 1.10  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.9  2003/11/24 15:46:03  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.8  2003/11/14 21:48:35  graham
-- First cut cardinality-checked datatype-constraint rules to pass test cases.
-- Backward chaining is still to do.
--
-- Revision 1.7  2003/11/13 01:13:47  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.6  2003/11/12 20:44:24  graham
-- Added some vocabulary to Namespace.
-- Enhaced ScopedName to allow null namespace prefixes,
-- following N3 display conventions.
--
-- Revision 1.5  2003/10/24 21:05:08  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
-- Revision 1.4  2003/10/22 16:18:37  graham
-- Move common namespace definitions into Namespace module
-- (May later move these into separate modules.)
--
-- Revision 1.3  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.2  2003/09/30 20:02:40  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.1  2003/09/24 18:51:36  graham
-- Add module Namespace and test cases.
--
-- Revision 1.1  2003/09/24 12:51:00  graham
-- Add separate QName module and test suite
--
