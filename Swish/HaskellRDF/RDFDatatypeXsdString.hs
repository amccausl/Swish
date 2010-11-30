--------------------------------------------------------------------------------
--  $Id: RDFDatatypeXsdString.hs,v 1.2 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFDatatypeXsdString
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines the structures used by swish to represent and
--  manipulate RDF xsd:string datatyped literals.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFDatatypeXsdString
    ( rdfDatatypeXsdString
    , rdfDatatypeValXsdString
    , typeNameXsdString, namespaceXsdString
    , axiomsXsdString, rulesXsdString
    , prefixXsdString
    )
where

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula
    , makeRDFGraphFromN3String
    , makeRDFFormula
    , makeN3ClosureRule
    )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBindingModify
    )

import Swish.HaskellRDF.RDFDatatype
    ( RDFDatatype
    , RDFDatatypeVal
    , RDFDatatypeMod
    , makeRdfDtOpenVarBindingModifiers
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..) )

import Swish.HaskellRDF.ClassRestrictionRule
    ( makeRDFDatatypeRestrictionRules
    )

import Swish.HaskellRDF.Datatype
    ( Datatype(..)
    , DatatypeVal(..)
    , DatatypeMap(..)
    , DatatypeRel(..), DatatypeRelPr
    , altArgs
    , UnaryFnTable,  unaryFnApp
    , BinaryFnTable, binaryFnApp 
    , BinMaybeFnTable, binMaybeFnApp 
    , DatatypeMod(..) 
    , makeVmod_2_0
    )

import Swish.HaskellRDF.Ruleset
    ( makeRuleset 
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceRDFS
    , namespaceRDFD
    , namespaceXSD
    , namespaceXsdType
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    , addVarBinding
    , VarBindingModify(..)
    )

{- in Prelude???
import Maybe
    ( Maybe (..), maybeToList )

import Monad
    ( liftM )
-}

------------------------------------------------------------
--  Misc values
------------------------------------------------------------

--  Local name for Integer datatype
nameXsdString      = "string"

-- |Type name for xsd:integer datatype
typeNameXsdString  = ScopedName namespaceXSD nameXsdString

-- |Namespace for xsd:integer datatype functions
namespaceXsdString = namespaceXsdType nameXsdString

--  Helper to catenate strings with newline separator,
--  used for making textual representations of graphs.
--  (the newline makes N3 parser diagnostics easier to interpret)
--
infixr 5 +++
(+++) :: String -> ShowS
(+++) str = ((str++"\n")++)

--  Compose with function of two arguments
c2 = (.) . (.)

------------------------------------------------------------
--  Declare exported RDFDatatype value for xsd:integer
------------------------------------------------------------

rdfDatatypeXsdString :: RDFDatatype
rdfDatatypeXsdString = Datatype rdfDatatypeValXsdString

------------------------------------------------------------
--  Implmentation of RDFDatatypeVal for xsd:integer
------------------------------------------------------------

-- |Define Datatype value for xsd:string
--
rdfDatatypeValXsdString :: RDFDatatypeVal String
rdfDatatypeValXsdString = DatatypeVal
    { tvalName      = typeNameXsdString
    , tvalRules     = rdfRulesetXsdString  -- Ruleset RDFGraph
    , tvalMkRules   = makeRDFDatatypeRestrictionRules rdfDatatypeValXsdString
                                           -- RDFGraph -> [RDFRules]
    , tvalMkMods    = makeRdfDtOpenVarBindingModifiers rdfDatatypeValXsdString
    , tvalMap       = mapXsdString         -- DatatypeMap Integer
    , tvalRel       = relXsdString         -- [DatatypeRel Integer]
    , tvalMod       = modXsdString         -- [DatatypeMod Integer]
    }

-- |mapXsdString contains functions that perform lexical-to-value
--  and value-to-canonical-lexical mappings for xsd:string values
--
--  These are identity mappings.
--
mapXsdString :: DatatypeMap String
mapXsdString = DatatypeMap
    { -- mapL2V :: String -> Maybe String
      mapL2V = Just
      -- mapV2L :: String -> Maybe String
    , mapV2L = Just
    }

-- |relXsdString contains useful relations for xsd:string values.
--
relXsdString :: [DatatypeRel String]
relXsdString =
    [ relXsdStringEq
    , relXsdStringNe
    ]

mkStrRel2 ::
    String -> DatatypeRelPr String -> UnaryFnTable String
    -> DatatypeRel String
mkStrRel2 nam pr fns = DatatypeRel
    { dtRelName = ScopedName namespaceXsdString nam
    , dtRelFunc = altArgs pr fns unaryFnApp
    }

mkStrRel3 ::
    String -> DatatypeRelPr String -> BinaryFnTable String
    -> DatatypeRel String
mkStrRel3 nam pr fns = DatatypeRel
    { dtRelName = ScopedName namespaceXsdString nam
    , dtRelFunc = altArgs pr fns binaryFnApp
    }

mkStrRel3maybe ::
    String -> DatatypeRelPr String -> BinMaybeFnTable String
    -> DatatypeRel String
mkStrRel3maybe nam pr fns = DatatypeRel
    { dtRelName = ScopedName namespaceXsdString nam
    , dtRelFunc = altArgs pr fns binMaybeFnApp
    }

liftL2 :: (a->a->Bool) -> ([a]->a) -> ([a]->a) -> [a] -> Bool
liftL2 p i1 i2 as = p (i1 as) (i2 as)

lcomp :: (a->a->Bool) -> [a] -> Bool
lcomp p = liftL2 p head (head . tail)

-- eq

relXsdStringEq :: DatatypeRel String
relXsdStringEq = mkStrRel2 "eq" (lcomp (==))
    ( repeat (const True, []) )

-- ne

relXsdStringNe :: DatatypeRel String
relXsdStringNe = mkStrRel2 "ne" (lcomp (/=))
    ( repeat (const True, []) )

-- |modXsdString contains variable binding modifiers for xsd:string values.
--
modXsdString :: [RDFDatatypeMod String]
modXsdString =
    [ modXsdStringEq
    , modXsdStringNe
    ]

modXsdStringEq = modXsdStringCompare "eq" (==)
modXsdStringNe = modXsdStringCompare "ne" (/=)

modXsdStringCompare ::
    String -> (String->String->Bool) -> RDFDatatypeMod String
modXsdStringCompare nam rel = DatatypeMod
    { dmName = (ScopedName namespaceXsdString nam)
    , dmModf = [ f0 ]
    , dmAppf = makeVmod_2_0
    }
    where
        f0 vs@[v1,v2] = if rel v1 v2 then vs else []
        f0 _          = []

-- |rulesetXsdString contains rules and axioms that allow additional
--  deductions when xsd:string values appear in a graph.
--
--  makeRuleset :: Namespace -> [Formula ex] -> [Rule ex] -> Ruleset ex
--
rdfRulesetXsdString =
    makeRuleset namespaceXsdString axiomsXsdString rulesXsdString

mkPrefix ns =
    "@prefix " ++ nsPrefix ns ++ ": <" ++ nsURI ns ++ "> . \n"

prefixXsdString =
    mkPrefix namespaceRDF  ++
    mkPrefix namespaceRDFS ++
    mkPrefix namespaceRDFD ++
    mkPrefix namespaceXSD  ++
    mkPrefix namespaceXsdString ++
    " \n"

mkAxiom :: String -> String -> RDFFormula
mkAxiom local gr =
    makeRDFFormula namespaceXsdString local (prefixXsdString++gr)

axiomsXsdString =
    [ mkAxiom "dt"      "xsd:string rdf:type rdfs:Datatype ."
    ]

rulesXsdString = rulesXsdStringClosure ++ rulesXsdStringRestriction

rulesXsdStringRestriction =
    makeRDFDatatypeRestrictionRules rdfDatatypeValXsdString gr
    where
        gr = makeRDFGraphFromN3String rulesXsdStringStr

rulesXsdStringStr = prefixXsdString
    +++ "xsd_string:Eq a rdfd:GeneralRestriction ; "
    +++ "  rdfd:onProperties (rdf:_1 rdf:_2) ; "
    +++ "  rdfd:constraint xsd_string:eq ; "
    +++ "  rdfd:maxCardinality \"1\"^^xsd:nonNegativeInteger . "
    +++ "xsd_string:Ne a rdfd:GeneralRestriction ; "
    +++ "  rdfd:onProperties (rdf:_1 rdf:_2) ; "
    +++ "  rdfd:constraint xsd_string:ne ; "
    +++ "  rdfd:maxCardinality \"1\"^^xsd:nonNegativeInteger . "

rulesXsdStringClosure =
    [ xsdstrls
    , xsdstrsl
    ]

--  Infer string from plain literal
xsdstrls = makeN3ClosureRule namespaceXsdString "ls"
            "?a ?p ?l ."
            "?a ?p ?s ."
            (stringPlain "?s" "?l")

--  Infer plain literal from string
xsdstrsl = makeN3ClosureRule namespaceXsdString "sl"
            "?a ?p ?s ."
            "?a ?p ?l ."
            (stringPlain "?s" "?l")

--  Map between string and plain literal values
stringPlain :: String -> String -> RDFVarBindingModify
stringPlain svar lvar =
    stringPlainValue (vn svar) (vn lvar)
    where
            vn ('?':n) = Var n

--  Variable binding modifier to create new binding to a canonical
--  form of a datatyped literal.
stringPlainValue ::
    RDFLabel -> RDFLabel -> RDFVarBindingModify
stringPlainValue svar lvar = VarBindingModify
        { vbmName   = ScopedName namespaceRDFD "stringPlain"
        , vbmApply  = concatMap app1
        , vbmVocab  = [svar,lvar]
        , vbmUsage  = [[svar],[lvar],[]]
        }
    where
        app1 vbind = app2 (vbMap vbind svar) (vbMap vbind lvar) vbind
        app2 (Just (Lit s (Just typeNameXsdString)))
             (Just (Lit l (Nothing)))
             vbind
             | s == l
             = [vbind]
        app2 (Just (Lit s (Just typeNameXsdString)))
             (Nothing)
             vbind
             = [addVarBinding lvar (Lit s (Nothing)) vbind]
        app2 (Nothing)
             (Just (Lit l (Nothing)))
             vbind
             = [addVarBinding svar (Lit l (Just typeNameXsdString)) vbind]
        app2 _ _ _ = []

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
-- $Source: /file/cvsdev/HaskellRDF/RDFDatatypeXsdString.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: RDFDatatypeXsdString.hs,v $
-- Revision 1.2  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.1  2003/12/18 20:46:24  graham
-- Added xsd:string module to capture equivalence of xsd:string
-- and plain literals without a language tag
--
