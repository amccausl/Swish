{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XTypeSynonymInstances #-}

--------------------------------------------------------------------------------
--  $Id: RDFGraph.hs,v 1.48 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFGraph
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a memory-based RDF graph instance.
--
--------------------------------------------------------------------------------

------------------------------------------------------------
-- Simple labelled directed graph value
------------------------------------------------------------

module Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..)
    , isLiteral, isUntypedLiteral, isTypedLiteral, isXMLLiteral
    , isDatatyped, isMemberProp, isUri, isBlank, isQueryVar
    , getLiteralText, getScopedName, makeBlank
    , RDFTriple
    , NSGraph(..), RDFGraph
    , NamespaceMap, RevNamespaceMap
    , emptyNamespaceMap
    , LookupFormula(..), Formula, FormulaMap, emptyFormulaMap
    , addArc, merge
    , allLabels, allNodes, remapLabels, remapLabelList
    , newNode, newNodes
    , setNamespaces, getNamespaces
    , setFormulae, getFormulae, setFormula, getFormula
    , toRDFGraph, emptyRDFGraph {-, updateRDFGraph-}
      -- Re-export from GraphClass
    , LDGraph(..), Label (..), Arc(..)
    , arc, arcSubj, arcPred, arcObj, Selector
      -- Export selected RDFLabel values
    , res_rdf_type, res_rdf_first, res_rdf_rest, res_rdf_nil
    , res_rdfs_member
    , res_rdfd_GeneralRestriction
    , res_rdfd_onProperties, res_rdfd_constraint, res_rdfd_maxCardinality
    , res_owl_sameAs
    , res_operator_plus, res_operator_minus
    , res_operator_slash, res_operator_star
      -- Exported for testing:
    , grMatchMap, grEq
    , mapnode, maplist
    )
where

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , makeNamespaceQName
    , getQName, getScopedNameURI
    , ScopedName(..)
    , makeScopedName, makeQNameScopedName
    , nullScopedName
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceRDFS
    , namespaceRDFD
    , namespaceRDFC
    , namespaceRDFO
    , namespaceXSD
    , namespaceXsdType
    , namespaceOWL
    , namespaceMATH
    , namespaceLOG
    , namespaceDAML
    , namespaceLang, langTag, isLang
    , rdf_type
    , rdf_first, rdf_rest, rdf_nil, rdf_XMLLiteral
    , rdfs_member
    , rdfd_GeneralRestriction
    , rdfd_onProperties, rdfd_constraint, rdfd_maxCardinality
    , owl_sameAs
    , operator_plus, operator_minus, operator_slash, operator_star
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    , newQName, qnameFromPair, qnameFromURI
    , getNamespace, getLocalName, getQNameURI
    , splitURI
    )

import Swish.HaskellRDF.GraphClass
    ( LDGraph(..), Label (..)
    , Arc(..), arc, arcSubj, arcPred, arcObj
    , Selector )

import Swish.HaskellRDF.GraphMatch
    ( graphMatch, LabelMap(..), ScopedLabel(..) )

import Swish.HaskellUtils.MiscHelpers
    ( hash, lower, quote )

import Swish.HaskellUtils.ListHelpers
    ( addSetElem )

import Swish.HaskellUtils.LookupMap
    ( LookupMap(..), LookupEntryClass(..)
    , mapFind, mapFindMaybe, mapReplaceOrAdd, mapEq, mapVals, mapKeys
    , mapTranslateKeys, mapTranslateVals
    , mapTranslateEntries, mapTranslateEntriesM )

import Swish.HaskellUtils.FunctorM
    ( FunctorM(..) )

import Data.Char
    ( isDigit )

import Data.Maybe
    ( isJust )

import Data.List
    ( nub, intersect, union, findIndices )

-----------------------------------------------------------
--  RDF graph node values
------------------------------------------------------------
--
--  cf. http://www.w3.org/TR/rdf-concepts/#section-Graph-syntax
--
--  This is extended from the RDF abstract graph syntax in the
--  following ways:
--  (a) a graph can be part of a resource node or blank node
--      (cf. Notation3 formulae)
--  (b) a "variable" node option is distinguished from a
--      blank node.
--      I have found this useful for encoding and handling
--      queries, even though query variables can be expressed
--      as blank nodes.
--  (c) a "NoNode" option is defined.
--      This might otherwise be handled by Maybe (RDFLabel g)

data RDFLabel =
      Res ScopedName                    -- resource
    | Lit String (Maybe ScopedName)     -- literal [type/language]
    | Blank String                      -- blank node
    | Var String                        -- variable (not used in ordinary graphs)
    | NoNode                            -- no node  (not used in ordinary graphs)

instance Eq RDFLabel where
    (==) = labelEq

instance Show RDFLabel where
    show (Res sn)           = show sn
    show (Lit st Nothing)   = quote st
    show (Lit st (Just nam))
        | isLang nam = quote st ++ "@"  ++ (langTag nam)
        | otherwise  = quote st ++ "^^" ++ (show nam)
    show (Blank ln)         = "_:"++ln
    show (Var ln)           = "?"++ln
    show NoNode             = "<NoNode>"

instance Ord RDFLabel where
    -- Optimize some common cases..
    compare (Res sn1)      (Res sn2)      = compare sn1 sn2
    compare (Blank ln1)    (Blank ln2)    = compare ln1 ln2
    compare (Res _)        (Blank _)      = LT
    compare (Blank _)      (Res _)        = GT
    -- .. else use show string comparison
    compare l1 l2 = compare (show l1) (show l2)
    -- Similarly for <=
    (Res qn1)   <= (Res qn2)      = qn1 <= qn2
    (Blank ln1) <= (Blank ln2)    = ln1 <= ln2
    (Res _)     <= (Blank _)      = True
    (Blank _)   <= (Res _)        = False
    l1 <= l2                      = (show l1) <= (show l2)

instance Label RDFLabel where
    labelIsVar (Blank _)    = True
    labelIsVar (Var _)      = True
    labelIsVar _            = False
    getLocal   (Blank loc)  = loc
    getLocal   (Var   loc)  = '?':loc
    getLocal   (Res   sn)   = "Res_"++snLocal sn
    getLocal   (NoNode)     = "None"
    getLocal   _            = "Lit_"
    makeLabel  ('?':loc)    = Var loc
    makeLabel  loc          = Blank loc
    labelHash seed lb       = hash seed (showCanon lb)

--  Get canonical string for RDF label.
--  Used for hashing, so that equivalent labels always return
--  the same hash value.
showCanon :: RDFLabel -> String
showCanon (Res sn)           = "<"++getScopedNameURI sn++">"
showCanon (Lit st (Just nam))
        | isLang nam = quote st ++ "@"  ++ (langTag nam)
        | otherwise  = quote st ++ "^^" ++ (getScopedNameURI nam)
showCanon lb                 = show lb


-- Define equality of nodes possibly based on different graph types.
--
-- The version of equality defined here is not strictly RDF abstract syntax
-- equality, but my interpretation of equivalence for the purposes of
-- entailment, in the absence of any specific datatype knowledge other
-- than XML literals.
--
labelEq :: RDFLabel -> RDFLabel -> Bool
labelEq (Res q1)            (Res q2)        = (q1 == q2)
labelEq (Blank s1)          (Blank s2)      = (s1 == s2)
labelEq (Var v1)            (Var v2)        = (v1 == v2)
labelEq (Lit s1 t1)         (Lit s2 t2)     = (s1 == s2) && (t1 == t2)
labelEq _                   _               = False

---------------------------------------------------------
--  Selected RDFLabel values
---------------------------------------------------------

res_rdf_type                = Res rdf_type
res_rdf_first               = Res rdf_first
res_rdf_rest                = Res rdf_rest
res_rdf_nil                 = Res rdf_nil
res_rdfs_member             = Res rdfs_member
res_rdfd_GeneralRestriction = Res rdfd_GeneralRestriction
res_rdfd_onProperties       = Res rdfd_onProperties
res_rdfd_constraint         = Res rdfd_constraint
res_rdfd_maxCardinality     = Res rdfd_maxCardinality
res_owl_sameAs              = Res owl_sameAs
res_operator_plus           = Res operator_plus
res_operator_minus          = Res operator_minus
res_operator_slash          = Res operator_slash
res_operator_star           = Res operator_star

---------------------------------------------------------
--  Additional functions on RDFLabel values
---------------------------------------------------------

-- |Test if supplied labal is a URI resource node
isUri :: RDFLabel -> Bool
isUri (Res _) = True
isUri  _      = False

-- |Test if supplied labal is a literal node
isLiteral :: RDFLabel -> Bool
isLiteral (Lit _ _) = True
isLiteral  _        = False

-- |Test if supplied labal is an untyped literal node
isUntypedLiteral :: RDFLabel -> Bool
isUntypedLiteral (Lit _ Nothing  ) = True
isUntypedLiteral (Lit _ (Just tn)) = isLang tn
isUntypedLiteral  _                = False

-- |Test if supplied labal is an untyped literal node
isTypedLiteral :: RDFLabel -> Bool
isTypedLiteral (Lit _ (Just tn)) = not (isLang tn)
isTypedLiteral  _                = False

-- |Test if supplied labal is an XML literal node
isXMLLiteral :: RDFLabel -> Bool
isXMLLiteral = isDatatyped rdf_XMLLiteral

-- |Test if supplied label is an typed literal node of a given datatype
isDatatyped :: ScopedName -> RDFLabel -> Bool
isDatatyped d  (Lit _ (Just n)) = (n == d)
isDatatyped _  _                = False

-- |Test if supplied label is a container membership property
--
--  Check for namespace is RDF namespace and
--  first character of local name is '_' and
--  remaining characters of local name are all digits
isMemberProp :: RDFLabel -> Bool
isMemberProp (Res sn) = ( snScope sn == namespaceRDF  ) &&
                        ( head loc   == '_'   ) &&
                        ( and . map isDigit . tail $ loc )
                        where
                            loc = snLocal sn
isMemberProp _        = False

-- |Test if supplied labal is a blank node
isBlank :: RDFLabel -> Bool
isBlank (Blank _) = True
isBlank  _        = False

-- |Test if supplied labal is a query variable
isQueryVar :: RDFLabel -> Bool
isQueryVar (Var _) = True
isQueryVar  _      = False

-- |Extract text value from a literal node
getLiteralText :: RDFLabel -> String
getLiteralText (Lit s _) = s
getLiteralText  _        = ""

-- |Extract ScopedName value from a resource node
getScopedName :: RDFLabel -> ScopedName
getScopedName (Res sn) = sn
getScopedName  _       = nullScopedName

-- |Make a blank node from a supplied query variable,
--  or return the supplied label unchanged.
--  (Use this in when substituting an existential for an
--  unsubstituted query variable.)
makeBlank :: RDFLabel -> RDFLabel
makeBlank  (Var loc)    = Blank loc
makeBlank  lb           = lb

---------------------------------------------------------
--  RDF Triple (statement)
---------------------------------------------------------

type RDFTriple = Arc RDFLabel

---------------------------------------------------------
--  Namespace prefix list entry
---------------------------------------------------------

type NamespaceMap = LookupMap Namespace

data RevNamespace = RevNamespace Namespace

instance LookupEntryClass RevNamespace String String where
    keyVal   (RevNamespace (Namespace pre uri)) = (uri,pre)
    newEntry (uri,pre) = (RevNamespace (Namespace pre uri))

type RevNamespaceMap = LookupMap RevNamespace

emptyNamespaceMap = LookupMap [] :: NamespaceMap

---------------------------------------------------------
--  Graph formula entry
---------------------------------------------------------

data LookupFormula lb gr = Formula
    { formLabel :: lb
    , formGraph :: gr
    }

instance ( Eq lb, Eq gr ) => Eq (LookupFormula lb gr) where
    f1 == f2 = ( formLabel f1 == formLabel f2 ) &&
               ( formGraph f1 == formGraph f2 )

instance (Label lb)
    => LookupEntryClass (LookupFormula lb (NSGraph lb)) lb (NSGraph lb)
    where
        keyVal fe      = (formLabel fe, formGraph fe)
        newEntry (k,v) = Formula { formLabel=k, formGraph=v }

instance (Label lb) => Show (LookupFormula lb (NSGraph lb))
    where
        show (Formula l g) = (show l) ++ " :- { " ++ (showArcs "    " g) ++ " }"

type Formula lb = LookupFormula lb (NSGraph lb)

type FormulaMap lb = LookupMap (LookupFormula lb (NSGraph lb))

emptyFormulaMap = LookupMap [] :: FormulaMap RDFLabel

{-  given up on trying to do Functor for formulae...
instance Functor (LookupFormula (NSGraph lb)) where
    fmap f fm = mapTranslateEntries (mapFormulaEntry f) fm
-}

formulaeMap :: (lb -> l2) -> FormulaMap lb -> FormulaMap l2
formulaeMap f fm = mapTranslateEntries (formulaEntryMap f) fm

formulaEntryMap ::
    (lb -> l2)
    -> LookupFormula lb (NSGraph lb)
    -> LookupFormula l2 (NSGraph l2)
formulaEntryMap f (Formula k gr) = Formula (f k) (fmap f gr)

--  What follows is a monadic variant of formulaeMap, used to
--  apply a transformation and collect some result in a single
--  pass.

formulaeMapM ::
    (Monad m) => (lb -> m l2) -> FormulaMap lb -> m (FormulaMap l2)
formulaeMapM f fm = mapTranslateEntriesM (formulaEntryMapM f) fm

formulaEntryMapM ::
    (Monad m)
    => (lb -> m l2)
    -> LookupFormula lb (NSGraph lb)
    -> m (LookupFormula l2 (NSGraph l2))
formulaEntryMapM f (Formula k gr) =
    do  { f2 <- f k
        ; g2 <- (fmapM f gr)
        ; return $ Formula f2 g2
        }

---------------------------------------------------------
--  Memory-based graph with namespaces and subgraphs
---------------------------------------------------------

data NSGraph lb = NSGraph
    { namespaces :: NamespaceMap
    , formulae   :: FormulaMap lb
    , statements :: [Arc lb]
    }

getNamespaces   :: NSGraph lb -> NamespaceMap
getNamespaces g = namespaces g

setNamespaces      :: NamespaceMap -> NSGraph lb -> NSGraph lb
setNamespaces ns g = g { namespaces=ns }

getFormulae   :: NSGraph lb -> FormulaMap lb
getFormulae g = formulae g

setFormulae      :: FormulaMap lb -> NSGraph lb -> NSGraph lb
setFormulae fs g = g { formulae=fs }

getFormula     :: (Label lb) => NSGraph lb -> lb -> Maybe (NSGraph lb)
getFormula g l = mapFindMaybe l (formulae g)

setFormula     :: (Label lb) => Formula lb -> NSGraph lb -> NSGraph lb
setFormula f g = g { formulae=(mapReplaceOrAdd f (formulae g)) }

instance (Label lb) => LDGraph NSGraph lb where
    getArcs g    = statements g
    setArcs as g = g { statements=as }

-- Optimized method to add arc .. don't check for duplicates.
addArc :: (Label lb) => Arc lb -> NSGraph lb -> NSGraph lb
addArc ar gr = gr { statements=(addSetElem ar (statements gr)) }

instance Functor NSGraph where
    fmap f g = g { statements = (map $ fmap f) (statements g)
                 , formulae   = formulaeMap f (formulae g)
                 }

instance FunctorM NSGraph where
    fmapM f g =
        do  { s2 <- (mapM $ fmapM f) (statements g)
            ; f2 <- formulaeMapM f (formulae g)
            ; return $ g { statements = s2, formulae = f2 }
            }

instance (Label lb) => Eq (NSGraph lb) where
    (==) = grEq

instance (Label lb) => Show (NSGraph lb) where
    show      gr = grShow "" gr
    showList grs = grShowList "" grs

grShowList _ []     = showString "[no graphs]"
grShowList p (g:gs) = showChar '[' . showString (grShow pp g) . showl gs
    where
        showl []     = showChar ']' -- showString $ "\n" ++ p ++ "]"
        showl (g:gs) = showString (",\n "++p++grShow pp g) . showl gs
        pp           = ' ':p

grShow   :: (Label lb) => String -> NSGraph lb -> String
grShow p g =
    "Graph, formulae: " ++ (showForm p g) ++ "\n" ++
    p ++ "arcs: " ++ (showArcs p g)
    where
        showForm p g = (foldr (++) "" (map ( (pp++) . show ) formulae ))
        (LookupMap formulae) = getFormulae g
        pp = "\n    " ++ p

showArcs :: (Label lb) => String -> NSGraph lb -> String
showArcs p g = (foldr (++) "" (map ( (pp++) . show ) (getArcs g) ))
    where
        pp = "\n    " ++ p

grEq :: (Label lb) => NSGraph lb -> NSGraph lb -> Bool
grEq g1 g2 = fst ( grMatchMap g1 g2 )

grMatchMap :: (Label lb) =>
    NSGraph lb -> NSGraph lb -> (Bool, LabelMap (ScopedLabel lb))
grMatchMap g1 g2 =
    graphMatch matchable (getArcs g1) (getArcs g2)
    where
        matchable l1 l2 = (mapFormula g1 l1) == (mapFormula g2 l2)
        mapFormula g l  = mapFindMaybe l (getFormulae g)

toNSGraph :: (Eq lb, Show lb) => [Arc lb] -> NSGraph lb
toNSGraph arcs =
    NSGraph
        { statements = arcs
        , namespaces = emptyNamespaceMap
        , formulae   = LookupMap []
        }

---------------------------------------------------------
--  Merge RDF graphs, renaming bnodes in the second graph
--  as necessary
---------------------------------------------------------

-- |Merge RDF graphs, renaming blank and query variable nodes as
--  needed to neep variable nodes from the two graphs distinct in
--  the resulting graph.
merge :: (Label lb) => NSGraph lb -> NSGraph lb -> NSGraph lb
merge gr1 gr2 =
    let
        bn1   = allLabels labelIsVar gr1
        bn2   = allLabels labelIsVar gr2
        dupbn = intersect bn1 bn2
        allbn = union bn1 bn2
    in
        add gr1 (remapLabels dupbn allbn id gr2)

-- |Return list of all labels (including properties) in the graph
--  satisfying a supplied filter predicate.
allLabels :: (Label lb) => (lb -> Bool) -> NSGraph lb -> [lb]
allLabels p gr = filter p (unionNodes p (formulaNodes p gr) (labels gr) )

-- |Return list of all subjects and objects in the graph
--  satisfying a supplied filter predicate.
allNodes :: (Label lb) => (lb -> Bool) -> NSGraph lb -> [lb]
allNodes p gr = unionNodes p [] (nodes gr)

--  List all nodes in graph formulae satisfying a supplied predicate
formulaNodes :: (Label lb) => (lb -> Bool) -> NSGraph lb -> [lb]
formulaNodes p gr = foldl (unionNodes p) fkeys (map (allLabels p) fvals)
    where
        -- fm :: (Label lb) => FormulaMap lb
        --                     LookupMap LookupFormula (NSGraph lb) lb
        fm    = formulae gr
        -- fvals :: (Label lb) => [NSGraph lb]
        fvals = mapVals fm
        -- fkeys :: (Label lb) => [lb]
        fkeys = filter p $ mapKeys fm

--  Helper to filter variable nodes and merge with those found so far
unionNodes :: (Label lb) => (lb -> Bool) -> [lb] -> [lb] -> [lb]
unionNodes p ls1 ls2 = ls1 `union` (filter p ls2)

---------------------------------------------------------
--  Remap selected nodes in a graph
---------------------------------------------------------

-- |Remap selected nodes in graph:
--
--  dupbn is list of variable nodes to be renamed
--  allbn is list of variable nodes used that must be avoided
--  cnvbn is a node conversion function that is applied to nodes
--        from 'dupbn' in the graph that are to be replaced by
--        new blank nodes.  If no such conversion is required,
--        supply 'id'.  Function 'makeBlank' can be used to convert
--        RDF query nodes into RDF blank nodes.
--  gr    is graph in which nodes are to be renamed
--
--  This is the node renaming operation that prevents graph-scoped
--  variable nodes from being merged when two graphs are merged.
remapLabels ::
    (Label lb) => [lb] -> [lb] -> (lb -> lb) -> NSGraph lb -> NSGraph lb
remapLabels dupbn allbn cnvbn gr = fmap (mapnode dupbn allbn cnvbn) gr

-- |Externally callable function to construct a list of (old,new)
--  values to be used for graph label remapping.  The supplied arguments
--  are (a) a list of labels to be remaped, and (b) a list of labels
--  to be avoided by the remapping:  the latter should be a list of
--  all the variable nodes in the graph to which the remapping will be
--  applied.
remapLabelList ::
    (Label lb) => [lb] -> [lb] -> [(lb,lb)]
remapLabelList remap avoid = maplist remap avoid id []

--  Remap a single graph node.
--  If the node is not one of those to be remapped,
--  the supplied value is returned unchanged.
mapnode ::
    (Label lb) => [lb] -> [lb] -> (lb -> lb) -> lb -> lb
mapnode dupbn allbn cnvbn nv =
    mapFind nv nv (LookupMap (maplist dupbn allbn cnvbn []))

--  Construct a list of (oldnode,newnode) values to be used for
--  graph label remapping.  The function operates recursiovely, adding
--  new nodes generated to the mapping list (mapbn') and also to the
--  list of nodes to be avoided (allbn').
maplist ::
    (Label lb) => [lb] -> [lb] -> (lb -> lb) -> [(lb,lb)] -> [(lb,lb)]
maplist []         _     _     mapbn = mapbn
maplist (dn:dupbn) allbn cnvbn mapbn = maplist dupbn allbn' cnvbn mapbn'
    where
        dnmap  = newNode (cnvbn dn) allbn
        mapbn' = (dn,dnmap):mapbn
        allbn' = dnmap:allbn

-- |Given a node and a list of existing nodes, find a new node for
--  the supplied node that does not clash with any existing node.
--  (Generates an non-terminating list of possible replacements, and
--  picks the first one that isn't already in use.)
--
--  [[[TODO: optimize this for common case nnn and _nnn:
--    always generate _nnn and keep track of last allocated]]]
newNode :: (Label lb) => lb -> [lb] -> lb
newNode dn existnodes =
    head $ newNodes dn existnodes

-- |Given a node and a list of existing nodes, generate a list of new
--  nodes for the supplied node that do not clash with any existing node.
newNodes :: (Label lb) => lb -> [lb] -> [lb]
newNodes dn existnodes =
    filter (not . (flip elem existnodes)) $ trynodes (noderootindex dn)

noderootindex :: (Label lb) => lb -> (String,Int)
noderootindex dn = (nh,nx) where
    (nh,nt) = splitnodeid $ getLocal dn
    nx      = if null nt then 0 else read nt

splitnodeid :: String -> (String,String)
splitnodeid dn = splitAt (tx+1) dn where
    tx = last $ (-1):findIndices (not . isDigit) dn

trynodes :: (Label lb) => (String,Int) -> [lb]
trynodes (nr,nx) = [ makeLabel (nr++(show n)) | n <- iterate (+1) nx ]

trybnodes :: (Label lb) => (String,Int) -> [lb]
trybnodes (nr,nx) = [ makeLabel (nr++(show n)) | n <- iterate (+1) nx ]

---------------------------------------------------------
--  Memory-based RDF graph type and graph class functions
---------------------------------------------------------

type RDFGraph = NSGraph RDFLabel

-- |Create a new RDF graph from a supplied list of arcs
toRDFGraph :: [Arc RDFLabel] -> RDFGraph
toRDFGraph arcs = toNSGraph arcs

-- |Create a new, empty RDF graph.
emptyRDFGraph :: RDFGraph
emptyRDFGraph = toRDFGraph []

{-
-- |Update an RDF graph using a supplied list of arcs, keeping
--  prefix definitions and formula definitions from the original.
--
--  [[[TODO:  I think this may be redundant - the default graph
--  class has an update method which accepts a function to update
--  the arcs, not touching other parts of the graph value.]]]
updateRDFGraph :: RDFGraph -> [Arc RDFLabel] -> RDFGraph
updateRDFGraph gr as = gr { statements=as }
-}

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
-- $Source: /file/cvsdev/HaskellRDF/RDFGraph.hs,v $
-- $Author: graham $
-- $Revision: 1.48 $
-- $Log: RDFGraph.hs,v $
-- Revision 1.48  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.47  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.46  2004/01/06 16:29:56  graham
-- Fix up module exports to avoid GHC warnings
--
-- Revision 1.45  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.44  2003/11/24 17:20:34  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.43  2003/11/24 15:46:03  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.42  2003/11/14 21:48:35  graham
-- First cut cardinality-checked datatype-constraint rules to pass test cases.
-- Backward chaining is still to do.
--
-- Revision 1.41  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.40  2003/10/24 21:02:42  graham
-- Changed kind-structure of LookupMap type classes.
--
-- Revision 1.39  2003/10/22 15:47:46  graham
-- Working on datatype inference support.
--
-- Revision 1.38  2003/10/01 00:36:25  graham
-- Added RDFGraph method to test for container membership property label.
-- Added RDFQuery filter function to select container membership properties.
--
-- Revision 1.37  2003/09/30 16:39:41  graham
-- Refactor proof code to use new ruleset logic.
-- Moved some support code from RDFProofCheck to RDFRuleset.
--
-- Revision 1.36  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.35  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.34  2003/07/03 20:31:07  graham
-- Add initial draft of datatype framework.
--
-- Revision 1.33  2003/07/02 21:27:30  graham
-- Graph closure with instance rule tested.
-- About to change ProofTest for graph forward chaining to return
-- a single result graph.
--
-- Revision 1.32  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.31  2003/06/27 21:02:59  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.30  2003/06/25 21:16:52  graham
-- Reworked N3 formatting logic to support proof display.
-- Basic proof display is working.
--
-- Revision 1.29  2003/06/19 19:49:07  graham
-- RDFProofCheck compiles, but test fails
--
-- Revision 1.28  2003/06/17 15:43:35  graham
-- remapNodes now accepts a node-mapping function rather than just
-- a Boolean to control conversion of query variable nodes to blank
-- nodes, and who knows what else.
--
-- Revision 1.27  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.26  2003/06/12 00:49:05  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
-- Revision 1.25  2003/06/10 17:38:34  graham
-- Remove some unneeded calss constraints from data type declarations
-- Reworked NSGraph to be an instance of Functor, replacing function
-- gmap with fmap.  Graph formulae are still not handled well:  the data types
-- will need re-working so that a "Formula lb" type constructor can be
-- introduced having the correct (* -> *) kind to be a Functor.
--
-- Revision 1.24  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.23  2003/05/30 15:04:56  graham
-- Fix references to defunct GraphHelpers module
--
-- Revision 1.22  2003/05/29 00:57:37  graham
-- Resolved swish performance problem, which turned out to an inefficient
-- method used by the parser to add arcs to a graph.
--
-- Revision 1.21  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.20  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.19  2003/05/27 19:15:50  graham
-- Graph merge (with blank node renaming) complete and passes tests.
--
-- Revision 1.18  2003/05/26 22:30:36  graham
-- Working on graph merge.
-- Added methods to Graph class for manipulating variable node.
-- Need to get RDFGraph to compile.  And test.
--
-- Revision 1.17  2003/05/23 19:33:36  graham
-- Added and tested RDF graph label translation functions
--
-- Revision 1.16  2003/05/23 00:02:42  graham
-- Fixed blank node id generation bug in N3Formatter
--
-- Revision 1.15  2003/05/14 22:39:23  graham
-- Initial formatter tests all run OK.
-- The formatter could still use so,me improvement,
-- but it
-- passes the minimal round-tripping tests.
--
-- Revision 1.14  2003/05/14 16:50:32  graham
-- Graph matching seems solid now:
-- RDFGraphTest and N3ParserTest pass all tests
-- Updated TODO file with comments from code
--
-- Revision 1.13  2003/05/08 18:55:36  graham
-- Updated graph matching module to deal consistently
-- with graphs containing formulae.  All graph tests now
-- run OK, but the GraphMatch module is a mess and
-- desperately needs restructuring.  Also, graph matching
-- performance needs to be improved.
--
-- Revision 1.12  2003/05/07 23:58:09  graham
-- More restructuring.
-- RDFGraphTest runs OK.
-- N3ParserTest needs to be updated to use new structure for formulae.
--
-- Revision 1.11  2003/05/07 19:25:00  graham
-- Restructured formula handling in RDF graph
--
-- Revision 1.10  2003/05/01 00:21:41  graham
-- Started refactoring LookupMap.
-- Revised module compiles OK.
-- Working on test module.
--
-- Revision 1.9  2003/04/29 22:07:10  graham
-- Some refactoring of N3 formatter.
-- N3 formatter now handles trivial cases.
-- More complex formatter test cases still to be developed.
--
-- Revision 1.8  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
-- Revision 1.7  2003/04/15 21:40:54  graham
-- N3Parser compiles
-- Some small changes to RDFGraph
-- Added some QName methods
--
-- Revision 1.6  2003/04/11 17:38:34  graham
-- Rename GraphLookupMap to LookupMap
--
-- Revision 1.5  2003/04/10 20:08:39  graham
-- Reorganized RDFGraph naming (RDFGraphTest OK)
-- Progressing N3Parser
--
-- Revision 1.4  2003/04/10 15:06:30  graham
-- RDFGraph now passes all test cases
--
-- Revision 1.3  2003/04/10 13:36:45  graham
-- Renamed GraphRDF to RDFGraph
--
-- Revision 1.1  2003/04/10 08:36:06  graham
-- Graph matching passes battery of new tests
-- Started work on RDF graph
--
