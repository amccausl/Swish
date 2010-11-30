--------------------------------------------------------------------------------
--  $Id: RDFQuery.hs,v 1.32 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFQuery
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines functions for querying an RDF graph to obtain
--  a set of variable substitutions, and to apply a set of variable
--  substitutions to a query pattern to obtain a new graph.
--
--  It also defines a few primitive graph access functions.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFQuery
    ( rdfQueryFind, rdfQueryFilter
    , rdfQueryBack, rdfQueryBackFilter, rdfQueryBackModify
    , rdfQueryInstance
    , rdfQuerySubs, rdfQueryBackSubs
    , rdfQuerySubsAll
    , rdfQuerySubsBlank, rdfQueryBackSubsBlank
    , rdfFindArcs, rdfSubjEq, rdfPredEq, rdfObjEq
    , rdfFindPredVal, rdfFindPredInt, rdfFindValSubj
    , rdfFindList
    -- debug
    , rdfQuerySubs2 )
where

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding, nullRDFVarBinding
    , RDFVarBindingFilter
    )

import Swish.HaskellRDF.RDFGraph
    ( Arc(..), LDGraph(..)
    , arcSubj, arcPred, arcObj
    , RDFLabel(..)
    , isDatatyped, isBlank, isQueryVar
    , getLiteralText, makeBlank
    , RDFTriple
    , RDFGraph, emptyRDFGraph
    , allLabels, remapLabels
    , res_rdf_first
    , res_rdf_rest
    , res_rdf_nil
    )

import Swish.HaskellRDF.MapXsdInteger
    ( mapXsdInteger
    )

import Swish.HaskellRDF.Datatype
    ( DatatypeMap(..)
    )

import Swish.HaskellRDF.VarBinding
    ( VarBinding(..)
    , makeVarBinding
    , applyVarBinding, joinVarBindings
    , VarBindingModify(..)
    , VarBindingFilter(..)
    )

import Swish.HaskellRDF.Vocabulary
    ( xsd_integer, xsd_nonneg_integer
    )

import Swish.HaskellUtils.FunctorM
    ( FunctorM(..) )

import Swish.HaskellUtils.ListHelpers
    ( listProduct, allp, anyp )

import Control.Monad.State
    ( State(..), modify )

import Data.Maybe
    ( catMaybes, isJust, fromJust )

------------------------------------------------------------
--  Primitive RDF graph queries
------------------------------------------------------------

-- |Basic graph-query function.
--  A very basic form of graph query, a query graph and
--  a target graph, and returns a list of 'RDFVarBinding'
--  values, each of which corresponds to a set of variable
--  bindings that make the query graph a subgraph of the
--  target graph, or [] if the query cannot be matched.
--
--  The triples of the query graph are matched sequentially
--  against the target graph, each taking account of any
--  variable bindings that have already been determined,
--  and adding new variable bindings as triples containing
--  query variables are matched against the graph.
--
rdfQueryFind :: RDFGraph -> RDFGraph -> [RDFVarBinding]
rdfQueryFind qg =
    rdfQueryPrim1 matchQueryVariable nullRDFVarBinding (getArcs qg)

--  Helper function to match query against a graph.
--  A node-query function is supplied to determine how query nodes
--  are matched against target graph nodes.  Also supplied is
--  an initial variable binding.
--
rdfQueryPrim1 ::
    NodeQuery RDFLabel -> RDFVarBinding -> [Arc RDFLabel]
    -> RDFGraph
    -> [RDFVarBinding]
rdfQueryPrim1 _     initv []       _  = [initv]
rdfQueryPrim1 nodeq initv (qa:qas) tg =
    let
        qam  = fmap (applyVarBinding initv) qa      -- subst vars already bound
        newv = rdfQueryPrim2 nodeq qam tg           -- new bindings, or null
    in
        concat
            [ rdfQueryPrim1 nodeq v2 qas tg
            | v1 <- newv
            , let v2 = joinVarBindings initv v1
            ]

--  Match single query term against graph, and return any new sets
--  of variable bindings thus defined, or [] if the query term
--  cannot be matched.  Each of the RDFVarBinding values returned
--  represents an alternative possible match for the query arc.
--
rdfQueryPrim2 ::
    NodeQuery RDFLabel -> Arc RDFLabel
    -> RDFGraph
    -> [RDFVarBinding]
rdfQueryPrim2 nodeq qa tg =
        catMaybes $ map (getBinding nodeq qa) $ getArcs tg

-- |RDF query filter.  This function applies a supplied query binding
--  filter to the result from a call of 'rdfQueryFind'.
--
--  If none of the query bindings found satisfy the filter, a null
--  list is returned (which is what 'rdfQueryFind' returns if the
--  query cannot be satisfied).
--
--  (Because of lazy evaluation, this should be as efficient as
--  applying the filter as the search proceeds.  I started to build
--  the filter logic into the query function itself, with consequent
--  increase in complexity, until I remembered lazy evaluation lets
--  me keep things separate.)
--
rdfQueryFilter ::
    RDFVarBindingFilter -> [RDFVarBinding] -> [RDFVarBinding]
rdfQueryFilter qbf qbs = filter (vbfTest qbf) qbs

------------------------------------------------------------
--  Backward-chaining RDF graph queries
------------------------------------------------------------

-- |Reverse graph-query function.
--  Similar to rdfQueryFind, but with different success criteria.
--  The query graph is matched against the supplied graph,
--  but not every triple of the query is required to be matched.
--  Rather, every triple of the target graph must be matched,
--  and substitutions for just the variables thus bound are
--  returned.  In effect, these are subsitutions in the query
--  that entail the target graph (where rdfQueryFind returns
--  substitutions that are entailed by the target graph).
--
--  Multiple substitutions may be used together, so the result
--  returned is a list of lists of query bindings.  Each inner
--  list contains several variable bindings that must all be applied
--  separately to the closure antecendents to obtain a collection of
--  expressions that together are antecedent to the supplied
--  conclusion.  A null list of bindings returned means the
--  conclusion can be inferred without any antecedents.
--
--  Note:  in back-chaining, the conditions required to prove each
--  target triple are derived independently, using the inference rule
--  for each such triple, so there are no requirements to check
--  consistency with previously determined variable bindings, as
--  there are when doing forward chaining.  A result of this is that
--  there may be redundant triples generated by the back-chaining
--  process.  Any process using back-chaining should deal with the
--  results returned accordingly.
--
--  An empty outer list is returned if no combination of
--  substitutions can infer the supplied target.
--
rdfQueryBack :: RDFGraph -> RDFGraph -> [[RDFVarBinding]]
rdfQueryBack qg tg =
    rdfQueryBack1 matchQueryVariable [] (getArcs qg) (getArcs tg)

rdfQueryBack1 ::
    NodeQuery RDFLabel -> [RDFVarBinding] -> [Arc RDFLabel] -> [Arc RDFLabel]
    -> [[RDFVarBinding]]
rdfQueryBack1 _     initv _   []       = [initv]
rdfQueryBack1 nodeq initv qas (ta:tas) = concat
    [ rdfQueryBack1 nodeq (nv:initv) qas tas
    | nv <- rdfQueryBack2 nodeq qas ta ]

--  Match a query against a single graph term, and return any new sets of
--  variable bindings thus defined.  Each member of the result is an
--  alternative possible set of variable bindings.  An empty list returned
--  means no match.
--
rdfQueryBack2 ::
    NodeQuery RDFLabel -> [Arc RDFLabel] -> Arc RDFLabel
    -> [RDFVarBinding]
rdfQueryBack2 nodeq qas ta =
    [ fromJust b | qa <- qas, let b = getBinding nodeq qa ta, isJust b ]

-- |RDF back-chaining query filter.  This function applies a supplied
--  query binding filter to the result from a call of 'rdfQueryBack'.
--
--  Each inner list contains bindings that must all be used to satisfy
--  the backchain query, so if any query binding does not satisfy the
--  filter, the entire corresponding row is removed
rdfQueryBackFilter ::
    RDFVarBindingFilter -> [[RDFVarBinding]] -> [[RDFVarBinding]]
rdfQueryBackFilter qbf qbss = filter (and . map (vbfTest qbf)) qbss

-- |RDF back-chaining query modifier.  This function applies a supplied
--  query binding modifier to the result from a call of 'rdfQueryBack'.
--
--  Each inner list contains bindings that must all be used to satisfy
--  a backchaining query, so if any query binding does not satisfy the
--  filter, the entire corresponding row is removed
--
rdfQueryBackModify ::
    VarBindingModify a b -> [[VarBinding a b]] -> [[VarBinding a b]]
rdfQueryBackModify qbm qbss = concatMap (rdfQueryBackModify1 qbm) qbss

--  Auxiliary back-chaining query variable binding modifier function:
--  for a supplied list of variable bindings, all of which must be used
--  together when backchaining:
--  (a) make each list member into a singleton list
--  (b) apply the binding modifier to each such list, which may result
--      in a list with zero, one or more elements.
--  (c) return the listProduct of these, each member of which is
--      an alternative list of variable bindings, where the members of
--      each alternative must be used together.
--
rdfQueryBackModify1 ::
    VarBindingModify a b -> [VarBinding a b] -> [[VarBinding a b]]
rdfQueryBackModify1 qbm qbs = listProduct $ map ((vbmApply qbm) . (:[])) qbs

------------------------------------------------------------
--  Simple entailment graph query
------------------------------------------------------------

-- |Simple entailment (instance) graph query.
--  This function queries a graph to find instances of the
--  query graph in the target graph.  It is very similar
--  to the normal forward chaining query 'rdfQueryFind',
--  except that blank nodes rather than query variable nodes
--  in the query graph are matched against nodes in the target
--  graph.  Neither graph should contain query variables.
--
--  An "instance" is defined by the RDF semantics specification,
--  per <http://www.w3.org/TR/rdf-mt/>, and is obtained by replacing
--  blank nodes with URIs, literals or other blank nodes.  RDF
--  "simple entailment" can be determined in terms of instances.
--  This function looks for a subgraph of the target graph that
--  is an instance of the query graph, which is a necessary and
--  sufficient condition for RDF entailment (see the Interpolation
--  Lemma in RDF Semantics, section 1.2).
--
--  It is anticipated that this query function can be used in
--  conjunction with backward chaining to determine when the
--  search for sufficient antecendents to determine some goal
--  has been concluded.
rdfQueryInstance :: RDFGraph -> RDFGraph -> [RDFVarBinding]
rdfQueryInstance qg =
    rdfQueryPrim1 matchQueryBnode nullRDFVarBinding (getArcs qg)

------------------------------------------------------------
--  Primitive RDF graph query support functions
------------------------------------------------------------

-- |Type of query node testing function.  Return value is:
--  - Nothing    if no match
--  - Just True  if match with new variable binding
--  - Just False if match with new variable binding
type NodeQuery a = a -> a -> Maybe Bool

--  Extract query binding from matching a single query triple with a
--  target triple, returning:
--  - Nothing if the query is not matched
--  - Just nullVarBinding if there are no new variable bindings
--  - Just binding is a new query binding for this match
getBinding ::
    NodeQuery RDFLabel -> Arc RDFLabel -> Arc RDFLabel
    -> Maybe RDFVarBinding
getBinding nodeq (Arc s1 p1 o1) (Arc s2 p2 o2) =
    makeBinding [(s1,s2),(p1,p2),(o1,o2)] []
    where
        makeBinding [] bs = Just $ makeVarBinding bs
        makeBinding (vr@(v,r):bvrs) bs =
            case nodeq v r of
                Nothing    -> Nothing
                Just False -> makeBinding bvrs bs
                Just True  -> makeBinding bvrs (vr:bs)

--  Match variable node against target node, returning
--  Nothing if they do not match, Just True if a variable
--  node is matched (thereby creating a new variable binding)
--  or Just False if a non-blank node is matched.
matchQueryVariable :: NodeQuery RDFLabel
matchQueryVariable (Var _) _ = Just True
matchQueryVariable q t
    | q == t    = Just False
    | otherwise = Nothing

--  Match blank query node against target node, returning
--  Nothing if they do not match, Just True if a blank node
--  is matched (thereby creating a new equivalence) or
--  Just False if a non-blank node is matched.
matchQueryBnode :: NodeQuery RDFLabel
matchQueryBnode (Blank _) _ = Just True
matchQueryBnode q t
    | q == t    = Just False
    | otherwise = Nothing

------------------------------------------------------------
--  Substitute results from RDF query back into a graph
------------------------------------------------------------

-- |Graph substitution function.
--  Uses the supplied variable bindings to substitute variables in
--  a supplied graph, returning a list of result graphs corresponding
--  to each set of variable bindings applied to the input graph.
--  This function is used for formward chaining substitutions, and
--  returns only those result graphs for which all query variables
--  are bound.
rdfQuerySubs :: [RDFVarBinding] -> RDFGraph -> [RDFGraph]
rdfQuerySubs vars gr =
    map fst $ filter (null . snd) $ rdfQuerySubsAll vars gr

-- |Graph back-substitution function.
--  Uses the supplied variable bindings from 'rdfQueryBack' to perform
--  a series of variable substitutions in a supplied graph, returning
--  a list of lists of result graphs corresponding to each set of variable
--  bindings applied to the input graphs.
--
--  The outer list of the result contains alternative antecedent lists
--  that satisfy the query goal.  Each inner list contains graphs that
--  must all be inferred to satisfy the query goal.
rdfQueryBackSubs ::
    [[RDFVarBinding]] -> RDFGraph -> [[(RDFGraph,[RDFLabel])]]
rdfQueryBackSubs varss gr = [ rdfQuerySubsAll v gr | v <- varss ]

-- |Graph substitution function.
--  This function performs the substitutions and returns a list of
--  result graphs each paired with a list unbound variables in each.
rdfQuerySubsAll :: [RDFVarBinding] -> RDFGraph -> [(RDFGraph,[RDFLabel])]
rdfQuerySubsAll vars gr = [ rdfQuerySubs2 v gr | v <- vars ]

-- |Graph substitution function.
--  This function performs each of the substitutions in 'vars', and
--  replaces any nodes corresponding to unbound query variables
--  with new blank nodes.
rdfQuerySubsBlank :: [RDFVarBinding] -> RDFGraph -> [RDFGraph]
rdfQuerySubsBlank vars gr =
    [ remapLabels vs bs makeBlank g
    | v <- vars
    , let (g,vs) = rdfQuerySubs2 v gr
    , let bs     = allLabels isBlank g
    ]

-- |Graph back-substitution function, replacing variables with bnodes.
--  Uses the supplied variable bindings from 'rdfQueryBack' to perform
--  a series of variable substitutions in a supplied graph, returning
--  a list of lists of result graphs corresponding to each set of variable
--  bindings applied to the input graphs.
--
--  The outer list of the result contains alternative antecedent lists
--  that satisfy the query goal.  Each inner list contains graphs that
--  must all be inferred to satisfy the query goal.
rdfQueryBackSubsBlank :: [[RDFVarBinding]] -> RDFGraph -> [[RDFGraph]]
rdfQueryBackSubsBlank varss gr = [ rdfQuerySubsBlank v gr | v <- varss ]

--  This function applies a substitution for a single set of variable
--  bindings, returning the result and a list of unbound variables.
--  It uses a state transformer monad to collect the list of
--  unbound variables.
--
--  Adding an empty graph forces elimination of duplicate arcs.
rdfQuerySubs2 :: RDFVarBinding -> RDFGraph -> (RDFGraph,[RDFLabel])
rdfQuerySubs2 varb gr = (add emptyRDFGraph g,vs)
    where
        (g,vs) = runState ( fmapM (mapNode varb) gr ) []

--  Auxiliary monad function for rdfQuerySubs2.
--  This returns a state transformer Monad which in turn returns the
--  substituted node value based on the supplied query variable bindings.
--  The monad state is a list of labels which accumulates all those
--  variables seen for which no substitution was available.
mapNode :: RDFVarBinding -> RDFLabel -> State [RDFLabel] RDFLabel
mapNode varb lab =
    case vbMap varb lab of
        Just v  -> return v
        Nothing ->
            if isQueryVar lab then
                do  { modify (addVar lab)
                    ; return lab
                    }
            else
                return lab

--  Add variable to list of variables, if not already there
addVar :: RDFLabel -> [RDFLabel] -> [RDFLabel]
addVar var vars = if var `elem` vars then vars else var:vars

------------------------------------------------------------
--  Simple lightweight query primitives
------------------------------------------------------------
--
--  [[[TODO:  modify above code to use these for all graph queries]]]

-- |rdfFindArcs is the main function here:  it takes a predicate on an
--  RDF statement and a graph, and returns all statements in the graph
--  satisfying that predicate.
--
--  Use combinations of these as follows:
--
--  (a) find all statements with given subject:
--          rdfQuerySimple (rdfSubjEq s)
--  (b) find all statements with given property:
--          rdfQuerySimple (rdfPredEq p)
--  (c) find all statements with given object:
--          rdfQuerySimple (rdfObjEq  o)
--  (d) find all statements matching conjunction of these conditions:
--          rdfQuerySimple (allp [...])
--  (e) find all statements matching disjunction of these conditions:
--          rdfQuerySimple (anyp [...])
--  (See ListHelpers for allp, anyp.)
--
--  Custom predicates can also be used.
--
rdfFindArcs :: (RDFTriple -> Bool) -> RDFGraph -> [RDFTriple]
rdfFindArcs p = filter p . getArcs

-- |Test if statement has given subject
rdfSubjEq :: RDFLabel -> RDFTriple -> Bool
rdfSubjEq s = (s==) . arcSubj

-- |Test if statement has given predicate
rdfPredEq :: RDFLabel -> RDFTriple -> Bool
rdfPredEq p = (p==) . arcPred

-- |Test if statement has given object
rdfObjEq  :: RDFLabel -> RDFTriple -> Bool
rdfObjEq o  = (o==) . arcObj

{-
-- |Find statements with given subject
rdfFindSubj :: RDFLabel -> RDFGraph -> [RDFTriple]
rdfFindSubj s = rdfFindArcs (rdfSubjEq s)

-- |Find statements with given predicate
rdfFindPred :: RDFLabel -> RDFGraph -> [RDFTriple]
rdfFindPred p = rdfFindArcs (rdfPredEq p)
-}

-- |Find values of given predicate for a given subject
rdfFindPredVal :: RDFLabel -> RDFLabel -> RDFGraph -> [RDFLabel]
rdfFindPredVal s p = map arcObj . rdfFindArcs (allp [rdfSubjEq s,rdfPredEq p])

-- |Find integer values of a given predicate for a given subject
rdfFindPredInt :: RDFLabel -> RDFLabel -> RDFGraph -> [Integer]
rdfFindPredInt s p = catMaybes . map getint . filter isint . pvs
    where
        pvs = rdfFindPredVal s p
        isint  = anyp
            [ isDatatyped xsd_integer
            , isDatatyped xsd_nonneg_integer
            ]
        getint = mapL2V mapXsdInteger . getLiteralText

-- |Find all subjects that have a of given value for for a given predicate
rdfFindValSubj :: RDFLabel -> RDFLabel -> RDFGraph -> [RDFLabel]
rdfFindValSubj p o = map arcSubj . rdfFindArcs (allp [rdfPredEq p,rdfObjEq o])

------------------------------------------------------------
--  List query
------------------------------------------------------------

-- |Return a list of nodes that comprise an rdf:collection value,
--  given the head element of the collection.  If the list is
--  ill-formed then some arbitrary value is returned.
--
rdfFindList :: RDFGraph -> RDFLabel -> [RDFLabel]
rdfFindList gr hd = findhead $ rdfFindList gr findrest
    where
        findhead  = headOr (const []) $
                    map (:) (rdfFindPredVal hd res_rdf_first gr)
        findrest  = headOr res_rdf_nil (rdfFindPredVal hd res_rdf_rest gr)
        {-
        findhead  = headOr (const [])
                    [ (ob:) | Arc _ sb ob <- subgr, sb == res_rdf_first ]
        findrest  = headOr res_rdf_nil
                    [ ob | Arc _ sb ob <- subgr, sb == res_rdf_rest  ]
        subgr     = filter ((==) hd . arcSubj) $ getArcs gr
        -}
        headOr    = foldr const
        -- headOr _ (x:_) = x
        -- headOr x []    = x

------------------------------------------------------------
--  Interactive tests
------------------------------------------------------------

{-
s1 = Blank "s1"
p1 = Blank "p1"
o1 = Blank "o1"
s2 = Blank "s2"
p2 = Blank "p2"
o2 = Blank "o2"
qs1 = Var "s1"
qp1 = Var "p1"
qo1 = Var "o1"
qs2 = Var "s2"
qp2 = Var "p2"
qo2 = Var "o2"

qa1 = Arc qs1 qp1 qo1
qa2 = Arc qs2 qp2 qo2
qa3 = Arc qs2  p2 qo2
ta1 = Arc s1 p1 o1
ta2 = Arc s2 p2 o2

g1  = toRDFGraph [ta1,ta2]
g2  = toRDFGraph [qa3]

gb1  = getBinding matchQueryVariable qa1 ta1    -- ?s1=_:s1, ?p1=_:p1, ?o1=_:o1
gvs1 = qbMap (fromJust gb1) qs1                 -- _:s1
gvp1 = qbMap (fromJust gb1) qp1                 -- _:p1
gvo1 = qbMap (fromJust gb1) qo1                 -- _:o1
gvs2 = qbMap (fromJust gb1) qs2                 -- Nothing

gb3  = getBinding matchQueryVariable qa3 ta1    -- Nothing
gb4  = getBinding matchQueryVariable qa3 ta2    -- ?s2=_:s1, ?o2=_:o1

mqvs1 = matchQueryVariable qs2 s1
mqvp1 = matchQueryVariable p2  p1

--  rdfQueryFind

qfa  = rdfQueryFind g2 g1

qp2a = rdfQueryPrim2 matchQueryVariable qa3 g1
-}

{- more tests

qb1a = rdfQueryBack1 [] [qa1] [ta1,ta2]
qb1 = rdfQueryBack1 [] [qa1,qa2] [ta1,ta2]
ql1 = length qb1
qv1 = map (qb1!!0!!0) [qs1,qp1,qo1,qs2,qp2,qo2]
qv2 = map (qb1!!0!!1) [qs1,qp1,qo1,qs2,qp2,qo2]
qv3 = map (qb1!!1!!0) [qs1,qp1,qo1,qs2,qp2,qo2]
qv4 = map (qb1!!1!!1) [qs1,qp1,qo1,qs2,qp2,qo2]
qv5 = map (qb1!!2!!0) [qs1,qp1,qo1,qs2,qp2,qo2]
qv6 = map (qb1!!2!!1) [qs1,qp1,qo1,qs2,qp2,qo2]
qv7 = map (qb1!!3!!0) [qs1,qp1,qo1,qs2,qp2,qo2]
qv8 = map (qb1!!3!!1) [qs1,qp1,qo1,qs2,qp2,qo2]

qb2 = rdfQueryBack2 matchQueryVariable [qa1,qa2] ta1
ql2 = length qb2
qv1 = map (qbMap $ head qb2)        [qs1,qp1,qo1,qs2,qp2,qo2]
qv2 = map (qbMap $ head $ tail qb2) [qs1,qp1,qo1,qs2,qp2,qo2]
qb3 = rdfQueryBack2 matchQueryVariable [qa1,qa3] ta1

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
-- $Source: /file/cvsdev/HaskellRDF/RDFQuery.hs,v $
-- $Author: graham $
-- $Revision: 1.32 $
-- $Log: RDFQuery.hs,v $
-- Revision 1.32  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.31  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.30  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.29  2003/11/14 16:04:43  graham
-- Add primitive query to get integer values from a graph.
--
-- Revision 1.28  2003/11/14 16:01:30  graham
-- Separate RDFVarBinding from module RDFQuery.
--
-- Revision 1.27  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.26  2003/10/16 16:01:48  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.25  2003/10/15 16:40:52  graham
-- Reworked RDFQuery to use new query binding framework.
-- (Note: still uses VarBindingFilter rather than VarBindingModify.
-- The intent is to incorproate the VarBindingModify logic into RDFProof,
-- displaying the existing use of BindingFilter.)
--
-- Revision 1.24  2003/10/09 17:16:13  graham
-- Added test cases to exercise features of rules used to capture
-- RDF semantics.  Also added proof test case using XML literal.
--
-- Revision 1.23  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.22  2003/10/01 00:38:00  graham
-- Correct error in previous commit.
--
-- Revision 1.21  2003/10/01 00:36:25  graham
-- Added RDFGraph method to test for container membership property label.
-- Added RDFQuery filter function to select container membership properties.
--
-- Revision 1.20  2003/09/30 20:02:40  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.19  2003/09/30 16:39:41  graham
-- Refactor proof code to use new ruleset logic.
-- Moved some support code from RDFProofCheck to RDFRuleset.
--
-- Revision 1.18  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.17  2003/07/03 20:31:07  graham
-- Add initial draft of datatype framework.
--
-- Revision 1.16  2003/07/02 22:39:36  graham
-- Subgraph entailment and Graph closure instance entailment rules
-- now tested.  RDF forward chaining revised to combine output graphs,
-- to preserve blank node relationships.
--
-- Revision 1.15  2003/07/02 21:27:30  graham
-- Graph closure with instance rule tested.
-- About to change ProofTest for graph forward chaining to return
-- a single result graph.
--
-- Revision 1.14  2003/07/02 13:51:14  graham
-- Intermediate save:  partially coded RDFS rules.
--
-- Revision 1.13  2003/06/27 20:46:00  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.12  2003/06/26 15:37:23  graham
-- Added rdfQueryInstance, and tests, all works.
--
-- Revision 1.11  2003/06/25 09:52:25  graham
-- Replaced Rule class with algebraic data type
--
-- Revision 1.10  2003/06/19 19:49:07  graham
-- RDFProofCheck compiles, but test fails
--
-- Revision 1.9  2003/06/19 00:26:29  graham
-- Query binding filter methods tested.
--
-- Revision 1.8  2003/06/18 23:37:53  graham
-- Added query binding filter methods.  Not yet tested.
--
-- Revision 1.7  2003/06/18 14:59:27  graham
-- Augmented query variable binding structure.
-- RDFQuery tests OK.
--
-- Revision 1.6  2003/06/18 01:29:29  graham
-- Fixed up some problems with backward chaining queries.
-- Query test cases still to complete.
-- Proof incomplete.
--
-- Revision 1.5  2003/06/17 17:53:08  graham
-- Added backward chaining query primitive.
--
-- Revision 1.4  2003/06/17 16:29:20  graham
-- Eliminate redundant Maybe in return type of rdfQueryPrim.
-- (A null list suffices for the Nothing case.)
--
-- Revision 1.3  2003/06/17 15:59:09  graham
-- Update to use revised version of remapNodes, which accepts a
-- node-mapping function rather than just a Boolean to control conversion
-- of query variable nodes to blank
-- nodes.
--
-- Revision 1.2  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.1  2003/06/12 00:49:06  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
