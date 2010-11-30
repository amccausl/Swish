{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XUndecidableInstances #-}
--------------------------------------------------------------------------------
--  $Id: RDFProof.hs,v 1.22 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFProof
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98 + multi-parameter classes
--
--  This module instantiates the 'Proof' framework for
--  constructing proofs over RDFGraph expressions.
--  The intent is that this can be used to test some
--  correspondences between the RDF Model theory and
--  corresponding proof theory based on closure rules
--  applied to the graph, per <http://www.w3.org/TR/rdf-mt/>.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFProof
    ( RDFProof, RDFProofStep
    , makeRDFProof, makeRDFProofStep
    , makeRdfInstanceEntailmentRule
    , makeRdfSubgraphEntailmentRule
    , makeRdfSimpleEntailmentRule )
where

import Swish.HaskellRDF.RDFQuery
    (  rdfQueryInstance
    , rdfQuerySubs 
    )

import Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFRuleset )

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..), RDFGraph
    --, makeBlank
    , merge , allLabels , remapLabelList
    {-, newNode, newNodes
    , toRDFGraph -}, emptyRDFGraph
    )

import Swish.HaskellRDF.VarBinding
    (  makeVarBinding
    )

import Swish.HaskellRDF.Proof
    ( Proof(..), Step(..) )

import Swish.HaskellRDF.Rule
    ( Expression(..), Rule(..) )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..)
    )

import Swish.HaskellRDF.GraphClass
    ( Label(..), LDGraph(..), replaceArcs )

import Swish.HaskellUtils.LookupMap
    ( makeLookupMap, mapFind )

import Swish.HaskellUtils.ListHelpers
    ( subset
    , powerSet
    , powerSequences_len
    , flist
    )

------------------------------------------------------------
--  Type instantiation of Proof framework for RDFGraph data
------------------------------------------------------------
--
--  This is a partial instantiation of the proof framework.
--  Details for applying inference rules are specific to the
--  graph instance type.

------------------------------------------------------------
--  Proof datatypes for graph values
------------------------------------------------------------

-- |Instances of LDGraph are also instance of the
--  Expression class, for which proofs can be constructed.
--  The empty RDF graph is always True (other enduring
--  truths are asserted as axioms.
instance (Label lb, LDGraph lg lb) => Expression (lg lb) where
    isValid gr = null $ getArcs gr

------------------------------------------------------------
--  Define RDF-specific types for proof framework
------------------------------------------------------------

type RDFProof     = Proof RDFGraph

type RDFProofStep = Step RDFGraph

------------------------------------------------------------
--  Helper functions for constructing proofs on RDF graphs
------------------------------------------------------------

-- |Make an RDF graph proof step
--
--  rul     is a rule to use for this step
--  ants    is a list of antecedent RDF formulae for this step
--  con     is an RDF formula that is the consequent for this step
--
makeRDFProofStep ::
    RDFRule -> [RDFFormula] -> RDFFormula
    -> RDFProofStep
makeRDFProofStep rul ants con = Step
    { stepRule = rul
    , stepAnt  = ants
    , stepCon  = con
    }

-- |Make an RDF proof
--
--  rsets   is a list of RDF rulesets that constitute a proof context
--          for this proof.
--  base    is an initial statement from which the goal is claimed
--          to be proven.
--  goal    is a statement that is claimed to be proven.
--
makeRDFProof ::
    [RDFRuleset] -> RDFFormula -> RDFFormula
    -> [RDFProofStep]
    -> RDFProof
makeRDFProof rsets base goal steps = Proof
    { proofContext = rsets
    , proofInput   = base
    , proofResult  = goal
    , proofChain   = steps
    }

------------------------------------------------------------
--  RDF instance entailment inference rule
------------------------------------------------------------

-- |Make an inference rule dealing with RDF instance entailment;
--  i.e. entailments that are due to replacement of a URI or literal
--  node with a blank node.
--
--  The part of this rule expected to be useful is 'checkInference'.
--  The 'fwdApply' and 'bwdApply' functions defined here may return
--  rather large results if applied to graphs with many variables or
--  a large vocabulary, and are defined for experimentation.
--
--  Forward and backward chaining is performed with respect to a
--  specified vocabulary.  In the case of backward chaining, it would
--  otherwise be impossible to bound the options thus generated.
--  In the case of forward chaining, it is often not desirable to
--  have the properties generalized.  If forward or backward backward
--  chaining will not be used, supply an empty vocabulary.
--  Note:  graph method 'allNodes' can be used to obtain a list of all
--  the subjects and objuects used ina  graph, not counting nested
--  formulae;  use a call of the form:
--    allNodes (not . labelIsVar) graph
makeRdfInstanceEntailmentRule :: ScopedName -> [RDFLabel] -> RDFRule
makeRdfInstanceEntailmentRule name vocab = newrule
    where
        newrule = Rule
            { ruleName = name
            , fwdApply = rdfInstanceEntailFwdApply vocab
            , bwdApply = rdfInstanceEntailBwdApply vocab
            , checkInference = rdfInstanceEntailCheckInference
            }

--  Instance entailment forward chaining
--
--  Note:  unless the initial graph is small, the total result
--  here could be very large.  The existential generalizations are
--  sequenced in increasing number of substitutions applied.
--  This sequencing is determined by the powerset function used,
--  which generates subsets in increasing order of size
--  (see module 'ListHelpers').
--
--  The instances generated are all copies of the merge of the
--  supplied graphs, with some or all of the non-variable nodes
--  replaced by blank nodes.
rdfInstanceEntailFwdApply :: [RDFLabel] -> [RDFGraph] -> [RDFGraph]
rdfInstanceEntailFwdApply vocab ante =
    let
        --  Merge antecedents to single graph, renaming bnodes if needed.
        --  (Null test and using 'foldl1' to avoid merging if possible.)
        mergeGraph  = if null ante then emptyRDFGraph
                        else (foldl1 merge ante)
        --  Obtain lists of variable and non-variable nodes
        --  (was: nonvarNodes = allLabels (not . labelIsVar) mergeGraph)
        nonvarNodes = vocab
        varNodes    = allLabels (labelIsVar) mergeGraph
        --  Obtain list of possible remappings for non-variable nodes
        mapList     = remapLabelList nonvarNodes varNodes
        mapSubLists = powerSet mapList
        mapGr ls gr = fmap (\l -> mapFind l l (makeLookupMap ls)) gr
    in
        --  Return all remappings of the original merged graph
        flist (map mapGr mapSubLists) mergeGraph

--  Instance entailment backward chaining (for specified vocabulary)
--
--  [[[TODO:  this is an incomplete implementation, there being no
--  provision for instantiating some variables and leaving others
--  alone.  This can be overcome in many cases by combining instance
--  and subgraph chaining.
--  Also, there is no provision for instantiating some variables in
--  a triple and leaving others alone.  This may be fixed later if
--  this function is really needed to be completely faithful to the
--  precise notion of instance entailment.]]]
rdfInstanceEntailBwdApply :: [RDFLabel] -> RDFGraph -> [[RDFGraph]]
rdfInstanceEntailBwdApply vocab cons =
    let
        --  Obtain list of variable nodes
        varNodes     = allLabels (labelIsVar) cons
        --  Generate a substitution for each combination of variable
        --  and vocabulary node.
        varBindings  = map (makeVarBinding . zip varNodes) vocSequences
        vocSequences = powerSequences_len (length varNodes) vocab
    in
        --  Generate a substitution for each combination of variable
        --  and vocabulary:
        [ rdfQuerySubs [v] cons | v <- varBindings ]

--  Instance entailment inference checker
rdfInstanceEntailCheckInference :: [RDFGraph] -> RDFGraph -> Bool
rdfInstanceEntailCheckInference ante cons =
    let
        mante = if null ante then emptyRDFGraph -- merged antecedents
                    else (foldl1 merge ante)
        qvars = rdfQueryInstance cons mante     -- all query matches
        bsubs = rdfQuerySubs qvars cons         -- all back substitutions
    in
        --  Return True if any back-substitution matches the original
        --  merged antecendent graph.
        or (map (mante ==) bsubs)

--  Instance entailment notes.
--
--  Relation to simple entailment (s-entails):
--
--  (1) back-substitution yields original graph
--  ex:s1 ex:p1 ex:o1  s-entails  ex:s1 ex:p1 _:o1  by [_:o1/ex:o1]
--
--  (2) back-substitution yields original graph
--  ex:s1 ex:p1 ex:o1  s-entails  ex:s1 ex:p1 _:o2  by [_:o2/ex:o1]
--  ex:s1 ex:p1  _:o1             ex:s1 ex:p1 _:o3     [_:o3/_:o1]
--
--  (3) back-substitution does not yield original graph
--  ex:s1 ex:p1 ex:o1  s-entails  ex:s1 ex:p1 _:o2  by [_:o2/ex:o1]
--  ex:s1 ex:p1  _:o1             ex:s1 ex:p1 _:o3     [_:o3/ex:o1]
--
--  (4) consider
--  ex:s1 ex:p1 ex:o1  s-entails  ex:s1 ex:p1 ex:o1
--  ex:s1 ex:p1 ex:o2             ex:s1 ex:p1 ex:o2
--  ex:s1 ex:p1 ex:o3             ex:s1 ex:p1 _:o1
--                                ex:s1 ex:p1 _:o2
--  where [_:o1/ex:o1,_:o2/ex:o2] yields a simple entailment but not
--  an instance entailment, but [_:o1/ex:o3,_:o2/ex:o3] is also
--  (arguably) an instance entailment.  Therefore, it is not sufficient
--  to look only at the "largest" substitutions to determine instance
--  entailment.
--
--  All this means that when checking for instance entailment by
--  back substitution, all of the query results must be checked.
--  This seems clumsy.  If this function is heavily used with
--  multiple query matches, a modified query that uses each
--  triple of the target graph exactly once may be required.

------------------------------------------------------------
--  RDF subgraph entailment inference rule
------------------------------------------------------------

-- |Make an inference rule dealing with RDF subgraph entailment.
--  The part of this rule expected to be useful is 'checkInference'.
--  The 'fwdApply' function defined here may return rather large
--  results.  But in the name of completeness and experimentation
--  with the possibilities of lazy evaluation, it has been defined.
--
--  Backward chaining is not performed, as there is no reasonable way
--  to choose a meaningful supergraph of that supplied.
makeRdfSubgraphEntailmentRule :: ScopedName -> RDFRule
makeRdfSubgraphEntailmentRule name = newrule
    where
        newrule = Rule
            { ruleName = name
            , fwdApply = rdfSubgraphEntailFwdApply
            , bwdApply = const []
            , checkInference = rdfSubgraphEntailCheckInference
            }

--  Subgraph entailment forward chaining
--
--  Note:  unless the initial graph is small, the total result
--  here could be very large.  The subgraphs are sequenced in
--  increasing size of the sub graph.  This sequencing is determined
--  by the 'powerSet' function used which generates subsets in
--  increasing order of size (see module 'ListHelpers').
rdfSubgraphEntailFwdApply :: [RDFGraph] -> [RDFGraph]
rdfSubgraphEntailFwdApply ante =
    let
        --  Merge antecedents to single graph, renaming bnodes if needed.
        --  (Null test and using 'foldl1' to avoid merging if possible.)
        mergeGraph  = if null ante then emptyRDFGraph
                        else (foldl1 merge ante)
    in
        --  Return all subgraphs of the full graph constructed above
        map (replaceArcs mergeGraph) (init $ powerSet $ getArcs mergeGraph)

--  Subgraph entailment inference checker
--
--  This is of dubious utiltiy, as it doesn't allow for node renaming.
--  The simple entailment inference rule is probably more useful here.
rdfSubgraphEntailCheckInference :: [RDFGraph] -> RDFGraph -> Bool
rdfSubgraphEntailCheckInference ante cons =
    let
        --  Combine antecedents to single graph, renaming bnodes if needed.
        --  (Null test and using 'foldl1' to avoid merging if possible.)
        fullGraph  = if null ante then emptyRDFGraph
                        else (foldl1 add ante)
    in
        --  Check each consequent graph arc is in the antecedent graph
        getArcs cons `subset` getArcs fullGraph

------------------------------------------------------------
--  RDF simple entailment inference rule
------------------------------------------------------------

-- |Make an inference rule dealing with RDF simple entailment.
--  The part of this rule expected to be useful is 'checkInference'.
--  The 'fwdApply' and 'bwdApply' functions defined return null
--  results, indicating that they are not useful for the purposes
--  of proof discovery.
makeRdfSimpleEntailmentRule :: ScopedName -> RDFRule
makeRdfSimpleEntailmentRule name = newrule
    where
        newrule = Rule
            { ruleName = name
            , fwdApply = const []
            , bwdApply = const []
            , checkInference = rdfSimpleEntailCheckInference
            }

--  Simple entailment inference checker
--
--  Note:  antecedents here are presumed to share bnodes.
--         (Use 'merge' instead of 'add' for non-shared bnodes)
--
rdfSimpleEntailCheckInference :: [RDFGraph] -> RDFGraph -> Bool
rdfSimpleEntailCheckInference ante cons =
    let agr = if null ante then emptyRDFGraph else foldl1 add ante
    in
        not $ null $ rdfQueryInstance cons agr

{- original..
        not $ null $ rdfQueryInstance cons (foldl1 merge ante)
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
-- $Source: /file/cvsdev/HaskellRDF/RDFProof.hs,v $
-- $Author: graham $
-- $Revision: 1.22 $
-- $Log: RDFProof.hs,v $
-- Revision 1.22  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.21  2003/12/16 07:05:37  graham
-- Working on updated RDFProofContext
--
-- Revision 1.20  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.19  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.18  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.17  2003/10/02 13:41:26  graham
-- Supporting changes for RDF axioms and rules defined as Rulesets,
-- and moved out of module RDFProofCheck.
-- Datatype named using ScopedName rather than QName
-- (Datatype framework is still work in progress).
--
-- Revision 1.16  2003/09/30 20:02:39  graham
-- Proof mechanisms now use scoped names and rulesets.
-- Move some functionality between modules so that RDFProofCheck
-- contains less generic code.
--
-- Revision 1.15  2003/09/30 16:39:41  graham
-- Refactor proof code to use new ruleset logic.
-- Moved some support code from RDFProofCheck to RDFRuleset.
--
-- Revision 1.14  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.13  2003/07/02 21:27:30  graham
-- Graph closure with instance rule tested.
-- About to change ProofTest for graph forward chaining to return
-- a single result graph.
--
-- Revision 1.12  2003/07/01 14:20:30  graham
-- Added instance entailment to proof check module.
--
-- Revision 1.11  2003/06/30 19:07:00  graham
-- Instance entailment, subgraph entailment and simple entailment
-- tests now working.
--
-- Revision 1.10  2003/06/27 20:46:00  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.9  2003/06/25 21:16:53  graham
-- Reworked N3 formatting logic to support proof display.
-- Basic proof display is working.
--
-- Revision 1.8  2003/06/25 09:52:25  graham
-- Replaced Rule class with algebraic data type
--
-- Revision 1.7  2003/06/24 23:08:18  graham
-- Replaced Rule class with algebraic data type
--
-- Revision 1.6  2003/06/24 19:56:31  graham
-- Basic proof-check now works
--
-- Revision 1.5  2003/06/19 19:49:07  graham
-- RDFProofCheck compiles, but test fails
--
-- Revision 1.4  2003/06/18 18:40:08  graham
-- Basic proof backchaining tests OK.
-- Next:  add filtering on variable bindings.
--
-- Revision 1.3  2003/06/18 01:29:29  graham
-- Fixed up some problems with backward chaining queries.
-- Query test cases still to complete.
-- Proof incomplete.
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
