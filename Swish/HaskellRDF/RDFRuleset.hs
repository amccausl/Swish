--------------------------------------------------------------------------------
--  $Id: RDFRuleset.hs,v 1.20 2004/02/09 22:22:44 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFRuleset
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines some datatypes and functions that are
--  used to define rules and rulesets over RDF graphs
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFRuleset
    ( RDFFormula, RDFRule, RDFRuleMap
    , RDFClosure, RDFRuleset, RDFRulesetMap
    , nullRDFFormula
    , GraphClosure(..), makeGraphClosureRule
    , makeRDFGraphFromN3String
    , makeRDFFormula
    , makeRDFClosureRule
    , makeN3ClosureRule
    , makeN3ClosureSimpleRule
    , makeN3ClosureModifyRule
    , makeN3ClosureAllocatorRule
    , makeNodeAllocTo
    -- for debugging
    , graphClosureFwdApply, graphClosureBwdApply
    )
where

import Swish.HaskellRDF.RDFQuery
    ( rdfQueryFind
    , rdfQueryBack, rdfQueryBackModify
    , rdfQuerySubs
    , rdfQuerySubsBlank
    )

import Swish.HaskellRDF.RDFGraph
    ( Label (..), RDFLabel(..), RDFGraph
    , makeBlank, newNodes
    , merge, allLabels
    , toRDFGraph, emptyRDFGraph )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding, RDFVarBindingModify )

import Swish.HaskellRDF.N3Parser
    ( parseN3fromString )

import Swish.HaskellRDF.Ruleset
    ( Ruleset(..), RulesetMap
    )

import Swish.HaskellRDF.Rule
    ( Formula(..), Rule(..), RuleMap
    , fwdCheckInference
    , nullScope
    )

import Swish.HaskellRDF.VarBinding
    ( makeVarBinding
    , applyVarBinding, joinVarBindings
    , VarBindingModify(..)
    , vbmCompose
    , varBindingId
    )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..) )

import Swish.HaskellRDF.Vocabulary
    ( swishName )

{-
import Swish.HaskellRDF.Proof
    ( Proof(..), Step(..) )
-}

import Swish.HaskellRDF.GraphClass
    ( Label(..), Arc(..), LDGraph(..) )

import Swish.HaskellUtils.ListHelpers
    ( equiv, flist )

import Swish.HaskellUtils.ErrorM
    ( ErrorM(..) )

import Data.List
    ( nub )


------------------------------------------------------------
--  Datatypes for RDF ruleset
------------------------------------------------------------

type RDFFormula     = Formula RDFGraph

type RDFRule        = Rule RDFGraph

type RDFRuleMap     = RuleMap RDFGraph

type RDFClosure     = GraphClosure RDFLabel

type RDFRuleset     = Ruleset RDFGraph

type RDFRulesetMap  = RulesetMap RDFGraph

------------------------------------------------------------
--  Declare null RDF formula
------------------------------------------------------------

nullRDFFormula :: Formula RDFGraph
nullRDFFormula = Formula
    { formName = ScopedName nullScope "nullRDFGraph"
    , formExpr = emptyRDFGraph
    }

------------------------------------------------------------
--  Datatype for graph closure rule
------------------------------------------------------------

-- |Datatype for constructing a graph closure rule
data GraphClosure lb = GraphClosure
    { nameGraphRule :: ScopedName   -- ^ Name of rule for proof display
    , ruleAnt       :: [Arc lb]     -- ^ Antecedent triples pattern
                                    --   (may include variable nodes)
    , ruleCon       :: [Arc lb]     -- ^ Consequent triples pattern
                                    --   (may include variable nodes)
    , ruleModify    :: VarBindingModify lb lb
                                    -- ^ Structure that defines additional
                                    --   constraints and/or variable
                                    --   bindings based on other matched
                                    --   query variables.  Matching the
                                    --   antecedents.  Use 'varBindingId' if
                                    --   no additional variable constraints
                                    --   or bindings are added beyond those
                                    --   arising from graph queries.
    }

instance (Label lb) => Eq (GraphClosure lb) where
    c1 == c2 = (nameGraphRule c1 == nameGraphRule c2) &&
               (ruleAnt c1) `equiv` (ruleAnt c2) &&
               (ruleCon c1) `equiv` (ruleCon c2)

instance (Label lb) => Show (GraphClosure lb) where
    show c = "GraphClosure "++show (nameGraphRule c)

------------------------------------------------------------
--  Define inference rule based on RDF graph closure rule
------------------------------------------------------------

-- |Define a value of type Rule based on an RDFClosure value.
makeGraphClosureRule :: GraphClosure RDFLabel -> Rule RDFGraph
makeGraphClosureRule grc = newrule
    where
        newrule = Rule
            { ruleName       = nameGraphRule grc
            , fwdApply       = graphClosureFwdApply grc
            , bwdApply       = graphClosureBwdApply grc
            , checkInference = fwdCheckInference newrule
            }

--  Forward chaining function based on RDF graph closure description
--
--  Note:  antecedents here are presumed to share bnodes.
--
graphClosureFwdApply :: GraphClosure RDFLabel -> [RDFGraph] -> [RDFGraph]
graphClosureFwdApply grc grs =
    let gr   = if null grs then emptyRDFGraph else foldl1 add grs
        vars = queryFind (ruleAnt grc) gr
        varm = vbmApply (ruleModify grc) vars
        cons = querySubs varm (ruleCon grc)
    in
        {-
        seq cons $
        seq (trace "\ngraphClosureFwdApply") $
        seq (traceShow "\nvars: " vars) $
        seq (traceShow "\nvarm: " varm) $
        seq (traceShow "\ncons: " cons) $
        seq (trace "\n") $
        -}
        --  Return null list or single result graph that is the union
        --  (not merge) of individual results:
        if null cons then [] else [foldl1 add cons]
        -- cons {- don't merge results -}

--  Backward chaining function based on RDF graph closure description
graphClosureBwdApply :: GraphClosure RDFLabel -> RDFGraph -> [[RDFGraph]]
graphClosureBwdApply grc gr =
    let vars = rdfQueryBackModify (ruleModify grc) $
               queryBack (ruleCon grc) gr
        --  This next function eliminates duplicate variable bindings.
        --  It is strictly redundant, but comparing variable
        --  bindings is much cheaper than comparing graphs.
        --  I don't know if many duplicate graphs will be result
        --  of exact duplicate variable bindings, so this may be
        --  not very effective.
        varn = map nub vars
    in
        --  The 'nub ante' below eliminates duplicate antecedent graphs,
        --  based on graph matching, which tests for equivalence under
        --  bnode renaming, with a view to reducing redundant arcs in
        --  the merged antecedent graph, hence less to prove in
        --  subsequent back-chaining steps.
        --
        --  Each antecedent is reduced to a single RDF graph, when
        --  bwdApply specifies a list of expressions corresponding to
        --  each antecedent.
        [ [foldl1 merge (nub ante)]
          | vs <- varn
          , let ante = querySubsBlank vs (ruleAnt grc) ]

------------------------------------------------------------
--  RDF graph query and substitution support functions
------------------------------------------------------------

queryFind :: [Arc RDFLabel] -> RDFGraph -> [RDFVarBinding]
queryFind qas tg = rdfQueryFind (toRDFGraph qas) tg

queryBack :: [Arc RDFLabel] -> RDFGraph -> [[RDFVarBinding]]
queryBack qas tg = rdfQueryBack (toRDFGraph qas) tg

querySubs :: [RDFVarBinding] -> [Arc RDFLabel] -> [RDFGraph]
querySubs vars qas =
    {-
    seq (trace "\nquerySubs") $
    seq (traceShow "\nvars: " vars)
    seq (traceShow "\narcs: "  qas)
    seq (trace "\n") $
    -}
    rdfQuerySubs vars (toRDFGraph qas)

querySubsBlank :: [RDFVarBinding] -> [Arc RDFLabel] -> [RDFGraph]
querySubsBlank vars qas = rdfQuerySubsBlank vars (toRDFGraph qas)

------------------------------------------------------------
--  Method for creating an RDF formula value from N3 text
------------------------------------------------------------

-- |Helper function to parse a string containing Notation3
--  and return the corresponding RDFGraph value.
makeRDFGraphFromN3String :: String -> RDFGraph
makeRDFGraphFromN3String str = case parseN3fromString str of
    Error  msg -> error msg
    Result gr  -> gr

-- |Create an RDF formula given:
--  a namespace, a local name and a Notation 3 string that
--  is parsed to yield an RDF graph value.
makeRDFFormula ::
    Namespace -> String -> String -> RDFFormula
makeRDFFormula scope local gr = Formula
    { formName = ScopedName scope local
    , formExpr = makeRDFGraphFromN3String gr
    }

------------------------------------------------------------
--  Create an RDF closure rule from supplied graphs
------------------------------------------------------------

-- |Constructs an RDF graph closure rule.  That is, a rule that
--  given some set of antecedent statements returns new statements
--  that may be added to the graph.
--
--  sname   is a scoped name for the new rule.
--  antgrs  is a list of RDFGraphs that are the entecedent of the rule.
--          (Note:  bnodes and variable names are assumed to be shared
--          by all the entecedent graphs supplied.  [[[is this right?]]])
--  congr   is an RDFGraph containing that is the consequent graph.
--  vmod    is a variable binding modifier value that may impose
--          additional conditions on the variable bindings that
--          can be used for this inference rule, or which may
--          cause new values to be allocated for unbound variables.
--          These modifiers allow for certain inference patterns
--          that are not captured by simple "closure rules", such
--          as the allocation of bnodes corresponding to literals,
--          and are an extension point for incorporating datatypes
--          into an inference process.
--          If no additional constraints or variable bindings are
--          to be applied, use value 'varBindingId'
--
makeRDFClosureRule ::
    ScopedName -> [RDFGraph] -> RDFGraph -> RDFVarBindingModify
    -> RDFRule
makeRDFClosureRule sname antgrs congr vmod = makeGraphClosureRule
    GraphClosure
        { nameGraphRule = sname
        , ruleAnt       = concatMap getArcs antgrs
        , ruleCon       = getArcs congr
        , ruleModify    = vmod
        }

------------------------------------------------------------
--  Methods to create an RDF closure rule from N3 input
------------------------------------------------------------
--
--  These functions are used internally by Swish to construct
--  rules from textual descriptions.

-- |Constructs an RDF graph closure rule.  That is, a rule that
--  given some set of antecedent statements returns new statements
--  that may be added to the graph.  This is the basis for
--  implementation of most of the inference rules given in the
--  RDF formal semantics document.
--
--  scope   is a namespace to which the rule is allocated
--  local   is a local name for the rule in the given namespace
--  ant     is a string containing the Notation3 representation
--          of the antecedent graph.  (Note: multiple antecedents
--          can be handled by combining multiple graphs.)
--  con     is a string containing the Notation3 representation
--          of the consequent graph.
--  vmod    is a variable binding modifier value that may impose
--          additional conditions on the variable bindings that
--          can be used for this inference rule, or which may
--          cause new values to be allocated for unbound variables.
--          These modifiers allow for certain inference patterns
--          that are not captured by simple "closure rules", such
--          as the allocation of bnodes corresponding to literals,
--          and are an extension point for incorporating datatypes
--          into an inference process.
--          If no additional constraints or variable bindings are
--          to be applied, use value 'varBindingId'
--
makeN3ClosureRule ::
    Namespace -> String
    -> String -> String -> RDFVarBindingModify
    -> RDFRule
makeN3ClosureRule scope local ant con vmod =
    makeRDFClosureRule (ScopedName scope local) [antgr] congr vmod
    where
        antgr = makeRDFGraphFromN3String ant
        congr = makeRDFGraphFromN3String con

-- |Construct a simple RDF graph closure rule without
--  additional node allocations or variable binding constraints.
--
makeN3ClosureSimpleRule ::
    Namespace -> String -> String -> String -> RDFRule
makeN3ClosureSimpleRule scope local ant con =
    makeN3ClosureRule scope local ant con varBindingId

-- |Constructs an RDF graph closure rule that incorporates
--  a variable binding filter and a variable binding modifier.
--
--  scope   is a namespace to which the rule is allocated
--  local   is a local name for the rule in the given namespace
--  ant     is a string containing the Notation3 representation
--          of the antecedent graph.  (Note: multiple antecedents
--          can be handled by combining multiple graphs.)
--  con     is a string containing the Notation3 representation
--          of the consequent graph.
--  vflt    is a variable binding modifier value that may impose
--          additional conditions on the variable bindings that
--          can be used for this inference rule.
--          These modifiers allow for certain inference patterns
--          that are not captured by simple "closure rules", such
--          as deductions that pertain only to certain kinds of
--          nodes in a graph.
--  vmod    is a variable binding modifier that is applied to the
--          variable bindings obtained, typically to create some
--          additional variable bindings.  This is applied before
--          the filter rule 'vflt'.
--
makeN3ClosureModifyRule ::
    Namespace -> String
    -> String -> String -> RDFVarBindingModify -> RDFVarBindingModify
    -> RDFRule
makeN3ClosureModifyRule scope local ant con vflt vmod =
    makeN3ClosureRule scope local ant con modc
    where
        modc  = case vbmCompose vmod vflt of
            Just x  -> x
            Nothing -> varBindingId
{-
    makeRDFClosureRule (ScopedName scope local) [antgr] congr modc
    where
        antgr = makeRDFGraphFromN3String ant
        congr = makeRDFGraphFromN3String con
        modc  = case vbmCompose vmod vflt of
            Just x  -> x
            Nothing -> varBindingId
-}

-- |Construct an RDF graph closure rule with a bnode allocator.
--
--  This function is rather like makeN3ClosureModifyRule, except that
--  the variable binding modifier is a function from the variables in
--  the variables and bnodes contained in the antecedent graph.
--
--  scope   is a namespace tom which the rule is allocated
--  local   is a local name for the rule in the given namespace
--  ant     is a string containing the Notation3 representation
--          of the antecedent graph.  (Note: multiple antecedents
--          can be handled by combining multiple graphs.)
--  con     is a string containing the Notation3 representation
--          of the consequent graph.
--  vflt    is a variable binding modifier value that may impose
--          additional conditions on the variable bindings that
--          can be used for this inference rule.
--  aloc    is a function applied to a list of nodes to yield a
--          variable binding modifier value.
--          The supplied parameter is applied to a list of all of
--          the variable nodes (including all blank nodes) in the
--          antecedent graph, and then composed with the 'vflt'
--          value (above).  This allows any node allocation
--          function to avoid allocating any blank nodes that
--          are already used in the antecedent graph.
--          (See function makeNodeAllocTo).
--
makeN3ClosureAllocatorRule ::
    Namespace -> String
    -> String -> String
    -> RDFVarBindingModify -> ( [RDFLabel] -> RDFVarBindingModify )
    -> RDFRule
makeN3ClosureAllocatorRule scope local ant con vflt aloc =
    makeRDFClosureRule (ScopedName scope local) [antgr] congr modc
    where
        antgr = makeRDFGraphFromN3String ant
        congr = makeRDFGraphFromN3String con
        vmod  = aloc (allLabels labelIsVar antgr)
        modc  = case vbmCompose vmod vflt of
            Just x  -> x
            Nothing -> varBindingId


------------------------------------------------------------
--  Query binding modifier for "allocated to" logic
------------------------------------------------------------

-- |This function defines a variable binding mofifier that
--  allocates a new blank node for each value bound to
--  a query variable, and binds it to another variable
--  in each query binding.
--
--  This provides a single binding for query variables that would
--  otherwise be unbound by a query.  For example, consider the
--  inference pattern:
--    ?a hasUncle ?c => ?a hasFather ?b . ?b hasBrother ?c .
--  For a given ?a and ?c, there is insufficient information
--  here to instantiate a value for variable ?b.  Using this
--  function as part of a graph instance closure rule allows
--  forward chaining to allocate a single bnode for each
--  occurrence of ?a, so that given:
--    Jimmy hasUncle Fred .
--    Jimmy hasUncle Bob .
--  leads to exactly one bnode inference of:
--    Jimmy hasFather _:f .
--  giving:
--    Jimmy hasFather _:f .
--    _:f hasBrother Fred .
--    _:f hasBrother Bob .
--  rather than:
--    Jimmy hasFather _:f1 .
--    _:f1 hasBrother Fred .
--    Jimmy hasFather _:f2 .
--    _:f2 hasBrother Bob .
--
--  This form of constrained allocation of bnodes is also required for
--  some of the inference patterns described by the RDF formal semantics,
--  particularly those where bnodes are substituted for URIs or literals.
--
--  bindvar is a variable node to which a new blank node is bound
--  alocvar is a variable which is bound in each query to a graph
--          node to which new blank nodes are allocated.
--
makeNodeAllocTo ::
    RDFLabel -> RDFLabel
    -> [RDFLabel] -> RDFVarBindingModify
makeNodeAllocTo bindvar alocvar exbnode = VarBindingModify
        { vbmName   = swishName "makeNodeAllocTo"
        , vbmApply  = applyNodeAllocTo bindvar alocvar exbnode
        , vbmVocab  = [alocvar,bindvar]
        , vbmUsage  = [[bindvar]]
        }

--  Auxiliary function that performs the node allocation defined
--  by makeNodeAllocTo.
--
--  bindvar is a variable node to which a new blank node is bound
--  alocvar is a variable which is bound in each query to a graph
--          node to which new blank nodes are allocated.
--  exbnode is a list of existing blank nodes, to be avoided by
--          the new blank node allocator.
--  vars    is a list of variable bindings to which new bnode
--          allocations for the indicated bindvar are to be added.
--
applyNodeAllocTo ::
    RDFLabel -> RDFLabel -> [RDFLabel] -> [RDFVarBinding] -> [RDFVarBinding]
applyNodeAllocTo bindvar alocvar exbnode vars =
    let
        app vbind = applyVarBinding vbind
        alocnodes = zip (nub $ flist (map app vars) alocvar)
                        (newNodes (makeBlank bindvar) exbnode)
        newvb var = joinVarBindings
            ( makeVarBinding $ head
              [ [(bindvar,b)] | (v,b) <- alocnodes, app var alocvar == v ] )
            var
    in
        map newvb vars


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
-- $Source: /file/cvsdev/HaskellRDF/RDFRuleset.hs,v $
-- $Author: graham $
-- $Revision: 1.20 $
-- $Log: RDFRuleset.hs,v $
-- Revision 1.20  2004/02/09 22:22:44  graham
-- Graph matching updates:  change return value to give some indication
-- of the extent match achieved in the case of no match.
-- Added new module GraphPartition and test cases.
-- Add VehicleCapcity demonstration script.
--
-- Revision 1.19  2003/12/20 12:53:40  graham
-- Fix up code to compile and test with GHC 5.04.3
--
-- Revision 1.18  2003/12/20 12:00:14  graham
-- Introduced new TraceHelpers module for Hugs-2003 compatibility.
--
-- Revision 1.17  2003/12/19 21:01:25  graham
-- Change Debug.Trace import (from Hugs.Trace)
--
-- Revision 1.16  2003/12/18 18:27:47  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.15  2003/12/16 07:05:37  graham
-- Working on updated RDFProofContext
--
-- Revision 1.14  2003/12/11 19:10:29  graham
-- Forward chaining now adds antecedent graphs rather than merging them,
-- so that
-- bnodes carried over from the original input are not separated.
-- Future developments should provide controlled scoping for bnodes,
-- to avoid
-- errors this may cause.
--
-- Revision 1.13  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.12  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.11  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.10  2003/11/25 23:02:17  graham
-- Reworked datatype variable modifier logic.
-- Limited range of test cases so far all pass.
--
-- Revision 1.9  2003/11/14 21:48:35  graham
-- First cut cardinality-checked datatype-constraint rules to pass test cases.
-- Backward chaining is still to do.
--
-- Revision 1.8  2003/11/13 01:13:48  graham
-- Reworked ruleset to use ScopedName lookup.
-- Various minor fixes.
--
-- Revision 1.7  2003/11/06 17:58:33  graham
-- About to rework Datatype to better support class-based reasoning.
--
-- Revision 1.6  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.5  2003/10/09 17:16:13  graham
-- Added test cases to exercise features of rules used to capture
-- RDF semantics.  Also added proof test case using XML literal.
--
-- Revision 1.4  2003/10/09 13:58:59  graham
-- Sync with CVS.  Preparing to eliminate QueryBindingFilter in favour
-- of using just QueryBindingModifier.
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
-- Revision 1.1  2003/09/30 16:38:19  graham
-- Add Ruleset and RDFRuleset modules to provide proof context elements
--
