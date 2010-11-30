--------------------------------------------------------------------------------
--  $Id: RDFProofContext.hs,v 1.13 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  RDFProofContext
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module contains proof-context declarations based on
--  the RDF, RDFS and RDF datatyping semantics specifications.
--  These definitions consist of namespaces (for identification
--  in proofs), axioms and inference rules.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.RDFProofContext
    ( rulesetRDF
    , rulesetRDFS
    , rulesetRDFD )
where

import Swish.HaskellRDF.BuiltInDatatypes
    ( findRDFDatatype )

import Swish.HaskellRDF.RDFProof
    ( makeRdfSubgraphEntailmentRule
    , makeRdfSimpleEntailmentRule )

import Swish.HaskellRDF.RDFRuleset 
    ( RDFFormula 
    , makeRDFFormula
    , makeN3ClosureRule
    , makeN3ClosureSimpleRule
    , makeN3ClosureModifyRule
    , makeN3ClosureAllocatorRule
    , makeNodeAllocTo )

import Swish.HaskellRDF.RDFVarBinding
    ( RDFVarBinding
    , RDFVarBindingModify
    , RDFVarBindingFilter
    , rdfVarBindingUriRef, rdfVarBindingBlank
    , rdfVarBindingLiteral
    , rdfVarBindingUntypedLiteral 
    , rdfVarBindingXMLLiteral, rdfVarBindingDatatyped
    , rdfVarBindingMemberProp
    )

import Swish.HaskellRDF.RDFGraph
    ( RDFLabel(..)
    , isUri, isDatatyped
    , getLiteralText )

import Swish.HaskellRDF.VarBinding
    ( applyVarBinding
    , addVarBinding
    , VarBindingModify(..)
    , makeVarFilterModify
    , varFilterDisjunction
    )

import Swish.HaskellRDF.Ruleset
    ( makeRuleset )

import Swish.HaskellRDF.Datatype
    ( typeMkCanonicalForm )

import Swish.HaskellUtils.Namespace
    ( Namespace(..), ScopedName(..)
    )

import Swish.HaskellRDF.Vocabulary
    ( namespaceRDF
    , namespaceRDFS
    , namespaceRDFD
    , scopeRDF
    , scopeRDFS
    , scopeRDFD
    )

import Data.Maybe
    ( isJust, fromJust )

import Control.Monad
    ( liftM )

------------------------------------------------------------
--  Define query binding filter auxiliaries
------------------------------------------------------------

makeFormula :: Namespace -> String -> String -> RDFFormula
makeFormula scope local gr =
    makeRDFFormula scope local (prefixRDF++gr)

requireAny :: [RDFVarBindingFilter] -> RDFVarBindingFilter
requireAny rs = varFilterDisjunction rs

isLiteralV            :: String -> RDFVarBindingFilter
isLiteralV    ('?':l) = rdfVarBindingLiteral        (Var l)

isUntypedLitV         :: String -> RDFVarBindingFilter
isUntypedLitV ('?':l) = rdfVarBindingUntypedLiteral (Var l)

isXMLLitV             :: String -> RDFVarBindingFilter
isXMLLitV     ('?':x) = rdfVarBindingXMLLiteral     (Var x)

isUriRefV             :: String -> RDFVarBindingFilter
isUriRefV     ('?':u) = rdfVarBindingUriRef         (Var u)

isBlankV              :: String -> RDFVarBindingFilter
isBlankV      ('?':b) = rdfVarBindingBlank          (Var b)

isDatatypedV                  :: String -> String -> RDFVarBindingFilter
isDatatypedV  ('?':d) ('?':l) = rdfVarBindingDatatyped (Var d) (Var l)

isMemberPropV         :: String -> RDFVarBindingFilter
isMemberPropV ('?':l) = rdfVarBindingMemberProp     (Var l)


allocateTo :: String -> String -> [RDFLabel] -> RDFVarBindingModify
allocateTo bv av = makeNodeAllocTo (vn bv) (vn av)
    where
        vn ('?':n) = Var n

--  Create new binding for datatype
valueSame :: String -> String -> String -> String -> RDFVarBindingModify
valueSame val1 typ1 val2 typ2 =
    sameDatatypedValue (vn val1) (vn typ1) (vn val2) (vn typ2)
    where
            vn ('?':n) = Var n

--  Variable binding modifier to create new binding to a canonical
--  form of a datatyped literal.
sameDatatypedValue ::
    RDFLabel -> RDFLabel -> RDFLabel -> RDFLabel -> RDFVarBindingModify
sameDatatypedValue val1 typ1 val2 typ2 = VarBindingModify
        { vbmName   = ScopedName namespaceRDFD "sameValue"
        , vbmApply  = sameDatatypedValueApplyAll val1 typ1 val2 typ2
        , vbmVocab  = [val1,typ1,val2,typ2]
        , vbmUsage  = [[val2]]
        }

sameDatatypedValueApplyAll ::
    RDFLabel -> RDFLabel -> RDFLabel -> RDFLabel
    -> [RDFVarBinding]
    -> [RDFVarBinding]
sameDatatypedValueApplyAll val1 typ1 val2 typ2 vbinds =
    {-
    trace "\nsameDatatypedValueApplyAll:" $
    seq (traceShow "\nval1:" val1) $
    seq (traceShow "\ntyp1:" typ1) $
    seq (traceShow "\nval2:" val2) $
    seq (traceShow "\ntyp2:" typ2) $
    seq (traceShow "\nvbinds:" vbinds) $
    trace "\n" $
    -}
    concatMap (sameDatatypedValueApply val1 typ1 val2 typ2) vbinds

--  Auxiliary function that handles variable binding updates
--  for sameDatatypedValue
sameDatatypedValueApply ::
    RDFLabel -> RDFLabel -> RDFLabel -> RDFLabel
    -> RDFVarBinding
    -> [RDFVarBinding]
sameDatatypedValueApply val1 typ1 val2 typ2 vbind =
    {-
    trace "\nsameDatatypedValueApply:" $
    seq (traceShow "\nval1:"   val1) $
    seq (traceShow "\ntyp1:"   typ1) $
    seq (traceShow "\nval2:"   val2) $
    seq (traceShow "\ntyp2:"   typ2) $
    seq (traceShow "\nvbind:"  vbind) $
    seq (traceShow "\nresult:" result) $
    trace "\n" $
    -}
    result
    where
        v1    = applyVarBinding vbind val1
        t1    = applyVarBinding vbind typ1
        t2    = applyVarBinding vbind typ2
        sametype = getCanonical v1 t1 t2
        result   =
            if (isUri t1) && (isUri t2) then
                if (t1 == t2) then
                    if isJust sametype then
                        [addVarBinding val2 (fromJust $ sametype) vbind]
                    else
                        []
                else
                    error "subtype conversions not yet defined"
            else
                []

getCanonical :: RDFLabel -> RDFLabel -> RDFLabel -> Maybe RDFLabel
getCanonical v1 t1 t2 =
    if (isDatatyped dqn1 v1) && (isJust mdt1) then
        liftM mkLit $ typeMkCanonicalForm dt1 (getLiteralText v1)
    else
        Nothing
    where
        dqn1  = case t1 of { (Res dqnam) -> dqnam }
        dqn2  = case t2 of { (Res dqnam) -> dqnam }
        mdt1  = findRDFDatatype dqn1
        dt1   = fromJust mdt1
        mkLit st = Lit st (Just dqn2)

{- -- Test data
qnamint = ScopedName namespaceXSD "integer"
xsdint  = Res qnamint
lab010  = Lit "010" (Just qnamint)
can010  = getCanonical lab010 xsdint xsdint
nsex    = Namespace "ex" "http://example.org/"
resexp  = Res (ScopedName nsex "p")
resexs  = Res (ScopedName nsex "s")

vara = Var "a"
varb = Var "b"
varc = Var "c"
vard = Var "d"
varp = Var "p"
vars = Var "s"
vart = Var "t"

vb1  = makeVarBinding [(vara,lab010),(varb,xsdint),(vard,xsdint)]
vb2  = sameDatatypedValueApply vara varb varc vard vb1
vb3  = vbmApply (sameDatatypedValue vara varb varc vard) [vb1]
vb3t = vb3 == vb2
vb4  = vbmApply (valueSame "?a" "?b" "?c" "?d") [vb1]
vb4t = vb4 == vb2
vb5  = vbmApply (valueSame "?a" "?b" "?c" "?b") [vb1]
vb5t = vb5 == vb2

vb6  = makeVarBinding [(vars,lab010),(varp,resexp),(vara,resexs),(vard,xsdint)]
vb7  = vbmApply (valueSame "?s" "?d" "?t" "?d") [vb6]
vb8  = makeVarBinding [(vars,lab010),(varp,resexp),(vara,resexs),(vard,xsdint)
                      ,(vart,fromJust can010)]
vb8t = vb7 == [vb8]
-- -}

------------------------------------------------------------
--  Common definitions
------------------------------------------------------------

prefixRDF :: String
prefixRDF =
    "@prefix rdf:  <" ++ nsURI namespaceRDF  ++ "> . \n" ++
    "@prefix rdfs: <" ++ nsURI namespaceRDFS ++ "> . \n" ++
    "@prefix rdfd: <" ++ nsURI namespaceRDFD ++ "> . \n" ++
    " \n"

------------------------------------------------------------
--  Define RDF axioms
------------------------------------------------------------

-- scopeRDF  = Namespace "rs-rdf"  "http://id.ninebynine.org/2003/Ruleset/rdf#"

--  RDF axioms (from RDF semantics document, section 3.1)
--
--  (See also, container property rules below)
--
rdfa1 :: RDFFormula
rdfa1 = makeFormula scopeRDF "a1" "rdf:type      rdf:type rdf:Property ."

rdfa2 :: RDFFormula
rdfa2 = makeFormula scopeRDF "a2" "rdf:subject   rdf:type rdf:Property ."

rdfa3 :: RDFFormula
rdfa3 = makeFormula scopeRDF "a3" "rdf:predicate rdf:type rdf:Property ."

rdfa4 :: RDFFormula
rdfa4 = makeFormula scopeRDF "a4" "rdf:object    rdf:type rdf:Property ."

rdfa5 :: RDFFormula
rdfa5 = makeFormula scopeRDF "a5" "rdf:first     rdf:type rdf:Property ."

rdfa6 :: RDFFormula
rdfa6 = makeFormula scopeRDF "a6" "rdf:rest      rdf:type rdf:Property ."

rdfa7 :: RDFFormula
rdfa7 = makeFormula scopeRDF "a7" "rdf:value     rdf:type rdf:Property ."

rdfa8 :: RDFFormula
rdfa8 = makeFormula scopeRDF "a8" "rdf:nil       rdf:type rdf:List ."

axiomsRDF :: [RDFFormula]
axiomsRDF =
    [ rdfa1,  rdfa2,  rdfa3,  rdfa4,  rdfa5
    , rdfa6,  rdfa7,  rdfa8
    ]

------------------------------------------------------------
--  Define RDF rules
------------------------------------------------------------

--  RDF subgraph entailment (from RDF semantics document section 2)
--
-- rdfsub :: Swish.HaskellRDF.RDFRuleset.RDFRule 
rdfsub = makeRdfSubgraphEntailmentRule (ScopedName scopeRDF "sub")

--  RDF simple entailment (from RDF semantics document section 7.1)
--  (Note: rules se1 and se2 are combined here, because the scope of
--  the "allocatedTo" modifier is the application of a single rule.)
--
rdfse = makeRdfSimpleEntailmentRule (ScopedName scopeRDF "se")

--  RDF bnode-for-literal assignments (from RDF semantics document section 7.1)
--
rdflg = makeN3ClosureAllocatorRule scopeRDF "lg"
            "?x  ?a ?l . "
            "?x  ?a ?b . ?b rdf:_allocatedTo ?l ."
            (makeVarFilterModify $ isLiteralV "?l")
            (allocateTo "?b" "?l")

--  RDF bnode-for-literal back-tracking (from RDF semantics document section 7.1)
--
rdfgl = makeN3ClosureSimpleRule scopeRDF "gl"
            "?x  ?a ?l . ?b rdf:_allocatedTo ?l . "
            "?x  ?a ?b ."

--  RDF entailment rules (from RDF semantics document section 7.2)
--
--  (Note, statements with property rdf:_allocatedTo are introduced to
--  track bnodes introduced according to rule rdflf.)
--
rdfr1 = makeN3ClosureSimpleRule scopeRDF "r1"
            "?x ?a ?y ."
            "?a rdf:type rdf:Property ."

rdfr2 = makeN3ClosureRule scopeRDF "r2"
            "?x  ?a ?b . ?b rdf:_allocatedTo ?l . "
            "?b rdf:type rdf:XMLLiteral ."
            (makeVarFilterModify $ isXMLLitV "?l")

--  Container property axioms (from RDF semantics document section 3.1)
--
--  (Using here an inference rule with a filter in place of an axiom schema)
--
--  This is a restricted form of the given axioms, in that the axioms
--  are asserted only for container membership terms that appear in
--  the graph.
--
--  (This may be very inefficient for forward chaining when dealing with
--  large graphs:  may need to look at query logic to see if the search for
--  container membership properties can be optimized.  This may call for a
--  custom inference rule.)
--
rdfcp1 = makeN3ClosureRule scopeRDF "cp1"
            "?x  ?c ?y . "
            "?c rdf:type rdf:Property ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfcp2 = makeN3ClosureRule scopeRDF "cp2"
            "?c  ?p ?y . "
            "?c rdf:type rdf:Property ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfcp3 = makeN3ClosureRule scopeRDF "cp3"
            "?x  ?p ?c . "
            "?c rdf:type rdf:Property ."
            (makeVarFilterModify $ isMemberPropV "?c")

--  Collect RDF rules
--
rulesRDF =
    [ rdfsub,     rdfse
    , rdflg,      rdfgl
    , rdfr1,      rdfr2
    , rdfcp1,     rdfcp2,     rdfcp3
    ]

--  Define ruleset for RDF inference

rulesetRDF = makeRuleset scopeRDF axiomsRDF rulesRDF

------------------------------------------------------------
--  Define RDFS axioms
------------------------------------------------------------

-- scopeRDFS = Namespace "rdfs" "http://id.ninebynine.org/2003/Ruleset/rdfs#"

--  RDFS axioms (from RDF semantics document, section 4.1)
--
--  (See also, container property rules below)
--

rdfsa01 :: RDFFormula
rdfsa01 = makeFormula scopeRDFS "a01"
    "rdf:type           rdfs:domain rdfs:Resource ."

rdfsa02 :: RDFFormula
rdfsa02 = makeFormula scopeRDFS "a02"
    "rdf:type           rdfs:range  rdfs:Class ."

rdfsa03 :: RDFFormula
rdfsa03 = makeFormula scopeRDFS "a03"
    "rdfs:domain        rdfs:domain rdf:Property ."

rdfsa04 :: RDFFormula
rdfsa04 = makeFormula scopeRDFS "a04"
    "rdfs:domain        rdfs:range  rdfs:Class ."

rdfsa05 :: RDFFormula
rdfsa05 = makeFormula scopeRDFS "a05"
    "rdfs:range         rdfs:domain rdf:Property ."

rdfsa06 :: RDFFormula
rdfsa06 = makeFormula scopeRDFS "a06"
    "rdfs:range         rdfs:range  rdfs:Class ."

rdfsa07 :: RDFFormula
rdfsa07 = makeFormula scopeRDFS "a07"
    "rdfs:subPropertyOf rdfs:domain rdf:Property ."

rdfsa08 :: RDFFormula
rdfsa08 = makeFormula scopeRDFS "a08"
    "rdfs:subPropertyOf rdfs:range  rdf:Property ."

rdfsa09 :: RDFFormula
rdfsa09 = makeFormula scopeRDFS "a09"
    "rdfs:subClassOf    rdfs:domain rdfs:Class ."

rdfsa10 :: RDFFormula
rdfsa10 = makeFormula scopeRDFS "a10"
    "rdfs:subClassOf    rdfs:range  rdfs:Class ."

rdfsa11 :: RDFFormula
rdfsa11 = makeFormula scopeRDFS "a11"
    "rdf:subject        rdfs:domain rdf:Statement ."

rdfsa12 :: RDFFormula
rdfsa12 = makeFormula scopeRDFS "a12"
    "rdf:subject        rdfs:range  rdfs:Resource ."

rdfsa13 :: RDFFormula
rdfsa13 = makeFormula scopeRDFS "a13"
    "rdf:predicate      rdfs:domain rdf:Statement ."

rdfsa14 :: RDFFormula
rdfsa14 = makeFormula scopeRDFS "a14"
    "rdf:predicate      rdfs:range  rdfs:Resource ."

rdfsa15 :: RDFFormula
rdfsa15 = makeFormula scopeRDFS "a15"
    "rdf:object         rdfs:domain rdf:Statement ."

rdfsa16 :: RDFFormula
rdfsa16 = makeFormula scopeRDFS "a16"
    "rdf:object         rdfs:range  rdfs:Resource ."

rdfsa17 :: RDFFormula
rdfsa17 = makeFormula scopeRDFS "a17"
    "rdfs:member        rdfs:domain rdfs:Resource ."

rdfsa18 :: RDFFormula
rdfsa18 = makeFormula scopeRDFS "a18"
    "rdfs:member        rdfs:range  rdfs:Resource ."

rdfsa19 :: RDFFormula
rdfsa19 = makeFormula scopeRDFS "a19"
    "rdf:first          rdfs:domain rdf:List ."

rdfsa20 :: RDFFormula
rdfsa20 = makeFormula scopeRDFS "a20"
    "rdf:first          rdfs:range  rdfs:Resource ."

rdfsa21 :: RDFFormula
rdfsa21 = makeFormula scopeRDFS "a21"
    "rdf:rest           rdfs:domain rdf:List ."

rdfsa22 :: RDFFormula
rdfsa22 = makeFormula scopeRDFS "a22"
    "rdf:rest           rdfs:range  rdf:List ."

rdfsa23 :: RDFFormula
rdfsa23 = makeFormula scopeRDFS "a23"
    "rdfs:seeAlso       rdfs:domain rdfs:Resource ."

rdfsa24 :: RDFFormula
rdfsa24 = makeFormula scopeRDFS "a24"
    "rdfs:seeAlso       rdfs:range  rdfs:Resource ."

rdfsa25 :: RDFFormula
rdfsa25 = makeFormula scopeRDFS "a25"
    "rdfs:isDefinedBy   rdfs:domain rdfs:Resource ."

rdfsa26 :: RDFFormula
rdfsa26 = makeFormula scopeRDFS "a26"
    "rdfs:isDefinedBy   rdfs:range  rdfs:Resource ."

rdfsa27 :: RDFFormula
rdfsa27 = makeFormula scopeRDFS "a27"
    "rdfs:isDefinedBy   rdfs:subPropertyOf rdfs:seeAlso ."

rdfsa28 :: RDFFormula
rdfsa28 = makeFormula scopeRDFS "a28"
    "rdfs:comment       rdfs:domain rdfs:Resource ."

rdfsa29 :: RDFFormula
rdfsa29 = makeFormula scopeRDFS "a29"
    "rdfs:comment       rdfs:range  rdfs:Literal ."

rdfsa30 :: RDFFormula
rdfsa30 = makeFormula scopeRDFS "a30"
    "rdfs:label         rdfs:domain rdfs:Resource ."

rdfsa31 :: RDFFormula
rdfsa31 = makeFormula scopeRDFS "a31"
    "rdfs:label         rdfs:range  rdfs:Literal ."

rdfsa32 :: RDFFormula
rdfsa32 = makeFormula scopeRDFS "a32"
    "rdf:value          rdfs:domain rdfs:Resource ."

rdfsa33 :: RDFFormula
rdfsa33 = makeFormula scopeRDFS "a33"
    "rdf:value          rdfs:range  rdfs:Resource ."

rdfsa34 :: RDFFormula
rdfsa34 = makeFormula scopeRDFS "a34"
    "rdf:Alt            rdfs:subClassOf    rdfs:Container ."

rdfsa35 :: RDFFormula
rdfsa35 = makeFormula scopeRDFS "a35"
    "rdf:Bag            rdfs:subClassOf    rdfs:Container ."

rdfsa36 :: RDFFormula
rdfsa36 = makeFormula scopeRDFS "a36"
    "rdf:Seq            rdfs:subClassOf    rdfs:Container ."

rdfsa37 :: RDFFormula
rdfsa37 = makeFormula scopeRDFS "a37"
    "rdfs:ContainerMembershipProperty rdfs:subClassOf rdf:Property ."

rdfsa38 :: RDFFormula
rdfsa38 = makeFormula scopeRDFS "a38"
    "rdf:XMLLiteral     rdf:type           rdfs:Datatype ."

rdfsa39 :: RDFFormula
rdfsa39 = makeFormula scopeRDFS "a39"
    "rdf:XMLLiteral     rdfs:subClassOf    rdfs:Literal ."

rdfsa40 :: RDFFormula
rdfsa40 = makeFormula scopeRDFS "a40"
    "rdfs:Datatype      rdfs:subClassOf    rdfs:Class ."

axiomsRDFS :: [RDFFormula]
axiomsRDFS =
    [          rdfsa01, rdfsa02, rdfsa03, rdfsa04
    , rdfsa05, rdfsa06, rdfsa07, rdfsa08, rdfsa09
    , rdfsa10, rdfsa11, rdfsa12, rdfsa13, rdfsa14
    , rdfsa15, rdfsa16, rdfsa17, rdfsa18, rdfsa19
    , rdfsa20, rdfsa21, rdfsa22, rdfsa23, rdfsa24
    , rdfsa25, rdfsa26, rdfsa27, rdfsa28, rdfsa29
    , rdfsa30, rdfsa31, rdfsa32, rdfsa33, rdfsa34
    , rdfsa35, rdfsa36, rdfsa37, rdfsa38, rdfsa39
    , rdfsa40
    ]

------------------------------------------------------------
--  Define RDFS rules
------------------------------------------------------------

{-
rdfr2 = makeN3ClosureRule scopeRDF "r2"
            "?x  ?a ?b . ?b rdf:_allocatedTo ?l . "
            "?b rdf:type rdf:XMLLiteral ."
            (makeVarFilterModify $ isXMLLit "?l")
-}

--  RDFS entailment rules (from RDF semantics document section 7.2)
--
--  (Note, statements with property rdf:_allocatedTo are introduced to
--  track bnodes introduced according to rule rdflf.)
--
rdfsr1 = makeN3ClosureRule scopeRDFS "r1"
            "?x  ?a ?b . ?b rdf:_allocatedTo ?l . "
            "?b rdf:type rdfs:Literal ."
            (makeVarFilterModify $ isUntypedLitV "?l" )

rdfsr2 = makeN3ClosureSimpleRule scopeRDFS "r2"
            "?x ?a ?y . ?a rdfs:domain ?z ."
            "?x rdf:type ?z ."

rdfsr3 = makeN3ClosureRule scopeRDFS "r3"
            "?u ?a ?v . ?a rdfs:range ?z ."
            "?v rdf:type ?z ."
            (makeVarFilterModify $ requireAny [isUriRefV "?v",isBlankV "?v"])

rdfsr4a = makeN3ClosureSimpleRule scopeRDFS "r4a"
            "?x ?a ?y ."
            "?x rdf:type rdfs:Resource ."

rdfsr4b = makeN3ClosureRule scopeRDFS "r4b"
            "?x ?a ?u ."
            "?u rdf:type rdfs:Resource ."
            (makeVarFilterModify $ requireAny [isUriRefV "?u",isBlankV "?u"])

rdfsr5  = makeN3ClosureSimpleRule scopeRDFS "r5"
            "?a rdfs:subPropertyOf ?b . ?b rdfs:subPropertyOf ?c ."
            "?a rdfs:subPropertyOf ?c ."

rdfsr6  = makeN3ClosureSimpleRule scopeRDFS "r6"
            "?x rdf:type rdf:Property ."
            "?x rdfs:subPropertyOf ?x ."

rdfsr7  = makeN3ClosureSimpleRule scopeRDFS "r7"
            "?x ?a ?y . ?a rdfs:subPropertyOf ?b ."
            "?x ?b ?y ."

rdfsr8  = makeN3ClosureSimpleRule scopeRDFS "r8"
            "?x rdf:type rdfs:Class ."
            "?x rdfs:subClassOf rdfs:Resource ."

rdfsr9  = makeN3ClosureSimpleRule scopeRDFS "r9"
            "?x rdfs:subClassOf ?y . ?a rdf:type ?x ."
            "?a rdf:type ?y ."

rdfsr10 = makeN3ClosureSimpleRule scopeRDFS "r10"
            "?x rdf:type rdfs:Class ."
            "?x rdfs:subClassOf ?x ."

rdfsr11 = makeN3ClosureSimpleRule scopeRDFS "r11"
            "?x rdfs:subClassOf ?y . ?y rdfs:subClassOf ?z ."
            "?x rdfs:subClassOf ?z ."

rdfsr12 = makeN3ClosureSimpleRule scopeRDFS "r12"
            "?x rdf:type rdfs:ContainerMembershipProperty ."
            "?x rdfs:subPropertyOf rdfs:member ."

rdfsr13 = makeN3ClosureSimpleRule scopeRDFS "r13"
            "?x rdf:type rdfs:Datatype ."
            "?x rdfs:subClassOf rdfs:Literal ."

--  These are valid only under an extensional strengthening of RDFS,
--  discussed in section 7.3.1 of the RDF semantics specification:

rdfsrext1 = makeN3ClosureSimpleRule scopeRDFS "ext1"
            "?x rdfs:domain ?y . ?y rdfs:subClassOf ?z ."
            "?x rdfs:domain ?z ."

rdfsrext2 = makeN3ClosureSimpleRule scopeRDFS "ext2"
            "?x rdfs:range ?y . ?y rdfs:subClassOf ?z ."
            "?x rdfs:range ?z ."

rdfsrext3 = makeN3ClosureSimpleRule scopeRDFS "ext3"
            "?x rdfs:domain ?y . ?z rdfs:subPropertyOf ?x ."
            "?z rdfs:domain ?y ."

rdfsrext4 = makeN3ClosureSimpleRule scopeRDFS "ext4"
            "?x rdfs:range ?y . ?z rdfs:subPropertyOf ?x ."
            "?z rdfs:range ?y ."

rdfsrext5 = makeN3ClosureSimpleRule scopeRDFS "ext5"
            "rdf:type rdfs:subPropertyOf ?z . ?z rdfs:domain ?y ."
            "rdfs:Resource rdfs:subClassOf ?y ."

rdfsrext6 = makeN3ClosureSimpleRule scopeRDFS "rext6"
            "rdfs:subClassOf rdfs:subPropertyOf ?z . ?z rdfs:domain ?y ."
            "rdfs:Class rdfs:subClassOf ?y ."

rdfsrext7 = makeN3ClosureSimpleRule scopeRDFS "rext7"
            "rdfs:subPropertyOf rdfs:subPropertyOf ?z . ?z rdfs:domain ?y ."
            "rdfs:Property rdfs:subClassOf ?y ."

rdfsrext8 = makeN3ClosureSimpleRule scopeRDFS "rext8"
            "rdfs:subClassOf rdfs:subPropertyOf ?z . ?z rdfs:range ?y ."
            "rdfs:Class rdfs:subClassOf ?y ."

rdfsrext9 = makeN3ClosureSimpleRule scopeRDFS "rext9"
            "rdfs:subPropertyOf rdfs:subPropertyOf ?z . ?z rdfs:range ?y ."
            "rdfs:Property rdfs:subClassOf ?y ."


--  Container property axioms (from RDF semantics document section 4.1)
--
--  (Using here an inference rule with a filter in place of an axiom schema)
--
--  This is a restricted form of the given axioms, in that the axioms
--  are asserted only for container membership terms that appear in
--  the graph.
--
--  (This may be very inefficient for forward chaining when dealing with
--  large graphs:  may need to look at query logic to see if the search for
--  container membership properties can be optimized.  This may call for a
--  custom inference rule.)
--
rdfscp11 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?c ?y . "
            "?c rdf:type rdfs:ContainerMembershipProperty ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp12 = makeN3ClosureRule scopeRDFS "cp1"
            "?c  ?p ?y . "
            "?c rdf:type rdfs:ContainerMembershipProperty ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp13 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?p ?c . "
            "?c rdf:type rdfs:ContainerMembershipProperty ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp21 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?c ?y . "
            "?c rdfs:domain rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp22 = makeN3ClosureRule scopeRDFS "cp1"
            "?c  ?p ?y . "
            "?c rdfs:domain rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp23 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?p ?c . "
            "?c rdfs:domain rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp31 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?c ?y . "
            "?c rdfs:range rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp32 = makeN3ClosureRule scopeRDFS "cp1"
            "?c  ?p ?y . "
            "?c rdfs:range rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

rdfscp33 = makeN3ClosureRule scopeRDFS "cp1"
            "?x  ?p ?c . "
            "?c rdfs:range rdfs:Resource ."
            (makeVarFilterModify $ isMemberPropV "?c")

--  Collect RDFS rules
--
rulesRDFS =
    [ rdfsr1,    rdfsr2,    rdfsr3,    rdfsr4a,   rdfsr4b
    , rdfsr5,    rdfsr6,    rdfsr7,    rdfsr8,    rdfsr9
    , rdfsr10,   rdfsr11,   rdfsr12,   rdfsr13
    , rdfscp11,   rdfscp12,   rdfscp13
    , rdfscp21,   rdfscp22,   rdfscp23
    , rdfscp31,   rdfscp32,   rdfscp33
    ]

--  Define ruleset for RDFS inference

rulesetRDFS = makeRuleset scopeRDFS axiomsRDFS rulesRDFS

------------------------------------------------------------
--  Define RDFD (datatyping) axioms
------------------------------------------------------------

-- scopeRDFD = Namespace "rdfd" "http://id.ninebynine.org/2003/Ruleset/rdfd#"

axiomsRDFD =
    [
    ]

------------------------------------------------------------
--  Define RDFD (datatyping) axioms
------------------------------------------------------------

--  RDFD closure rules from semantics document, section 7.4

--  Infer type of datatyped literal
--
rdfdr1 = makeN3ClosureRule scopeRDFD "r1"
            "?d rdf:type rdfs:Datatype . ?a ?p ?l . ?b rdf:_allocatedTo ?l . "
            "?b rdf:type ?d ."
            (makeVarFilterModify $ isDatatypedV "?d" "?l")

--  Equivalent literals with same datatype:
--  (generate canonical form, or operate in proof mode only)
--
rdfdr2 = makeN3ClosureRule scopeRDFD "r2"
            "?d rdf:type rdfs:Datatype . ?a ?p ?s ."
            "?a ?p ?t ."
            (valueSame "?s" "?d" "?t" "?d")

{- Note that valueSame does datatype check.  Otherwise use:
rdfdr2 = makeN3ClosureModifyRule scopeRDFD "r2"
            "?d rdf:type rdfs:Datatype . ?a ?p ?s ."
            "?a ?p ?t ."
            (makeVarFilterModify $ isDatatypedV "?d" "?s")
            (valueSame "?s" "?d" "?t" "?d")
-}

--  Equivalent literals with different datatypes:
--  (generate canonical form, or operate in proof mode only)
--
rdfdr3 = makeN3ClosureModifyRule scopeRDFD "r3"
            ( "?d rdf:type rdfs:Datatype . ?e rdf:type rdfs:Datatype . " ++
              "?a ?p ?s ." )
            "?a ?p ?t ."
            (makeVarFilterModify $ isDatatypedV "?s" "?d")
            (valueSame "?s" "?d" "?t" "?e")

--  Collect RDFD rules
--
rulesRDFD =
    [ rdfdr1, rdfdr2, rdfdr3
    ]

--  Define ruleset for RDFD inference
--
rulesetRDFD = makeRuleset scopeRDFD axiomsRDFD rulesRDFD

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
-- $Source: /file/cvsdev/HaskellRDF/RDFProofContext.hs,v $
-- $Author: graham $
-- $Revision: 1.13 $
-- $Log: RDFProofContext.hs,v $
-- Revision 1.13  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.12  2003/12/20 12:00:14  graham
-- Introduced new TraceHelpers module for Hugs-2003 compatibility.
--
-- Revision 1.11  2003/12/19 21:01:25  graham
-- Change Debug.Trace import (from Hugs.Trace)
--
-- Revision 1.10  2003/12/18 18:27:47  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.9  2003/12/16 07:05:37  graham
-- Working on updated RDFProofContext
--
-- Revision 1.8  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.7  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.6  2003/12/01 18:51:38  graham
-- Described syntax for Swish script.
-- Created Swish scripting test data.
-- Edited export/import lists in Swish main program modules.
--
-- Revision 1.5  2003/11/24 17:20:35  graham
-- Separate module Vocabulary from module Namespace.
--
-- Revision 1.4  2003/10/22 16:18:37  graham
-- Move common namespace definitions into Namespace module
-- (May later move these into separate modules.)
--
-- Revision 1.3  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.2  2003/10/09 13:58:59  graham
-- Sync with CVS.  Preparing to eliminate QueryBindingFilter in favour
-- of using just QueryBindingModifier.
--
-- Revision 1.1  2003/10/02 13:39:41  graham
-- RDF axioms and rules defined as Rulesets, and moved out of module
-- RDFProofCheck into RDFProorfContext, with corresponding test cases
-- moved to module RDFProorfContextTest.
--
