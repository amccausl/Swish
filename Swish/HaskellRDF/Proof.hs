--------------------------------------------------------------------------------
--  $Id: Proof.hs,v 1.19 2004/01/07 19:49:12 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Proof
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a framework for constructing proofs
--  over some expression form.  It is intended to be used
--  with RDF graphs, but the structures aim to be quite
--  generic with respect to the expression forms allowed.
--
--  It does not define any proof-finding strategy.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.Proof
    ( Proof(..), Step(..)
    , checkProof, explainProof, checkStep, showProof, showsProof, showsFormula )
where

import Swish.HaskellRDF.Ruleset
    ( Ruleset(..)
    , makeRuleset, getRulesetNamespace, getRulesetAxioms, getRulesetRules )

import Swish.HaskellRDF.Rule
    ( Expression(..), Formula(..), Rule(..)
    , fwdCheckInference
    , showsFormula, showsFormulae, showsWidth )

import Swish.HaskellUtils.Namespace
    ( Namespace(..)
    , ScopedName(..)
    , getScopePrefix, getScopeURI
    , getQName, getScopedNameURI )

import Swish.HaskellUtils.ShowM
    ( ShowM(..), showm )

import Swish.HaskellUtils.ListHelpers
    ( subset )

import Data.List
    ( union, intersect, intersperse )

import Data.Maybe
    ( isJust, fromJust, catMaybes )


------------------------------------------------------------
--  Proof framework
------------------------------------------------------------

-- |Step in proof chain
--
--  The display name for a proof step comes from the display name of its
--  consequence formula.
data Step ex = Step
    { stepRule :: Rule ex           -- ^ Inference rule used
    , stepAnt  :: [Formula ex]      -- ^ Antecedents of inference rule
    , stepCon  :: Formula ex        -- ^ Named consequence of inference rule
    } deriving Show

-- |Proof is a structure that presents a chain of rule applications
--  that yield a result expression from a given expression
data Proof ex = Proof
    { proofContext :: [Ruleset ex]  -- ^ Proof context:  list of rulesets,
                                    --   each of which provides a number of
                                    --   axioms and rules.
    , proofInput   :: Formula ex    -- ^ Given expression
    , proofResult  :: Formula ex    -- ^ Result expression
    , proofChain   :: [Step ex]     -- ^ Chain of inference rule applications
                                    --   progressing from input to result
    }

-- |Return a list of axioms from all the rulesets in a proof
proofAxioms = concat . map rsAxioms . proofContext

-- |Return a list of rules from all the rulesets in a proof
proofRules = concat . map rsRules . proofContext

-- |Return list of axioms actually referenced by a proof
proofAxiomsUsed :: Proof ex -> [Formula ex]
proofAxiomsUsed proof = foldl union [] $ map stepAxioms (proofChain proof)
    where
        stepAxioms st = stepAnt st `intersect` proofAxioms proof

-- |Check consistency of given proof.
--  The supplied rules and axioms are assumed to be correct.
checkProof :: (Expression ex) => Proof ex -> Bool
checkProof pr =
    checkProof1 (proofRules pr) initExpr (proofChain pr) goalExpr
    where
        initExpr = (formExpr $ proofInput pr):(map formExpr $ proofAxioms pr)
        goalExpr = (formExpr $ proofResult pr)

checkProof1 :: (Expression ex) => [Rule ex] -> [ex] -> [Step ex] -> ex -> Bool
checkProof1 _     prev []       res = res `elem` prev
checkProof1 rules prev (st:steps) res =
    checkStep rules prev st &&
    checkProof1 rules ((formExpr $ stepCon st):prev) steps res

--  A proof step is valid if rule is in list of rules
--  and the antecedents are sufficient to obtain the conclusion
--  and the antecedents are in the list of formulae already proven.
--
--  Note:  this function depends on the ruleName of any rule being
--  unique among all rules.  In particular the name of the step rule
--  being in correspondence with the name of one of the indicated
--  valid rules of inference.
checkStep :: (Expression ex) => [Rule ex] -> [ex] -> Step ex -> Bool
checkStep rules prev step =
    -- Rule name is one of supplied rules, and
    (ruleName srul `elem` map ruleName rules) &&
    -- Antecedent expressions are all previously accepted expressions
    (sant `subset` prev)   &&
    -- Inference rule yields concequence from antecendents
    checkInference srul sant scon
    where
        --  Rule from proof step:
        srul = stepRule step
        --  Antecedent expressions from proof step:
        sant = map formExpr $ stepAnt step
        --  Consequentent expression from proof step:
        scon = formExpr $ stepCon step


{-
    (formExpr (stepCon step) `elem` sfwd)
    -- (or $ map (`subset` sant) sbwd)
    where
        --  Rule from proof step:
        srul = stepRule step
        --  Antecedent expressions from proof step:
        sant = map formExpr $ stepAnt step
        --  Forward chaining from antecedents of proof step
        scon = map formExpr $ stepCon step
        --  Forward chaining from antecedents of proof step

        sfwd = fwdApply srul sant
        --  Backward chaining from consequent of proof step
        --  (Does not work because of introduction of existentials)
        sbwd = bwdApply srul (formExpr $ stepCon step)
-}

-- |Check proof, and return identification of failing step.
explainProof ::
    (Expression ex) => Proof ex -> Maybe String
explainProof pr =
    explainProof1 (proofRules pr) initExpr (proofChain pr) goalExpr
    where
        initExpr = (formExpr $ proofInput pr):(map formExpr $ proofAxioms pr)
        goalExpr = (formExpr $ proofResult pr)

explainProof1 ::
    (Expression ex) => [Rule ex] -> [ex] -> [Step ex] -> ex -> Maybe String
explainProof1 _     prev []       res   =
    if res `elem` prev then Nothing else Just "Result not demonstrated"
explainProof1 rules prev (st:steps) res =
    case explainStep rules prev st  of
        Nothing -> explainProof1 rules ((formExpr $ stepCon st):prev) steps res
        Just ex -> Just ("Invalid step: "++show (formName $ stepCon st)++": "++ex)

--  A proof step is valid if rule is in list of rules
--  and the antecedents are sufficient to obtain the conclusion
--  and the antecedents are in the list of formulae already proven.
--
--  Note:  this function depends on the ruleName of any rule being
--  unique among all rules.  In particular the name of the step rule
--  being in correspondence with the name of one of the indicated
--  valid rules of inference.
--
--  Return Nothing if step is OK, or Just string describing failure
--
explainStep :: (Expression ex) => [Rule ex] -> [ex] -> Step ex -> Maybe String
explainStep rules prev step =
        if null errors then Nothing else Just $ concat (intersperse ", " errors)
    where
        --  Rule from proof step:
        srul = stepRule step
        --  Antecedent expressions from proof step:
        sant = map formExpr $ stepAnt step
        --  Consequentent expression from proof step:
        scon = formExpr $ stepCon step
        --  Tests for step to be valid
        errors = catMaybes
            -- Rule name is one of supplied rules, and
            [ require (ruleName srul `elem` map ruleName rules)
                      ("rule "++show (ruleName srul)++" not present")
            -- Antecedent expressions are all previously accepted expressions
            , require (sant `subset` prev)
                      ("antecedent not axiom or previous result")
            -- Inference rule yields consequence from antecedents
            , require (checkInference srul sant scon)
                      ("rule does not deduce consequence from antecedents")
            ]
        require b s = if b then Nothing else Just s

-- |showsProof
--  Create a displayable form of a proof, returned as a ShowS value.
--
--  This function is intended to allow the calling function some control
--  of multiline displays by providing:
--  (1) the first line of the proof is not preceded by any text, so
--      it may be appended to some preceding text on the same line,
--  (2) the supplied newline string is used to separate lines of the
--      formatted text, and may include any desired indentation, and
--  (3) no newline is output following the final line of text.
showsProof :: (ShowM ex) => String -> Proof ex -> ShowS
showsProof newline proof =
    if null axioms then shProof else shAxioms . shProof
    where
        axioms = proofAxiomsUsed proof
        shAxioms =
            showString    ("Axioms:" ++ newline) .
            showsFormulae newline (proofAxiomsUsed proof) newline
        shProof =
            showString    ("Input:" ++ newline) .
            showsFormula  newline (proofInput  proof) .
            showString    (newline ++ "Proof:" ++ newline) .
            showsSteps    newline (proofChain  proof)

-- |showProof
--  Returns a simple string representation of a proof.
showProof :: (ShowM ex) => String -> Proof ex -> String
showProof newline proof = showsProof newline proof ""

-- |showsSteps
--  Create a displayable form of a list of labelled proof steps
showsSteps :: (ShowM ex) => String -> [Step ex] -> ShowS
showsSteps _       []     = id
showsSteps newline [s]    = showsStep  newline s
showsSteps newline (s:ss) = showsStep  newline s .
                            showString newline .
                            showsSteps newline ss

-- |showsStep
--  Create a displayable form of a labelled proof step.
showsStep :: (ShowM ex) => String -> Step ex -> ShowS
showsStep newline s = showsFormula newline (stepCon s) .
                      showString newline .
                      showString ("  (by ["++rulename++"] from "++antnames++")")
    where
        rulename = show . ruleName $ stepRule s
        antnames = showNames $ map (show . formName) (stepAnt s)

-- |showNames
--  Return a string containing a list of names.
showNames :: [String] -> String
showNames []      = "<nothing>"
showNames [n]     = showName n
showNames [n1,n2] = showName n1 ++ " and " ++ showName n2
showNames (n1:ns) = showName n1 ++ ", " ++ showNames ns

-- |showNames
--  Return a string representing a single name.
showName n = "["++n++"]"


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
-- $Source: /file/cvsdev/HaskellRDF/Proof.hs,v $
-- $Author: graham $
-- $Revision: 1.19 $
-- $Log: Proof.hs,v $
-- Revision 1.19  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.18  2003/12/18 18:27:47  graham
-- Datatyped literal inferences all working
-- (except equivalent literals with different datatypes)
--
-- Revision 1.17  2003/12/11 19:11:07  graham
-- Script processor passes all initial tests.
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
-- Revision 1.13  2003/07/02 13:51:14  graham
-- Intermediate save:  partially coded RDFS rules.
--
-- Revision 1.12  2003/07/01 14:20:30  graham
-- Added instance entailment to proof check module.
--
-- Revision 1.11  2003/06/27 20:46:00  graham
-- Coded initial version of RDF simple entailment rule.
-- New rule still needs testing, but other test cases still OK.
--
-- Revision 1.10  2003/06/26 15:37:23  graham
-- Added rdfQueryInstance, and tests, all works.
--
-- Revision 1.9  2003/06/25 21:16:53  graham
-- Reworked N3 formatting logic to support proof display.
-- Basic proof display is working.
--
-- Revision 1.8  2003/06/24 23:08:18  graham
-- Replaced Rule class with algebraic data type
--
-- Revision 1.7  2003/06/24 19:56:31  graham
-- Basic proof-check now works
--
-- Revision 1.6  2003/06/19 19:49:07  graham
-- RDFProofCheck compiles, but test fails
--
-- Revision 1.5  2003/06/18 18:40:08  graham
-- Basic proof backchaining tests OK.
-- Next:  add filtering on variable bindings.
--
-- Revision 1.4  2003/06/13 21:40:08  graham
-- Graph closure forward chaining works.
-- Backward chaining generates existentials.
-- Some problems with query logic for backward chaining.
--
-- Revision 1.3  2003/06/10 01:04:46  graham
-- Proof framework in progress;  compiles, incomplete
--
-- Revision 1.2  2003/06/04 00:49:53  graham
-- Proof module compiles OK
--
-- Revision 1.1  2003/06/03 19:24:54  graham
-- Started work on inference/proof module
--
