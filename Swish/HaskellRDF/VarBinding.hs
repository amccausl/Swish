{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XTypeSynonymInstances #-}
--------------------------------------------------------------------------------
--  $Id: VarBinding.hs,v 1.12 2004/01/07 19:49:13 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  VarBinding
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines functions for representing and manipulating query
--  binding variable sets.  This is the key data that mediates between
--  query and back substitution when performing inferences.  A framework
--  of query variable modifiers is provided that can be used to
--  implement richer inferences, such as filtering of  query results,
--  or replacing values based on known relationships.
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.VarBinding
    ( VarBinding(..), nullVarBinding
    , boundVars, subBinding, makeVarBinding
    , applyVarBinding, joinVarBindings, addVarBinding
    , VarBindingModify(..), OpenVarBindingModify
    , vbmCompatibility, vbmCompose
    , composeSequence, findCompositions, findComposition
    , VarBindingFilter(..)
    , makeVarFilterModify
    , makeVarTestFilter, makeVarCompareFilter
    , varBindingId, nullVarBindingModify
    , varFilterDisjunction, varFilterConjunction
    , varFilterEQ, varFilterNE
    )
where

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..) 
    , makeLookupMap, mapFindMaybe
    )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..) )

import Swish.HaskellRDF.Vocabulary
    ( swishName )

import Swish.HaskellUtils.ListHelpers
    ( equiv, subset, flist, headOrNothing, permutations )

import Data.Maybe
    ( catMaybes, fromMaybe, isJust, fromJust, listToMaybe )

import Data.List
    ( find, intersect, union, (\\) )


------------------------------------------------------------
--  Query variable bindings
------------------------------------------------------------

-- |VarBinding is the type of an arbitrary variable bindings
--  value, where the type of the bound values is not specified.
--
data VarBinding a b = VarBinding
    { vbMap  :: a -> Maybe b
    , vbEnum :: [(a,b)]
    , vbNull :: Bool
    }

-- |VarBinding is an instance of class Eq, so that variable
--  bindings can be compared for equivalence
--
instance (Eq a, Eq b) => Eq (VarBinding a b) where
    vb1 == vb2 = (vbEnum vb1) `equiv` (vbEnum vb2)

-- |VarBinding is an instance of class Show, so that variable
--  bindings can be displayed
--
instance (Show a, Show b) => Show (VarBinding a b) where
    show vb = show (vbEnum vb)

-- |nullVarBinding:  maps no query variables.
--
nullVarBinding :: VarBinding a b
nullVarBinding = VarBinding
    { vbMap  = const Nothing
    , vbEnum = []
    , vbNull = True
    }

-- |Return a list of the variables bound by a supplied variable binding
--
boundVars :: VarBinding a b -> [a]
boundVars = map fst . vbEnum

-- |VarBinding subset function, tests to see if one query binding
--  is a subset of another;  i.e. every query variable mapping defined
--  by one is also defined by the other.
--
subBinding :: (Eq a, Eq b) => (VarBinding a b) -> (VarBinding a b) -> Bool
subBinding vb1 vb2 = (vbEnum vb1) `subset` (vbEnum vb2)

-- |Function to make a variable binding from a list of
--  pairs of variable and corresponding assigned value.
--
makeVarBinding :: (Eq a, Show a, Eq b, Show b) => [(a,b)] -> VarBinding a b
makeVarBinding vrbs =
    if null vrbs then nullVarBinding -- (nullVarBinding :: VarBinding a b)
    else VarBinding
        { vbMap  = selectFrom vrbs
        , vbEnum = vrbs
        , vbNull = null vrbs
        }
    where
        selectFrom = flip mapFindMaybe . makeLookupMap
        --  selectFrom bs is the VarBinding lookup function
        {-
        selectFrom :: (Eq a) => [(a,b)] -> a -> Maybe b
        selectFrom []         _ = Nothing
        selectFrom ((v,r):bs) l = if l == v then Just r
                                    else selectFrom bs l
        -}

-- |Apply query binding to a supplied value, returning the value
--  unchanged if no binding is defined
--
applyVarBinding :: VarBinding a a -> a -> a
applyVarBinding vbind v = fromMaybe v (vbMap vbind v)

-- |Join a pair of query bindings, returning a new binding that
--  maps all variables recognized by either of the input bindings.
--  If the bindings should overlap, such overlap is not detected and
--  the value from the first binding provided is used arbitrarily.
--
joinVarBindings :: (Eq a) => VarBinding a b -> VarBinding a b -> VarBinding a b
joinVarBindings vb1 vb2
    | vbNull vb1 = vb2
    | vbNull vb2 = vb1
    | otherwise  = VarBinding
        { vbMap  = mv12
        , vbEnum = map (\v -> (v,fromJust (mv12 v))) bv12
        , vbNull = False
        }
    where
        -- flist fs a = map ($ a) fs;  see also monad function 'ap'
        mv12 = headOrNothing . filter isJust . flist [ vbMap vb1, vbMap vb2 ]
        bv12 = boundVars vb1 `union` boundVars vb2

-- |Add a single new value to a variable binding and return the resulting
--  new variable binding.
--
addVarBinding :: (Eq a, Show a, Eq b, Show b) => a -> b -> VarBinding a b
    -> VarBinding a b
addVarBinding lb val vbind = joinVarBindings vbind $ makeVarBinding [(lb,val)]

------------------------------------------------------------
--  Datatypes for variable binding modifiers
------------------------------------------------------------

-- |Define the type of a function to modify variable bindings in
--  forward chaining based on rule antecedent matches.  This
--  function is used to implement the "allocated to" logic described
--  in Appendix B of the RDF semantics document, in which a specific
--  blank node is associated with all matches of some specific value
--  by applications of the rule on a given graph.
--  Use 'id' if no modification of the variable bindings is required.
--
--  This datatype consists of the modifier function itself, which
--  operates on a list of variable bindings rather than a single
--  variable binding (because some modifications share context across
--  a set of bindings), and some additional descriptive information
--  that allows possible usage patterns to be analyzed.
--
--  Some usage patterns (see vbmUsage):
--  (a) filter:  all variables are input variables, and the effect
--      of the modifier function is to drop variable bindings that
--      don't satisfy some criterion.
--      Identifiable by an empty element in vbmUsage.
--  (b) source:  all variables are output variables:  a raw query
--      could be viewed as a source of variable bindings.
--      Identifiable by an element of vbmUsage equal to vbmVocab.
--  (c) modifier:  for each supplied variable binding, one or more
--      new variable bindings may be created that contain the
--      input variables bound as supplied plus some additional variables.
--      Identifiable by an element of vbmUsage some subset of vbmVocab.
--
--  A variety of variable usage patterns may be supported by a given
--  modifier:  a modifier may be used to define new variable bindings
--  from existing bindings in a number of ways, or simply to check that
--  some required relationship between bindings is satisfied.
--  (Example, for a + b = c, any one variable can be deduced from the
--  other two, or all three may be supplied to check that the relationship
--  does indeed hold.)
--
data VarBindingModify a b = VarBindingModify
    { vbmName   :: ScopedName
                            -- ^Name used to identify this variable binding
                            --  modifier when building inference rules.
    , vbmApply  :: [VarBinding a b] -> [VarBinding a b]
                            -- ^Apply variable binding modifier to a
                            --  list of variable bindings, returning a
                            --  new list.  The result list is not
                            --  necessarily the same length as the
                            --  supplied list.
    , vbmVocab  :: [a]      -- ^List of variables used by this modifier.
                            --  All results of applying this modifier contain
                            --  bindings for these variables.
    , vbmUsage  :: [[a]]    -- ^List of binding modifier usage patterns
                            --  supported.  Each pattern is characterized as
                            --  a list of variables for which new bindings
                            --  may be created by some application of this
                            --  modifier, assuming that bindings for all other
                            --  variables in vbmVocab are supplied.
    }

-- |Allow a VarBindingModify value to be accessed using a LookupMap.
--
instance LookupEntryClass
    (VarBindingModify a b) ScopedName (VarBindingModify a b)
    where
        keyVal   vbm     = (vbmName vbm,vbm)
        newEntry (_,vbm) = vbm

-- |Type for variable binding modifier that has yet to be instantiated
--  with respect to the variables that it operates upon.
--
type OpenVarBindingModify lb vn = [lb] -> VarBindingModify lb vn

-- |Extract variable binding name from OpenVarBindingModify value
--
--  (Because only the name is required, the application to an undefined
--  list of variable labels should never be evaluated, as long as the
--  name is not dependent on the variable names in any way.)
--
--  NOT QUITE... some of the functions that create OpenVarBindingModify
--  instances also pattern-match the number of labels provided, forcing
--  evaluation of the labels parameter, even though it's not used.
--
openVbmName :: OpenVarBindingModify lb vn -> ScopedName
openVbmName ovbm = vbmName (ovbm (error "Undefined labels in variable binding"))

-- |Allow an OpenVarBindingModify value to be accessed using a LookupMap.
--
instance LookupEntryClass
    (OpenVarBindingModify a b) ScopedName (OpenVarBindingModify a b)
    where
        keyVal   ovbm     = (openVbmName ovbm,ovbm)
        newEntry (_,ovbm) = ovbm

-- |Allow an OpenVarBindingModify value to be accessed using a LookupMap.
--
instance Show (OpenVarBindingModify a b)
    where
        show = show . openVbmName

-- |Variable binding modifier compatibility test.
--
--  Given a list of bound variables and a variable binding modifier, return
--  a list of new variables that may be bound, or Nothing.
--
--  Note:  if the usage pattern component is well-formed (i.e. all
--  elements different) then at most one element can be compatible with
--  a given input variable set.
--
vbmCompatibility :: (Eq a) => VarBindingModify a b -> [a] -> Maybe [a]
vbmCompatibility vbm vars = find compat (vbmUsage vbm)
    where
        compat ovars = vbmCompatibleVars vars (vbmVocab vbm) ovars

-- |Variable binding usage compatibility test.
--
--  bvars   are variables supplied with bindings
--  vocab   are variables returned with bindings by a modifier
--  ovars   are variables assigned new bindings by a modifier
--
--  Returns True if the supplied variable bindings can be compatibly
--  processed by a variable binding usage with supplied vocabulary and
--  usage pattern.
--
vbmCompatibleVars :: (Eq a) => [a] -> [a] -> [a] -> Bool
vbmCompatibleVars bvars vocab ovars =
    null (ivars `intersect` ovars) &&       -- ivars and ovars don't overlap
    null ((vocab \\ ovars) \\ ivars)        -- ovars and ivars cover vocab
    where
        ivars = bvars `intersect` vocab

-- |Compose variable binding modifiers.
--
--  Returns Just a new variable binding modifier that corresponds to
--  applying the first supplied modifier and then applying the second
--  one, or Nothing if the two modifiers cannot be compatibly composed.
--
--  NOTE:  this function does not, in general, commute.
--
--  NOTE:  if there are different ways to achieve the same usage, that
--  usage is currently repeated in the result returned.
--
vbmCompose :: (Eq a) => VarBindingModify a b -> VarBindingModify a b
    -> Maybe (VarBindingModify a b)
vbmCompose
    (VarBindingModify nam1 app1 voc1 use1)
    (VarBindingModify nam2 app2 voc2 use2)
    | not (null use12) = Just $ VarBindingModify
        { vbmName  = swishName ("_"++(snLocal nam1)++"_"++(snLocal nam2)++"_")
        , vbmApply = app2 . app1
        , vbmVocab = voc1 `union` voc2
        , vbmUsage = use12
        }
    | otherwise = Nothing
    where
        use12 = compatibleUsage voc1 use1 use2

-- |Determine compatible ways in which variable binding modifiers may
--  be combined.
--
--  voc1    is the total vocabulary of the first modifier to be applied
--  use1    is a list of usage patterns for the first modifier.
--  use2    is a list of usage patterns for the second modifier.
--
--  Returns a list of possible usage patterns for the composition of
--  the first modifier with the second modifier, or an empty list if
--  the modifiers are incompatible.
--
--  The total vocabulary of a modifier is the complete set of variables
--  that are used or bound by the modifier.  After the modifier has been
--  applied, bindings must exist for all of these variables.
--
--  A usage pattern of a modifier is a set of variables for which new
--  bindings may be generated by the modifier.
--
--  The only way in which two variable binding modifiers can be incompatible
--  with each other is when they both attempt to create a new binding for
--  the same variable.  (Note that this does not mean the composition will
--  be compatible with all inputs:  see vbmCompatibleVars above.)
--
--  NOTE:  if there are different ways to achieve the same usage, that
--  usage is currently repeated in the result returned.
--
compatibleUsage :: (Eq a) => [a] -> [[a]] -> [[a]] -> [[a]]
compatibleUsage voc1 use1 use2 =
    [ u1++u2 | u2 <- use2, null (voc1 `intersect` u2), u1 <- use1 ]

-- |Find all compatible compositions of a list of variable binding
--  modifiers for a given set of supplied bound variables.
findCompositions :: (Eq a) => [VarBindingModify a b] -> [a]
    -> [VarBindingModify a b]
findCompositions vbms vars =
    catMaybes $ map (composeCheckSequence vars) (permutations vbms)

-- |Compose sequence of variable binding modifiers, and check
--  that the result can be used compatibly with a supplied list
--  of bound variables, returning Just (composed modifier), or Nothing
--
composeCheckSequence :: (Eq a) => [a] -> [VarBindingModify a b]
    -> Maybe (VarBindingModify a b)
composeCheckSequence vars vbms = useWith vars $ composeSequence vbms
    where
        --  Check that a Maybe modifier is compatible for use with an
        --  indicated set of bound variables, and return (Just modifier)
        --  or Nothing.
        useWith _    Nothing    = Nothing
        useWith vars (Just vbm)
            | isJust $ vbmCompatibility vbm vars = (Just vbm)
            | otherwise                          = Nothing

-- |Compose sequence of variable binding modifiers.
--
composeSequence :: (Eq a) => [VarBindingModify a b]
    -> Maybe (VarBindingModify a b)
composeSequence [] = Just varBindingId
composeSequence (vbm:vbms) =
    foldl composePair (Just vbm) vbms

-- |Compose a pair of variable binding modifiers, returning
--  Just (composed modifier), or Nothing
--
composePair :: (Eq a) => Maybe (VarBindingModify a b) -> VarBindingModify a b
    -> Maybe (VarBindingModify a b)
composePair Nothing     _    = Nothing
composePair (Just vbm1) vbm2 = vbmCompose vbm1 vbm2

-- |Return Just a compatible composition of variable binding modifiers
--  for a given set of supplied bound variables, or Nothing if there
--  is no compatible composition
--
findComposition :: (Eq a) => [VarBindingModify a b] -> [a]
    -> Maybe (VarBindingModify a b)
findComposition = listToMaybe `c2` findCompositions
    where
        c2 = (.) . (.)  -- compose with function of two arguments

-- |Variable binding modifier that returns exactly those
--  variable bindings presented.
--
varBindingId :: VarBindingModify a b
varBindingId = VarBindingModify
    { vbmName   = swishName "varBindingId"
    , vbmApply  = id
    , vbmVocab  = []
    , vbmUsage  = [[]]
    }

-- |Null variable binding modifier
--
--  This is like varBindingId except parameterized by some labels.
--  I think this is redundant, and should be eliminated.
--
nullVarBindingModify :: OpenVarBindingModify a b
nullVarBindingModify lbs = VarBindingModify
    { vbmName   = swishName "nullVarBindingModify"
    , vbmApply  = id
    , vbmVocab  = lbs
    , vbmUsage  = [[]]
    }

------------------------------------------------------------
--  Query binding filters
------------------------------------------------------------

-- |VarBindingFilter is a function type that tests to see if
--  a query binding satisfies some criterion.
--
--  Queries often want to apply some kind of filter or condition
--  to the variable bindings that are processed.  In inference rules,
--  it sometimes seems desirable to stipulate additional conditions on
--  the things that are matched.
--
--  This function type is used to perform such tests.
--  A number of simple implementations are included below.
data VarBindingFilter a b = VarBindingFilter
    { vbfName   :: ScopedName
    , vbfVocab  :: [a]
    , vbfTest   :: (VarBinding a b) -> Bool
    }

-- |Make a variable binding modifier from a variable binding filter value.
makeVarFilterModify :: VarBindingFilter a b -> VarBindingModify a b
makeVarFilterModify vbf = VarBindingModify
    { vbmName   = vbfName vbf
    , vbmApply  = filter (vbfTest vbf)
    , vbmVocab  = vbfVocab vbf
    , vbmUsage  = [[]]
    }

-- |Make a variable test filter for a named variable using a
--  supplied value testing function.
makeVarTestFilter ::
    ScopedName -> (b -> Bool) -> a -> VarBindingFilter a b
makeVarTestFilter nam vtest var = VarBindingFilter
    { vbfName   = nam
    , vbfVocab  = [var]
    , vbfTest   = \vb -> case vbMap vb var of
                    Just val  -> vtest val
                    _         -> False
    }

-- |Make a variable comparison filter for named variables using
--  a supplied value comparison function.
makeVarCompareFilter ::
    ScopedName -> (b -> b -> Bool) -> a -> a -> VarBindingFilter a b
makeVarCompareFilter nam vcomp v1 v2 = VarBindingFilter
    { vbfName   = nam
    , vbfVocab  = [v1,v2]
    , vbfTest   = \vb -> case (vbMap vb v1,vbMap vb v2) of
                    (Just val1, Just val2) -> vcomp val1 val2
                    _                      -> False
    }

------------------------------------------------------------
--  Declare some generally useful query binding filters
------------------------------------------------------------

-- |This function generates a query binding filter that ensures that
--  two indicated query variables are mapped to the same value.
varFilterEQ :: (Eq b) => a -> a -> VarBindingFilter a b
varFilterEQ v1 v2 =
    makeVarCompareFilter (swishName "varFilterEQ") (==) v1 v2

-- |This function generates a query binding filter that ensures that
--  two indicated query variables are mapped to different values.
varFilterNE :: (Eq b) => a -> a -> VarBindingFilter a b
varFilterNE v1 v2 =
    makeVarCompareFilter (swishName "varFilterNE") (/=) v1 v2

-- |This function composes a number of query binding filters
--  into a composite filter that accepts any query binding that
--  satisfies at least one of the component values.
varFilterDisjunction :: (Eq a) => [VarBindingFilter a b]
    -> VarBindingFilter a b
varFilterDisjunction vbfs = VarBindingFilter
    { vbfName   = swishName "varFilterDisjunction"
    , vbfVocab  = foldl1 union (map vbfVocab vbfs)
    , vbfTest   = or . flist (map vbfTest vbfs)
    }

-- |This function composes a number of query binding filters
--  into a composite filter that accepts any query binding that
--  satisfies all of the component values.
--
--  The same function could be achieved by composing the component
--  filter-based modifiers, but this function is more convenient
--  as it avoids the need to check for modifier compatibility.
--
varFilterConjunction :: (Eq a) => [VarBindingFilter a b]
    -> VarBindingFilter a b
varFilterConjunction vbfs = VarBindingFilter
    { vbfName   = swishName "varFilterConjunction"
    , vbfVocab  = foldl1 union (map vbfVocab vbfs)
    , vbfTest   = and . flist (map vbfTest vbfs)
    }

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
-- $Source: /file/cvsdev/HaskellRDF/VarBinding.hs,v $
-- $Author: graham $
-- $Revision: 1.12 $
-- $Log: VarBinding.hs,v $
-- Revision 1.12  2004/01/07 19:49:13  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.11  2003/12/10 03:48:58  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.10  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.9  2003/12/08 17:29:19  graham
-- Moved OpenVarBinding type definitions from -Datatype to -VarBinding modules.
--
-- Revision 1.8  2003/12/08 16:58:27  graham
-- Add name to variable binding modifiers and filters.
-- Add namespace for Swish-defined names.
--
-- Revision 1.7  2003/12/04 02:53:28  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.6  2003/10/24 21:05:08  graham
-- Working on datatype inference.  Most of the variable binding logic
-- is done, but the rule structure still needs to be worked out to support
-- forward and backward chaining through the same rule.
--
-- Revision 1.5  2003/10/22 15:47:46  graham
-- Working on datatype inference support.
--
-- Revision 1.4  2003/10/16 16:01:49  graham
-- Reworked RDFProof and RDFProofContext to use new query binding
-- framework.  Also fixed a bug in the variable binding filter code that
-- caused failures when a variable used was not bound.
--
-- Revision 1.3  2003/10/15 16:40:52  graham
-- Reworked RDFQuery to use new query binding framework.
-- (Note: still uses VarBindingFilter rather than VarBindingModify.
-- The intent is to incorproate the VarBindingModify logic into RDFProof,
-- displaying the existing use of BindingFilter.)
--
-- Revision 1.2  2003/10/15 00:07:01  graham
-- Added variable binding filter structures, and some common filters
--
-- Revision 1.1  2003/10/14 20:30:58  graham
-- Add separate module for generic variable binding functions.
--
